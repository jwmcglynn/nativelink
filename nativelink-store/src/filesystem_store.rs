// Copyright 2024 The NativeLink Authors. All rights reserved.
//
// Licensed under the Functional Source License, Version 1.1, Apache 2.0 Future License (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    See LICENSE file for details
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use core::fmt::{Debug, Formatter};
use core::hash::Hash;
use core::pin::Pin;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use core::time::Duration;
use std::borrow::Cow;
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::sync::{Arc, Weak};
use std::time::SystemTime;

use async_lock::{Mutex, RwLock};
use async_trait::async_trait;
use bytes::{Bytes, BytesMut};
use futures::stream::{StreamExt, TryStreamExt};
use futures::{Future, TryFutureExt};
use nativelink_config::stores::FilesystemSpec;
use nativelink_error::{Code, Error, ErrorContext, ResultExt, make_err};
use nativelink_metric::MetricsComponent;
use nativelink_util::background_spawn;
use nativelink_util::buf_channel::{
    DropCloserReadHalf, DropCloserWriteHalf, make_buf_channel_pair,
};
use nativelink_util::common::{DigestInfo, fs};
use nativelink_util::evicting_map::{EvictingMap, EvictionSnapshot, LenEntry};
use nativelink_util::fs::FileSlot;
use nativelink_util::health_utils::{HealthRegistryBuilder, HealthStatus, HealthStatusIndicator};
#[cfg(unix)]
use nativelink_util::spawn_blocking;
use nativelink_util::store_trait::{
    RemoveItemCallback, StoreDriver, StoreKey, StoreKeyBorrow, StoreOptimizations, UploadSizeInfo,
};
use tokio::io::{AsyncReadExt, AsyncWriteExt, Take};
use tokio::sync::Semaphore;
use tokio::time::timeout;
use tokio_stream::wrappers::ReadDirStream;
use tracing::{debug, error, trace, warn};

use crate::callback_utils::RemoveItemCallbackHolder;
use crate::cas_utils::is_zero_digest;

// Default size to allocate memory of the buffer when reading files.
const DEFAULT_BUFF_SIZE: usize = 32 * 1024;
// Default block size of all major filesystems is 4KB
const DEFAULT_BLOCK_SIZE: u64 = 4 * 1024;

pub const STR_FOLDER: &str = "s";
pub const DIGEST_FOLDER: &str = "d";

/// Suffix for the sibling directory that holds per-digest read-only
/// **executable** (0o555) variants of CAS blobs (see
/// [`FilesystemStore::with_executable_hardlink_source`]). It is a sibling of
/// `content_path` rather than a child so the normal content/temp scan and prune
/// logic never touches it. Cleared on startup; entries are regenerable.
#[cfg(unix)]
const EXECUTABLE_DIR_SUFFIX: &str = ".exec";

type KeyLocks<K> = Arc<std::sync::Mutex<HashMap<K, Arc<Mutex<()>>>>>;

struct KeyLockRegistration<K: Clone + Eq + Hash> {
    locks: KeyLocks<K>,
    key: K,
    lock: Arc<Mutex<()>>,
}

impl<K: Clone + Eq + Hash> KeyLockRegistration<K> {
    fn new(locks: &KeyLocks<K>, key: K) -> Self {
        let lock = locks
            .lock()
            .expect("key lock registry poisoned")
            .entry(key.clone())
            .or_insert_with(|| Arc::new(Mutex::new(())))
            .clone();
        Self {
            locks: Arc::clone(locks),
            key,
            lock,
        }
    }

    async fn lock(&self) -> async_lock::MutexGuard<'_, ()>
    where
        K: Send + Sync,
    {
        self.lock.lock().await
    }
}

impl<K: Clone + Eq + Hash> Drop for KeyLockRegistration<K> {
    fn drop(&mut self) {
        let mut locks = self.locks.lock().expect("key lock registry poisoned");
        if let Some(current) = locks.get(&self.key) {
            // Every waiter clones its lock while holding this registry mutex.
            if Arc::ptr_eq(current, &self.lock) && Arc::strong_count(&self.lock) == 2 {
                locks.remove(&self.key);
            }
        }
    }
}

#[cfg(unix)]
type ExecutableLocks = KeyLocks<DigestInfo>;
#[cfg(unix)]
type ExecutableLockRegistration = KeyLockRegistration<DigestInfo>;
type PathOwner = Weak<RwLock<EncodedFilePath>>;

#[cfg(unix)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExecutableCreation {
    Ready,
    Superseded,
}

#[cfg(test)]
type ExecutablePause = (
    tokio::sync::oneshot::Sender<()>,
    tokio::sync::oneshot::Receiver<()>,
);

#[cfg(unix)]
#[derive(Debug)]
struct PendingExecutable {
    owner: PathOwner,
    path: OsString,
}

#[cfg(all(test, unix))]
mod executable_lock_registration_tests {
    use super::*;
    use futures::FutureExt;

    const TEST_HASH: &str = "0123456789abcdef000000000000000000010000000000000123456789abcdef";

    fn test_digest() -> DigestInfo {
        DigestInfo::try_new(TEST_HASH, 1).expect("valid test digest")
    }

    fn lock_count(locks: &ExecutableLocks) -> usize {
        locks.lock().expect("executable_locks poisoned").len()
    }

    #[test]
    fn completed_registration_removes_idle_lock() {
        let locks = Arc::new(std::sync::Mutex::new(HashMap::new()));
        futures::executor::block_on(async {
            let registration = ExecutableLockRegistration::new(&locks, test_digest());
            let guard = registration.lock().await;
            assert_eq!(lock_count(&locks), 1);
            drop(guard);
            drop(registration);
        });
        assert_eq!(lock_count(&locks), 0);
    }

    #[test]
    fn failed_registration_removes_idle_lock() {
        let locks = Arc::new(std::sync::Mutex::new(HashMap::new()));
        let result = futures::executor::block_on(async {
            let registration = ExecutableLockRegistration::new(&locks, test_digest());
            let _guard = registration.lock().await;
            Err::<(), ()>(())
        });
        assert!(result.is_err());
        assert_eq!(lock_count(&locks), 0);
    }

    #[test]
    fn canceled_waiter_preserves_then_removes_shared_lock() {
        let locks = Arc::new(std::sync::Mutex::new(HashMap::new()));
        let owner = ExecutableLockRegistration::new(&locks, test_digest());
        let owner_guard = futures::executor::block_on(owner.lock());
        let waiter = ExecutableLockRegistration::new(&locks, test_digest());

        let waiting = async move {
            let _guard = waiter.lock().await;
        };
        assert!(waiting.now_or_never().is_none());
        assert_eq!(lock_count(&locks), 1);

        drop(owner_guard);
        drop(owner);
        assert_eq!(lock_count(&locks), 0);
    }
}

#[derive(Clone, Copy, Debug)]
pub enum FileType {
    Digest,
    String,
}

#[derive(Debug, MetricsComponent)]
pub struct SharedContext {
    // Used in testing to know how many active drop() spawns are running.
    // TODO(palfrey) It is probably a good idea to use a spin lock during
    // destruction of the store to ensure that all files are actually
    // deleted (similar to how it is done in tests).
    #[metric(help = "Number of active drop spawns")]
    pub active_drop_spawns: AtomicU64,
    #[metric(help = "Path to the configured temp path")]
    temp_path: String,
    #[metric(help = "Path to the configured content path")]
    content_path: String,
    content_locks: KeyLocks<StoreKey<'static>>,
    content_owners: std::sync::Mutex<HashMap<StoreKey<'static>, PathOwner>>,
    #[cfg(unix)]
    executable_locks: ExecutableLocks,
    #[cfg(unix)]
    executable_owners: std::sync::Mutex<HashMap<DigestInfo, PathOwner>>,
    #[cfg(unix)]
    pending_executables: std::sync::Mutex<HashMap<DigestInfo, PendingExecutable>>,
    /// A failed private-temp cleanup requires filesystem recovery and reopening the store.
    /// Already-admitted writes may finish; this is not a physical peak-byte limit.
    write_admission_failed: AtomicBool,
    #[cfg(test)]
    retirement_observer: std::sync::Mutex<Option<tokio::sync::oneshot::Sender<()>>>,
    #[cfg(test)]
    executable_reservation_pause: std::sync::Mutex<Option<ExecutablePause>>,
    #[cfg(test)]
    executable_ready_pause: std::sync::Mutex<Option<ExecutablePause>>,
}

impl SharedContext {
    fn stop_new_allocations(&self) {
        if !self.write_admission_failed.swap(true, Ordering::AcqRel) {
            warn!(
                "Unreclaimed filesystem allocation prevents new allocations; recover the filesystem and reopen the store"
            );
        }
    }

    fn check_write_admission(&self) -> Result<(), Error> {
        if self.write_admission_failed.load(Ordering::Acquire) {
            return Err(make_err!(
                Code::ResourceExhausted,
                "Unreclaimed filesystem allocation prevents new allocations; recover the filesystem and reopen the store"
            ));
        }
        Ok(())
    }
}

#[derive(Eq, PartialEq, Debug)]
enum PathType {
    Content,
    Temp,
    Custom(OsString),
}

/// [`EncodedFilePath`] stores the path to the file
/// including the context, path type and key to the file.
/// The whole [`StoreKey`] is stored as opposed to solely
/// the [`DigestInfo`] so that it is more usable for things
/// such as BEP -see Issue #1108
#[derive(Debug)]
pub struct EncodedFilePath {
    shared_context: Arc<SharedContext>,
    path_type: PathType,
    key: StoreKey<'static>,
    registered_key: Option<StoreKey<'static>>,
}

impl EncodedFilePath {
    #[inline]
    fn get_file_path(&self) -> Cow<'_, OsStr> {
        get_file_path_raw(&self.path_type, self.shared_context.as_ref(), &self.key)
    }
}

#[inline]
fn get_file_path_raw<'a>(
    path_type: &'a PathType,
    shared_context: &SharedContext,
    key: &StoreKey<'a>,
) -> Cow<'a, OsStr> {
    let folder = match path_type {
        PathType::Content => &shared_context.content_path,
        PathType::Temp => &shared_context.temp_path,
        PathType::Custom(path) => return Cow::Borrowed(path),
    };
    Cow::Owned(to_full_path_from_key(folder, key))
}

impl Drop for EncodedFilePath {
    fn drop(&mut self) {
        if let Some(key) = &self.registered_key {
            let mut owners = self
                .shared_context
                .content_owners
                .lock()
                .expect("content owner registry poisoned");
            if owners
                .get(key)
                .is_some_and(|owner| owner.strong_count() == 0)
            {
                owners.remove(key);
            }
        }
        #[cfg(unix)]
        if let Some(StoreKey::Digest(digest)) = &self.registered_key {
            let mut owners = self
                .shared_context
                .executable_owners
                .lock()
                .expect("executable owner registry poisoned");
            if owners
                .get(digest)
                .is_some_and(|owner| owner.strong_count() == 0)
            {
                owners.remove(digest);
            }
        }
        // `drop()` can be called during shutdown, so we use `path_type` flag to know if the
        // file actually needs to be deleted.
        if self.path_type == PathType::Content {
            return;
        }

        let file_path = self.get_file_path().to_os_string();
        let shared_context = self.shared_context.clone();
        // .fetch_add returns previous value, so we add one to get approximate current value
        let current_active_drop_spawns = shared_context
            .active_drop_spawns
            .fetch_add(1, Ordering::Relaxed)
            + 1;
        debug!(
            %current_active_drop_spawns,
            ?file_path,
            "Spawned a filesystem_delete_file"
        );
        background_spawn!("filesystem_delete_file", async move {
            match fs::remove_file(&file_path).await {
                Ok(()) => debug!(?file_path, "File deleted"),
                // The file already being gone is the desired end state of a
                // delete, not a failure — e.g. an entry marked Temp after an
                // already-gone unref points at a path that was never created.
                Err(err) if err.code == Code::NotFound => {
                    debug!(?file_path, "File already gone, nothing to delete");
                }
                Err(err) => {
                    shared_context.stop_new_allocations();
                    error!(?file_path, ?err, "Failed to delete file");
                }
            }
            // .fetch_sub returns previous value, so we subtract one to get approximate current value
            let current_active_drop_spawns = shared_context
                .active_drop_spawns
                .fetch_sub(1, Ordering::Relaxed)
                - 1;
            debug!(
                ?current_active_drop_spawns,
                ?file_path,
                "Dropped a filesystem_delete_file"
            );
        });
    }
}

fn current_content_owner(
    context: &SharedContext,
    key: &StoreKey<'static>,
) -> Option<Arc<RwLock<EncodedFilePath>>> {
    let owner = context
        .content_owners
        .lock()
        .expect("content owner registry poisoned")
        .get(key)
        .cloned();
    owner.and_then(|owner| owner.upgrade())
}

async fn publish_file_generation<Fe: FileEntry>(
    map: &Arc<FsEvictingMap<'_, Fe>>,
    key: &StoreKey<'static>,
    entry: &Arc<Fe>,
    rename_fn: fn(&OsStr, &OsStr) -> Result<(), std::io::Error>,
) -> Result<(), Error> {
    let path = entry.get_encoded_file_path();
    let context = Arc::clone(&path.read().await.shared_context);
    let registration = KeyLockRegistration::new(&context.content_locks, key.clone());
    let _gate = registration.lock().await;
    if !map.contains_if(key, |current| Arc::ptr_eq(current, entry)) {
        return Ok(());
    }
    // Never upgrade a Weak under its registry mutex: the last Arc's Drop takes that mutex.
    if let Some(previous) = current_content_owner(&context, key)
        && !Arc::ptr_eq(&previous, path)
    {
        let mut encoded = previous.write().await;
        retire_locked_path(&mut encoded, &Arc::downgrade(&previous)).await?;
    }
    let mut encoded = path.write().await;
    let from = encoded.get_file_path().into_owned();
    let to = get_file_path_raw(&PathType::Content, &context, key).into_owned();
    if !map.contains_if(key, |current| Arc::ptr_eq(current, entry)) {
        return Ok(());
    }
    rename_fn(&from, &to).err_tip(|| "Failed to publish content generation")?;
    encoded.path_type = PathType::Content;
    encoded.key = key.clone();
    context
        .content_owners
        .lock()
        .expect("content owner registry poisoned")
        .insert(key.clone(), Arc::downgrade(path));
    Ok(())
}

/// This creates the file path from the [`StoreKey`]. If
/// it is a string, the string, prefixed with [`STR_PREFIX`]
/// for backwards compatibility, is stored.
///
/// If it is a [`DigestInfo`], it is prefixed by [`DIGEST_PREFIX`]
/// followed by the string representation of a digest - the hash in hex,
/// a hyphen then the size in bytes
///
/// Previously, only the string representation of the [`DigestInfo`] was
/// used with no prefix
#[inline]
fn to_full_path_from_key(folder: &str, key: &StoreKey<'_>) -> OsString {
    match key {
        StoreKey::Str(str) => format!("{folder}/{STR_FOLDER}/{str}"),
        StoreKey::Digest(digest_info) => format!("{folder}/{DIGEST_FOLDER}/{digest_info}"),
    }
    .into()
}

pub trait FileEntry: LenEntry + Send + Sync + Debug + 'static {
    /// Responsible for creating the underlying `FileEntry`.
    fn create(data_size: u64, block_size: u64, encoded_file_path: RwLock<EncodedFilePath>) -> Self;

    /// Creates a (usually) temp file, opens it and returns the path to the temp file.
    fn make_and_open_file(
        block_size: u64,
        encoded_file_path: EncodedFilePath,
    ) -> impl Future<Output = Result<(Self, FileSlot, OsString), Error>> + Send
    where
        Self: Sized;

    /// Returns the underlying size of the data in bytes
    fn data_size(&self) -> u64;

    /// Returns the underlying reference to the size of the data in bytes
    fn data_size_mut(&mut self) -> &mut u64;

    /// Returns the actual size of the underlying file on the disk after accounting for filesystem block size.
    fn size_on_disk(&self) -> u64;

    /// Gets the underlying `EncodedfilePath`.
    fn get_encoded_file_path(&self) -> &Arc<RwLock<EncodedFilePath>>;

    /// Returns a reader that will read part of the underlying file.
    fn read_file_part(
        &self,
        offset: u64,
        length: u64,
    ) -> impl Future<Output = Result<Take<FileSlot>, Error>> + Send;

    /// This function is a safe way to extract the file name of the underlying file. To protect users from
    /// accidentally creating undefined behavior we encourage users to do the logic they need to do with
    /// the filename inside this function instead of extracting the filename and doing the logic outside.
    /// This is because the filename is not guaranteed to exist after this function returns, however inside
    /// the callback the file is always guaranteed to exist and immutable.
    /// DO NOT USE THIS FUNCTION TO EXTRACT THE FILENAME AND STORE IT FOR LATER USE.
    fn get_file_path_locked<
        T,
        Fut: Future<Output = Result<T, Error>> + Send,
        F: FnOnce(OsString) -> Fut + Send,
    >(
        &self,
        handler: F,
    ) -> impl Future<Output = Result<T, Error>> + Send;
}

pub struct FileEntryImpl {
    shared_context: Arc<SharedContext>,
    data_size: u64,
    block_size: u64,
    // We lock around this as it gets rewritten when we move between temp and content types
    encoded_file_path: Arc<RwLock<EncodedFilePath>>,
}

impl FileEntryImpl {
    pub fn get_shared_context_for_test(&mut self) -> Arc<SharedContext> {
        Arc::clone(&self.shared_context)
    }
}

impl FileEntry for FileEntryImpl {
    fn create(
        data_size: u64,
        block_size: u64,
        mut encoded_file_path: RwLock<EncodedFilePath>,
    ) -> Self {
        let shared_context = Arc::clone(&encoded_file_path.get_mut().shared_context);
        let initial_owner = {
            let path = encoded_file_path.get_mut();
            (path.path_type == PathType::Content)
                .then(|| (Arc::clone(&path.shared_context), path.key.clone()))
        };
        let encoded_file_path = Arc::new(encoded_file_path);
        if let Some((context, key)) = initial_owner {
            context
                .content_owners
                .lock()
                .expect("content owner registry poisoned")
                .insert(key, Arc::downgrade(&encoded_file_path));
        }
        Self {
            shared_context,
            data_size,
            block_size,
            encoded_file_path,
        }
    }

    /// This encapsulates the logic for the edge case of if the file fails to create
    /// the cleanup of the file is handled without creating a `FileEntry`, which would
    /// try to cleanup the file as well during `drop()`.
    async fn make_and_open_file(
        block_size: u64,
        encoded_file_path: EncodedFilePath,
    ) -> Result<(Self, FileSlot, OsString), Error> {
        let temp_full_path = encoded_file_path.get_file_path().to_os_string();
        let temp_file_result = fs::create_file(temp_full_path.clone())
            .or_else(|mut err| async {
                let remove_result = fs::remove_file(&temp_full_path).await.err_tip(|| {
                    format!(
                        "Failed to remove file {} in filesystem store",
                        temp_full_path.display()
                    )
                });
                if let Err(remove_err) = remove_result {
                    err = err.merge(remove_err);
                }
                warn!(?err, ?block_size, ?temp_full_path, "Failed to create file",);
                Err(err).err_tip(|| {
                    format!(
                        "Failed to create {} in filesystem store",
                        temp_full_path.display()
                    )
                })
            })
            .await?;

        Ok((
            <Self as FileEntry>::create(
                0, /* Unknown yet, we will fill it in later */
                block_size,
                RwLock::new(encoded_file_path),
            ),
            temp_file_result,
            temp_full_path,
        ))
    }

    fn data_size(&self) -> u64 {
        self.data_size
    }

    fn data_size_mut(&mut self) -> &mut u64 {
        &mut self.data_size
    }

    fn size_on_disk(&self) -> u64 {
        self.data_size.div_ceil(self.block_size) * self.block_size
    }

    fn get_encoded_file_path(&self) -> &Arc<RwLock<EncodedFilePath>> {
        &self.encoded_file_path
    }

    fn read_file_part(
        &self,
        offset: u64,
        length: u64,
    ) -> impl Future<Output = Result<Take<FileSlot>, Error>> + Send {
        self.get_file_path_locked(move |full_content_path| async move {
            let file = fs::open_file(&full_content_path, offset, length)
                .await
                .err_tip(|| {
                    format!(
                        "Failed to open file in filesystem store {}",
                        full_content_path.display()
                    )
                })?;
            Ok(file)
        })
    }

    async fn get_file_path_locked<
        T,
        Fut: Future<Output = Result<T, Error>> + Send,
        F: FnOnce(OsString) -> Fut + Send,
    >(
        &self,
        handler: F,
    ) -> Result<T, Error> {
        let encoded_file_path = self.get_encoded_file_path().read().await;
        handler(encoded_file_path.get_file_path().to_os_string()).await
    }
}

impl Debug for FileEntryImpl {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("FileEntryImpl")
            .field("data_size", &self.data_size)
            .field("encoded_file_path", &"<behind mutex>")
            .finish()
    }
}

fn make_temp_digest(mut digest: DigestInfo) -> DigestInfo {
    static DELETE_FILE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let mut hash = *digest.packed_hash();
    hash[24..].clone_from_slice(
        &DELETE_FILE_COUNTER
            .fetch_add(1, Ordering::Relaxed)
            .to_le_bytes(),
    );
    digest.set_packed_hash(*hash);
    digest
}

pub fn make_temp_key(key: &StoreKey) -> StoreKey<'static> {
    StoreKey::Digest(make_temp_digest(key.borrow().into_digest()))
}

impl LenEntry for FileEntryImpl {
    #[inline]
    fn len(&self) -> u64 {
        self.size_on_disk()
    }

    fn is_empty(&self) -> bool {
        self.data_size == 0
    }

    fn on_remove(&self) -> impl Future<Output = ()> + Send + 'static {
        let path = Arc::clone(&self.encoded_file_path);
        // Start owned work before returning; dropping a caller cannot skip retirement.
        let task = background_spawn!("filesystem_store_retire_generation", async move {
            let context = Arc::clone(&path.read().await.shared_context);
            #[cfg(unix)]
            let key = path.read().await.registered_key.clone();
            if let Err(err) = retire_file_path(&path).await {
                context.stop_new_allocations();
                warn!(?err, "Failed to retire removed file generation");
            }
            #[cfg(unix)]
            if let Some(StoreKey::Digest(digest)) = key {
                remove_executable_generation(&context, digest, &path).await;
            }
            #[cfg(test)]
            {
                let sender = context
                    .retirement_observer
                    .lock()
                    .expect("retirement observer poisoned")
                    .take();
                if let Some(sender) = sender {
                    let _ = sender.send(());
                }
            }
        });
        async move {
            if let Err(err) = task.await {
                warn!(?err, "File generation retirement task failed");
            }
        }
    }

    async fn unref(&self) {
        if let Err(err) = retire_file_path(&self.encoded_file_path).await {
            self.shared_context.stop_new_allocations();
            warn!(?err, "Failed to retire file generation");
        }
    }
}

fn forget_content_owner(context: &SharedContext, key: &StoreKey<'static>, owner: &PathOwner) {
    let mut owners = context
        .content_owners
        .lock()
        .expect("content owner registry poisoned");
    if owners
        .get(key)
        .is_some_and(|current| Weak::ptr_eq(current, owner))
    {
        owners.remove(key);
    }
}

async fn retire_locked_path(encoded: &mut EncodedFilePath, owner: &PathOwner) -> Result<(), Error> {
    if encoded.path_type == PathType::Temp {
        debug!(key = ?encoded.key, "File is already a temp file");
        return Ok(());
    }
    if encoded.path_type == PathType::Content {
        let is_owner = encoded
            .shared_context
            .content_owners
            .lock()
            .expect("content owner registry poisoned")
            .get(&encoded.key)
            .is_some_and(|current| Weak::ptr_eq(current, owner));
        if !is_owner {
            return Err(make_err!(
                Code::Internal,
                "Content pathname belongs to another generation"
            ));
        }
    }
    let from = encoded.get_file_path().into_owned();
    let new_key = make_temp_key(&encoded.key);
    let to = to_full_path_from_key(&encoded.shared_context.temp_path, &new_key);
    if let Err(err) = fs::rename(&from, &to).await {
        let source_gone = err.code == Code::NotFound
            && matches!(fs::metadata(&from).await, Err(meta) if meta.code == Code::NotFound);
        if !source_gone {
            return Err(err).err_tip(|| "Failed to rename file");
        }
        debug!(key = ?encoded.key, "Failed to rename file (already gone, treating as benign)");
    }
    if encoded.path_type == PathType::Content {
        forget_content_owner(&encoded.shared_context, &encoded.key, owner);
    }
    encoded.path_type = PathType::Temp;
    encoded.key = new_key;
    Ok(())
}

async fn retire_file_path(path: &Arc<RwLock<EncodedFilePath>>) -> Result<(), Error> {
    let (context, key) = {
        let encoded = path.read().await;
        if encoded.path_type == PathType::Temp {
            debug!(key = ?encoded.key, "File is already a temp file");
            return Ok(());
        }
        (Arc::clone(&encoded.shared_context), encoded.key.clone())
    };
    let registration = KeyLockRegistration::new(&context.content_locks, key);
    let _gate = registration.lock().await;
    let mut encoded = path.write().await;
    retire_locked_path(&mut encoded, &Arc::downgrade(path)).await
}

#[cfg(test)]
async fn wait_for_executable_pause(slot: &std::sync::Mutex<Option<ExecutablePause>>) {
    let pause = slot.lock().expect("executable pause poisoned").take();
    if let Some((entered, resume)) = pause {
        let _ = entered.send(());
        let _ = resume.await;
    }
}

#[cfg(unix)]
fn executable_reservation_bytes(data_size: u64, block_size: u64) -> Option<(u64, u64)> {
    if block_size == 0 {
        return None;
    }
    let primary = data_size.div_ceil(block_size).checked_mul(block_size)?;
    Some((primary, primary.checked_mul(2)?))
}

#[cfg(unix)]
fn copy_executable_variant(
    source: &OsStr,
    variant: &OsStr,
    rename_fn: fn(&OsStr, &OsStr) -> Result<(), std::io::Error>,
) -> (Result<(), Error>, bool) {
    use std::os::unix::fs::PermissionsExt;
    let mut temporary = variant.to_os_string();
    temporary.push(".tmp");
    let result = (|| {
        std::fs::copy(source, &temporary).err_tip(|| "Executable copy failed")?;
        std::fs::set_permissions(&temporary, std::fs::Permissions::from_mode(0o555))
            .err_tip(|| "Executable permissions failed")?;
        let file = std::fs::File::open(&temporary).err_tip(|| "Executable reopen failed")?;
        file.sync_all().err_tip(|| "Executable sync failed")?;
        drop(file);
        rename_fn(&temporary, variant).err_tip(|| "Executable publication failed")?;
        Ok(())
    })();
    if result.is_err() {
        // The caller still holds the executable gate; no other generation can own this temp path.
        if let Err(err) = std::fs::remove_file(&temporary)
            && err.kind() != std::io::ErrorKind::NotFound
        {
            return (
                Err(Error::from(err).append("Executable temporary cleanup failed")),
                false,
            );
        }
    }
    (result, true)
}

#[cfg(unix)]
async fn remove_executable_generation(
    context: &SharedContext,
    digest: DigestInfo,
    owner: &Arc<RwLock<EncodedFilePath>>,
) {
    // No content-path or admission gate may be held while waiting for this lock.
    let registration = ExecutableLockRegistration::new(&context.executable_locks, digest);
    let _guard = registration.lock().await;
    let identity = Arc::downgrade(owner);
    let pending_path = context
        .pending_executables
        .lock()
        .expect("pending executable registry poisoned")
        .get(&digest)
        .filter(|item| Weak::ptr_eq(&item.owner, &identity))
        .map(|item| item.path.clone());
    if let Some(path) = pending_path {
        let removed = match fs::remove_file(&path).await {
            Ok(()) => true,
            Err(err) if err.code == Code::NotFound => true,
            Err(err) => {
                context.stop_new_allocations();
                warn!(?err, ?path, "Failed to retire executable temporary");
                false
            }
        };
        if removed {
            let mut pending = context
                .pending_executables
                .lock()
                .expect("pending executable registry poisoned");
            if pending
                .get(&digest)
                .is_some_and(|item| Weak::ptr_eq(&item.owner, &identity))
            {
                pending.remove(&digest);
            }
        }
    }
    let matches = context
        .executable_owners
        .lock()
        .expect("executable owner registry poisoned")
        .get(&digest)
        .is_some_and(|current| Weak::ptr_eq(current, &identity));
    if !matches {
        return;
    }
    let path = format!(
        "{}{EXECUTABLE_DIR_SUFFIX}/{DIGEST_FOLDER}/{digest}",
        context.content_path
    );
    match fs::remove_file(&path).await {
        Ok(()) => {}
        Err(err) if err.code == Code::NotFound => {}
        Err(err) => {
            context.stop_new_allocations();
            warn!(?err, ?path, "Failed to remove executable generation");
            return;
        }
    }
    let mut owners = context
        .executable_owners
        .lock()
        .expect("executable owner registry poisoned");
    if owners
        .get(&digest)
        .is_some_and(|current| Weak::ptr_eq(current, &identity))
    {
        owners.remove(&digest);
    }
}

#[inline]
fn digest_from_filename(file_name: &str) -> Result<DigestInfo, Error> {
    let (hash, size) = file_name.split_once('-').err_tip(|| "")?;
    let size = size.parse::<i64>()?;
    DigestInfo::try_new(hash, size)
}

pub fn key_from_file(file_name: &str, file_type: FileType) -> Result<StoreKey<'_>, Error> {
    match file_type {
        FileType::String => Ok(StoreKey::new_str(file_name)),
        FileType::Digest => digest_from_filename(file_name).map(StoreKey::Digest),
    }
}

/// The number of files to read the metadata for at the same time when running
/// `add_files_to_cache`.
const SIMULTANEOUS_METADATA_READS: usize = 200;

type FsEvictingMap<'a, Fe> =
    EvictingMap<StoreKeyBorrow, StoreKey<'a>, Arc<Fe>, SystemTime, RemoveItemCallbackHolder>;

async fn add_files_to_cache<Fe: FileEntry>(
    evicting_map: &FsEvictingMap<'_, Fe>,
    anchor_time: &SystemTime,
    shared_context: &Arc<SharedContext>,
    block_size: u64,
    rename_fn: fn(&OsStr, &OsStr) -> Result<(), std::io::Error>,
) -> Result<(), Error> {
    #[expect(clippy::too_many_arguments)]
    async fn process_entry<Fe: FileEntry>(
        evicting_map: &FsEvictingMap<'_, Fe>,
        file_name: &str,
        file_type: FileType,
        atime: SystemTime,
        data_size: u64,
        block_size: u64,
        anchor_time: &SystemTime,
        shared_context: &Arc<SharedContext>,
    ) -> Result<(), Error> {
        let key = key_from_file(file_name, file_type)?;

        let file_entry = Fe::create(
            data_size,
            block_size,
            RwLock::new(EncodedFilePath {
                shared_context: shared_context.clone(),
                path_type: PathType::Content,
                key: key.borrow().into_owned(),
                registered_key: Some(key.borrow().into_owned()),
            }),
        );
        let time_since_anchor = if let Ok(d) = anchor_time.duration_since(atime) {
            d
        } else {
            warn!(
                %file_name,
                atime = %humantime::format_rfc3339(atime),
                anchor_time = %humantime::format_rfc3339(*anchor_time),
                "File access time newer than FilesystemStore start time",
            );
            Duration::ZERO
        };
        evicting_map
            .insert_with_time(
                key.into_owned().into(),
                Arc::new(file_entry),
                i32::try_from(time_since_anchor.as_secs()).unwrap_or(i32::MAX),
            )
            .await;
        Ok(())
    }

    async fn read_files(
        folder: Option<&str>,
        shared_context: &SharedContext,
    ) -> Result<Vec<(String, SystemTime, u64, bool)>, Error> {
        // Note: In Dec 2024 this is for backwards compatibility with the old
        // way files were stored on disk. Previously all files were in a single
        // folder regardless of the StoreKey type. This allows old versions of
        // nativelink file layout to be upgraded at startup time.
        // This logic can be removed once more time has passed.
        let read_dir = folder.map_or_else(
            || format!("{}/", shared_context.content_path),
            |folder| format!("{}/{folder}/", shared_context.content_path),
        );

        let (_permit, dir_handle) = fs::read_dir(read_dir)
            .await
            .err_tip(|| "Failed opening content directory for iterating in filesystem store")?
            .into_inner();

        let read_dir_stream = ReadDirStream::new(dir_handle);
        read_dir_stream
            .map(|dir_entry| async move {
                let dir_entry = dir_entry.unwrap();
                let file_name = dir_entry.file_name().into_string().unwrap();
                let metadata = dir_entry
                    .metadata()
                    .await
                    .err_tip(|| "Failed to get metadata in filesystem store")?;
                // We need to filter out folders - we do not want to try to cache the s and d folders.
                let is_file =
                    metadata.is_file() || !(file_name == STR_FOLDER || file_name == DIGEST_FOLDER);
                // Using access time is not perfect, but better than random. We do not update the
                // atime when a file is actually "touched", we rely on whatever the filesystem does
                // when we read the file (usually update on read).
                let atime = metadata
                    .accessed()
                    .or_else(|_| metadata.modified())
                    .unwrap_or(SystemTime::UNIX_EPOCH);
                Result::<(String, SystemTime, u64, bool), Error>::Ok((
                    file_name,
                    atime,
                    metadata.len(),
                    is_file,
                ))
            })
            .buffer_unordered(SIMULTANEOUS_METADATA_READS)
            .try_collect()
            .await
    }

    /// Note: In Dec 2024 this is for backwards compatibility with the old
    /// way files were stored on disk. Previously all files were in a single
    /// folder regardless of the [`StoreKey`] type. This moves files from the old cache
    /// location to the new cache location, under [`DIGEST_FOLDER`].
    async fn move_old_cache(
        shared_context: &Arc<SharedContext>,
        rename_fn: fn(&OsStr, &OsStr) -> Result<(), std::io::Error>,
    ) -> Result<(), Error> {
        let file_infos = read_files(None, shared_context).await?;

        let from_path = &shared_context.content_path;

        let to_path = format!("{}/{DIGEST_FOLDER}", shared_context.content_path);

        for (file_name, _, _, _) in file_infos.into_iter().filter(|x| x.3) {
            let from_file: OsString = format!("{from_path}/{file_name}").into();
            let to_file: OsString = format!("{to_path}/{file_name}").into();

            if let Err(err) = rename_fn(&from_file, &to_file) {
                warn!(?from_file, ?to_file, ?err, "Failed to rename file",);
            } else {
                debug!(?from_file, ?to_file, "Renamed file (old cache)",);
            }
        }
        Ok(())
    }

    async fn add_files_to_cache<Fe: FileEntry>(
        evicting_map: &FsEvictingMap<'_, Fe>,
        anchor_time: &SystemTime,
        shared_context: &Arc<SharedContext>,
        block_size: u64,
        folder: &str,
    ) -> Result<(), Error> {
        let file_infos = read_files(Some(folder), shared_context).await?;
        let file_type = match folder {
            STR_FOLDER => FileType::String,
            DIGEST_FOLDER => FileType::Digest,
            _ => panic!("Invalid folder type"),
        };

        let path_root = format!("{}/{folder}", shared_context.content_path);

        for (file_name, atime, data_size, _) in file_infos.into_iter().filter(|x| x.3) {
            let result = process_entry(
                evicting_map,
                &file_name,
                file_type,
                atime,
                data_size,
                block_size,
                anchor_time,
                shared_context,
            )
            .await;
            if let Err(err) = result {
                warn!(?file_name, ?err, "Failed to add file to eviction cache",);
                // Ignore result.
                drop(fs::remove_file(format!("{path_root}/{file_name}")).await);
            }
        }
        Ok(())
    }

    move_old_cache(shared_context, rename_fn).await?;

    add_files_to_cache(
        evicting_map,
        anchor_time,
        shared_context,
        block_size,
        DIGEST_FOLDER,
    )
    .await?;

    add_files_to_cache(
        evicting_map,
        anchor_time,
        shared_context,
        block_size,
        STR_FOLDER,
    )
    .await?;
    Ok(())
}

async fn prune_temp_path(temp_path: &str) -> Result<(), Error> {
    async fn prune_temp_inner(temp_path: &str, subpath: &str) -> Result<(), Error> {
        let (_permit, dir_handle) = fs::read_dir(format!("{temp_path}/{subpath}"))
            .await
            .err_tip(
                || "Failed opening temp directory to prune partial downloads in filesystem store",
            )?
            .into_inner();

        let mut read_dir_stream = ReadDirStream::new(dir_handle);
        while let Some(dir_entry) = read_dir_stream.next().await {
            let path = dir_entry?.path();
            if let Err(err) = fs::remove_file(&path).await
                && err.code != Code::NotFound
            {
                return Err(err)
                    .err_tip(|| "Failed to reclaim filesystem temporary during startup");
            }
        }
        Ok(())
    }

    prune_temp_inner(temp_path, STR_FOLDER).await?;
    prune_temp_inner(temp_path, DIGEST_FOLDER).await?;
    Ok(())
}

// Sometimes we get files to emplace that are identical to the existing files
// Due to the evict/remove/replace cycle taking some amount of time, we actually
// want to drop these
// Return value is "is duplicate"
pub async fn check_duplicate_files<Fe>(
    evicting_map: &Arc<FsEvictingMap<'_, Fe>>,
    key: &StoreKey<'static>,
    entry: &Arc<Fe>,
) -> Result<bool, Error>
where
    Fe: FileEntry,
{
    let maybe_existing_item = evicting_map.get(&key.borrow().into_owned()).await;
    if let Some(existing_item) = maybe_existing_item {
        if Arc::ptr_eq(entry, &existing_item) {
            warn!("Tried to check duplicate of an entry we already have!");
            return Ok(evicting_map.contains_if(key, |current| Arc::ptr_eq(current, entry)));
        }
        let temp_file_encoded_file_path = entry.get_encoded_file_path().write().await;
        let existing_item_encoded_file_path = existing_item.get_encoded_file_path().write().await;
        if entry.data_size() == existing_item.data_size() {
            const CHUNK_SIZE: usize = 16 * 1024; // 16kb chunks, kinda picked out of the air
            let file_length = entry.data_size();
            let existing_path = existing_item_encoded_file_path.get_file_path();
            let temp_path = temp_file_encoded_file_path.get_file_path();
            trace!(?existing_path, ?temp_path, "Checking duplicate files");
            let mut temp_file = fs::open_file(&temp_path, 0, file_length).await?;
            let mut existing_file = fs::open_file(&existing_path, 0, file_length).await?;

            let mut temp_buffer: [u8; CHUNK_SIZE] = [0; CHUNK_SIZE];
            let mut existing_buffer: [u8; CHUNK_SIZE] = [0; CHUNK_SIZE];
            // in a file_length file, there are 0 to file_length-1 entries
            // not file_length. It's counting all the bytes, starting from 0
            for offset in (0..file_length - 1).step_by(CHUNK_SIZE) {
                let buffer_size = if offset + (CHUNK_SIZE as u64) <= file_length {
                    CHUNK_SIZE
                } else if file_length < CHUNK_SIZE as u64 {
                    usize::try_from(file_length)
                        .expect("Always succeeds because file_length < 16384")
                } else {
                    usize::try_from(file_length - offset).expect("Always succeeds because offset < file_length, and offset-file_length must be < 16384")
                };
                if let Err(err) = temp_file.read_exact(&mut temp_buffer[0..buffer_size]).await {
                    warn!(
                        ?err,
                        ?temp_path,
                        file_length,
                        offset,
                        buffer_size,
                        "Failed to read temp file, skipping duplicate check"
                    );
                    return Ok(false);
                }
                if let Err(err) = existing_file
                    .read_exact(&mut existing_buffer[0..buffer_size])
                    .await
                {
                    warn!(
                        ?err,
                        ?existing_path,
                        file_length,
                        offset,
                        buffer_size,
                        "Failed to read existing, skipping duplicate check"
                    );
                    return Ok(false);
                }
                if temp_buffer.ne(&existing_buffer) {
                    trace!(
                        ?existing_path,
                        ?temp_path,
                        "Files are different, so non-duplicate"
                    );
                    return Ok(false);
                }
            }
            trace!(
                ?existing_path,
                ?temp_path,
                "Identical files, so don't need to edit, skipping emplace"
            );
            return Ok(
                evicting_map.contains_if(key, |current| Arc::ptr_eq(current, &existing_item))
            );
        }
        trace!(
            entry_data_size = entry.data_size(),
            existing_data_size = existing_item.data_size(),
            existing_path = ?existing_item_encoded_file_path.get_file_path(),
            "Different data sizes, so non-duplicate"
        );
    } else {
        trace!("No existing entry, so not duplicate");
    }
    Ok(false)
}

#[derive(Debug, MetricsComponent)]
pub struct FilesystemStore<Fe: FileEntry = FileEntryImpl> {
    #[metric]
    shared_context: Arc<SharedContext>,
    #[metric(group = "evicting_map")]
    evicting_map: Arc<FsEvictingMap<'static, Fe>>,
    #[metric(help = "Block size of the configured filesystem")]
    block_size: u64,
    #[metric(help = "Size of the configured read buffer size")]
    read_buffer_size: usize,
    weak_self: Weak<Self>,
    rename_fn: fn(&OsStr, &OsStr) -> Result<(), std::io::Error>,
    /// Limits concurrent write operations to prevent disk I/O saturation.
    write_semaphore: Option<Semaphore>,
    /// Per-digest single-flight locks guarding creation of the executable
    /// variant in `{content_path}.exec`, so each variant's writable fd is
    /// opened exactly once. The outer lock is sync and only ever held to
    /// get/insert/remove the per-digest async lock — never across I/O.
    #[cfg(unix)]
    executable_locks: ExecutableLocks,
    #[cfg(unix)]
    executable_admissions: ExecutableLocks,
}

impl<Fe: FileEntry> FilesystemStore<Fe> {
    pub async fn new(spec: &FilesystemSpec) -> Result<Arc<Self>, Error> {
        Self::new_with_timeout_and_rename_fn(spec, |from, to| std::fs::rename(from, to)).await
    }

    pub async fn new_with_timeout_and_rename_fn(
        spec: &FilesystemSpec,
        rename_fn: fn(&OsStr, &OsStr) -> Result<(), std::io::Error>,
    ) -> Result<Arc<Self>, Error> {
        async fn create_subdirs(path: &str) -> Result<(), Error> {
            fs::create_dir_all(format!("{path}/{STR_FOLDER}"))
                .await
                .err_tip(|| format!("Failed to create directory {path}/{STR_FOLDER}"))?;
            fs::create_dir_all(format!("{path}/{DIGEST_FOLDER}"))
                .await
                .err_tip(|| format!("Failed to create directory {path}/{DIGEST_FOLDER}"))
        }

        let now = SystemTime::now();

        let empty_policy = nativelink_config::stores::EvictionPolicy::default();
        let eviction_policy = spec.eviction_policy.as_ref().unwrap_or(&empty_policy);
        let evicting_map = Arc::new(EvictingMap::new(eviction_policy, now));
        #[cfg(unix)]
        let executable_locks = Arc::new(std::sync::Mutex::new(HashMap::new()));

        // Create temp and content directories and the s and d subdirectories.

        create_subdirs(&spec.temp_path).await?;
        create_subdirs(&spec.content_path).await?;

        // Executable-variant directory: a sibling of `content_path` holding
        // per-digest 0o555 copies used as hardlink sources for executable
        // inputs (see `with_executable_hardlink_source`). Cleared on startup —
        // the variants are regenerable and we never want a stale one to leak
        // across runs. Unix-only: the executable bit (and the ETXTBSY race it
        // guards against) does not apply on Windows.
        #[cfg(unix)]
        {
            let executable_dir = format!("{}{EXECUTABLE_DIR_SUFFIX}", spec.content_path);
            match fs::remove_dir_all(&executable_dir).await {
                Ok(()) => {}
                Err(err) if err.code == Code::NotFound => {}
                Err(err) => {
                    return Err(err).err_tip(|| "Failed to clear executable storage on reopen");
                }
            }
            fs::create_dir_all(format!("{executable_dir}/{DIGEST_FOLDER}"))
                .await
                .err_tip(|| format!("Failed to create executable dir {executable_dir}"))?;
        }

        let shared_context = Arc::new(SharedContext {
            active_drop_spawns: AtomicU64::new(0),
            temp_path: spec.temp_path.clone(),
            content_path: spec.content_path.clone(),
            content_locks: Arc::new(std::sync::Mutex::new(HashMap::new())),
            content_owners: std::sync::Mutex::new(HashMap::new()),
            #[cfg(unix)]
            executable_locks: Arc::clone(&executable_locks),
            #[cfg(unix)]
            executable_owners: std::sync::Mutex::new(HashMap::new()),
            #[cfg(unix)]
            pending_executables: std::sync::Mutex::new(HashMap::new()),
            write_admission_failed: AtomicBool::new(false),
            #[cfg(test)]
            retirement_observer: std::sync::Mutex::new(None),
            #[cfg(test)]
            executable_reservation_pause: std::sync::Mutex::new(None),
            #[cfg(test)]
            executable_ready_pause: std::sync::Mutex::new(None),
        });

        let block_size = if spec.block_size == 0 {
            DEFAULT_BLOCK_SIZE
        } else {
            spec.block_size
        };
        add_files_to_cache(
            evicting_map.as_ref(),
            &now,
            &shared_context,
            block_size,
            rename_fn,
        )
        .await?;
        prune_temp_path(&shared_context.temp_path).await?;

        let read_buffer_size = if spec.read_buffer_size == 0 {
            DEFAULT_BUFF_SIZE
        } else {
            spec.read_buffer_size as usize
        };
        let write_semaphore = if spec.max_concurrent_writes > 0 {
            Some(Semaphore::new(spec.max_concurrent_writes))
        } else {
            None
        };
        Ok(Arc::new_cyclic(|weak_self| Self {
            shared_context,
            evicting_map,
            block_size,
            read_buffer_size,
            weak_self: weak_self.clone(),
            rename_fn,
            write_semaphore,
            #[cfg(unix)]
            executable_locks,
            #[cfg(unix)]
            executable_admissions: Arc::new(std::sync::Mutex::new(HashMap::new())),
        }))
    }

    pub fn get_arc(&self) -> Option<Arc<Self>> {
        self.weak_self.upgrade()
    }

    /// Path of the read-only executable (0o555) variant for `digest`.
    #[cfg(unix)]
    fn executable_variant_path(&self, digest: &DigestInfo) -> OsString {
        format!(
            "{}{EXECUTABLE_DIR_SUFFIX}/{DIGEST_FOLDER}/{digest}",
            self.shared_context.content_path
        )
        .into()
    }

    /// Runs `handler` with a private, read-only **executable** (0o555) copy of
    /// the blob for `digest`, creating it at most once. The handler contract
    /// keeps eviction exclusion alive through the caller's hardlink or copy;
    /// returning the path would release that protection too early.
    ///
    /// Why this exists: a CAS blob is stored read-only **0o444** and shared
    /// across actions by hardlink, so it cannot carry the executable bit and
    /// must never be `chmod`'d (that mutates the shared inode — the #2347
    /// corruption class). Materializing an executable input therefore needs a
    /// separate 0o555 inode. Doing that copy *per action* opens a writable fd
    /// in the worker's hot path; under fork-heavy concurrency a child can
    /// inherit that fd and a concurrent `execve` of the executable then fails
    /// with `ETXTBSY` ("Text file busy", os error 26). Creating the 0o555 inode
    /// **once** — writer fd fsync'd and closed, then atomically renamed into
    /// place before the inode is ever hardlinked or executed — and hardlinking
    /// it thereafter keeps the per-action path hardlink-only.
    /// Creation and the handler share the same per-digest lock as eviction,
    /// so the variant cannot be removed after path resolution but before the
    /// caller's hardlink/copy completes.
    #[cfg(unix)]
    pub async fn with_executable_hardlink_source<
        T,
        Fut: Future<Output = Result<T, Error>> + Send,
        F: FnOnce(OsString) -> Fut + Send,
    >(
        &self,
        digest: &DigestInfo,
        handler: F,
    ) -> Result<T, Error> {
        let variant_path = self.executable_variant_path(digest);
        let mut handler = Some(handler);
        // Permit one generation re-resolution, including replacement after successful creation.
        for _ in 0..2 {
            let primary = self.get_file_entry_for_digest(digest).await?;
            for phase in 0..2 {
                let registration = ExecutableLockRegistration::new(&self.executable_locks, *digest);
                let guard = registration.lock().await;
                let current = self
                    .evicting_map
                    .contains_if(&(*digest).into(), |entry| Arc::ptr_eq(entry, &primary));
                let identity = Arc::downgrade(primary.get_encoded_file_path());
                let owned = self
                    .shared_context
                    .executable_owners
                    .lock()
                    .expect("executable owner registry poisoned")
                    .get(digest)
                    .is_some_and(|owner| Weak::ptr_eq(owner, &identity));
                if current && owned && fs::metadata(&variant_path).await.is_ok() {
                    return handler.take().expect("handler called once")(variant_path.clone())
                        .await;
                }
                drop(guard);
                drop(registration);
                if !current || phase == 1 {
                    break;
                }
                if self
                    .create_executable_variant(digest, &variant_path, Arc::clone(&primary))
                    .await?
                    == ExecutableCreation::Superseded
                {
                    break;
                }
                #[cfg(test)]
                wait_for_executable_pause(&self.shared_context.executable_ready_pause).await;
            }
        }
        // Absence keeps the existing typed client-recovery contract; a present replacement is not missing.
        self.get_file_entry_for_digest(digest).await?;
        Err(make_err!(
            Code::Aborted,
            "Cache generation changed repeatedly during executable materialization"
        ))
    }

    /// Non-unix has no separate executable variant, but callers use the same
    /// handler API so the primary FileEntry remains pinned through their
    /// filesystem operation on every platform.
    #[cfg(not(unix))]
    pub async fn with_executable_hardlink_source<
        T,
        Fut: Future<Output = Result<T, Error>> + Send,
        F: FnOnce(OsString) -> Fut + Send,
    >(
        &self,
        digest: &DigestInfo,
        handler: F,
    ) -> Result<T, Error> {
        let file_entry = self.get_file_entry_for_digest(digest).await?;
        file_entry.get_file_path_locked(handler).await
    }

    /// Reserves and materializes an executable copy in a cancellation-owned critical task.
    #[cfg(unix)]
    async fn create_executable_variant(
        &self,
        digest: &DigestInfo,
        variant_path: &OsStr,
        primary: Arc<Fe>,
    ) -> Result<ExecutableCreation, Error> {
        let store = self
            .get_arc()
            .ok_or_else(|| make_err!(Code::Internal, "Store is shutting down"))?;
        let digest = *digest;
        let variant = variant_path.to_os_string();
        background_spawn!("filesystem_store_create_executable_variant", async move {
            let admission = ExecutableLockRegistration::new(&store.executable_admissions, digest);
            let _admitted = admission.lock().await;
            store.shared_context.check_write_admission()?;
            let (base, weight) =
                executable_reservation_bytes(primary.data_size(), store.block_size).ok_or_else(
                    || {
                        make_err!(
                            Code::ResourceExhausted,
                            "Executable allocation size overflow"
                        )
                    },
                )?;
            // No entry, content-path or executable gate may be held across admission callbacks.
            let mut generation_matched = false;
            let admitted = store
                .evicting_map
                .reweight_if(&digest.into(), weight, |entry| {
                    generation_matched = Arc::ptr_eq(entry, &primary);
                    generation_matched
                })
                .await;
            if !admitted {
                if !generation_matched {
                    return Ok(ExecutableCreation::Superseded);
                }
                return Err(make_err!(
                    Code::ResourceExhausted,
                    "Executable allocation cannot be admitted for the current cache generation"
                ));
            }
            #[cfg(test)]
            wait_for_executable_pause(&store.shared_context.executable_reservation_pause).await;
            let context = Arc::clone(&store.shared_context);
            let generation = Arc::clone(primary.get_encoded_file_path());
            let map = Arc::clone(&store.evicting_map);
            let expected = Arc::clone(&primary);
            let rename_fn = store.rename_fn;
            let outcome = primary
                .get_file_path_locked(move |source| async move {
                    let registration =
                        ExecutableLockRegistration::new(&context.executable_locks, digest);
                    let _guard = registration.lock().await;
                    if !map.contains_if(&digest.into(), |entry| Arc::ptr_eq(entry, &expected)) {
                        return Ok((Ok(ExecutableCreation::Superseded), true));
                    }
                    let identity = Arc::downgrade(&generation);
                    let owned = context
                        .executable_owners
                        .lock()
                        .expect("executable owner registry poisoned")
                        .get(&digest)
                        .is_some_and(|owner| Weak::ptr_eq(owner, &identity));
                    if owned && fs::metadata(&variant).await.is_ok() {
                        return Ok((Ok(ExecutableCreation::Ready), true));
                    }
                    if let Err(err) = context.check_write_admission() {
                        return Ok((Err(err), true));
                    }
                    // A previous generation's path is not a cache hit, even for the same digest.
                    if let Err(err) = fs::remove_file(&variant).await
                        && err.code != Code::NotFound
                    {
                        context.stop_new_allocations();
                        return Ok((Err(err), false));
                    }
                    context
                        .executable_owners
                        .lock()
                        .expect("executable owner registry poisoned")
                        .remove(&digest);
                    let publish_path = variant.clone();
                    let mut temporary = variant.clone();
                    temporary.push(".tmp");
                    context
                        .pending_executables
                        .lock()
                        .expect("pending executable registry poisoned")
                        .insert(
                            digest,
                            PendingExecutable {
                                owner: identity.clone(),
                                path: temporary,
                            },
                        );
                    let copied =
                        spawn_blocking!("filesystem_store_executable_variant", move || {
                            copy_executable_variant(&source, &publish_path, rename_fn)
                        })
                        .await;
                    let outcome = match copied {
                        Ok((result, cleaned)) => {
                            (result.map(|()| ExecutableCreation::Ready), cleaned)
                        }
                        Err(err) => (Err(Error::from(err)), false),
                    };
                    if outcome.1 {
                        let mut pending = context
                            .pending_executables
                            .lock()
                            .expect("pending executable registry poisoned");
                        if pending
                            .get(&digest)
                            .is_some_and(|item| Weak::ptr_eq(&item.owner, &identity))
                        {
                            pending.remove(&digest);
                        }
                    } else {
                        context.stop_new_allocations();
                    }
                    if outcome.0.is_ok() {
                        context
                            .executable_owners
                            .lock()
                            .expect("executable owner registry poisoned")
                            .insert(digest, identity);
                    }
                    Ok(outcome)
                })
                .await;
            let (result, temporary_removed) = match outcome {
                Ok(outcome) => outcome,
                Err(err) => (Err(err), false),
            };
            // Both the primary read guard and executable gate have been released here.
            // Failed cleanup keeps the current charge and stops new allocation until reopen.
            // Eviction may retire the entry, so the latch does not promise retained charge forever.
            // A late rollback cannot affect a replacement generation.
            if result.is_err() && temporary_removed {
                store
                    .evicting_map
                    .reweight_if(&digest.into(), base, |entry| Arc::ptr_eq(entry, &primary))
                    .await;
            }
            result
        })
        .await
        .err_tip(|| "Executable allocation task failed")?
    }

    pub async fn get_file_entry_for_digest(&self, digest: &DigestInfo) -> Result<Arc<Fe>, Error> {
        // Zero-digest blobs have no backing file on disk (FilesystemStore
        // never persists zero-byte content). The previous implementation
        // returned a synthetic FileEntry whose content_path did not exist,
        // which downstream callers would then try to hard_link from,
        // silently producing missing or empty output files in worker
        // execution directories. Return NotFound so callers are forced to
        // take the explicit zero-digest path (e.g. fs::create_file).
        if is_zero_digest(digest) {
            return Err(make_err!(
                Code::NotFound,
                "{digest} is a zero-digest; FilesystemStore does not persist zero-byte files. \
                 Callers must materialise empty files directly rather than going through get_file_entry_for_digest."
            ));
        }
        self.evicting_map.get(&digest.into()).await.ok_or_else(|| {
            make_err!(Code::NotFound, "{digest} not found in filesystem store").with_context(
                ErrorContext::MissingDigest {
                    hash: digest.packed_hash().to_string(),
                    size: digest.size_bytes() as i64,
                },
            )
        })
    }

    async fn update_file(
        self: Pin<&Self>,
        mut entry: Fe,
        mut temp_file: FileSlot,
        final_key: StoreKey<'static>,
        mut reader: DropCloserReadHalf,
    ) -> Result<u64, Error> {
        let mut data_size = 0;
        loop {
            let mut data = reader
                .recv()
                .await
                .err_tip(|| "Failed to receive data in filesystem store")?;
            let data_len = data.len();
            if data_len == 0 {
                break; // EOF.
            }
            temp_file
                .write_all_buf(&mut data)
                .await
                .err_tip(|| "Failed to write data into filesystem store")?;
            data_size += data_len as u64;
        }

        let permit = if let Some(sem) = &self.write_semaphore {
            Some(sem.acquire().await.map_err(|err| {
                Error::from_std_err(Code::Internal, &err).append("Write semaphore closed")
            })?)
        } else {
            None
        };

        // tokio defers write errors to the next write or flush call, so without an explicit flush
        // the final write's failure is silently swallowed by `sync_all`, and a truncated file would
        // be renamed into the content path.
        temp_file
            .flush()
            .await
            .err_tip(|| "Failed to flush in filesystem store")?;
        temp_file
            .as_ref()
            .sync_all()
            .await
            .err_tip(|| "Failed to sync_data in filesystem store")?;

        drop(permit);

        temp_file.advise_dontneed();
        trace!(?temp_file, "Dropping file to update_file");
        drop(temp_file);

        *entry.data_size_mut() = data_size;
        self.emplace_file(final_key, Arc::new(entry)).await?;
        Ok(data_size)
    }

    async fn emplace_file(&self, key: StoreKey<'static>, entry: Arc<Fe>) -> Result<(), Error> {
        let evicting_map = Arc::clone(&self.evicting_map);
        let rename_fn = self.rename_fn;
        // Publication and cleanup must finish even if the uploading caller is canceled.
        background_spawn!("filesystem_store_emplace_file", async move {
            {
                let mut path = entry.get_encoded_file_path().write().await;
                path.registered_key = Some(key.clone());
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let from = path.get_file_path().into_owned();
                    if let Err(err) =
                        fs::set_permissions(&from, std::fs::Permissions::from_mode(0o444)).await
                    {
                        warn!(?err, ?from, "Failed to set CAS blob read-only");
                    }
                }
            }
            if check_duplicate_files(&evicting_map, &key, &entry).await? {
                return Ok(());
            }
            evicting_map
                .insert(key.borrow().into_owned().into(), Arc::clone(&entry))
                .await;
            let result = publish_file_generation(&evicting_map, &key, &entry, rename_fn).await;
            if result.is_err() {
                // publish_file_generation has released every path gate before cleanup callbacks.
                evicting_map
                    .remove_if(&key, |current| Arc::ptr_eq(current, &entry))
                    .await;
            }
            result
        })
        .await
        .err_tip(|| "Failed to join filesystem store publication")?
    }

    pub fn get_eviction_snapshot(&self) -> EvictionSnapshot {
        self.evicting_map.get_snapshot()
    }

    // Only for tests, so we can run check_duplicate_files
    pub fn get_evicting_map(&self) -> Arc<FsEvictingMap<'static, Fe>> {
        self.evicting_map.clone()
    }

    // Separated out so tests can use this
    pub async fn make_temp_file(
        &self,
        temp_key: StoreKey<'static>,
    ) -> Result<(Fe, FileSlot, OsString), Error> {
        self.shared_context.check_write_admission()?;
        Fe::make_and_open_file(
            self.block_size,
            EncodedFilePath {
                shared_context: self.shared_context.clone(),
                path_type: PathType::Temp,
                key: temp_key,
                registered_key: None,
            },
        )
        .await
    }
}

#[async_trait]
impl<Fe: FileEntry> StoreDriver for FilesystemStore<Fe> {
    async fn has_with_results(
        self: Pin<&Self>,
        keys: &[StoreKey<'_>],
        results: &mut [Option<u64>],
    ) -> Result<(), Error> {
        let own_keys = keys
            .iter()
            .map(|sk| sk.borrow().into_owned())
            .collect::<Vec<_>>();
        self.evicting_map
            .sizes_for_keys(own_keys.iter(), results, false /* peek */)
            .await;
        // We need to do a special pass to ensure our zero files exist.
        // If our results failed and the result was a zero file, we need to
        // create the file by spec.
        for (key, result) in keys.iter().zip(results.iter_mut()) {
            if result.is_some() || !is_zero_digest(key.borrow()) {
                continue;
            }
            let (mut tx, rx) = make_buf_channel_pair();
            let send_eof_result = tx.send_eof();
            self.update(key.borrow(), rx, UploadSizeInfo::ExactSize(0))
                .await
                .err_tip(|| format!("Failed to create zero file for key {}", key.as_str()))
                .merge(
                    send_eof_result
                        .err_tip(|| "Failed to send zero file EOF in filesystem store has"),
                )?;

            *result = Some(0);
        }
        Ok(())
    }

    async fn update(
        self: Pin<&Self>,
        key: StoreKey<'_>,
        mut reader: DropCloserReadHalf,
        _upload_size: UploadSizeInfo,
    ) -> Result<u64, Error> {
        if is_zero_digest(key.borrow()) {
            // don't need to add, because zero length files are just assumed to exist.
            return Ok(0);
        }

        let temp_key = make_temp_key(&key);

        // There's a possibility of deadlock here where we take all of the
        // file semaphores with make_and_open_file and the semaphores for
        // whatever is populating reader is exhasted on the threads that
        // have the FileSlots and not on those which can't.  To work around
        // this we don't take the FileSlot until there's something on the
        // reader available to know that the populator is active.
        reader.peek().await?;

        let (entry, temp_file, temp_full_path) = self.make_temp_file(temp_key).await?;

        self.update_file(entry, temp_file, key.into_owned(), reader)
            .await
            .err_tip(|| {
                format!(
                    "While processing with temp file {}",
                    temp_full_path.display()
                )
            })
    }

    fn optimized_for(&self, optimization: StoreOptimizations) -> bool {
        matches!(
            optimization,
            StoreOptimizations::FileUpdates | StoreOptimizations::SubscribesToUpdateOneshot
        )
    }

    async fn update_oneshot(self: Pin<&Self>, key: StoreKey<'_>, data: Bytes) -> Result<(), Error> {
        if is_zero_digest(key.borrow()) {
            return Ok(());
        }

        let temp_key = make_temp_key(&key);
        let (mut entry, mut temp_file, temp_full_path) = self
            .make_temp_file(temp_key)
            .await
            .err_tip(|| "Failed to create temp file in filesystem store update_oneshot")?;

        // Write directly without channel overhead
        if !data.is_empty() {
            temp_file
                .write_all(&data)
                .await
                .err_tip(|| format!("Failed to write data to {}", temp_full_path.display()))?;
        }

        let _permit = if let Some(sem) = &self.write_semaphore {
            Some(sem.acquire().await.map_err(|err| {
                Error::from_std_err(Code::Internal, &err).append("Write semaphore closed")
            })?)
        } else {
            None
        };

        // See comment in `update_file` above.
        temp_file
            .flush()
            .await
            .err_tip(|| "Failed to flush in filesystem store update_oneshot")?;
        temp_file
            .as_ref()
            .sync_all()
            .await
            .err_tip(|| "Failed to sync_data in filesystem store update_oneshot")?;

        drop(_permit);

        temp_file.advise_dontneed();
        drop(temp_file);

        *entry.data_size_mut() = data.len() as u64;
        self.emplace_file(key.into_owned(), Arc::new(entry)).await
    }

    async fn update_with_whole_file(
        self: Pin<&Self>,
        key: StoreKey<'_>,
        path: OsString,
        file: FileSlot,
        upload_size: UploadSizeInfo,
    ) -> Result<(u64, Option<FileSlot>), Error> {
        let file_size = match upload_size {
            UploadSizeInfo::ExactSize(size) => size,
            UploadSizeInfo::MaxSize(_) => file
                .as_ref()
                .metadata()
                .await
                .err_tip(|| format!("While reading metadata for {}", path.display()))?
                .len(),
        };
        if file_size == 0 {
            // don't need to add, because zero length files are just assumed to exist
            return Ok((0, None));
        }
        self.shared_context.check_write_admission()?;
        let entry = Fe::create(
            file_size,
            self.block_size,
            RwLock::new(EncodedFilePath {
                shared_context: self.shared_context.clone(),
                path_type: PathType::Custom(path),
                key: key.borrow().into_owned(),
                registered_key: Some(key.borrow().into_owned()),
            }),
        );
        // We are done with the file, if we hold a reference to the file here, it could
        // result in a deadlock if `emplace_file()` also needs file descriptors.
        trace!(?file, "Dropping file to to update_with_whole_file");
        file.advise_dontneed();
        drop(file);
        self.emplace_file(key.into_owned(), Arc::new(entry))
            .await
            .err_tip(|| "Could not move file into store in upload_file_to_store, maybe dest is on different volume?")?;
        return Ok((file_size, None));
    }

    async fn get_part(
        self: Pin<&Self>,
        key: StoreKey<'_>,
        writer: &mut DropCloserWriteHalf,
        offset: u64,
        length: Option<u64>,
    ) -> Result<(), Error> {
        if is_zero_digest(key.borrow()) {
            self.has(key.borrow())
                .await
                .err_tip(|| "Failed to check if zero digest exists in filesystem store")?;
            writer
                .send_eof()
                .err_tip(|| "Failed to send zero EOF in filesystem store get_part")?;
            return Ok(());
        }
        let owned_key = key.into_owned();
        let entry = self.evicting_map.get(&owned_key).await.ok_or_else(|| {
            make_err!(
                Code::NotFound,
                "{} not found in filesystem store here",
                owned_key.as_str()
            )
        })?;
        let read_limit = length.unwrap_or(u64::MAX);
        let failed_entry = Arc::clone(&entry);
        let mut temp_file = entry.read_file_part(offset, read_limit).or_else(|err| async move {
            // If the file is not found, we need to remove it from the eviction map.
            if err.code == Code::NotFound {
                // Map said the file was present but `open()` hit ENOENT.
                // Self-heals: we remove the stale entry below and a
                // fast/slow caller re-populates from the slow store, so
                // this is a recoverable warn, not a fatal error.
                warn!(
                    ?err,
                    key = ?owned_key,
                    "Filesystem store map/disk divergence: removing entry; reader will fall through to slow store",
                );
                self.evicting_map.remove_if(&owned_key, |current| Arc::ptr_eq(current, &failed_entry)).await;
            }
            Err(err)
        }).await?;

        loop {
            let mut buf = BytesMut::with_capacity(self.read_buffer_size);
            temp_file
                .read_buf(&mut buf)
                .await
                .err_tip(|| "Failed to read data in filesystem store")?;
            if buf.is_empty() {
                break; // EOF.
            }
            writer
                .send(buf.freeze())
                .await
                .err_tip(|| "Failed to send chunk in filesystem store get_part")?;
        }
        temp_file.get_ref().advise_dontneed();
        writer
            .send_eof()
            .err_tip(|| "Filed to send EOF in filesystem store get_part")?;

        Ok(())
    }

    fn inner_store(&self, _digest: Option<StoreKey>) -> &dyn StoreDriver {
        self
    }

    fn as_any<'a>(&'a self) -> &'a (dyn core::any::Any + Sync + Send + 'static) {
        self
    }

    fn as_any_arc(self: Arc<Self>) -> Arc<dyn core::any::Any + Sync + Send + 'static> {
        self
    }

    fn register_health(self: Arc<Self>, registry: &mut HealthRegistryBuilder) {
        registry.register_indicator(self);
    }

    fn register_remove_callback(
        self: Arc<Self>,
        callback: Arc<dyn RemoveItemCallback>,
    ) -> Result<(), Error> {
        self.evicting_map
            .add_remove_callback(RemoveItemCallbackHolder::new(callback));
        Ok(())
    }
}

#[async_trait]
impl<Fe: FileEntry> HealthStatusIndicator for FilesystemStore<Fe> {
    fn get_name(&self) -> &'static str {
        "FilesystemStore"
    }

    /// Lightweight probe: `stat()` the `content_path` directory. No
    /// write-semaphore / eviction-map contention with production
    /// traffic, and bounded so a hung NFS / EBS mount can't wedge the
    /// indicator.
    async fn check_health(&self, _namespace: Cow<'static, str>) -> HealthStatus {
        const HEALTH_PROBE_TIMEOUT: Duration = Duration::from_secs(2);
        if let Err(err) = self.shared_context.check_write_admission() {
            return HealthStatus::new_failed(self, err.message_string().into());
        }

        let content_path = &self.shared_context.content_path;
        let stat = tokio::fs::metadata(&content_path);
        match timeout(HEALTH_PROBE_TIMEOUT, stat).await {
            Ok(Ok(meta)) if meta.is_dir() => {
                HealthStatus::new_ok(self, "FilesystemStore::check_health: ok".into())
            }
            Ok(Ok(_)) => HealthStatus::new_failed(
                self,
                format!(
                    "FilesystemStore::check_health: content_path {content_path} is not a directory"
                )
                .into(),
            ),
            Ok(Err(e)) => {
                warn!(
                    ?e,
                    %content_path,
                    "FilesystemStore::check_health: stat errored",
                );
                HealthStatus::new_failed(
                    self,
                    format!("FilesystemStore::check_health: stat errored: {e}").into(),
                )
            }
            Err(_) => {
                warn!(
                    %content_path,
                    timeout_secs = HEALTH_PROBE_TIMEOUT.as_secs(),
                    "FilesystemStore::check_health: stat timed out",
                );
                HealthStatus::Timeout {
                    struct_name: self.struct_name(),
                }
            }
        }
    }
}

#[cfg(all(test, unix))]
mod generation_tests {
    use super::*;
    use futures::{FutureExt, poll};
    use nativelink_macro::nativelink_test;
    use nativelink_util::common::make_temp_path;
    use nativelink_util::store_trait::StoreLike;
    use tokio::sync::oneshot;

    enum CleanupFailure {
        Primary,
        Executable,
        StaleExecutable,
        PendingExecutable,
        RetiredTemporary,
    }

    async fn check_cleanup_failure(failure: CleanupFailure) -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let spec = FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                block_size: 1,
                ..Default::default()
            };
            let store = FilesystemStore::<FileEntryImpl>::new(&spec).await?;
            let removed = DigestInfo::new([1; 32], 10);
            let cached = DigestInfo::new([2; 32], 10);
            let fresh = DigestInfo::new([3; 32], 10);
            for digest in [removed, cached] {
                store
                    .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                    .await?;
                if digest == cached || !matches!(failure, CleanupFailure::StaleExecutable) {
                    store
                        .with_executable_hardlink_source(&digest, |_| async { Ok(()) })
                        .await?;
                }
            }
            let primary = store.get_file_entry_for_digest(&removed).await?;
            let variant = format!("{}.exec/{DIGEST_FOLDER}/{removed}", spec.content_path);
            match failure {
                CleanupFailure::Primary => {
                    // A missing destination directory is not a vanished source.
                    tokio::fs::remove_dir_all(format!("{}/{DIGEST_FOLDER}", spec.temp_path))
                        .await?;
                }
                CleanupFailure::Executable => {
                    tokio::fs::remove_file(&variant).await?;
                    tokio::fs::create_dir(&variant).await?;
                }
                CleanupFailure::StaleExecutable => {
                    // A pre-existing variant with no owning primary generation must be removed.
                    tokio::fs::create_dir(&variant).await?;
                }
                CleanupFailure::PendingExecutable => {
                    let temporary = OsString::from(format!("{variant}.tmp"));
                    tokio::fs::create_dir(&temporary).await?;
                    store
                        .shared_context
                        .pending_executables
                        .lock()
                        .unwrap()
                        .insert(
                            removed,
                            PendingExecutable {
                                owner: Arc::downgrade(primary.get_encoded_file_path()),
                                path: temporary,
                            },
                        );
                }
                CleanupFailure::RetiredTemporary => {}
            }
            assert!(
                !store
                    .shared_context
                    .write_admission_failed
                    .load(Ordering::Acquire)
            );
            if matches!(failure, CleanupFailure::StaleExecutable) {
                store
                    .with_executable_hardlink_source(&removed, |_| async { Ok(()) })
                    .await
                    .expect_err("stale executable cleanup fails");
                assert!(
                    store
                        .shared_context
                        .write_admission_failed
                        .load(Ordering::Acquire)
                );
            }
            assert!(
                store
                    .get_evicting_map()
                    .remove(&StoreKey::Digest(removed))
                    .await
            );
            let mut failed_temporary = None;
            if matches!(failure, CleanupFailure::RetiredTemporary) {
                // The reader pins the retired inode until this actual final Drop.
                assert!(
                    !store
                        .shared_context
                        .write_admission_failed
                        .load(Ordering::Acquire)
                );
                let retired = primary
                    .get_encoded_file_path()
                    .read()
                    .await
                    .get_file_path()
                    .into_owned();
                tokio::fs::remove_file(&retired).await?;
                tokio::fs::create_dir(&retired).await?;
                failed_temporary = Some(retired);
                drop(primary);
                // Drop increments this counter synchronously before scheduling deletion.
                while store
                    .shared_context
                    .active_drop_spawns
                    .load(Ordering::Acquire)
                    != 0
                    || !store
                        .shared_context
                        .write_admission_failed
                        .load(Ordering::Acquire)
                {
                    tokio::task::yield_now().await;
                }
            }
            assert!(
                store
                    .shared_context
                    .write_admission_failed
                    .load(Ordering::Acquire)
            );
            assert_eq!(store.has(removed).await?, None);
            assert_eq!(
                store
                    .update_oneshot(fresh, Bytes::from_static(b"0123456789"))
                    .await
                    .unwrap_err()
                    .code,
                Code::ResourceExhausted
            );
            assert_eq!(
                store.get_part_unchunked(cached, 0, None).await?,
                Bytes::from_static(b"0123456789")
            );
            store
                .with_executable_hardlink_source(&cached, |path| async move {
                    assert_eq!(tokio::fs::read(path).await?, b"0123456789");
                    Ok(())
                })
                .await?;
            assert!(matches!(
                HealthStatusIndicator::check_health(&*store, Cow::Borrowed("test")).await,
                HealthStatus::Failed { .. }
            ));
            if let Some(path) = failed_temporary {
                drop(store);
                let error = FilesystemStore::<FileEntryImpl>::new(&spec)
                    .await
                    .err()
                    .expect("reopen must reject an unreclaimed owned temporary");
                assert!(error.messages.iter().any(|message| {
                    message.contains("Failed to reclaim filesystem temporary during startup")
                }));
                assert!(tokio::fs::metadata(&path).await?.is_dir());
                // Simulate explicit recovery of only this fixture's failed allocation.
                tokio::fs::remove_dir(&path).await?;
                let reopened = FilesystemStore::<FileEntryImpl>::new(&spec).await?;
                reopened
                    .update_oneshot(fresh, Bytes::from_static(b"0123456789"))
                    .await?;
            }
            Ok(())
        })
        .await
        .err_tip(|| "retirement failure control did not complete")?
    }

    #[nativelink_test]
    async fn failed_primary_retirement_stops_new_allocations() -> Result<(), Error> {
        check_cleanup_failure(CleanupFailure::Primary).await
    }

    #[nativelink_test]
    async fn failed_executable_retirement_stops_new_allocations() -> Result<(), Error> {
        check_cleanup_failure(CleanupFailure::Executable).await
    }

    #[nativelink_test]
    async fn failed_stale_executable_cleanup_stops_new_allocations() -> Result<(), Error> {
        check_cleanup_failure(CleanupFailure::StaleExecutable).await
    }

    #[nativelink_test]
    async fn failed_pending_executable_retirement_stops_new_allocations() -> Result<(), Error> {
        check_cleanup_failure(CleanupFailure::PendingExecutable).await
    }

    #[nativelink_test]
    async fn failed_retired_temporary_deletion_stops_new_allocations() -> Result<(), Error> {
        check_cleanup_failure(CleanupFailure::RetiredTemporary).await
    }

    #[nativelink_test]
    async fn canceled_removal_finishes_its_owned_primary_and_executable_cleanup()
    -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let content = make_temp_path("content");
            let digest = DigestInfo::new([1; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: content.clone(),
                temp_path: make_temp_path("temp"),
                ..Default::default()
            })
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let (entered_tx, entered_rx) = oneshot::channel();
            let (release_tx, release_rx) = oneshot::channel();
            let handler_store = Arc::clone(&store);
            let handler = tokio::spawn(async move {
                handler_store
                    .with_executable_hardlink_source(&digest, |path| async move {
                        let _ = entered_tx.send(());
                        release_rx
                            .await
                            .map_err(|_| make_err!(Code::Internal, "handler release dropped"))?;
                        fs::metadata(path).await?;
                        Ok(())
                    })
                    .await
            });
            entered_rx
                .await
                .map_err(|_| make_err!(Code::Internal, "handler did not enter"))?;
            let (done_tx, done_rx) = oneshot::channel();
            *store.shared_context.retirement_observer.lock().unwrap() = Some(done_tx);
            let map = store.get_evicting_map();
            let key = StoreKey::Digest(digest);
            let mut removal = map.remove(&key).boxed();
            assert!(poll!(removal.as_mut()).is_pending());
            assert!(
                !map.contains_if(&key, |_| true),
                "removal and hook dispatch precede cancellation"
            );
            drop(removal);
            let _ = release_tx.send(());
            handler.await.err_tip(|| "handler task failed")??;
            timeout(Duration::from_secs(5), done_rx)
                .await
                .err_tip(|| "owned retirement did not finish")?
                .map_err(|_| make_err!(Code::Internal, "retirement observer dropped"))?;
            assert_eq!(
                fs::metadata(format!("{content}/{DIGEST_FOLDER}/{digest}"))
                    .await
                    .unwrap_err()
                    .code,
                Code::NotFound
            );
            assert_eq!(
                fs::metadata(store.executable_variant_path(&digest))
                    .await
                    .unwrap_err()
                    .code,
                Code::NotFound
            );
            assert!(
                store
                    .shared_context
                    .content_owners
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            assert!(
                store
                    .shared_context
                    .executable_owners
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            assert!(
                store
                    .shared_context
                    .pending_executables
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            Ok(())
        })
        .await
        .err_tip(|| "generation control did not complete")?
    }

    #[nativelink_test]
    async fn late_generation_cleanup_preserves_replacement_executable_and_temporary()
    -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let digest = DigestInfo::new([2; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                block_size: 1,
                ..Default::default()
            })
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let old = store.get_file_entry_for_digest(&digest).await?;
            store
                .with_executable_hardlink_source(&digest, |_| async { Ok(()) })
                .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"9876543210"))
                .await?;
            let variant = store.executable_variant_path(&digest);
            // Recreate the delayed old callback's still-present variant using its actual generation.
            tokio::fs::write(&variant, b"0123456789").await?;
            store
                .shared_context
                .executable_owners
                .lock()
                .unwrap()
                .insert(digest, Arc::downgrade(old.get_encoded_file_path()));
            store
                .with_executable_hardlink_source(&digest, |path| async move {
                    assert_eq!(tokio::fs::read(path).await?, b"9876543210");
                    Ok(())
                })
                .await?;
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 20 of unlimited")
            );
            let current = store.get_file_entry_for_digest(&digest).await?;
            let mut temporary = variant.clone();
            temporary.push(".tmp");
            tokio::fs::write(&temporary, b"replacement temporary").await?;
            store
                .shared_context
                .pending_executables
                .lock()
                .unwrap()
                .insert(
                    digest,
                    PendingExecutable {
                        owner: Arc::downgrade(current.get_encoded_file_path()),
                        path: temporary.clone(),
                    },
                );
            remove_executable_generation(
                &store.shared_context,
                digest,
                old.get_encoded_file_path(),
            )
            .await;
            assert_eq!(tokio::fs::read(&variant).await?, b"9876543210");
            assert_eq!(tokio::fs::read(&temporary).await?, b"replacement temporary");
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 20 of unlimited")
            );
            let mut original = Vec::new();
            old.read_file_part(0, u64::MAX)
                .await?
                .read_to_end(&mut original)
                .await?;
            assert_eq!(original, b"0123456789");
            store
                .get_evicting_map()
                .remove(&StoreKey::Digest(digest))
                .await;
            assert_eq!(
                fs::metadata(&temporary).await.unwrap_err().code,
                Code::NotFound
            );
            assert!(
                store
                    .shared_context
                    .executable_owners
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            assert!(
                store
                    .shared_context
                    .pending_executables
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            Ok(())
        })
        .await
        .err_tip(|| "generation control did not complete")?
    }

    #[nativelink_test]
    async fn weak_owner_registry_releases_last_owner_without_erasing_a_replacement()
    -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                ..Default::default()
            })
            .await?;
            let key = StoreKey::Digest(DigestInfo::new([4; 32], 10));
            let make_owner = || {
                Arc::new(RwLock::new(EncodedFilePath {
                    shared_context: Arc::clone(&store.shared_context),
                    path_type: PathType::Content,
                    key: key.clone(),
                    registered_key: Some(key.clone()),
                }))
            };
            let first = make_owner();
            store
                .shared_context
                .content_owners
                .lock()
                .unwrap()
                .insert(key.clone(), Arc::downgrade(&first));
            let lookup = current_content_owner(&store.shared_context, &key).unwrap();
            drop(first);
            let replacement = make_owner();
            store
                .shared_context
                .content_owners
                .lock()
                .unwrap()
                .insert(key.clone(), Arc::downgrade(&replacement));
            drop(lookup);
            let observed = current_content_owner(&store.shared_context, &key).unwrap();
            assert!(Arc::ptr_eq(&observed, &replacement));
            drop(observed);
            drop(replacement);
            assert!(
                store
                    .shared_context
                    .content_owners
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            assert!(
                store
                    .shared_context
                    .content_locks
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            Ok(())
        })
        .await
        .err_tip(|| "generation control did not complete")?
    }

    #[test]
    fn executable_reservation_rejects_rounding_and_total_overflow() {
        assert_eq!(executable_reservation_bytes(1, 4096), Some((4096, 8192)));
        assert_eq!(
            executable_reservation_bytes(4097, 4096),
            Some((8192, 16384))
        );
        assert_eq!(executable_reservation_bytes(u64::MAX, 1), None);
        assert_eq!(executable_reservation_bytes(u64::MAX, 4096), None);
        assert_eq!(executable_reservation_bytes(1, u64::MAX), None);
        assert_eq!(executable_reservation_bytes(1, 0), None);
    }

    #[derive(Debug)]
    struct RemovalSignal {
        digest: DigestInfo,
        sender: std::sync::Mutex<Option<oneshot::Sender<()>>>,
    }

    impl RemoveItemCallback for RemovalSignal {
        fn callback<'a>(
            &'a self,
            key: StoreKey<'a>,
        ) -> Pin<Box<dyn Future<Output = ()> + Send + 'a>> {
            if key == StoreKey::Digest(self.digest) {
                if let Some(sender) = self.sender.lock().unwrap().take() {
                    let _ = sender.send(());
                }
            }
            Box::pin(async {})
        }
    }

    struct CopyGate {
        entered: std::sync::Mutex<Option<oneshot::Sender<()>>>,
        released: std::sync::Mutex<bool>,
        changed: std::sync::Condvar,
    }

    struct ReleaseCopyGate {
        gate: Arc<CopyGate>,
        slot: &'static std::sync::Mutex<Option<Arc<CopyGate>>>,
    }

    impl Drop for ReleaseCopyGate {
        fn drop(&mut self) {
            self.slot.lock().unwrap().take();
            *self.gate.released.lock().unwrap() = true;
            self.gate.changed.notify_all();
        }
    }

    #[nativelink_test(flavor = "multi_thread")]
    async fn canceled_copy_rollback_cannot_change_a_replacement_charge() -> Result<(), Error> {
        static GATE: std::sync::Mutex<Option<Arc<CopyGate>>> = std::sync::Mutex::new(None);
        timeout(Duration::from_secs(5), async {
            let digest = DigestInfo::new([5; 32], 10);
            let other = DigestInfo::new([6; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new_with_timeout_and_rename_fn(
                &FilesystemSpec {
                    content_path: make_temp_path("content"),
                    temp_path: make_temp_path("temp"),
                    block_size: 1,
                    eviction_policy: Some(nativelink_config::stores::EvictionPolicy {
                        max_count: 1,
                        ..Default::default()
                    }),
                    ..Default::default()
                },
                |from, to| {
                    if to.to_string_lossy().contains(".exec/") {
                        let gate = GATE.lock().unwrap().take();
                        if let Some(gate) = gate {
                            if let Some(sender) = gate.entered.lock().unwrap().take() {
                                let _ = sender.send(());
                            }
                            let mut released = gate.released.lock().unwrap();
                            while !*released {
                                released = gate.changed.wait(released).unwrap();
                            }
                            return Err(std::io::Error::other(
                                "injected executable publication failure",
                            ));
                        }
                    }
                    std::fs::rename(from, to)
                },
            )
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let (entered_tx, entered_rx) = oneshot::channel();
            let gate = Arc::new(CopyGate {
                entered: std::sync::Mutex::new(Some(entered_tx)),
                released: std::sync::Mutex::new(false),
                changed: std::sync::Condvar::new(),
            });
            *GATE.lock().unwrap() = Some(Arc::clone(&gate));
            let release = ReleaseCopyGate { gate, slot: &GATE };
            let creator_store = Arc::clone(&store);
            let creator = tokio::spawn(async move {
                creator_store
                    .with_executable_hardlink_source(&digest, |_| async { Ok(()) })
                    .await
            });
            entered_rx
                .await
                .map_err(|_| make_err!(Code::Internal, "copy did not reach publication"))?;
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 20 of unlimited")
            );

            let (old_removed_tx, old_removed_rx) = oneshot::channel();
            Arc::clone(&store).register_remove_callback(Arc::new(RemovalSignal {
                digest,
                sender: std::sync::Mutex::new(Some(old_removed_tx)),
            }))?;
            let evict_store = Arc::clone(&store);
            let eviction = tokio::spawn(async move {
                evict_store
                    .update_oneshot(other, Bytes::from_static(b"abcdefghij"))
                    .await
            });
            old_removed_rx
                .await
                .map_err(|_| make_err!(Code::Internal, "old map generation not removed"))?;
            let (replacement_tx, replacement_rx) = oneshot::channel();
            Arc::clone(&store).register_remove_callback(Arc::new(RemovalSignal {
                digest: other,
                sender: std::sync::Mutex::new(Some(replacement_tx)),
            }))?;
            let replacement_store = Arc::clone(&store);
            let replacement = tokio::spawn(async move {
                replacement_store
                    .update_oneshot(digest, Bytes::from_static(b"replacement bytes"))
                    .await
            });
            replacement_rx
                .await
                .map_err(|_| make_err!(Code::Internal, "replacement not admitted"))?;
            creator.abort();
            assert!(creator.await.unwrap_err().is_cancelled());
            drop(release);
            // Acquiring admission proves the detached creator finished its failed-copy rollback.
            let admission = ExecutableLockRegistration::new(&store.executable_admissions, digest);
            let admitted = admission.lock().await;
            drop(admitted);
            drop(admission);
            replacement.await.err_tip(|| "replacement task failed")??;
            eviction.await.err_tip(|| "eviction task failed")??;
            assert_eq!(store.has(digest).await?, Some(17));
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 17 of unlimited")
            );
            store
                .with_executable_hardlink_source(&digest, |path| async move {
                    assert_eq!(tokio::fs::read(path).await?, b"replacement bytes");
                    Ok(())
                })
                .await?;
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 34 of unlimited")
            );
            assert!(
                store
                    .shared_context
                    .pending_executables
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            Ok(())
        })
        .await
        .err_tip(|| "copy supersession did not complete")?
    }

    fn arm_executable_pause(
        slot: &std::sync::Mutex<Option<ExecutablePause>>,
    ) -> (oneshot::Receiver<()>, oneshot::Sender<()>) {
        let (entered_tx, entered_rx) = oneshot::channel();
        let (resume_tx, resume_rx) = oneshot::channel();
        assert!(
            slot.lock()
                .unwrap()
                .replace((entered_tx, resume_rx))
                .is_none()
        );
        (entered_rx, resume_tx)
    }

    async fn pause_entered(receiver: oneshot::Receiver<()>) -> Result<(), Error> {
        receiver
            .await
            .map_err(|_| make_err!(Code::Internal, "executable pause was not reached"))
    }

    fn assert_missing_execute_status(error: Error, digest: DigestInfo) {
        use nativelink_proto::google::rpc::PreconditionFailure;
        use nativelink_util::action_messages::{ActionResult, to_execute_response};
        use prost::Message;
        assert_eq!(error.code, Code::NotFound);
        let response = to_execute_response(ActionResult {
            error: Some(error),
            ..Default::default()
        });
        let status = response.status.unwrap();
        assert_eq!(status.code, Code::FailedPrecondition as i32);
        assert_eq!(status.details.len(), 1);
        let details = PreconditionFailure::decode(status.details[0].value.as_slice()).unwrap();
        assert_eq!(details.violations.len(), 1);
        assert_eq!(details.violations[0].r#type, "MISSING");
        assert_eq!(
            details.violations[0].subject,
            format!("blobs/{}/{}", digest.packed_hash(), digest.size_bytes())
        );
    }

    #[nativelink_test]
    async fn eviction_after_reservation_preserves_missing_blob_recovery() -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let digest = DigestInfo::new([7; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                block_size: 1,
                ..Default::default()
            })
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let (entered, resume) =
                arm_executable_pause(&store.shared_context.executable_reservation_pause);
            let materializing = Arc::clone(&store);
            let task = tokio::spawn(async move {
                materializing
                    .with_executable_hardlink_source(&digest, |_| async { Ok(()) })
                    .await
            });
            pause_entered(entered).await?;
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 20 of unlimited")
            );
            store
                .get_evicting_map()
                .remove(&StoreKey::Digest(digest))
                .await;
            let _ = resume.send(());
            let error = task
                .await
                .err_tip(|| "materialization task failed")?
                .expect_err("evicted input is missing");
            assert_missing_execute_status(error, digest);
            assert!(
                store
                    .shared_context
                    .pending_executables
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            Ok(())
        })
        .await
        .err_tip(|| "post-reservation missing recovery did not finish")?
    }

    #[nativelink_test]
    async fn replacement_after_reservation_is_resolved_once_without_false_missing()
    -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let digest = DigestInfo::new([8; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                block_size: 1,
                ..Default::default()
            })
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let (entered, resume) =
                arm_executable_pause(&store.shared_context.executable_reservation_pause);
            let materializing = Arc::clone(&store);
            let task = tokio::spawn(async move {
                materializing
                    .with_executable_hardlink_source(&digest, |path| async move {
                        Ok(tokio::fs::read(path).await?)
                    })
                    .await
            });
            pause_entered(entered).await?;
            store
                .get_evicting_map()
                .remove(&StoreKey::Digest(digest))
                .await;
            store
                .update_oneshot(digest, Bytes::from_static(b"replacement bytes"))
                .await?;
            let _ = resume.send(());
            assert_eq!(
                task.await.err_tip(|| "materialization task failed")??,
                b"replacement bytes"
            );
            assert_eq!(store.has(digest).await?, Some(17));
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 34 of unlimited")
            );
            Ok(())
        })
        .await
        .err_tip(|| "post-reservation replacement did not finish")?
    }

    #[nativelink_test]
    async fn repeated_replacement_after_ready_is_bounded_without_false_missing() -> Result<(), Error>
    {
        timeout(Duration::from_secs(5), async {
            let digest = DigestInfo::new([9; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                block_size: 1,
                ..Default::default()
            })
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let calls = Arc::new(AtomicU64::new(0));
            let handler_calls = Arc::clone(&calls);
            let (first_entered, first_resume) =
                arm_executable_pause(&store.shared_context.executable_ready_pause);
            let materializing = Arc::clone(&store);
            let task = tokio::spawn(async move {
                materializing
                    .with_executable_hardlink_source(&digest, |_| async move {
                        handler_calls.fetch_add(1, Ordering::Relaxed);
                        Ok(())
                    })
                    .await
            });
            pause_entered(first_entered).await?;
            store
                .get_evicting_map()
                .remove(&StoreKey::Digest(digest))
                .await;
            store
                .update_oneshot(digest, Bytes::from_static(b"abcdefghij"))
                .await?;
            let (second_entered, second_resume) =
                arm_executable_pause(&store.shared_context.executable_ready_pause);
            let _ = first_resume.send(());
            pause_entered(second_entered).await?;
            store
                .get_evicting_map()
                .remove(&StoreKey::Digest(digest))
                .await;
            store
                .update_oneshot(digest, Bytes::from_static(b"ABCDEFGHIJ"))
                .await?;
            let _ = second_resume.send(());
            let error = task
                .await
                .err_tip(|| "materialization task failed")?
                .expect_err("two replaced generations exhaust this public call");
            assert_eq!(error.code, Code::Aborted);
            assert_eq!(error.context, ErrorContext::None);
            assert_eq!(calls.load(Ordering::Relaxed), 0);
            assert_eq!(
                store.get_part_unchunked(digest, 0, None).await?,
                Bytes::from_static(b"ABCDEFGHIJ")
            );
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 10 of unlimited")
            );
            Ok(())
        })
        .await
        .err_tip(|| "post-ready generation churn was not bounded")?
    }

    #[nativelink_test]
    async fn canceled_caller_after_reservation_keeps_owned_allocation_completion()
    -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            let digest = DigestInfo::new([10; 32], 10);
            let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                content_path: make_temp_path("content"),
                temp_path: make_temp_path("temp"),
                block_size: 1,
                ..Default::default()
            })
            .await?;
            store
                .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                .await?;
            let (entered, resume) =
                arm_executable_pause(&store.shared_context.executable_reservation_pause);
            let materializing = Arc::clone(&store);
            let task = tokio::spawn(async move {
                materializing
                    .with_executable_hardlink_source(&digest, |_| async { Ok(()) })
                    .await
            });
            pause_entered(entered).await?;
            task.abort();
            assert!(task.await.unwrap_err().is_cancelled());
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 20 of unlimited")
            );
            let _ = resume.send(());
            let admission = ExecutableLockRegistration::new(&store.executable_admissions, digest);
            let admitted = admission.lock().await;
            drop(admitted);
            drop(admission);
            assert_eq!(
                fs::metadata(store.executable_variant_path(&digest))
                    .await?
                    .len(),
                10
            );
            assert!(
                store
                    .shared_context
                    .pending_executables
                    .lock()
                    .unwrap()
                    .is_empty()
            );
            store
                .get_evicting_map()
                .remove(&StoreKey::Digest(digest))
                .await;
            assert!(
                store
                    .get_eviction_snapshot()
                    .to_string()
                    .starts_with("Bytes: 0 of unlimited")
            );
            Ok(())
        })
        .await
        .err_tip(|| "canceled reservation owner did not finish")?
    }

    #[nativelink_test]
    async fn unmatched_reservation_is_superseded_not_capacity_failure() -> Result<(), Error> {
        timeout(Duration::from_secs(5), async {
            for replace in [false, true] {
                let digest = DigestInfo::new([11; 32], 10);
                let store = FilesystemStore::<FileEntryImpl>::new(&FilesystemSpec {
                    content_path: make_temp_path("content"),
                    temp_path: make_temp_path("temp"),
                    block_size: 1,
                    ..Default::default()
                })
                .await?;
                store
                    .update_oneshot(digest, Bytes::from_static(b"0123456789"))
                    .await?;
                let primary = store.get_file_entry_for_digest(&digest).await?;
                let admission =
                    ExecutableLockRegistration::new(&store.executable_admissions, digest);
                let admitted = admission.lock().await;
                let creating = Arc::clone(&store);
                let task = tokio::spawn(async move {
                    let path = creating.executable_variant_path(&digest);
                    creating
                        .create_executable_variant(&digest, &path, primary)
                        .await
                });
                store
                    .get_evicting_map()
                    .remove(&StoreKey::Digest(digest))
                    .await;
                if replace {
                    store
                        .update_oneshot(digest, Bytes::from_static(b"replacement bytes"))
                        .await?;
                }
                drop(admitted);
                drop(admission);
                assert_eq!(
                    task.await.err_tip(|| "creation task failed")??,
                    ExecutableCreation::Superseded
                );
                assert_eq!(store.has(digest).await?, replace.then_some(17));
                assert_eq!(
                    fs::metadata(store.executable_variant_path(&digest))
                        .await
                        .unwrap_err()
                        .code,
                    Code::NotFound
                );
            }
            Ok(())
        })
        .await
        .err_tip(|| "unmatched reservation did not finish")?
    }
}
