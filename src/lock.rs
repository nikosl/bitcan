use fs4::{lock_contended_error, FileExt as _};
use snafu::prelude::*;
use std::fs::{self, File, OpenOptions};
use std::path::{Path, PathBuf};

use snafu::Whatever;

type Result<T> = std::result::Result<T, Whatever>;

struct FileUninit;
struct FileInit;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum DirLockState {
    Locked,
    Unlocked,
}

#[derive(Debug)]
pub(crate) struct DirLock(File, PathBuf);

impl DirLock {
    pub fn lock(&self) -> Result<DirLockState> {
        match self.0.try_lock_exclusive() {
            Ok(()) => Ok(DirLockState::Unlocked),
            Err(e) => {
                if e.kind() == lock_contended_error().kind() {
                    Ok(DirLockState::Locked)
                } else {
                    whatever!("failed to lock: {:?}", e)
                }
            }
        }
    }

    pub(crate) fn unlock(&self) -> Result<()> {
        self.0
            .unlock()
            .with_whatever_context(|e| format!("failed to unlock: {e:?}"))?;

        fs::remove_file(&self.1)
            .with_whatever_context(|e| format!("failed to remove lock file: {e:?}"))
    }

    pub(crate) fn open(p: impl AsRef<Path>) -> Result<Self> {
        let p = p.as_ref();
        let f = Self::open_file(p)?;

        Ok(Self(f, p.to_owned()))
    }

    fn open_file(p: &Path) -> Result<File> {
        OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(false)
            .open(p)
            .with_whatever_context(|e| format!("failed to open lock file: {e}"))
    }
}

impl Drop for DirLock {
    fn drop(&mut self) {
        let _lock = self.unlock();
        let _close = fs::remove_file(&self.1);
    }
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    #[test]
    fn test_lock_unlock() {
        let lockf = assert_fs::NamedTempFile::new("lock_file").unwrap();
        let lock_file_path = lockf.path();

        let dir_lock = DirLock::open(lock_file_path).unwrap();

        // Ensure the initial state is unlocked
        assert_eq!(dir_lock.lock().unwrap(), DirLockState::Unlocked);

        // Lock the directory
        assert_eq!(dir_lock.lock().unwrap(), DirLockState::Locked);

        // Unlock the directory
        assert!(dir_lock.unlock().is_ok());

        // Ensure the directory is unlocked after unlocking
        assert_eq!(dir_lock.lock().unwrap(), DirLockState::Unlocked);
    }

    #[test]
    fn test_lock_cleanup() {
        let lockf = assert_fs::NamedTempFile::new("lock_file").unwrap();
        let lock_file_path = lockf.path();

        let dir_lock = DirLock::open(lock_file_path).unwrap();
        dir_lock.lock().unwrap();

        mem::drop(dir_lock);

        assert!(
            !lock_file_path.exists(),
            "lock file should not exist after drop"
        );
    }
}
