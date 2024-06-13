#![allow(dead_code, unused)]
#![warn(clippy::pedantic)]
#![doc = include_str!("../README.md")]

mod lock;
mod log;
mod model;

use std::collections::{BTreeMap, HashMap};
use std::fs::{self, File, OpenOptions};
use std::io::{self, prelude::*};
use std::io::{ErrorKind, SeekFrom};
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use fs4::{lock_contended_error, FileExt};

use lock::{DirLock, DirLockState};
use log::hint::{HintFile, HintRO, HintRW};
use log::FileId;
use model::LogEntryHeader;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use snafu::{prelude::*, Whatever};

use crate::model::{KeyEntry, LogEntry, Timestamp};

type Result<T> = std::result::Result<T, Whatever>;

pub const DIR_WR_LOCK: &str = ".bitcask.lock";
const MERGE_LOCK: &str = ".bitcask.merge.lock";

#[derive(Debug)]
#[must_use]
pub struct Bitcan<K, V> {
    directory: PathBuf,
    data_files: DataFiles<K, V>,
    key_dir: KeyDir<K>,
    dir_lock: DirLock,
    active_file: ActiveDataFile<K, V>,
    rw_instance: bool,
}

impl<K, V> Bitcan<K, V>
where
    K: DeserializeOwned + Serialize + std::hash::Hash + Eq + Clone,
    V: DeserializeOwned + Serialize,
{
    /// Opens a Bitcan database at the specified path.
    ///
    /// # Arguments
    ///
    /// * `p` - The path to the Bitcan database.
    ///
    /// # Returns
    ///
    /// Returns a `Result` containing the opened Bitcan database if successful, or an error if the database cannot be opened.
    ///
    /// # Errors
    ///
    /// Returns an error if the database cannot be opened.
    pub fn open(p: impl AsRef<Path>) -> Result<Self> {
        let p = p.as_ref();
        // TODO: recreate the key directory using hint files

        let dir_lock = DirLock::open(p.join(DIR_WR_LOCK))?;
        let rw_instance = matches!(dir_lock.lock(), Ok(DirLockState::Unlocked));

        let mut data_files = DataFiles::open(p)?;
        let key_dir = data_files.key_dir()?;

        // TODO: RO instance should not have an active file
        let (active_file, df) = ActiveDataFile::create(p)?;
        data_files.insert(df.file_id, df);

        Ok(Self {
            directory: p.to_owned(),
            data_files,
            key_dir,
            dir_lock,
            active_file,
            rw_instance,
        })
    }

    /// Puts a key-value pair into the Bitcan database.
    /// If the key already exists, the value will be updated.
    /// If the key does not exist, a new key-value pair will be created.
    /// The key and value must be serializable.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to insert.
    /// * `value` - The value to insert.
    ///
    /// # Returns
    ///
    /// Returns a `Result` containing `()` if successful, or an error if the key-value pair cannot be inserted.
    ///
    /// # Errors
    ///
    /// Returns an error if the key-value pair cannot be inserted.
    pub fn put(&mut self, key: K, value: &V) -> Result<()>
    where
        K: Serialize,
        V: Serialize,
    {
        ensure_whatever!(self.rw_instance, "read-only instance");

        let key_entry = self.active_file.append(&key, value)?;
        self.key_dir.insert(key, key_entry);

        Ok(())
    }

    /// Deletes a key-value pair from the Bitcan database.
    /// If the key does not exist, nothing will happen.
    /// The key must be serializable.
    ///
    /// # Arguments
    ///
    /// # Returns
    ///
    /// # Errors
    ///
    /// # Example
    ///
    pub fn get(&mut self, key: &K) -> Result<Option<V>> {
        if let Some(ke) = self.key_dir.get(key) {
            let mut df = self
                .data_files
                .get_mut(ke.file_id())
                .with_whatever_context(|| "no data file")?;

            let v: V = df.get(ke)?;

            Ok(Some(v))
        } else {
            Ok(None)
        }
    }

    /// Deletes a key-value pair from the Bitcan database.
    ///
    /// # Arguments
    /// * `key` - The key to remove.
    ///
    /// # Returns
    /// ()
    ///
    /// # Errors
    ///
    /// Returns an error if the key-value pair cannot be removed.
    pub fn remove(&mut self, key: &K) -> Result<()> {
        ensure_whatever!(self.rw_instance, "read-only instance");

        if let Some(item) = self.key_dir.get(key) {
            self.active_file.tombstone(key)?;
            self.active_file.lost(u64::from(item.value_size()));

            self.key_dir.remove(key);
        }

        Ok(())
    }

    /// Syncs the Bitcan database to disk.
    ///
    /// # Errors
    ///
    /// Returns an error if the database cannot be synced.
    pub fn sync(&mut self) -> Result<()> {
        self.active_file.sync()
    }

    /// Flushes the Bitcan database to disk.
    ///
    /// # Errors
    ///
    /// Returns an error if the database cannot be flushed.
    pub fn flush(&mut self) -> Result<()> {
        self.active_file.flush()
    }

    /// Merges the data files in the Bitcan database.
    ///
    /// # Errors
    ///
    /// Returns an error if the data files cannot be merged.
    pub fn merge(&mut self) -> Result<()> {
        ensure_whatever!(self.rw_instance, "read-only instance");

        let lock = DirLock::open(self.path().join(MERGE_LOCK))?;
        ensure_whatever!(
            matches!(lock.lock(), Ok(DirLockState::Unlocked)),
            "merge lock contended"
        );

        let mut merge_keydir = KeyDir::<K>::new();
        let mut merge_datafiles = DataFiles::new(self.path());

        let (mut merge_file, df) = ActiveDataFile::create(self.path())?;
        let mut hint_file: HintFile<K, HintRW> = HintFile::write(*df.file_id(), self.path())?;

        merge_datafiles.insert(df.file_id, df);

        for (k, ke) in &self.key_dir.0 {
            let mut df = self
                .data_files
                .get_mut(ke.file_id())
                .with_whatever_context(|| "no data file")?;

            let le = df.get_log_entry(ke)?;
            let ke = merge_file.append_log_entry(&le, ke.timestamp())?;
            hint_file.append_keyentry(k.clone(), &ke)?;

            merge_keydir.insert(k.clone(), ke);
        }

        merge_file.sync()?;
        hint_file.sync()?;

        for df in self.data_files.iter() {
            fs::remove_file(df.path()).whatever_context("failed to remove file")?;
        }

        self.key_dir = merge_keydir;
        self.data_files = merge_datafiles;

        let (active_file, df) = ActiveDataFile::create(self.path())?;
        self.active_file = active_file;
        self.data_files.insert(*df.file_id(), df);

        // write hint file
        lock.unlock()?;

        Ok(())
    }

    pub fn fold<B, F>(&mut self, init: B, mut f: F) -> B
    where
        V: DeserializeOwned,
        F: FnMut(B, Result<(&K, V)>) -> B,
    {
        let mut b = init;
        for (k, ke) in &self.key_dir.0 {
            let r = self
                .data_files
                .get_mut(ke.file_id())
                .whatever_context("no data file")
                .and_then(move |df| df.get(ke))
                .map(move |v| (k, v));

            b = f(b, r);
        }
        b
    }

    /// Returns the path to the Bitcan database.
    /// The path is a reference to the directory containing the database.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.directory
    }

    /// Closes the Bitcan database.
    ///
    /// # Errors
    ///
    /// Returns an error if the database cannot `sync` data or
    /// if it cannot release the directory lock.
    pub fn close(mut self) -> Result<()> {
        self.sync()?;
        self.dir_lock.unlock()
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.key_dir.keys()
    }

    pub fn iter(&mut self) -> impl Iterator<Item = Result<(&'_ K, V)>>
    where
        V: DeserializeOwned,
    {
        Elems {
            bitcan: &mut self.data_files,
            iter: self.key_dir.0.iter(),
        }
    }
}

impl<'b, K, V> Iterator for Elems<'b, K, V>
where
    K: DeserializeOwned + Serialize + std::hash::Hash + Eq + Clone,
    V: DeserializeOwned + Serialize,
{
    type Item = Result<(&'b K, V)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, ke)| {
            let df = self
                .bitcan
                .get_mut(ke.file_id())
                .with_whatever_context(|| "no data file")?;

            let v: V = df.get(ke)?;

            Ok((k, v))
        })
    }
}

pub struct Elems<'b, K, V> {
    bitcan: &'b mut DataFiles<K, V>,
    iter: std::collections::hash_map::Iter<'b, K, KeyEntry>,
}

#[derive(Debug)]
#[must_use]
pub(crate) struct DataFile<K, V> {
    file_id: FileId,
    path: PathBuf,
    handle: File,
    _elems: std::marker::PhantomData<(K, V)>,
}

impl<K, V> DataFile<K, V>
where
    K: DeserializeOwned,
    V: DeserializeOwned,
{
    pub fn open(file_id: FileId, path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        ensure_whatever!(path.is_dir(), "not a directory");

        let path = file_id.datafile(path);
        ensure_whatever!(path.exists(), "data file does not exist: {path:?}");

        let handle = OpenOptions::new()
            .read(true)
            .open(&path)
            .with_whatever_context(|e| format!("failed to open file for read: {e}"))?;

        Ok(Self {
            file_id,
            path,
            handle,
            _elems: std::marker::PhantomData,
        })
    }

    pub fn get(&mut self, k: &KeyEntry) -> Result<V> {
        ensure_whatever!(*k.file_id() == self.file_id, "file_id mismatch");

        let len = k.value_size() as usize;
        let mut val = vec![0u8; len];

        self.read_bytes(k.offset(), &mut val)?;

        let v: V = LogEntry::deserialize(&val)?;

        Ok(v)
    }

    pub fn get_key_entry(&mut self, from: u64) -> Result<(K, KeyEntry)>
    where
        K: DeserializeOwned,
    {
        self.seek_at(from)?;

        let header = LogEntryHeader::from_reader(&mut self.handle)?;

        let key_offset = self.offset()?;

        let key_size = header.key_size();
        let mut key = vec![0u8; key_size as usize];
        self.read_bytes(key_offset, &mut key)?;

        let offset = self.offset()?;

        let key = LogEntry::deserialize(&key)?;
        let key_entry = KeyEntry::new(
            self.file_id,
            from,
            header.value_size(),
            offset,
            header.timestamp(),
        );

        let next_record = (offset + u64::from(header.value_size()));
        self.seek_at(next_record)?;

        Ok((key, key_entry))
    }

    pub fn get_log_entry(&mut self, k: &KeyEntry) -> Result<LogEntry> {
        ensure_whatever!(*k.file_id() == self.file_id, "file_id mismatch");

        let offset = k.start_offset();
        self.seek_at(offset)?;

        LogEntry::from_reader(&mut self.handle)
    }

    fn read_bytes(&mut self, from: u64, at: &mut [u8]) -> Result<()> {
        self.seek_at(from)?;

        self.handle
            .read_exact(at)
            .whatever_context("failed to read")?;

        Ok(())
    }

    // fn read_element<K, V>(&mut self, from: u64) -> Result<Element<K, V>>
    // where
    //     K: DeserializeOwned,
    //     V: DeserializeOwned,
    // {
    //     self.handle
    //         .seek(SeekFrom::Start(from))
    //         .whatever_context("failed to seek")?;

    //     let le = self.read_entry(from)?;

    //     let k = le.key_deserialize()?;
    //     let v = le.value_deserialize()?;

    //     Ok(Element { key: k, value: v })
    // }

    fn read_entry(&mut self, from: u64) -> Result<LogEntry> {
        self.seek_at(from)?;

        LogEntry::from_reader(&mut self.handle)
    }

    pub fn len(&self) -> u64 {
        self.handle.metadata().expect("non usable record").len()
    }

    pub fn keys(&mut self) -> Result<DataFileKeyIter<K, V>> {
        self.seek_at(0).map(|_| DataFileKeyIter {
            file: self,
            offset: 0,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn file_id(&self) -> &FileId {
        &self.file_id
    }

    pub fn hint(&self) -> Option<Result<HintFile<K, HintRO>>> {
        let parent = self.path.parent()?;
        let hint = self.file_id.hintfile(parent);

        if hint.exists() {
            Some(HintFile::read(self.file_id, parent))
        } else {
            None
        }
    }

    fn seek_at(&mut self, offset: u64) -> Result<u64> {
        self.handle
            .seek(SeekFrom::Start(offset))
            .whatever_context("failed to seek")
    }

    fn offset(&mut self) -> Result<u64> {
        self.handle
            .stream_position()
            .whatever_context("failed to get offset")
    }
}

struct DataFileKeyIter<'f, K, V> {
    file: &'f mut DataFile<K, V>,
    offset: u64,
}

impl<'f, K, V> Iterator for DataFileKeyIter<'f, K, V>
where
    K: DeserializeOwned,
    V: DeserializeOwned,
{
    type Item = Result<(K, KeyEntry)>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.file.len() {
            return None;
        }

        let e = self.file.get_key_entry(self.offset).and_then(|(k, ke)| {
            let cur = self.file.offset()?;

            self.offset = cur; //+ u64::from(ke.value_size());

            Ok((k, ke))
        });

        Some(e)
    }
}

// impl Iterator for DataFileIterator {
//     type Item = Result<LogEntry>;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.offset >= self.file.len() {
//             return None;
//         }

//         let entry = LogEntry::from_reader(&mut self.file.handle)
//             .whatever_context("failed to read entry")
//             .and_then(|e| {
//                 self.offset = self
//                     .file
//                     .handle
//                     .stream_position()
//                     .whatever_context("fail to seek")?;

//                 Ok(e)
//             });

//         Some(entry)
//     }
// }

// impl<> TryFrom<ActiveDataFile> for DataFile<K, V> {
//     type Error = Whatever;

//     fn try_from(value: ActiveDataFile) -> std::prelude::v1::Result<Self, Self::Error> {
//         let p = value.path.parent().expect("no parent");

//         Self::open(value.file_id, p)
//     }
// }

#[derive(Debug)]
#[must_use]
pub(crate) struct ActiveDataFile<K, V> {
    file_id: FileId,
    path: PathBuf,
    handle: File,
    offset: u64,
    lost_bytes: u64,
    _elems: std::marker::PhantomData<(K, V)>,
}

impl<K, V> ActiveDataFile<K, V> {
    fn len(&self) -> u64 {
        self.handle.metadata().unwrap().len()
    }

    fn created(&self) -> SystemTime {
        self.handle.metadata().unwrap().created().unwrap()
    }

    fn modified(&self) -> SystemTime {
        self.handle.metadata().unwrap().modified().unwrap()
    }
}

impl<K, V> ActiveDataFile<K, V>
where
    K: DeserializeOwned + Serialize,
    V: DeserializeOwned + Serialize,
{
    pub fn create(p: impl AsRef<Path>) -> Result<(ActiveDataFile<K, V>, DataFile<K, V>)> {
        let p = p.as_ref();

        Self::create_datafiles(p)
    }

    pub fn append(&mut self, key: &K, value: &V) -> Result<KeyEntry> {
        let timestamp = Timestamp::now();
        let entry_offset = self.offset()?;

        let entry = LogEntry::new(key, value, timestamp)?;
        let offset = self.append_bytes(&entry.to_bytes())?;

        let value_size = entry.value_size();
        let value_offset = offset - u64::from(value_size);

        let ke = KeyEntry::new(
            self.file_id,
            entry_offset,
            value_size,
            value_offset,
            timestamp,
        );

        Ok(ke)
    }

    pub fn tombstone(&mut self, key: &K) -> Result<u64> {
        let ts = Timestamp::now();
        let tombstone = LogEntry::tombstone(key, ts)?.to_bytes();

        self.append_bytes(&tombstone)
    }

    pub fn sync(&mut self) -> Result<()> {
        self.handle.sync_all().whatever_context("failed to sync")
    }

    pub fn flush(&mut self) -> Result<()> {
        self.handle.sync_data().whatever_context("failed to sync")
    }

    pub fn lost(&mut self, b: u64) {
        self.lost_bytes += b;
    }

    pub(crate) fn append_log_entry(
        &mut self,
        le: &LogEntry,
        timestamp: Timestamp,
    ) -> Result<KeyEntry> {
        let entry_offset = self.offset()?;

        let entry = le.to_bytes();
        let offset = self.append_bytes(&entry)?;

        let value_size = le.value_size();
        let value_offset = offset - u64::from(value_size);

        Ok(KeyEntry::new(
            self.file_id,
            entry_offset,
            value_size,
            value_offset,
            timestamp,
        ))
    }

    fn append_bytes(&mut self, buf: &[u8]) -> Result<u64> {
        self.handle
            .write_all(buf)
            .whatever_context("failed to write to file")?;

        self.offset = self.offset()?;

        Ok(self.offset)
    }

    fn create_datafiles(p: &Path) -> Result<(ActiveDataFile<K, V>, DataFile<K, V>)> {
        ensure_whatever!(p.is_dir(), "not a directory");

        let file_id = FileId::new();
        let ap = file_id.datafile(p);
        ensure_whatever!(!ap.exists(), "data file already exists: {ap:?}");

        let write_handle = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&ap)
            .with_whatever_context(|e| format!("failed to open file for writing: {e}"))?;

        // write_handle
        //     .allocate(4096)
        //     .whatever_context("failed to allocate space")?;

        write_handle.sync_all().whatever_context("failed to sync")?;

        let offset = 0;
        let since = Timestamp::now();

        let af = ActiveDataFile {
            file_id,
            path: ap,
            handle: write_handle,
            offset,
            lost_bytes: 0,
            _elems: std::marker::PhantomData,
        };

        let rf = DataFile::open(file_id, p)?;

        Ok((af, rf))
    }

    fn offset(&mut self) -> Result<u64> {
        self.handle
            .stream_position()
            .whatever_context("failed to get offset")
    }
}

impl<K, V> io::Write for ActiveDataFile<K, V> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.handle.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.handle.flush()
    }
}

#[derive(Debug)]
#[must_use]
struct DataFiles<K, V>(BTreeMap<FileId, DataFile<K, V>>, PathBuf);

impl<K, V> DataFiles<K, V>
where
    K: DeserializeOwned + Serialize + std::hash::Hash + Eq + Clone,
    V: DeserializeOwned + Serialize,
{
    pub fn open(p: impl Into<PathBuf>) -> Result<Self> {
        let p = p.into();
        ensure_whatever!(p.is_dir(), "not a directory");

        let dir = fs::read_dir(&p).with_whatever_context(|e| format!("failed to read dir: {e}"))?;
        let dir = dir
            .map(|e| {
                e.map(|e| e.path())
                    .with_whatever_context(|e| format!("failed to read entry: {e}"))
            })
            .collect::<Result<Vec<_>>>()?;

        let data_files = dir
            .iter()
            .filter(|p| p.is_file())
            .filter_map(|p| {
                let ext = p.extension().and_then(|e| e.to_str())?;
                let name = p.file_stem().and_then(|e| e.to_str())?;

                Some((name, ext))
            })
            .filter_map(|(name, ext)| if ext == "data" { Some(name) } else { None })
            .map(FileId::open)
            .map(|fid| {
                let fid = fid?;
                let df = DataFile::open(fid, &p)?;

                Ok((fid, df))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;

        Ok(Self(data_files, p))
    }

    pub fn key_dir(&mut self) -> Result<KeyDir<K>>
    where
        K: DeserializeOwned + Serialize + std::hash::Hash + Eq + Clone,
    {
        let key_dir = self
            .0
            .iter_mut()
            .map(|(_fid, df)| {
                let mut df = df;
                let keys = df.keys()?;

                Ok(keys)
            })
            .collect::<Result<Vec<_>>>()?;

        let mut keys = HashMap::new();
        for entry in key_dir.into_iter().flatten() {
            let (k, ke) = entry?;
            if ke.is_tombstone() {
                keys.remove(&k);
            } else {
                keys.insert(k, ke);
            }
        }

        Ok(KeyDir(keys))
    }

    pub fn new(dir: impl Into<PathBuf>) -> Self {
        DataFiles(BTreeMap::new(), dir.into())
    }

    pub(crate) fn get(&self, file_id: &FileId) -> Option<&DataFile<K, V>> {
        self.0.get(file_id)
    }

    pub(crate) fn get_mut(&mut self, file_id: &FileId) -> Option<&mut DataFile<K, V>> {
        self.0.get_mut(file_id)
    }

    pub(crate) fn insert(&mut self, file_id: FileId, df: DataFile<K, V>) {
        self.0.insert(file_id, df);
    }

    pub(crate) fn remove(&mut self, file_id: &FileId) {
        self.0.remove(file_id);
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn iter(&mut self) -> impl Iterator<Item = &DataFile<K, V>> {
        self.0.values()
    }
}

#[derive(Debug, Default)]
#[must_use]
struct KeyDir<K>(HashMap<K, KeyEntry>);

impl<K> KeyDir<K>
where
    K: std::hash::Hash + Eq + Clone,
{
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn insert(&mut self, key: K, ke: KeyEntry) {
        self.0.insert(key, ke);
    }

    fn remove(&mut self, key: &K) {
        self.0.remove(key);
    }

    fn get(&self, key: &K) -> Option<&KeyEntry> {
        self.0.get(key)
    }

    fn keys(&self) -> impl Iterator<Item = &K> {
        self.0.keys()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K> FromIterator<(K, KeyEntry)> for KeyDir<K>
where
    K: std::hash::Hash + Eq + Clone,
{
    fn from_iter<T: IntoIterator<Item = (K, KeyEntry)>>(iter: T) -> Self {
        KeyDir(iter.into_iter().collect())
    }
}

struct Element<'b, K, V> {
    key: &'b K,
    value: V,
}

#[cfg(test)]
mod tests {
    use std::u8;

    use super::*;
    use assert_fs::prelude::*;
    use bincode::Options;
    use insta::assert_yaml_snapshot;
    use predicates::prelude::*;
    use serde_binary::binary_stream::Endian;
    use serde_json::Value;

    #[test]
    fn test_datafile_create() -> Result<()> {
        let datadir = assert_fs::TempDir::new().unwrap();
        let (active, _): (ActiveDataFile<u16, u16>, _) = ActiveDataFile::create(&datadir)?;

        datadir
            .child(format!("{}.data", active.file_id).as_str())
            .assert(predicate::path::exists());

        Ok(())
    }

    #[allow(clippy::cast_possible_truncation)]
    #[test]
    fn test_datafile_append() -> Result<()> {
        let datadir = assert_fs::TempDir::new().unwrap().into_persistent_if(false);
        let (mut active, _) = ActiveDataFile::create(&datadir)?;

        let key = b"key";
        let value = b"value";

        let value_size = bincode::options()
            .with_big_endian()
            .serialize(value)
            .with_whatever_context(|_| "failed to serialize value")?
            .len() as u32;

        let key_entry = active.append(key, value).unwrap();

        assert_eq!(*key_entry.file_id(), active.file_id, "file_id");
        assert_eq!(key_entry.value_size(), value_size, "value_size");
        assert_eq!(
            key_entry.offset(),
            active.len() - u64::from(value_size),
            "offset"
        );

        Ok(())
    }

    #[allow(clippy::cast_possible_truncation)]
    #[test]
    fn test_datafile_append_read() -> Result<()> {
        let datadir = assert_fs::TempDir::new().unwrap().into_persistent_if(false);
        let (mut active, mut df) = ActiveDataFile::create(&datadir)?;

        let key = "key".to_owned();
        let value = "value".to_owned();

        let keya = "keyabcdef".to_owned();
        let valuea = "value_abcdef".to_owned();

        let key_entry = active.append(&key, &value).unwrap();
        let key_entry_a = active.append(&keya, &valuea).unwrap();

        let fid = df.file_id().to_string();
        assert_yaml_snapshot!(key_entry, { ".file_id" =>insta::dynamic_redaction(move |val, _| {
            assert_eq!(val.as_str().unwrap(), fid);
            "file_id"
        }), 
    ".timestamp" =>"ts" });

        let vbuff = df.get(&key_entry)?;
        assert_yaml_snapshot!(vbuff);

        let vbuff = df.get(&key_entry_a)?;
        assert_yaml_snapshot!(vbuff);

        Ok(())
    }

    #[test]
    fn test_datafile_append_m_get() -> Result<()> {
        #[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
        struct KeyStruct {
            key: u32,
            data: u32,
        }

        let datadir = assert_fs::TempDir::new().unwrap().into_persistent_if(false);

        let (mut active, mut ro) = ActiveDataFile::create(&datadir)?;

        let key = KeyStruct::default(); //serde_json::json!({"key": "value"}).to_string();
        let value = serde_json::json!({"value": "value"}).to_string();

        let _entry = active.append(&key, &value).unwrap();
        let key_entry = active.append(&key, &value).unwrap();
        let v: String = ro.get(&key_entry)?;

        assert_eq!(v, value);

        Ok(())
    }

    #[test]
    fn test_datafile_append_get() -> Result<()> {
        #[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
        struct KeyStruct {
            key: u32,
            data: u32,
        }
        let datadir = assert_fs::TempDir::new().unwrap().into_persistent_if(false);
        let (mut active, mut ro) = ActiveDataFile::create(&datadir)?;

        let key = KeyStruct::default(); //serde_json::json!({"key": "value"}).to_string();
        let value = serde_json::json!({"value": "value"}).to_string();

        let key_entry = active.append(&key, &value).unwrap();
        let v: String = ro.get(&key_entry)?;

        assert_eq!(v, value);

        assert_yaml_snapshot!(key_entry, { ".file_id" => "file_id", ".timestamp" =>"ts" });

        Ok(())
    }

    #[test]
    fn test_datafile_get_key_entry() -> Result<()> {
        let datadir = assert_fs::TempDir::new().unwrap().into_persistent_if(false);
        let (mut active, mut ro) = ActiveDataFile::create(&datadir)?;

        let entries = vec![("key", "value"), ("keya", "valuea"), ("keybb", "valuebb")];

        let mut expected = Vec::with_capacity(entries.len());
        for (k, v) in entries {
            let key_entry = active.append(&k.to_owned(), &v.to_owned())?;
            expected.push((k, key_entry));
        }

        let keys = ro.keys()?;
        keys.zip(expected.iter()).for_each(|(k, (ek, ev))| {
            let (k, ke) = k.expect("failed to get key entry");

            assert_eq!(k, *ek, "key");
            assert_eq!(ke, *ev, "value");
        });

        Ok(())
    }

    #[test]
    fn test_hintfile_exist() -> Result<()> {
        let dir = assert_fs::TempDir::new().unwrap().into_persistent_if(false);

        let file_id = FileId::new();

        File::create(file_id.datafile(&dir)).expect("failed to create datafile");
        let df: DataFile<u128, u128> = DataFile::open(file_id, &dir)?;

        assert!(df.hint().is_none(), "hint file should not exist");

        File::create(file_id.hintfile(&dir)).expect("failed to create hint file");

        assert!(df.hint().is_some(), "hint file should exist");

        Ok(())
    }

    #[cfg(test)]
    fn read_entry(p: &Path, at: u64, len: u32) -> Vec<u8> {
        let mut df = File::open(p).expect("failed to open file");

        let mut vbuff = vec![0u8; len as usize];

        df.seek(SeekFrom::Start(at)).expect("failed to seek");
        df.read_exact(&mut vbuff).expect("failed to read");

        vbuff
    }
}
