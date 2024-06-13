use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use std::path::{Path, PathBuf};

use serde::de::DeserializeOwned;
use snafu::{prelude::*, Whatever};

use crate::model::{CodecRead, HintEntry, KeyEntry};

use super::FileId;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct HintRO;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct HintRW;
pub(crate) trait HintMarker {}
impl HintMarker for HintRO {}
impl HintMarker for HintRW {}
impl HintMarker for () {}

#[derive(Debug)]
pub(crate) struct HintFile<K, P = ()>
where
    P: HintMarker,
{
    file_id: FileId,
    path: PathBuf,
    handle: File,
    _key: std::marker::PhantomData<K>,
    _perm: std::marker::PhantomData<P>,
}

impl<K> HintFile<K> {
    pub(crate) fn write(
        file_id: FileId,
        path: impl AsRef<Path>,
    ) -> Result<HintFile<K, HintRW>, Whatever>
    where
        K: serde::Serialize,
    {
        let path = file_id.hintfile(path);
        let handle = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .with_whatever_context(|e| format!("failed to create hint file: {e}"))?;

        Ok(HintFile::<K, HintRW> {
            file_id,
            path,
            handle,
            _key: std::marker::PhantomData,
            _perm: std::marker::PhantomData,
        })
    }

    pub(crate) fn read(
        file_id: FileId,
        path: impl AsRef<Path>,
    ) -> Result<HintFile<K, HintRO>, Whatever>
    where
        K: serde::de::DeserializeOwned,
    {
        let path = file_id.hintfile(path);
        let handle = OpenOptions::new()
            .read(true)
            .open(&path)
            .with_whatever_context(|e| format!("failed to open hint file: {e}"))?;

        Ok(HintFile::<K, HintRO> {
            file_id,
            path,
            handle,
            _key: std::marker::PhantomData,
            _perm: std::marker::PhantomData,
        })
    }
}

impl<K> HintFile<K, HintRW>
where
    K: serde::Serialize,
{
    pub fn append_keyentry(&mut self, key: K, ke: &KeyEntry) -> Result<(), Whatever> {
        let hint = HintEntry::new(key, ke.value_size(), ke.offset(), ke.timestamp()).unwrap();

        self.append(&hint)
    }

    pub fn append(&mut self, hint: &HintEntry) -> Result<(), Whatever> {
        let buf = hint.to_bytes();

        self.handle
            .write_all(&buf)
            .with_whatever_context(|e| format!("failed to write hint: {e}"))?;

        Ok(())
    }

    pub(crate) fn sync(&mut self) -> Result<(), Whatever> {
        self.handle
            .sync_all()
            .with_whatever_context(|e| format!("failed to sync hint file: {e}"))?;

        Ok(())
    }
}

impl<K> HintFile<K, HintRO>
where
    K: DeserializeOwned,
{
    pub(crate) fn next_record(&mut self) -> Result<Option<HintEntry>, Whatever> {
        HintEntry::from_reader(&mut self.handle)
    }

    pub fn keys(&mut self) -> impl Iterator<Item = Result<(K, KeyEntry), Whatever>> + '_ {
        let file_id = self.file_id;

        self.iter().map(move |r| {
            let h = r?;

            let ke = KeyEntry::new(file_id, 0, h.value_size(), h.value_offset(), h.timestamp());
            let k = h.key()?;

            Ok((k, ke))
        })
    }

    pub fn iter(&mut self) -> HintFileIterator<K> {
        HintFileIterator { file: self }
    }
}

impl<K> Read for HintFile<K, HintRO> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.handle.read(buf)
    }
}

// #[derive(Debug)]
// pub(crate) struct HintFileIterator<'a, K> {
//     file: &'a mut HintFile<K, HintRO>,
// }

// impl<'f, K> Iterator for HintFileIterator<'f, K>
// where
//     K: serde::de::DeserializeOwned,
// {
//     type Item = Result<HintEntry, Whatever>;

//     fn next(&mut self) -> Option<Self::Item> {
//         self.file.next_record().transpose()
//     }
// }
#[derive(Debug)]
pub(crate) struct HintFileIterator<'a, K> {
    file: &'a mut HintFile<K, HintRO>,
}

impl<'f, K> Iterator for HintFileIterator<'f, K>
where
    K: serde::de::DeserializeOwned,
{
    type Item = Result<HintEntry, Whatever>;

    fn next(&mut self) -> Option<Self::Item> {
        self.file.next_record().transpose()
    }
}

#[cfg(test)]
mod test_hint_file {
    use std::mem;

    use insta::assert_yaml_snapshot;

    use crate::model::Timestamp;

    use super::*;

    #[test]
    fn test_iter_records() {
        let dir = assert_fs::TempDir::new().unwrap();

        let file_id = FileId::new();
        let ts = Timestamp::from(1_717_699_061_549);

        let mut hint_file: HintFile<String, HintRW> = HintFile::write(file_id, dir.path()).unwrap();

        let values = vec![
            HintEntry::new("key1".to_string(), 123_456, 654_321, ts),
            HintEntry::new("key2".to_string(), 123_456, 654_321, ts),
            HintEntry::new("key3".to_string(), 123_456, 654_321, ts),
        ];

        for v in &values {
            let v = v.as_ref().unwrap();
            hint_file.append(v).unwrap();
        }

        mem::drop(hint_file);

        let mut hint_file: HintFile<String, HintRO> = HintFile::read(file_id, dir.path()).unwrap();

        let iter_h = hint_file
            .iter()
            .collect::<Result<Vec<_>, Whatever>>()
            .expect("iteration failed");

        assert_yaml_snapshot!(iter_h);
    }
}
