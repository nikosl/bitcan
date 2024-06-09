use std::io::prelude::*;
use std::time::{SystemTime, UNIX_EPOCH};

use bincode::Options as _;
use byteorder::ReadBytesExt as _;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use snafu::prelude::ensure_whatever;
use snafu::{ResultExt, Whatever};

use crate::log::FileId;

const CHECKSUM_SIZE: usize = std::mem::size_of::<u32>();
const TIMESTAMP_SIZE: usize = std::mem::size_of::<u64>();
const KEY_SIZE_SIZE: usize = std::mem::size_of::<u32>();
const VALUE_SIZE_SIZE: usize = std::mem::size_of::<u32>();
const OFFSET_SIZE: usize = std::mem::size_of::<u64>();

#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct KeyEntry {
    file_id: FileId,
    entry_offset: u64,
    value_size: u32,
    offset: u64,
    timestamp: Timestamp,
}

impl KeyEntry {
    pub fn new(
        file_id: FileId,
        entry_offset: u64,
        value_size: u32,
        offset: u64,
        timestamp: Timestamp,
    ) -> Self {
        KeyEntry {
            file_id,
            entry_offset,
            value_size,
            offset,
            timestamp,
        }
    }

    pub fn file_id(&self) -> &FileId {
        &self.file_id
    }

    pub fn value_size(&self) -> u32 {
        self.value_size
    }

    pub fn offset(&self) -> u64 {
        self.offset
    }

    pub fn timestamp(&self) -> Timestamp {
        self.timestamp
    }

    pub fn is_tombstone(&self) -> bool {
        self.value_size == 0
    }

    pub fn start_offset(&self) -> u64 {
        self.entry_offset
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Timestamp(u64);

impl Timestamp {
    #[allow(clippy::cast_possible_truncation)]
    pub fn now() -> Self {
        let ts = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64;

        ts.into()
    }

    pub fn to_be_bytes(self) -> [u8; 8] {
        self.0.to_be_bytes()
    }
}

impl From<Timestamp> for u64 {
    fn from(item: Timestamp) -> Self {
        item.0
    }
}

impl From<u64> for Timestamp {
    fn from(item: u64) -> Self {
        Timestamp(item)
    }
}

pub struct Checksum(adler::Adler32);

impl Checksum {
    pub fn new() -> Self {
        Self(adler::Adler32::new())
    }

    pub fn write(&mut self, buf: &[u8]) -> &mut Self {
        self.0.write_slice(buf);

        self
    }

    pub fn checksum(&self) -> u32 {
        self.0.checksum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub(crate) struct LogEntryHeader {
    checksum: u32,
    timestamp: Timestamp,
    key_size: u32,
    value_size: u32,
}

impl LogEntryHeader {
    pub const HEADER_SIZE: usize = CHECKSUM_SIZE + TIMESTAMP_SIZE + KEY_SIZE_SIZE + VALUE_SIZE_SIZE;

    pub fn from_reader<R>(reader: &mut R) -> Result<Self, Whatever>
    where
        R: Read,
    {
        let mut buf = [0u8; LogEntryHeader::HEADER_SIZE];
        reader
            .read_exact(&mut buf)
            .whatever_context("failed to read header")?;

        LogEntryHeader::from_bytes(&buf).whatever_context("failed to parse header")
    }

    pub fn from_bytes(b: &[u8]) -> Result<Self, Whatever> {
        use byteorder::BigEndian as BEndian;
        let mut cursor = std::io::Cursor::new(b);

        let checksum = cursor
            .read_u32::<BEndian>()
            .whatever_context("failed to read checksum")?;
        let timestamp = cursor
            .read_u64::<BEndian>()
            .whatever_context("failed to read timestamp")?;
        let key_size = cursor
            .read_u32::<BEndian>()
            .whatever_context("failed to read key size")?;
        let value_size = cursor
            .read_u32::<BEndian>()
            .whatever_context("failed to read value size")?;

        Ok(LogEntryHeader {
            checksum,
            timestamp: Timestamp(timestamp),
            key_size,
            value_size,
        })
    }

    pub fn checksum(&self) -> u32 {
        self.checksum
    }

    pub fn timestamp(&self) -> Timestamp {
        self.timestamp
    }

    pub fn key_size(&self) -> u32 {
        self.key_size
    }

    pub fn value_size(&self) -> u32 {
        self.value_size
    }

    pub fn is_tombstone(&self) -> bool {
        self.value_size == 0
    }
}

impl Ord for LogEntryHeader {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.timestamp.cmp(&other.timestamp)
    }
}

impl PartialOrd for LogEntryHeader {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[must_use]
pub struct LogEntry {
    header: LogEntryHeader,
    key: Vec<u8>,
    value: Vec<u8>,
}

impl LogEntry {
    #[allow(clippy::cast_possible_truncation)]
    pub fn new<K, V>(key: K, value: V, timestamp: Timestamp) -> Result<Self, Whatever>
    where
        K: Serialize,
        V: Serialize,
    {
        let key = serializer(key).whatever_context("failed to serialize key")?;
        let value = serializer(value).whatever_context("failed to serialize value")?;

        let key_size = key.len() as u32;
        let value_size = value.len() as u32;
        ensure_whatever!(value_size > 0, "empty value is not allowed");

        let checksum = Checksum::new()
            .write(&timestamp.to_be_bytes())
            .write(&key_size.to_be_bytes())
            .write(&value_size.to_be_bytes())
            .write(&key)
            .write(&value)
            .checksum();

        let header = LogEntryHeader {
            checksum,
            timestamp,
            key_size,
            value_size,
        };

        Ok(LogEntry { header, key, value })
    }

    pub fn from_reader<R>(reader: &mut R) -> Result<Self, Whatever>
    where
        R: Read,
    {
        let mut buf = [0u8; LogEntryHeader::HEADER_SIZE];
        reader
            .read_exact(&mut buf)
            .whatever_context("failed to read header")?;
        let header = LogEntryHeader::from_bytes(&buf).whatever_context("failed to parse header")?;

        let mut key = vec![0u8; header.key_size as usize];
        reader
            .read_exact(&mut key)
            .whatever_context("failed to read key")?;

        let mut value = vec![0u8; header.value_size as usize];
        reader
            .read_exact(&mut value)
            .whatever_context("failed to read value")?;

        Ok(LogEntry { header, key, value })
    }

    #[allow(clippy::cast_possible_truncation)]
    pub fn tombstone<K: Serialize>(key: K, timestamp: Timestamp) -> Result<Self, Whatever> {
        let key = serializer(key).whatever_context("failed to serialize key")?;
        let key_size = key.len() as u32;

        let checksum = Checksum::new()
            .write(&timestamp.to_be_bytes())
            .write(&key_size.to_be_bytes())
            .checksum();

        let header = LogEntryHeader {
            checksum,
            timestamp,
            key_size,
            value_size: 0,
        };

        Ok(LogEntry {
            header,
            key,
            value: vec![],
        })
    }

    pub fn key_bytes(&self) -> &[u8] {
        &self.key
    }

    pub fn value_bytes(&self) -> &[u8] {
        &self.value
    }

    pub fn key_size(&self) -> u32 {
        self.header.key_size
    }

    pub fn value_size(&self) -> u32 {
        self.header.value_size
    }

    pub fn len(&self) -> usize {
        LogEntryHeader::HEADER_SIZE + self.key.len() + self.value.len()
    }

    pub fn timestamp(&self) -> Timestamp {
        self.header.timestamp
    }

    pub fn checksum(&self) -> u32 {
        self.header.checksum
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut data = Vec::with_capacity(self.len());

        data.write_all(&self.header.checksum.to_be_bytes());
        data.write_all(&self.header.timestamp.to_be_bytes());
        data.write_all(&self.header.key_size.to_be_bytes());
        data.write_all(&self.header.value_size.to_be_bytes());
        data.write_all(&self.key);
        data.write_all(&self.value);

        data
    }

    pub fn is_tombstone(&self) -> bool {
        self.header.is_tombstone()
    }

    pub fn key_deserialize<V: DeserializeOwned>(&self) -> Result<V, Whatever> {
        deserializer(self.key_bytes()).whatever_context("failed to deserialize key")
    }

    pub fn value_deserialize<V: DeserializeOwned>(&self) -> Result<V, Whatever> {
        deserializer(self.value_bytes()).whatever_context("failed to deserialize value")
    }

    pub fn deserialize<V: DeserializeOwned>(value: &[u8]) -> Result<V, Whatever> {
        deserializer(value).whatever_context("failed to deserialize value")
    }
}

impl PartialEq for LogEntry {
    fn eq(&self, other: &Self) -> bool {
        self.header == other.header
    }
}

impl Eq for LogEntry {}

impl Ord for LogEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.header.cmp(&other.header)
    }
}

pub(crate) struct HintEntry {
    timestamp: Timestamp,
    key_size: u32,
    value_size: u32,
    value_offset: u64,
    key: Vec<u8>,
}

impl HintEntry {
    pub const HINT_HEADER_SIZE: usize =
        TIMESTAMP_SIZE + KEY_SIZE_SIZE + VALUE_SIZE_SIZE + OFFSET_SIZE;
}

impl PartialOrd for LogEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn serializer<V: Serialize>(v: V) -> Result<Vec<u8>, Whatever> {
    bincode::options()
        .with_big_endian()
        .with_limit(u64::from(u32::MAX))
        .serialize(&v)
        .with_whatever_context(|e| format!("failed to serialize data {e:?}"))
}

fn deserializer<'de, T: serde::Deserialize<'de>>(data: &'de [u8]) -> Result<T, Whatever> {
    bincode::options()
        .with_big_endian()
        .deserialize(data)
        .whatever_context("failed to deserialize data []")
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use insta::assert_yaml_snapshot;

    use super::*;

    #[test]
    fn test_log_entry_checksum() {
        let key = "key";
        let value = "value";

        let timestamp: Timestamp = 1_717_699_061_549.into();
        let log_entry = LogEntry::new(key, value, timestamp).unwrap();

        let ser = log_entry.to_bytes();
        let mut ser = Cursor::new(&ser);
        let log_entry_de = LogEntry::from_reader(&mut ser).unwrap();

        assert_yaml_snapshot!(log_entry);
        assert_yaml_snapshot!(log_entry_de);
    }

    #[test]
    fn test_log_entry_new_header() {
        let key = serde_json::json!({"key": "value"});
        let value = serde_json::json!({"value": "value"});

        // 1717699061549
        let timestamp: Timestamp = Timestamp::now();
        let log_entry = LogEntry::new(key, value, timestamp).unwrap();

        let ser = log_entry.to_bytes();
        let header = LogEntryHeader::from_bytes(&ser).unwrap();

        // assert_yaml_snapshot!(header, { ".checksum"=> 0u32 });
        // assert_debug_snapshot!(log_entry);
        assert_eq!(log_entry.checksum(), header.checksum, "checksum");
        assert_eq!(log_entry.timestamp(), header.timestamp, "timestamp");
        assert_eq!(log_entry.key_size(), header.key_size, "key_size");
        assert_eq!(log_entry.value_size(), header.value_size, "value_size");
    }

    #[test]
    fn test_log_entry_to_bytes() -> Result<(), Whatever> {
        let key = "test_key";
        let value = "test_value";
        let timestamp = Timestamp::now();
        let log_entry = LogEntry::new(key, value, timestamp).unwrap();

        let bytes = log_entry.to_bytes();
        let mut r = Cursor::new(&bytes);
        let actual = LogEntry::from_reader(&mut r)?;

        let header = log_entry.header;

        assert_eq!(actual.header, header, "header");

        let act_key: String = actual.key_deserialize()?;
        assert_eq!(act_key, key, "key");

        let act_val: String = actual.value_deserialize()?;
        assert_eq!(act_val, value, "value");

        Ok(())
    }

    #[test]
    fn test_log_entry_value_deserialize() {
        let key = "test_key";
        let value = "test_value";
        let timestamp = Timestamp::now();
        let log_entry = LogEntry::new(key, value, timestamp).unwrap();

        let deserialized_value: String = LogEntry::deserialize(log_entry.value_bytes()).unwrap();
        assert_eq!(deserialized_value, value);
    }
}
