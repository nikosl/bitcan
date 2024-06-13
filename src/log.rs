use std::fmt::{self, Display, Formatter};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use snafu::prelude::*;
use snafu::Whatever;
use ulid::Ulid;

pub(crate) mod hint;

#[derive(Debug)]
#[must_use]
enum FileRecords {
    HintFile(FileId),
    DataFile(FileId),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) struct FileId(Ulid);

impl FileId {
    pub fn new() -> Self {
        Self(Ulid::new())
    }

    pub fn open(id: impl AsRef<str>) -> Result<Self, Whatever> {
        let id = id.as_ref();

        Ulid::from_string(id)
            .map(FileId)
            .whatever_context("failed to parse file id")
    }

    pub fn datafile(&self, p: impl AsRef<Path>) -> PathBuf {
        p.as_ref().join(format!("{}.data", self.0))
    }

    pub fn hintfile(&self, p: impl AsRef<Path>) -> PathBuf {
        p.as_ref().join(format!("{}.hint", self.0))
    }
}

impl Display for FileId {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
