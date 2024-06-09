use std::fs::File;
use std::path::PathBuf;

use super::FileId;

#[derive(Debug)]
pub(crate) struct HintFile {
    file_id: FileId,
    path: PathBuf,
    handle: File,
    offset: u64,
}

#[derive(Debug)]
struct HintFileIterator {
    file: HintFile,
    offset: u64,
}
