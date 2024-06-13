use eyre::OptionExt;
use eyre::Result;
use std::{fs, mem};

use bitcan::Bitcan;
use insta::assert_yaml_snapshot;

#[test]
fn test_put() {
    let dir = assert_fs::TempDir::new().unwrap();

    let key = "key".to_string();
    let value = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();

    bitcan.put(key.clone(), &value).unwrap();
    let value: Option<String> = bitcan.get(&key).unwrap();

    assert_yaml_snapshot!(value)
}

#[test]
fn test_put_persist() {
    let dir = assert_fs::TempDir::new().unwrap();

    let key = "key".to_string();
    let value = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();

    bitcan.put(key.clone(), &value).unwrap();
    let _value: Option<String> = bitcan.get(&key).unwrap();

    mem::drop(bitcan);

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    let value: Option<String> = bitcan.get(&key).unwrap();

    assert_yaml_snapshot!(value)
}

#[test]
fn test_rm_persist() {
    let dir = assert_fs::TempDir::new().unwrap();

    let key = "key".to_string();
    let value = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();

    bitcan.put(key.clone(), &value).unwrap();
    let _value: Option<String> = bitcan.get(&key).unwrap();
    bitcan.remove(&key).unwrap();

    mem::drop(bitcan);

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    let value: Option<String> = bitcan.get(&key).unwrap();

    assert_yaml_snapshot!(value)
}

#[test]
fn test_merge_persist() -> Result<()> {
    let dir = assert_fs::TempDir::new().unwrap();

    let key = "key".to_string();
    let value = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    bitcan.put(key.clone(), &value).unwrap();

    mem::drop(bitcan);

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    let value: Option<String> = bitcan.get(&key).unwrap();

    assert_yaml_snapshot!(value);

    mem::drop(bitcan);

    let key2 = "key2".to_string();
    let value2 = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    bitcan.put(key2.clone(), &value2).unwrap();

    mem::drop(bitcan);

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    let value2: Option<String> = bitcan.get(&key2).unwrap();

    assert_yaml_snapshot!(value2);

    mem::drop(bitcan);

    let key3 = "key2".to_string();
    let value3 = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    bitcan.put(key3.clone(), &value3).unwrap();

    mem::drop(bitcan);

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    let value3: Option<String> = bitcan.get(&key3).unwrap();

    assert_yaml_snapshot!(value3);

    let pre_merge = lsdir(dir.path())?;
    bitcan.merge().unwrap();

    mem::drop(bitcan);

    let post_merge = lsdir(dir.path())?;
    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();

    for f in pre_merge {
        if let Some(f) = post_merge.iter().find(|&x| x == &f) {
            panic!("file found: {}", f);
        }
    }

    let value: Option<String> = bitcan.get(&key).unwrap();
    assert_yaml_snapshot!(value);
    let value2: Option<String> = bitcan.get(&key2).unwrap();
    assert_yaml_snapshot!(value2);
    let value3: Option<String> = bitcan.get(&key3).unwrap();
    assert_yaml_snapshot!(value3);

    Ok(())
}

#[test]
fn test_iter() -> Result<()> {
    let dir = assert_fs::TempDir::new().unwrap();

    let key = "key".to_string();
    let value = "value".to_string();

    let mut bitcan: Bitcan<String, String> = Bitcan::open(dir.path()).unwrap();
    bitcan.put(key.clone(), &value).unwrap();

    let key2 = "key2".to_string();
    let value2 = "value".to_string();

    bitcan.put(key2.clone(), &value2).unwrap();

    let key3 = "key3".to_string();
    let value3 = "value".to_string();

    bitcan.put(key3.clone(), &value3).unwrap();

    let mut col = bitcan
        .iter()
        .map(|r| {
            let (k, v) = r.unwrap();
            (k, format!("a{v}"))
        })
        .collect::<Vec<_>>();
    col.sort_by(|a, b| a.0.cmp(b.0));

    assert_yaml_snapshot!(col);

    Ok(())
}

#[cfg(test)]
fn lsdir(p: impl AsRef<std::path::Path>) -> Result<Vec<String>> {
    let dir = p.as_ref();

    let ls_dir = fs::read_dir(dir)?;
    let mut ls = vec![];
    for f in ls_dir {
        let f = f?;
        let name = f
            .file_name()
            .to_str()
            .ok_or_eyre("filename error")?
            .to_string();

        ls.push(name);
    }

    Ok(ls)
}
