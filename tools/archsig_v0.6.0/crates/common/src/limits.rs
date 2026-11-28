//! ファイル読込サイズ上限と JSON ネスト深度上限の共通定義と検査付き読込。

use std::io::Read;
use std::path::Path;

/// 入力ファイル読込の既定最大バイト数（64 MiB）。
pub const DEFAULT_MAX_FILE_BYTES: u64 = 64 * 1024 * 1024;

/// JSON パーサ／エンコーダの既定最大ネスト深度。
pub const DEFAULT_MAX_JSON_DEPTH: usize = 256;

/// 共通リソース上限設定。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommonLimits {
    pub max_file_bytes: u64,
    pub max_json_depth: usize,
}

impl Default for CommonLimits {
    fn default() -> Self {
        Self {
            max_file_bytes: DEFAULT_MAX_FILE_BYTES,
            max_json_depth: DEFAULT_MAX_JSON_DEPTH,
        }
    }
}

/// 通常ファイルを開き、サイズ上限を超えていればメモリ展開前にエラーを返す。
pub fn read_regular_file_bounded(path: &Path, max_bytes: u64) -> std::io::Result<Vec<u8>> {
    let file = std::fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(std::io::Error::other("not a regular file"));
    }
    if meta.len() > max_bytes {
        return Err(size_exceeded_error(meta.len(), max_bytes));
    }
    read_file_handle_bounded(file, max_bytes)
}

/// 既に開いた通常ファイルから上限 `max_bytes` まで安全に読み込む（TOCTOU 対策含む）。
pub fn read_file_handle_bounded(file: std::fs::File, max_bytes: u64) -> std::io::Result<Vec<u8>> {
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(std::io::Error::other("not a regular file"));
    }
    if meta.len() > max_bytes {
        return Err(size_exceeded_error(meta.len(), max_bytes));
    }
    let initial_cap = usize::try_from(meta.len().min(1024 * 1024)).unwrap_or(1024 * 1024);
    let mut bytes = Vec::with_capacity(initial_cap);
    let mut reader = file.take(max_bytes.saturating_add(1));
    reader.read_to_end(&mut bytes)?;
    if (bytes.len() as u64) > max_bytes {
        return Err(size_exceeded_error(bytes.len() as u64, max_bytes));
    }
    Ok(bytes)
}

fn size_exceeded_error(observed: u64, max_bytes: u64) -> std::io::Error {
    std::io::Error::new(
        std::io::ErrorKind::InvalidData,
        format!("file size {observed} bytes exceeds limit of {max_bytes} bytes"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn bounded_read_accepts_exact_limit_and_rejects_excess_or_non_regular() {
        let dir =
            std::env::temp_dir().join(format!("archsig-common-limits-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file_path = dir.join("sample.txt");
        {
            let mut f = std::fs::File::create(&file_path).unwrap();
            f.write_all(b"abcdef").unwrap();
        }
        assert_eq!(read_regular_file_bounded(&file_path, 6).unwrap(), b"abcdef");
        let err = read_regular_file_bounded(&file_path, 5).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert!(err.to_string().contains("exceeds limit of 5 bytes"));

        let dir_err = read_regular_file_bounded(&dir, 1024).unwrap_err();
        assert!(dir_err.to_string().contains("not a regular file"));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
