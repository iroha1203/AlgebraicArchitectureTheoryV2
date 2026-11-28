use super::PlatformError;
use archsig_common::control::Control;
use archsig_input::result::Signal;
use std::ffi::OsStr;
use std::io::Write;
use std::path::{Path, PathBuf};

pub(super) struct ProcessSignals;

impl ProcessSignals {
    pub(super) fn install() -> Result<Self, PlatformError> {
        Ok(ProcessSignals)
    }

    pub(super) fn control(&self) -> Control {
        Control::unlimited()
    }

    pub(super) fn prior_signal_exit_code(&self) -> Option<i32> {
        None
    }

    pub(super) fn freeze(&mut self) -> Option<Signal> {
        None
    }
}

pub(super) fn enter_immediate_delivery() {}

pub(super) fn begin_delivery(_code: u8) -> Result<(), PlatformError> {
    Ok(())
}

pub(super) fn write_stdout_line(line: &str) -> std::io::Result<()> {
    let mut out = std::io::stdout().lock();
    out.write_all(line.as_bytes())?;
    out.write_all(b"\n")?;
    out.flush()
}

pub(super) fn write_stderr_line(line: &str) -> std::io::Result<()> {
    let mut err = std::io::stderr().lock();
    err.write_all(line.as_bytes())?;
    err.write_all(b"\n")?;
    err.flush()
}

pub(super) fn rename_noreplace(from: &Path, to: &Path) -> std::io::Result<()> {
    if std::fs::symlink_metadata(to).is_ok() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "destination already exists",
        ));
    }
    std::fs::rename(from, to)
}

pub(super) fn read_reuse_result_nofollow(dir: &Path, max_bytes: u64) -> std::io::Result<Vec<u8>> {
    let meta = std::fs::symlink_metadata(dir)?;
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Err(std::io::Error::other(
            "reuse path is not a regular directory",
        ));
    }
    let path = dir.join("result.json");
    let file_meta = std::fs::symlink_metadata(&path)?;
    if file_meta.file_type().is_symlink() {
        return Err(std::io::Error::other("result.json must not be a symlink"));
    }
    archsig_common::limits::read_regular_file_bounded(&path, max_bytes)
}

pub(super) fn split_source_binding(value: &OsStr) -> Result<(String, PathBuf), &'static str> {
    let s = value.to_str().ok_or("source binding must be UTF-8")?;
    let (id, path) = s.split_once('=').ok_or("expected source-id=local-file")?;
    if id.is_empty() || path.is_empty() {
        return Err("source bindings need distinct IDs and nonempty paths");
    }
    Ok((id.to_owned(), PathBuf::from(path)))
}

pub(super) fn split_flag_value(arg: &OsStr) -> Option<(&str, std::ffi::OsString)> {
    let s = arg.to_str()?;
    let (flag, val) = s.split_once('=')?;
    if flag.len() <= 2 || !flag.starts_with("--") {
        return None;
    }
    Some((flag, std::ffi::OsString::from(val)))
}
