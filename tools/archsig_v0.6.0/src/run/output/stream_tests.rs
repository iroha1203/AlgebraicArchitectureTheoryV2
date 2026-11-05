use super::*;
use crate::run::{FileIo, write_json_to};
use archsig_input::result::Status;
use std::io::{self, Write};

fn root() -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!("archsig-stream-{}-{nanos}", std::process::id()));
    std::fs::create_dir(&path).unwrap();
    path
}
#[test]
fn file_io_write_json_keeps_bytes_and_create_new() {
    let dir = root();
    let path = dir.join("result.json");
    let document = Json::obj([
        ("雪", Json::str("\n\"\\".repeat(10_000))),
        ("a", Json::Nat(1)),
    ]);
    FileIo.write_json(&path, &document).unwrap();
    assert_eq!(
        std::fs::read(&path).unwrap(),
        document.canonical().as_bytes()
    );
    FileIo.flush(&path).unwrap();
    assert_eq!(
        FileIo
            .write_json(&path, &Json::Bool(false))
            .unwrap_err()
            .kind(),
        io::ErrorKind::AlreadyExists
    );
    assert_eq!(
        std::fs::read(&path).unwrap(),
        document.canonical().as_bytes()
    );
    std::fs::remove_dir_all(dir).unwrap();
}

// FileIoと同じbuffered helperへ、途中で失敗する実ファイルwriterを渡す。
struct FailsAfter {
    file: std::fs::File,
    remaining: usize,
    written: std::rc::Rc<std::cell::Cell<usize>>,
}
impl Write for FailsAfter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.remaining == 0 {
            return Err(io::ErrorKind::PermissionDenied.into());
        }
        let count = self.file.write(&bytes[..bytes.len().min(self.remaining)])?;
        self.remaining -= count;
        self.written.set(self.written.get() + count);
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.file.flush()
    }
}
struct FailingStream {
    after: usize,
    written: std::rc::Rc<std::cell::Cell<usize>>,
    renamed: bool,
}
impl Io for FailingStream {
    fn create_dir(&mut self, path: &Path) -> io::Result<()> {
        FileIo.create_dir(path)
    }
    fn write(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        FileIo.write(path, bytes)
    }
    fn write_json(&mut self, path: &Path, document: &Json) -> io::Result<()> {
        write_json_to(
            FailsAfter {
                file: std::fs::File::create_new(path)?,
                remaining: self.after,
                written: self.written.clone(),
            },
            document,
        )
    }
    fn flush(&mut self, path: &Path) -> io::Result<()> {
        FileIo.flush(path)
    }
    fn rename_noreplace(&mut self, from: &Path, to: &Path) -> io::Result<()> {
        self.renamed = true;
        FileIo.rename_noreplace(from, to)
    }
    fn remove_dir_all(&mut self, path: &Path) -> io::Result<()> {
        FileIo.remove_dir_all(path)
    }
}
#[test]
fn streaming_write_and_final_buffer_failures_leave_no_published_artifact() {
    // 短い文書はhelperの最後の明示flushで、長い文書はencode中のbuffer書出で失敗。
    for length in [10, 30_000] {
        let dir = root();
        let out = dir.join("out");
        let written = std::rc::Rc::new(std::cell::Cell::new(0));
        let mut io = FailingStream {
            after: 5,
            written: written.clone(),
            renamed: false,
        };
        let summary = Json::obj([("answer", Json::Bool(true))]);
        let result = publish(
            &mut io,
            &out,
            Json::str("雪".repeat(length)),
            &[],
            Outcome {
                status: Status::Interrupted,
                exit_code: 143,
                result: Some(out.join("result.json")),
                summary: Some(summary.clone()),
                issues: vec![],
            },
        );
        assert_eq!(written.get(), 5, "exercise a real partially written file");
        assert!(!io.renamed);
        assert_eq!(result.status, Status::Error);
        assert_eq!(result.exit_code, 74);
        assert!(result.result.is_none());
        assert_eq!(result.summary, Some(summary));
        assert_eq!(result.issues.len(), 1);
        assert!(result.issues[0].canonical().contains("output write failed"));
        assert!(!out.exists());
        assert_eq!(
            std::fs::read_dir(&dir).unwrap().count(),
            0,
            "remove the partial temporary directory"
        );
        std::fs::remove_dir(dir).unwrap();
    }
}

#[test]
fn file_io_publish_delivers_the_already_frozen_interrupted_document() {
    let dir = root();
    let out = dir.join("out");
    let document = Json::obj([
        ("status", Json::str("interrupted")),
        ("exit_code", Json::Nat(143)),
    ]);
    let expected = document.canonical();
    let outcome = publish(
        &mut FileIo,
        &out,
        document,
        &[],
        Outcome {
            status: Status::Interrupted,
            exit_code: 143,
            result: Some(out.join("result.json")),
            summary: None,
            issues: vec![],
        },
    );
    assert_eq!(outcome.status, Status::Interrupted);
    assert_eq!(outcome.exit_code, 143);
    assert_eq!(outcome.result, Some(out.join("result.json")));
    assert_eq!(
        std::fs::read(out.join("result.json")).unwrap(),
        expected.as_bytes()
    );
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1);
    std::fs::remove_dir_all(dir).unwrap();
}
