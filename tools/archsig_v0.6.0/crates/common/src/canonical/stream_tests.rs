use super::*;
use std::io::{self, Write};

struct ShortWriter {
    bytes: Vec<u8>,
    remaining: Option<usize>,
    interrupted: bool,
}
impl Write for ShortWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.interrupted {
            self.interrupted = false;
            return Err(io::ErrorKind::Interrupted.into());
        }
        if self.remaining == Some(0) {
            return Err(io::ErrorKind::PermissionDenied.into());
        }
        let count = bytes.len().min(3).min(self.remaining.unwrap_or(usize::MAX));
        self.bytes.extend_from_slice(&bytes[..count]);
        if let Some(left) = &mut self.remaining {
            *left -= count;
        }
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
#[test]
fn streaming_keeps_canonical_bytes_for_short_writes_and_utf8_escapes() {
    for count in [0, 255, 256, 257] {
        let text = format!(
            "{}{}\"\\終",
            "雪".repeat(count),
            (0u8..32).map(char::from).collect::<String>()
        );
        let value = Json::obj([
            ("é", Json::str(text)),
            (
                "a",
                Json::Arr(vec![Json::Bool(true), Json::Nat(u64::MAX), Json::obj([])]),
            ),
        ]);
        let expected = value.canonical();
        let mut writer = ShortWriter {
            bytes: vec![],
            remaining: None,
            interrupted: true,
        };
        value.write_canonical(&mut writer).unwrap();
        assert_eq!(writer.bytes, expected.as_bytes());
        assert!(expected.contains("\\u000a"));
        assert!(!expected.contains("\\n"));
    }
}
#[test]
fn streaming_errors_preserve_only_the_written_prefix() {
    let value = Json::obj([
        ("é", Json::str("雪\n\"\\終")),
        ("a", Json::Arr(vec![Json::Nat(7)])),
    ]);
    let expected = value.canonical();
    for at in 0..expected.len() {
        let mut writer = ShortWriter {
            bytes: vec![],
            remaining: Some(at),
            interrupted: false,
        };
        let error = value.write_canonical(&mut writer).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
        assert_eq!(writer.bytes, expected.as_bytes()[..at]);
    }
}
#[test]
fn streaming_deep_tree_uses_the_stack_safe_encoder() {
    let mut value = Json::Bool(false);
    for _ in 0..10_000 {
        value = Json::Arr(vec![value]);
    }
    let mut bytes = Vec::new();
    value.write_canonical(&mut bytes).unwrap();
    assert_eq!(bytes.len(), 20_005);
    assert_eq!(&bytes[..10_000], vec![b'['; 10_000]);
    assert_eq!(&bytes[10_000..10_005], b"false");
    assert_eq!(&bytes[10_005..], vec![b']'; 10_000]);
}
