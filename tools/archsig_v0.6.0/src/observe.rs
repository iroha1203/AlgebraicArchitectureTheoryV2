//! File evidence and explicitly enumerated finite tables; no Law evaluation.
mod evidence;
mod fibers;

use crate::run::Outcome;
use archsig_common::{
    canonical::Json,
    issue::{Code, Details, Issue, Location},
    json::{JNode, JValue},
};
use archsig_input::result::{ResultIssue, Status};
use std::{
    collections::BTreeMap,
    ffi::OsString,
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, Box<ResultIssue>>;

pub const EVIDENCE_HELP: &str =
    "Usage: archsig evidence --archmap A --atom SNAPSHOT/ATOM [--source ID=FILE ...]
  --archmap A       ArchMap JSON (required)
  --atom ID         Select snapshot/atom (required, repeatable, distinct)
  --source ID=FILE  Bind a source ID to a local file (repeatable, distinct)
  --help, -h        Show this help
Expand explicit references and verify SHA256, UTF-8 byte spans and excerpts.
Revision provenance, coverage, meaning and Law fidelity remain reading obligations.
Result: JSON on stdout; errors: receipt JSON on stderr. No files are written.
Exit: 0 verified bytes, 64 usage, 65 invalid input, 70 internal, 74 I/O,
130 SIGINT, 141 broken pipe, 143 SIGTERM.";
pub const FIBERS_HELP: &str = "Usage: archsig law-fibers --table TABLE
  --table TABLE  Explicit finite evaluation table JSON (required)
  --help, -h     Show this help
Compute counterexamples, partitions and descent on the supplied table.
Complete enumeration and faithful equality tokens are caller obligations; no Law DSL evaluation.
Result: JSON on stdout; errors: receipt JSON on stderr. No files are written.
Exit: 0 adequate on table (including vacuous), 1 counterexamples, 64 usage,
65 invalid input, 70 internal, 74 I/O, 130 SIGINT, 141 broken pipe, 143 SIGTERM.";

/// Successful read-only response, or help, and its exit status.
pub struct Response {
    pub text: String,
    pub code: u8,
}

/// Recognize only the two observation commands (including their help forms).
pub fn handles(args: &[OsString]) -> bool {
    matches!(
        args.first().and_then(|s| s.to_str()),
        Some("evidence" | "law-fibers")
    ) || (args.first().is_some_and(|s| s == "help")
        && matches!(
            args.get(1).and_then(|s| s.to_str()),
            Some("evidence" | "law-fibers")
        ))
}

pub fn execute(args: &[OsString]) -> std::result::Result<Response, Outcome> {
    let result = std::panic::catch_unwind(|| execute_inner(args)).unwrap_or_else(|_| {
        Err(Box::new(ResultIssue::Internal {
            operation: "observe".into(),
            message: "internal observation helper failure".into(),
        }))
    });
    result.map_err(|issue| {
        let (status, code) = match issue.as_ref() {
            ResultIssue::Usage { .. } => (Status::Invalid, 64),
            ResultIssue::Input(_) => (Status::Invalid, 65),
            ResultIssue::Io { .. } => (Status::Error, 74),
            _ => (Status::Error, 70),
        };
        Outcome {
            status,
            exit_code: code,
            result: None,
            issues: vec![issue.wire()],
            summary: None,
        }
    })
}

fn usage(argument: &str, message: &str) -> Box<ResultIssue> {
    Box::new(ResultIssue::Usage {
        argument: argument.into(),
        message: message.into(),
    })
}

fn execute_inner(args: &[OsString]) -> Result<Response> {
    let help_form = args.first().is_some_and(|s| s == "help");
    let kind = args
        .get(usize::from(help_form))
        .and_then(|s| s.to_str())
        .unwrap_or("");
    let evidence = kind == "evidence";
    if args.len() == 2 && (help_form || args[1] == "--help" || args[1] == "-h") {
        return Ok(Response {
            text: if evidence { EVIDENCE_HELP } else { FIBERS_HELP }.into(),
            code: 0,
        });
    }
    if help_form {
        return Err(usage("help", "help takes one command"));
    }
    let mut input = None;
    let mut atoms = Vec::new();
    let mut files = BTreeMap::new();
    let mut i = 1;
    while i < args.len() {
        let flag = args[i]
            .to_str()
            .ok_or_else(|| usage("", "flag must be UTF-8"))?;
        if !matches!(
            (evidence, flag),
            (true, "--archmap" | "--atom" | "--source") | (false, "--table")
        ) {
            return Err(usage(flag, "unknown flag or positional argument"));
        }
        let value = args
            .get(i + 1)
            .ok_or_else(|| usage(flag, "flag requires a value"))?;
        match flag {
            "--archmap" | "--table" => {
                if input.is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                input = Some(PathBuf::from(value));
            }
            "--atom" => {
                let value = value
                    .to_str()
                    .ok_or_else(|| usage(flag, "selector must be UTF-8"))?;
                let parts: Vec<_> = value.split('/').collect();
                if parts.len() != 2
                    || parts.iter().any(|s| s.is_empty())
                    || atoms.iter().any(|s| s == value)
                {
                    return Err(usage(flag, "select distinct nonempty snapshot/atom IDs"));
                }
                atoms.push(value.to_owned());
            }
            "--source" => {
                // Split the OS string so non-UTF-8 file paths remain usable.
                use std::os::unix::ffi::{OsStrExt, OsStringExt};
                let bytes = value.as_os_str().as_bytes();
                let at = bytes
                    .iter()
                    .position(|b| *b == b'=')
                    .ok_or_else(|| usage(flag, "expected source-id=local-file"))?;
                let id = std::str::from_utf8(&bytes[..at])
                    .map_err(|_| usage(flag, "source ID must be UTF-8"))?;
                if id.is_empty() || at + 1 == bytes.len() || files.contains_key(id) {
                    return Err(usage(
                        flag,
                        "source bindings need distinct IDs and nonempty paths",
                    ));
                }
                files.insert(
                    id.into(),
                    PathBuf::from(OsString::from_vec(bytes[at + 1..].to_vec())),
                );
            }
            _ => unreachable!(),
        }
        i += 2;
    }
    if evidence && atoms.is_empty() {
        return Err(usage("--atom", "at least one --atom is required"));
    }
    let input = input.ok_or_else(|| {
        usage(
            if evidence { "--archmap" } else { "--table" },
            "input file is required",
        )
    })?;
    let bytes = read(&input)?;
    let node = archsig_common::json::parse(&bytes).map_err(|mut issue| {
        if !evidence && let Location::ArchMap { pointer, span } = &issue.location {
            issue.location = Location::Definition {
                input: "table".into(),
                pointer: pointer.clone(),
                span: *span,
            };
        }
        Box::new(ResultIssue::Input(*issue))
    })?;
    if evidence {
        Ok(Response {
            text: evidence::expand(&node, &atoms, &files)?,
            code: 0,
        })
    } else {
        let (result, adequate) = fibers::check(&node)?;
        Ok(Response {
            text: result.canonical(),
            code: u8::from(!adequate),
        })
    }
}

fn read(path: &Path) -> Result<Vec<u8>> {
    let read = || {
        if !std::fs::metadata(path)?.is_file() {
            return Err(std::io::Error::other("not a regular file"));
        }
        std::fs::read(path)
    };
    read().map_err(|error| {
        Box::new(ResultIssue::Io {
            operation: "read",
            path: path.to_string_lossy().into_owned(),
            message: error.to_string(),
        })
    })
}

fn invalid(message: impl Into<String>) -> Box<ResultIssue> {
    Box::new(ResultIssue::Input(Issue {
        code: Code::Type,
        message: message.into(),
        location: Location::ArchMap {
            pointer: String::new(),
            span: None,
        },
        details: Details::Empty,
    }))
}
fn obj(node: &JNode) -> Result<&[(String, JNode)]> {
    if let JValue::Obj(fields) = &node.value {
        Ok(fields)
    } else {
        Err(invalid("expected an object"))
    }
}
fn field<'a>(node: &'a JNode, key: &str) -> Result<&'a JNode> {
    obj(node)?
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v)
        .ok_or_else(|| invalid(format!("missing field: {key}")))
}
fn arr(node: &JNode) -> Result<&[JNode]> {
    if let JValue::Arr(items) = &node.value {
        Ok(items)
    } else {
        Err(invalid("expected an array"))
    }
}
fn token(node: &JNode) -> Result<&str> {
    if let JValue::Str(value) = &node.value
        && !value.is_empty()
    {
        return Ok(value);
    }
    Err(invalid(
        "expected a nonempty string; missing values are not evaluations",
    ))
}
fn strings(items: &[&str]) -> Json {
    Json::Arr(items.iter().map(|s| Json::str(*s)).collect())
}

/// Serialize parser-validated JSON, retaining arbitrary atom values and number spelling.
fn encode(node: &JNode) -> String {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match &node.value {
        JValue::Null => "null".into(),
        JValue::Bool(b) => b.to_string(),
        JValue::Num(n) => n.clone(),
        JValue::Str(s) => Json::str(s).canonical(),
        JValue::Arr(items) => format!(
            "[{}]",
            items.iter().map(encode).collect::<Vec<_>>().join(",")
        ),
        JValue::Obj(fields) => object(fields.iter().map(|(k, v)| (k.as_str(), encode(v)))),
    })
}
fn object<'a>(fields: impl IntoIterator<Item = (&'a str, String)>) -> String {
    format!(
        "{{{}}}",
        fields
            .into_iter()
            .map(|(k, v)| format!("{}:{v}", Json::str(k).canonical()))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn augmented(node: &JNode, fields: &[(&str, String)]) -> Result<String> {
    Ok(object(
        obj(node)?
            .iter()
            .filter(|(k, _)| !fields.iter().any(|(name, _)| k == name))
            .map(|(k, v)| (k.as_str(), encode(v)))
            .chain(fields.iter().map(|(k, v)| (*k, v.clone()))),
    ))
}
