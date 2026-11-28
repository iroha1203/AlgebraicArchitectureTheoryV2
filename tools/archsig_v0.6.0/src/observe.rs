//! File evidence and explicitly enumerated finite tables; no Law evaluation.
mod evidence;
mod fibers;

pub use crate::cli::help::{EVIDENCE_HELP, FIBERS_HELP};
use crate::cli::{EvidenceArgs, FibersArgs, emit_progress};
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
    map_observe_result(result)
}

pub fn execute_evidence(
    args: &EvidenceArgs,
    max_file_bytes: u64,
) -> std::result::Result<Response, Outcome> {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_evidence_inner(&args.archmap, &args.atoms, &args.sources, max_file_bytes)
    }))
    .unwrap_or_else(|_| {
        Err(Box::new(ResultIssue::Internal {
            operation: "observe".into(),
            message: "internal observation helper failure".into(),
        }))
    });
    map_observe_result(result)
}

pub fn execute_fibers(
    args: &FibersArgs,
    max_file_bytes: u64,
) -> std::result::Result<Response, Outcome> {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_fibers_inner(&args.table, max_file_bytes)
    }))
    .unwrap_or_else(|_| {
        Err(Box::new(ResultIssue::Internal {
            operation: "observe".into(),
            message: "internal observation helper failure".into(),
        }))
    });
    map_observe_result(result)
}

fn map_observe_result(result: Result<Response>) -> std::result::Result<Response, Outcome> {
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
    let mut max_file_bytes = archsig_common::limits::DEFAULT_MAX_FILE_BYTES;
    let mut saw_max_file_bytes = false;
    let mut i = 1;
    while i < args.len() {
        let flag = args[i]
            .to_str()
            .ok_or_else(|| usage("", "flag must be UTF-8"))?;
        if !matches!(
            (evidence, flag),
            (
                true,
                "--archmap" | "--atom" | "--source" | "--max-file-bytes"
            ) | (false, "--table" | "--max-file-bytes")
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
            "--max-file-bytes" => {
                if saw_max_file_bytes {
                    return Err(usage(flag, "duplicate flag"));
                }
                let text = value
                    .to_str()
                    .ok_or_else(|| usage(flag, "byte limit must be UTF-8"))?;
                let parsed: u64 = text
                    .parse()
                    .ok()
                    .filter(|&n| n > 0)
                    .ok_or_else(|| usage(flag, "byte limit must be a positive integer"))?;
                max_file_bytes = parsed;
                saw_max_file_bytes = true;
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
                let (id, path) = crate::platform::split_source_binding(value.as_os_str())
                    .map_err(|msg| usage(flag, msg))?;
                if files.contains_key(&id) {
                    return Err(usage(
                        flag,
                        "source bindings need distinct IDs and nonempty paths",
                    ));
                }
                files.insert(id, path);
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
    if evidence {
        run_evidence_inner(&input, &atoms, &files, max_file_bytes)
    } else {
        run_fibers_inner(&input, max_file_bytes)
    }
}

fn run_evidence_inner(
    archmap: &Path,
    atoms: &[String],
    files: &BTreeMap<String, PathBuf>,
    max_file_bytes: u64,
) -> Result<Response> {
    emit_progress(&format!("evidence: reading archmap {}", archmap.display()));
    let bytes = read(archmap, max_file_bytes)?;
    let node = archsig_common::json::parse(&bytes)
        .map_err(|issue| Box::new(ResultIssue::Input(*issue)))?;
    emit_progress(&format!(
        "evidence: verifying {} atom selector(s)",
        atoms.len()
    ));
    Ok(Response {
        text: evidence::expand(&node, atoms, files, max_file_bytes)?,
        code: 0,
    })
}

fn run_fibers_inner(table: &Path, max_file_bytes: u64) -> Result<Response> {
    emit_progress(&format!("law-fibers: reading table {}", table.display()));
    let bytes = read(table, max_file_bytes)?;
    let node = archsig_common::json::parse(&bytes).map_err(|mut issue| {
        if let Location::ArchMap { pointer, span } = &issue.location {
            issue.location = Location::Definition {
                input: "table".into(),
                pointer: pointer.clone(),
                span: *span,
            };
        }
        Box::new(ResultIssue::Input(*issue))
    })?;
    emit_progress("law-fibers: evaluating table fibers");
    let (result, adequate) = fibers::check(&node)?;
    Ok(Response {
        text: result.canonical(),
        code: u8::from(!adequate),
    })
}

fn read(path: &Path, max_bytes: u64) -> Result<Vec<u8>> {
    archsig_common::limits::read_regular_file_bounded(path, max_bytes).map_err(|error| {
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
