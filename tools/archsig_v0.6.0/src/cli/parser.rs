//! 統一 CLI パーサ（全サブコマンド、`--flag=value`、`--ask-file`、`--project`、`reobserve` 省略補完）。

use super::{
    CliCommand, CliError, CliOptions, DetailLevel, OutOptions, OutputFormat, ParsedCli, help,
    parser_sub,
};
use crate::platform;
use crate::run::{CheckArgs, Checked, Command, ReobserveArgs, RunArgs, UsageError};
use archsig_common::limits::{
    DEFAULT_MAX_FILE_BYTES, read_reader_bounded, read_regular_file_bounded,
};
use archsig_input::manifest::parse_project_manifest;
use archsig_input::result::ResultIssue;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

pub(super) fn usage(argument: &str, message: impl Into<String>) -> CliError {
    CliError::Usage(Box::new(UsageError {
        argument: argument.to_owned(),
        message: message.into(),
        prefix_argument: true,
    }))
}

pub(super) fn raw_usage(argument: &str, message: impl Into<String>) -> CliError {
    CliError::Usage(Box::new(UsageError {
        argument: argument.to_owned(),
        message: message.into(),
        prefix_argument: false,
    }))
}

fn read_bounded_cli(path: &Path, max_bytes: u64) -> Result<Vec<u8>, CliError> {
    read_regular_file_bounded(path, max_bytes).map_err(|err| {
        CliError::Io(Box::new(ResultIssue::Io {
            operation: "read",
            path: path.to_string_lossy().into_owned(),
            message: format!("cannot read input {}: {err}", path.display()),
        }))
    })
}

#[derive(Debug)]
pub(super) struct RawToken {
    pub(super) flag: String,
    pub(super) attached: Option<OsString>,
    pub(super) raw_idx: usize,
}

pub(super) fn tokenize_flag(arg: &OsString, raw_idx: usize) -> RawToken {
    if let Some((flag, val)) = platform::split_flag_value(arg.as_os_str()) {
        return RawToken {
            flag: flag.to_owned(),
            attached: Some(val),
            raw_idx,
        };
    }
    RawToken {
        flag: arg.to_string_lossy().into_owned(),
        attached: None,
        raw_idx,
    }
}

pub(super) fn take_value(
    token: &RawToken,
    args: &[OsString],
    cursor: &mut usize,
) -> Result<OsString, CliError> {
    if let Some(val) = &token.attached {
        *cursor = token.raw_idx + 1;
        Ok(val.clone())
    } else {
        let next = args
            .get(token.raw_idx + 1)
            .ok_or_else(|| usage(&token.flag, "flag requires a value"))?;
        *cursor = token.raw_idx + 2;
        Ok(next.clone())
    }
}

fn parse_pos_u64(flag: &str, val: &OsString, label: &str) -> Result<u64, CliError> {
    let text = val
        .to_str()
        .ok_or_else(|| usage(flag, format!("{label} must be UTF-8")))?;
    text.parse::<u64>()
        .ok()
        .filter(|&n| n > 0)
        .ok_or_else(|| usage(flag, format!("{label} must be a positive integer")))
}

pub(super) fn ensure_no_attached(token: &RawToken) -> Result<(), CliError> {
    if token.attached.is_some() {
        return Err(usage(&token.flag, "flag does not accept a value"));
    }
    Ok(())
}

/// `--max-file-bytes` を先行スキャンし、`--project` / `--ask-file` 読込でも有効化する。
pub(super) fn prescan_max_file_bytes(rest: &[OsString]) -> Result<Option<u64>, CliError> {
    let mut found: Option<u64> = None;
    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if tok.flag == "--max-file-bytes" {
            if found.is_some() {
                return Err(usage("--max-file-bytes", "duplicate flag"));
            }
            let val = take_value(&tok, rest, &mut i)?;
            found = Some(parse_pos_u64("--max-file-bytes", &val, "byte limit")?);
        } else if tok.attached.is_some() || is_known_bool_flag(&tok.flag) {
            i += 1;
        } else if is_value_flag(&tok.flag) {
            i += 2;
        } else {
            i += 1;
        }
    }
    Ok(found)
}

fn is_known_bool_flag(flag: &str) -> bool {
    matches!(
        flag,
        "--help"
            | "-h"
            | "--create-parents"
            | "--overwrite"
            | "--no-fsync"
            | "--verbose"
            | "--progress"
            | "--evidence"
    )
}

fn is_value_flag(flag: &str) -> bool {
    matches!(
        flag,
        "--atom-definition"
            | "--law"
            | "--archmap"
            | "--ask"
            | "--ask-file"
            | "--project"
            | "--out"
            | "--reuse"
            | "--max-file-bytes"
            | "--shigure-limit"
            | "--format"
            | "--detail"
            | "--before-atom-definition"
            | "--before-law"
            | "--before-archmap"
            | "--before-ask"
            | "--before-ask-file"
            | "--alignment"
            | "--atom"
            | "--source"
            | "--table"
            | "--result"
            | "--answer"
    )
}

fn read_ask_file(
    path_val: &OsString,
    max_file_bytes: u64,
    used_stdin: &mut bool,
    flag_name: &str,
) -> Result<Vec<String>, CliError> {
    if path_val.is_empty() {
        return Err(usage(flag_name, "ask file path must be nonempty"));
    }
    let (bytes, label) = if path_val == "-" {
        if *used_stdin {
            return Err(usage(
                flag_name,
                "cannot read asks from stdin (`-`) more than once",
            ));
        }
        *used_stdin = true;
        let bytes =
            read_reader_bounded(std::io::stdin().lock(), max_file_bytes).map_err(|err| {
                CliError::Io(Box::new(ResultIssue::Io {
                    operation: "read",
                    path: "-".to_owned(),
                    message: format!("cannot read asks from stdin: {err}"),
                }))
            })?;
        (bytes, "stdin".to_owned())
    } else {
        let p = Path::new(path_val);
        let bytes = read_bounded_cli(p, max_file_bytes)?;
        (bytes, p.to_string_lossy().into_owned())
    };
    let text = std::str::from_utf8(&bytes).map_err(|err| {
        CliError::Input(Box::new(ResultIssue::Input(archsig_common::issue::Issue {
            code: archsig_common::issue::Code::Syntax,
            message: format!("ask file `{label}` is not valid UTF-8: {err}"),
            location: archsig_common::issue::Location::Definition {
                input: "ask_file".to_owned(),
                pointer: String::new(),
                span: Some((err.valid_up_to(), bytes.len())),
            },
            details: archsig_common::issue::Details::Empty,
        })))
    })?;
    Ok(text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_owned)
        .collect())
}

fn parse_shigure_limit(
    flag: &str,
    val: &OsString,
    limits: &mut archsig_shigure::ShigureLimits,
) -> Result<(), CliError> {
    let text = val
        .to_str()
        .ok_or_else(|| usage(flag, "shigure limit must be UTF-8"))?;
    let (name, raw_val) = text
        .split_once('=')
        .ok_or_else(|| usage(flag, "expected LIMIT_NAME=POSITIVE_INT"))?;
    let parsed = raw_val
        .parse::<u64>()
        .map_err(|_| usage(flag, format!("invalid integer for `{name}`: `{raw_val}`")))?;
    limits.set(name, parsed).map_err(|msg| usage(flag, msg))
}

#[derive(Clone, Copy, Default)]
pub(super) struct CommonFlagPolicy {
    pub(super) allow_out_flags: bool,
    pub(super) allow_detail: bool,
}

#[derive(Default)]
pub(super) struct CommonFlagState {
    pub(super) saw_format: bool,
    pub(super) saw_detail: bool,
    pub(super) saw_max_file_bytes: bool,
}

pub(super) fn parse_common_flag(
    token: &RawToken,
    args: &[OsString],
    cursor: &mut usize,
    options: &mut CliOptions,
    state: &mut CommonFlagState,
    policy: CommonFlagPolicy,
) -> Result<bool, CliError> {
    match token.flag.as_str() {
        "--format" => {
            if state.saw_format {
                return Err(usage("--format", "duplicate flag"));
            }
            let val = take_value(token, args, cursor)?;
            let text = val
                .to_str()
                .ok_or_else(|| usage("--format", "format must be UTF-8"))?;
            options.format = OutputFormat::parse(text).ok_or_else(|| {
                usage(
                    "--format",
                    format!("unknown format `{text}` (expected json, pretty, or human)"),
                )
            })?;
            state.saw_format = true;
            Ok(true)
        }
        "--detail" => {
            if !policy.allow_detail {
                return Err(usage(
                    "--detail",
                    "flag `--detail` is not supported for this command",
                ));
            }
            if state.saw_detail {
                return Err(usage("--detail", "duplicate flag"));
            }
            let val = take_value(token, args, cursor)?;
            let text = val
                .to_str()
                .ok_or_else(|| usage("--detail", "detail level must be UTF-8"))?;
            options.detail = Some(DetailLevel::parse(text).ok_or_else(|| {
                usage(
                    "--detail",
                    format!("unknown detail `{text}` (expected concise or full)"),
                )
            })?);
            state.saw_detail = true;
            Ok(true)
        }
        "--create-parents" => {
            if !policy.allow_out_flags {
                return Err(usage(
                    "--create-parents",
                    "flag `--create-parents` requires a command with `--out`",
                ));
            }
            ensure_no_attached(token)?;
            options.out_options.create_parents = true;
            *cursor = token.raw_idx + 1;
            Ok(true)
        }
        "--overwrite" => {
            if !policy.allow_out_flags {
                return Err(usage(
                    "--overwrite",
                    "flag `--overwrite` requires a command with `--out`",
                ));
            }
            ensure_no_attached(token)?;
            options.out_options.overwrite = true;
            *cursor = token.raw_idx + 1;
            Ok(true)
        }
        "--no-fsync" => {
            if !policy.allow_out_flags {
                return Err(usage(
                    "--no-fsync",
                    "flag `--no-fsync` requires a command with `--out`",
                ));
            }
            ensure_no_attached(token)?;
            options.out_options.no_fsync = true;
            *cursor = token.raw_idx + 1;
            Ok(true)
        }
        "--verbose" => {
            ensure_no_attached(token)?;
            options.verbose = true;
            *cursor = token.raw_idx + 1;
            Ok(true)
        }
        "--progress" => {
            ensure_no_attached(token)?;
            options.progress = true;
            *cursor = token.raw_idx + 1;
            Ok(true)
        }
        "--max-file-bytes" => {
            if state.saw_max_file_bytes {
                return Err(usage("--max-file-bytes", "duplicate flag"));
            }
            let val = take_value(token, args, cursor)?;
            options.max_file_bytes = parse_pos_u64("--max-file-bytes", &val, "byte limit")?;
            state.saw_max_file_bytes = true;
            Ok(true)
        }
        _ => Ok(false),
    }
}

pub(super) fn load_project(
    path: &Path,
    max_file_bytes: u64,
) -> Result<archsig_input::manifest::ProjectManifest, CliError> {
    let bytes = read_bounded_cli(path, max_file_bytes)?;
    parse_project_manifest(&bytes, path)
        .map_err(|issue| CliError::Input(Box::new(ResultIssue::Input(*issue))))
}

fn validate_out_path(out: Option<&Path>, opts: OutOptions) -> Result<(), CliError> {
    if let Some(out) = out {
        crate::run::output::out_ok_with_options(out, opts)
            .map_err(|message| raw_usage("--out", format!("--out {}: {message}", out.display())))?;
    }
    Ok(())
}

fn help_for_command(cmd: &str) -> Option<&'static str> {
    match cmd {
        "check" => Some(help::CHECK_HELP),
        "run" => Some(help::RUN_HELP),
        "reobserve" => Some(help::REOBSERVE_HELP),
        "digest" => Some(help::DIGEST_HELP),
        "inspect" => Some(help::INSPECT_HELP),
        "evidence" => Some(help::EVIDENCE_HELP),
        "law-fibers" => Some(help::FIBERS_HELP),
        "version" => Some(help::VERSION_HELP),
        _ => None,
    }
}

/// 統一 CLI 引数列をパースして `ParsedCli` を返す。
pub fn parse_cli(args: &[OsString]) -> Result<ParsedCli, CliError> {
    let words: Vec<_> = args.iter().map(|a| a.to_str()).collect();
    match words.as_slice() {
        [Some("--help" | "-h" | "help")] => {
            return Ok(ParsedCli {
                command: CliCommand::Help(help::HELP),
                options: CliOptions::default(),
            });
        }
        [Some("help"), Some(sub)] => {
            return if let Some(text) = help_for_command(sub) {
                Ok(ParsedCli {
                    command: CliCommand::Help(text),
                    options: CliOptions::default(),
                })
            } else {
                Err(usage(sub, format!("unknown command `{sub}`")))
            };
        }
        [Some("help"), extra, ..] => {
            return Err(usage(extra.unwrap_or(""), "help takes one command"));
        }
        [Some(sub), Some("--help" | "-h")] => {
            if let Some(text) = help_for_command(sub) {
                return Ok(ParsedCli {
                    command: CliCommand::Help(text),
                    options: CliOptions::default(),
                });
            }
        }
        _ => {}
    }

    let Some(cmd_raw) = args.first() else {
        return Err(usage(
            "",
            "specify command check, run, reobserve, evidence, law-fibers, or version",
        ));
    };
    let Some(cmd) = cmd_raw.to_str() else {
        return Err(usage(
            "",
            "expected command check, run, reobserve, digest, inspect, evidence, law-fibers, or version",
        ));
    };

    match cmd {
        "version" | "--version" => parser_sub::parse_version(cmd, &args[1..]),
        "check" => parse_check_or_run(false, &args[1..]),
        "run" => parse_check_or_run(true, &args[1..]),
        "reobserve" => parse_reobserve(&args[1..]),
        "digest" => parser_sub::parse_digest(&args[1..]),
        "inspect" => parser_sub::parse_inspect(&args[1..]),
        "evidence" => parser_sub::parse_evidence(&args[1..]),
        "law-fibers" => parser_sub::parse_law_fibers(&args[1..]),
        other => Err(usage(
            other,
            "expected command check, run, reobserve, digest, inspect, evidence, law-fibers, or version",
        )),
    }
}

fn parse_check_or_run(running: bool, rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let prescanned_max = prescan_max_file_bytes(rest)?;
    let mut options = CliOptions::default();
    if let Some(n) = prescanned_max {
        options.max_file_bytes = n;
    }
    let effective_read_max = prescanned_max.unwrap_or(DEFAULT_MAX_FILE_BYTES);

    let mut project_path: Option<PathBuf> = None;
    let mut definitions = Vec::new();
    let mut asks = Vec::new();
    let mut singles = BTreeMap::new();
    let mut cli_shigure_limits = Vec::new();
    let mut used_stdin = false;
    let mut state = CommonFlagState::default();

    let policy = CommonFlagPolicy {
        allow_out_flags: true,
        allow_detail: running,
    };
    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if parse_common_flag(&tok, rest, &mut i, &mut options, &mut state, policy)? {
            continue;
        }
        let flag = tok.flag.as_str();
        let known = matches!(
            flag,
            "--atom-definition" | "--law" | "--archmap" | "--out" | "--project"
        ) || (running
            && matches!(flag, "--ask" | "--ask-file" | "--reuse" | "--shigure-limit"));
        if !known {
            return Err(usage(
                flag,
                format!("unknown flag or positional argument `{flag}`"),
            ));
        }
        let value = take_value(&tok, rest, &mut i)?;
        match flag {
            "--project" => {
                if project_path.is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
                if value.is_empty() {
                    return Err(usage(flag, "project path must be nonempty"));
                }
                project_path = Some(PathBuf::from(value));
            }
            "--atom-definition" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                definitions.push(PathBuf::from(value));
            }
            "--ask" => {
                let s = value
                    .to_str()
                    .ok_or_else(|| usage(flag, "request must be UTF-8"))?;
                asks.push(s.to_owned());
            }
            "--ask-file" => {
                asks.extend(read_ask_file(
                    &value,
                    effective_read_max,
                    &mut used_stdin,
                    flag,
                )?);
            }
            "--shigure-limit" => cli_shigure_limits.push(value),
            _ => {
                if flag != "--out" && value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                if singles.contains_key(flag) {
                    return Err(usage(flag, "duplicate flag"));
                }
                singles.insert(flag.to_owned(), value);
            }
        }
    }

    if let Some(p) = project_path.as_deref() {
        let m = load_project(p, effective_read_max)?;
        if !state.saw_max_file_bytes
            && let Some(limit) = m.max_file_bytes
        {
            options.max_file_bytes = limit;
        }
        for (k, v) in &m.shigure_limits {
            options
                .shigure_limits
                .set(k, *v)
                .map_err(|msg| usage("--project", msg))?;
        }
        if definitions.is_empty() {
            definitions = m.atom_definitions;
        }
        if !singles.contains_key("--law") {
            singles.insert("--law".to_owned(), m.law.into_os_string());
        }
        if !singles.contains_key("--archmap")
            && let Some(archmap) = m.archmap
        {
            singles.insert("--archmap".to_owned(), archmap.into_os_string());
        }
        if running && asks.is_empty() {
            asks = m.asks;
        }
    }

    for val in cli_shigure_limits {
        parse_shigure_limit("--shigure-limit", &val, &mut options.shigure_limits)?;
    }
    if definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "at least one --atom-definition is required",
        ));
    }
    let law = singles
        .remove("--law")
        .ok_or_else(|| usage("--law", "--law is required"))?;
    let archmap = singles.remove("--archmap").map(PathBuf::from);
    if running && archmap.is_none() {
        return Err(usage("--archmap", "run requires --archmap"));
    }
    if running && asks.is_empty() {
        return Err(usage("--ask", "run requires at least one --ask"));
    }
    let out = singles.remove("--out").map(PathBuf::from);
    validate_out_path(out.as_deref(), options.out_options)?;
    let inputs = CheckArgs {
        atom_definitions: definitions,
        law: PathBuf::from(law),
        archmap,
        out,
    };
    if running {
        let args = RunArgs {
            inputs,
            asks,
            reuse: singles.remove("--reuse").map(PathBuf::from),
        };
        Ok(ParsedCli {
            command: CliCommand::Run(Checked::from_parts(
                args,
                options.max_file_bytes,
                options.shigure_limits.clone(),
            )),
            options,
        })
    } else {
        Ok(ParsedCli {
            command: CliCommand::Check(Checked::from_parts(
                inputs,
                options.max_file_bytes,
                options.shigure_limits.clone(),
            )),
            options,
        })
    }
}

fn parse_reobserve(rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let prescanned_max = prescan_max_file_bytes(rest)?;
    let effective_read_max = prescanned_max.unwrap_or(DEFAULT_MAX_FILE_BYTES);
    let mut options = CliOptions::default();
    if let Some(n) = prescanned_max {
        options.max_file_bytes = n;
    }

    let (mut before_defs, mut before_law, mut before_archmap, mut before_asks) =
        (Vec::new(), None, None, Vec::new());
    let (mut cur_defs, mut cur_law, mut cur_archmap, mut cur_asks, mut cur_out) =
        (Vec::new(), None, None, Vec::new(), None);
    let mut alignment: Option<PathBuf> = None;
    let mut used_stdin = false;
    let mut state = CommonFlagState::default();

    let policy = CommonFlagPolicy {
        allow_out_flags: true,
        allow_detail: true,
    };
    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if parse_common_flag(&tok, rest, &mut i, &mut options, &mut state, policy)? {
            continue;
        }
        let flag = tok.flag.as_str();
        if !matches!(
            flag,
            "--alignment"
                | "--before-atom-definition"
                | "--before-law"
                | "--before-archmap"
                | "--before-ask"
                | "--before-ask-file"
                | "--atom-definition"
                | "--law"
                | "--archmap"
                | "--ask"
                | "--ask-file"
                | "--out"
                | "--shigure-limit"
        ) {
            return Err(usage(flag, "unknown reobservation flag"));
        }
        let value = take_value(&tok, rest, &mut i)?;
        match flag {
            "--alignment" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                if alignment.replace(PathBuf::from(value)).is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
            }
            "--before-atom-definition" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                before_defs.push(PathBuf::from(value));
            }
            "--before-law" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                if before_law.replace(PathBuf::from(value)).is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
            }
            "--before-archmap" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                if before_archmap.replace(PathBuf::from(value)).is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
            }
            "--before-ask" => {
                let s = value
                    .to_str()
                    .ok_or_else(|| usage(flag, "request must be UTF-8"))?;
                before_asks.push(s.to_owned());
            }
            "--before-ask-file" => {
                before_asks.extend(read_ask_file(
                    &value,
                    effective_read_max,
                    &mut used_stdin,
                    flag,
                )?);
            }
            "--atom-definition" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                cur_defs.push(PathBuf::from(value));
            }
            "--law" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                if cur_law.replace(PathBuf::from(value)).is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
            }
            "--archmap" => {
                if value.is_empty() {
                    return Err(usage(flag, "path must be nonempty"));
                }
                if cur_archmap.replace(PathBuf::from(value)).is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
            }
            "--ask" => {
                let s = value
                    .to_str()
                    .ok_or_else(|| usage(flag, "request must be UTF-8"))?;
                cur_asks.push(s.to_owned());
            }
            "--ask-file" => {
                cur_asks.extend(read_ask_file(
                    &value,
                    effective_read_max,
                    &mut used_stdin,
                    flag,
                )?);
            }
            "--out" => {
                if cur_out.replace(PathBuf::from(value)).is_some() {
                    return Err(usage(flag, "duplicate flag"));
                }
            }
            "--shigure-limit" => parse_shigure_limit(flag, &value, &mut options.shigure_limits)?,
            _ => unreachable!(),
        }
    }

    if before_defs.is_empty() && !cur_defs.is_empty() {
        before_defs = cur_defs.clone();
    }
    if before_law.is_none() {
        before_law = cur_law.clone();
    }

    if before_defs.is_empty() {
        return Err(usage(
            "--before-atom-definition",
            "at least one --atom-definition is required",
        ));
    }
    let before_law = before_law.ok_or_else(|| usage("--before-law", "--law is required"))?;
    if before_archmap.is_none() {
        return Err(usage("--before-archmap", "run requires --archmap"));
    }
    if before_asks.is_empty() {
        return Err(usage("--before-ask", "run requires at least one --ask"));
    }
    if cur_defs.is_empty() {
        return Err(usage(
            "--atom-definition",
            "at least one --atom-definition is required",
        ));
    }
    let cur_law = cur_law.ok_or_else(|| usage("--law", "--law is required"))?;
    if cur_archmap.is_none() {
        return Err(usage("--archmap", "run requires --archmap"));
    }
    if cur_asks.is_empty() {
        return Err(usage("--ask", "run requires at least one --ask"));
    }
    validate_out_path(cur_out.as_deref(), options.out_options)?;

    let prev_checked = Checked::from_parts(
        RunArgs {
            inputs: CheckArgs {
                atom_definitions: before_defs,
                law: before_law,
                archmap: before_archmap,
                out: None,
            },
            asks: before_asks,
            reuse: None,
        },
        options.max_file_bytes,
        options.shigure_limits.clone(),
    );
    let cur_checked = Checked::from_parts(
        RunArgs {
            inputs: CheckArgs {
                atom_definitions: cur_defs,
                law: cur_law,
                archmap: cur_archmap,
                out: cur_out,
            },
            asks: cur_asks,
            reuse: None,
        },
        options.max_file_bytes,
        options.shigure_limits.clone(),
    );
    Ok(ParsedCli {
        command: CliCommand::Reobserve(ReobserveArgs::from_parts(
            prev_checked,
            cur_checked,
            alignment,
        )),
        options,
    })
}

/// 旧 `run::parse_args` 互換エントリ。
pub fn parse_legacy_command(args: &[OsString]) -> Result<Command, UsageError> {
    match parse_cli(args) {
        Ok(parsed) => match parsed.command {
            CliCommand::Check(c) => Ok(Command::Check(c)),
            CliCommand::Run(r) => Ok(Command::Run(r)),
            CliCommand::Reobserve(r) => Ok(Command::Reobserve(r)),
            CliCommand::Version => Ok(Command::Version),
            CliCommand::Help(h) => Ok(Command::Help(h)),
            CliCommand::Evidence(_)
            | CliCommand::LawFibers(_)
            | CliCommand::Digest(_)
            | CliCommand::InspectInputs(_)
            | CliCommand::InspectResult(_) => Err(UsageError {
                argument: args
                    .first()
                    .map(|a| a.to_string_lossy().into_owned())
                    .unwrap_or_default(),
                message: "command is handled via unified CLI entrypoint".to_owned(),
                prefix_argument: false,
            }),
        },
        Err(CliError::Usage(u)) => Err(*u),
        Err(CliError::Io(issue) | CliError::Input(issue)) => {
            let msg = match *issue {
                ResultIssue::Io { message, .. } => message,
                ResultIssue::Input(i) => i.message,
                _ => "invalid CLI input".to_owned(),
            };
            Err(UsageError {
                argument: "--project".to_owned(),
                message: msg,
                prefix_argument: true,
            })
        }
    }
}
