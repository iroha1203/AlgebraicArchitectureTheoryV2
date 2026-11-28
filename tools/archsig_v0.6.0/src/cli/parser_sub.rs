//! `digest`, `inspect`, `evidence`, `law-fibers`, `version` サブコマンド用パーサ。

use super::parser::{
    CommonFlagPolicy, CommonFlagState, ensure_no_attached, load_project, parse_common_flag,
    prescan_max_file_bytes, take_value, tokenize_flag, usage,
};
use super::{
    CliCommand, CliError, CliOptions, DigestArgs, EvidenceArgs, FibersArgs, InspectInputsArgs,
    InspectResultArgs, OutputFormat, ParsedCli,
};
use archsig_common::limits::DEFAULT_MAX_FILE_BYTES;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;

pub(super) fn parse_version(cmd: &str, rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let mut options = CliOptions::default();
    let mut saw_format = false;
    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if cmd == "--version" {
            return Err(usage(&tok.flag, "version takes no arguments"));
        }
        if tok.flag == "--format" && !saw_format {
            let val = take_value(&tok, rest, &mut i)?;
            let text = val
                .to_str()
                .ok_or_else(|| usage("--format", "format must be UTF-8"))?;
            options.format = OutputFormat::parse(text)
                .ok_or_else(|| usage("--format", format!("unknown format `{text}`")))?;
            saw_format = true;
        } else {
            return Err(usage(&tok.flag, "version takes no arguments"));
        }
    }
    Ok(ParsedCli {
        command: CliCommand::Version,
        options,
    })
}

pub(super) fn parse_digest(rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let prescanned_max = prescan_max_file_bytes(rest)?;
    let effective_read_max = prescanned_max.unwrap_or(DEFAULT_MAX_FILE_BYTES);
    let mut options = CliOptions::default();
    if let Some(n) = prescanned_max {
        options.max_file_bytes = n;
    }

    let mut project_path: Option<PathBuf> = None;
    let mut definitions = Vec::new();
    let mut state = CommonFlagState::default();

    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if parse_common_flag(
            &tok,
            rest,
            &mut i,
            &mut options,
            &mut state,
            CommonFlagPolicy::default(),
        )? {
            continue;
        }
        match tok.flag.as_str() {
            "--atom-definition" => {
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--atom-definition", "path must be nonempty"));
                }
                definitions.push(PathBuf::from(val));
            }
            "--project" => {
                if project_path.is_some() {
                    return Err(usage("--project", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--project", "project path must be nonempty"));
                }
                project_path = Some(PathBuf::from(val));
            }
            other => {
                return Err(usage(
                    other,
                    format!("unknown flag or positional argument `{other}`"),
                ));
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
        if definitions.is_empty() {
            definitions = m.atom_definitions;
        }
    }

    if definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "at least one --atom-definition is required",
        ));
    }

    Ok(ParsedCli {
        command: CliCommand::Digest(DigestArgs {
            atom_definitions: definitions,
        }),
        options,
    })
}

pub(super) fn parse_inspect(rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let prescanned_max = prescan_max_file_bytes(rest)?;
    let effective_read_max = prescanned_max.unwrap_or(DEFAULT_MAX_FILE_BYTES);
    let mut options = CliOptions::default();
    if let Some(n) = prescanned_max {
        options.max_file_bytes = n;
    }

    let mut project_path: Option<PathBuf> = None;
    let mut definitions = Vec::new();
    let mut law: Option<PathBuf> = None;
    let mut archmap: Option<PathBuf> = None;
    let mut result_dir: Option<PathBuf> = None;
    let mut answers = Vec::new();
    let mut evidence = false;
    let mut state = CommonFlagState::default();

    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if parse_common_flag(
            &tok,
            rest,
            &mut i,
            &mut options,
            &mut state,
            CommonFlagPolicy::default(),
        )? {
            continue;
        }
        match tok.flag.as_str() {
            "--atom-definition" => {
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--atom-definition", "path must be nonempty"));
                }
                definitions.push(PathBuf::from(val));
            }
            "--law" => {
                if law.is_some() {
                    return Err(usage("--law", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--law", "path must be nonempty"));
                }
                law = Some(PathBuf::from(val));
            }
            "--archmap" => {
                if archmap.is_some() {
                    return Err(usage("--archmap", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--archmap", "path must be nonempty"));
                }
                archmap = Some(PathBuf::from(val));
            }
            "--project" => {
                if project_path.is_some() {
                    return Err(usage("--project", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--project", "path must be nonempty"));
                }
                project_path = Some(PathBuf::from(val));
            }
            "--result" => {
                if result_dir.is_some() {
                    return Err(usage("--result", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--result", "path must be nonempty"));
                }
                result_dir = Some(PathBuf::from(val));
            }
            "--answer" => {
                let val = take_value(&tok, rest, &mut i)?;
                let s = val
                    .to_str()
                    .ok_or_else(|| usage("--answer", "answer ID must be UTF-8"))?;
                if s.is_empty() {
                    return Err(usage("--answer", "answer ID must be nonempty"));
                }
                answers.push(s.to_owned());
            }
            "--evidence" => {
                ensure_no_attached(&tok)?;
                evidence = true;
                i += 1;
            }
            other => {
                return Err(usage(
                    other,
                    format!("unknown flag or positional argument `{other}`"),
                ));
            }
        }
    }

    if let Some(dir) = result_dir {
        if project_path.is_some() || !definitions.is_empty() || law.is_some() || archmap.is_some() {
            return Err(usage(
                "--result",
                "--result cannot be combined with input file flags or --project",
            ));
        }
        return Ok(ParsedCli {
            command: CliCommand::InspectResult(InspectResultArgs {
                result_dir: dir,
                answers,
                evidence,
            }),
            options,
        });
    }

    if !answers.is_empty() || evidence {
        return Err(usage(
            if !answers.is_empty() {
                "--answer"
            } else {
                "--evidence"
            },
            "--answer and --evidence require --result DIR",
        ));
    }

    if let Some(p) = project_path.as_deref() {
        let m = load_project(p, effective_read_max)?;
        if !state.saw_max_file_bytes
            && let Some(limit) = m.max_file_bytes
        {
            options.max_file_bytes = limit;
        }
        if definitions.is_empty() {
            definitions = m.atom_definitions;
        }
        if law.is_none() {
            law = Some(m.law);
        }
        if archmap.is_none() {
            archmap = m.archmap;
        }
    }

    if definitions.is_empty() {
        return Err(usage(
            "--atom-definition",
            "specify --atom-definition (or --project) or --result DIR",
        ));
    }

    Ok(ParsedCli {
        command: CliCommand::InspectInputs(InspectInputsArgs {
            atom_definitions: definitions,
            law,
            archmap,
        }),
        options,
    })
}

pub(super) fn parse_evidence(rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let mut options = CliOptions::default();
    let mut archmap: Option<PathBuf> = None;
    let mut atoms: Vec<String> = Vec::new();
    let mut sources: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut state = CommonFlagState::default();

    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if parse_common_flag(
            &tok,
            rest,
            &mut i,
            &mut options,
            &mut state,
            CommonFlagPolicy::default(),
        )? {
            continue;
        }
        match tok.flag.as_str() {
            "--archmap" => {
                if archmap.is_some() {
                    return Err(usage("--archmap", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--archmap", "path must be nonempty"));
                }
                archmap = Some(PathBuf::from(val));
            }
            "--atom" => {
                let val = take_value(&tok, rest, &mut i)?;
                let text = val
                    .to_str()
                    .ok_or_else(|| usage("--atom", "selector must be UTF-8"))?;
                let parts: Vec<_> = text.split('/').collect();
                if parts.len() != 2
                    || parts.iter().any(|s| s.is_empty())
                    || atoms.iter().any(|s| s == text)
                {
                    return Err(usage(
                        "--atom",
                        "select distinct nonempty snapshot/atom IDs",
                    ));
                }
                atoms.push(text.to_owned());
            }
            "--source" => {
                let val = take_value(&tok, rest, &mut i)?;
                let (id, path) = crate::platform::split_source_binding(val.as_os_str())
                    .map_err(|msg| usage("--source", msg))?;
                if sources.contains_key(&id) {
                    return Err(usage(
                        "--source",
                        "source bindings need distinct IDs and nonempty paths",
                    ));
                }
                sources.insert(id, path);
            }
            other => return Err(usage(other, "unknown flag or positional argument")),
        }
    }

    if atoms.is_empty() {
        return Err(usage("--atom", "at least one --atom is required"));
    }
    let archmap = archmap.ok_or_else(|| usage("--archmap", "input file is required"))?;
    Ok(ParsedCli {
        command: CliCommand::Evidence(EvidenceArgs {
            archmap,
            atoms,
            sources,
        }),
        options,
    })
}

pub(super) fn parse_law_fibers(rest: &[OsString]) -> Result<ParsedCli, CliError> {
    let mut options = CliOptions::default();
    let mut table: Option<PathBuf> = None;
    let mut state = CommonFlagState::default();

    let mut i = 0;
    while i < rest.len() {
        let tok = tokenize_flag(&rest[i], i);
        if parse_common_flag(
            &tok,
            rest,
            &mut i,
            &mut options,
            &mut state,
            CommonFlagPolicy::default(),
        )? {
            continue;
        }
        match tok.flag.as_str() {
            "--table" => {
                if table.is_some() {
                    return Err(usage("--table", "duplicate flag"));
                }
                let val = take_value(&tok, rest, &mut i)?;
                if val.is_empty() {
                    return Err(usage("--table", "path must be nonempty"));
                }
                table = Some(PathBuf::from(val));
            }
            other => return Err(usage(other, "unknown flag or positional argument")),
        }
    }
    let table = table.ok_or_else(|| usage("--table", "input file is required"))?;
    Ok(ParsedCli {
        command: CliCommand::LawFibers(FibersArgs { table }),
        options,
    })
}
