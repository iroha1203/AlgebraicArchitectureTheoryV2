//! SHIGURE CLI `--ask` 構文の分類と解析。

use super::deliver::usage_issue;
use super::{AskPartition, ParsedShigureRequest, ShigureCliQuery};
use crate::run::{Outcome, Signals, output};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::result::Status;
use archsig_shigure::solver::ShigureQueryKind;
use std::collections::BTreeSet;

const SHIGURE_QUERY_PREFIXES: [&str; 6] = [
    "shigure_preservation",
    "shigure_solve",
    "shigure_interaction",
    "shigure_diagram",
    "shigure_path",
    "shigure_transfer",
];

/// `--ask` 文字列列に SHIGURE 問いが含まれるかを判定する。
pub(in crate::run) fn classify_asks(asks: &[String]) -> AskPartition {
    let mut shigure_count = 0usize;
    for ask in asks {
        if looks_like_shigure_ask(ask) {
            shigure_count += 1;
        }
    }
    if shigure_count == 0 {
        AskPartition::None
    } else if shigure_count == asks.len() {
        AskPartition::AllShigure
    } else {
        AskPartition::Mixed
    }
}

fn looks_like_shigure_ask(ask: &str) -> bool {
    let rhs = match (ask.find('='), ask.find('(')) {
        (Some(eq), Some(open)) if eq < open => ask[eq + 1..].trim_start(),
        (Some(eq), None) => ask[eq + 1..].trim_start(),
        _ => ask.trim_start(),
    };
    for prefix in SHIGURE_QUERY_PREFIXES {
        if let Some(rest) = rhs.strip_prefix(prefix)
            && (rest.is_empty()
                || !rest
                    .as_bytes()
                    .first()
                    .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_'))
        {
            return true;
        }
    }
    false
}

pub(super) fn parse_shigure_requests(
    asks: &[String],
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<Vec<ParsedShigureRequest>, Outcome> {
    let mut parsed = Vec::with_capacity(asks.len());
    let mut seen_ids = BTreeSet::new();
    for ask in asks {
        if let Err(signal) = control.checkpoint(Checkpoint::RequestSyntax) {
            return Err(output::notify(
                signals,
                Status::Interrupted,
                75,
                control.stop_reason(),
                vec![signal.issue()],
            ));
        }
        let req = parse_single_ask(ask).map_err(|msg| {
            output::notify(
                signals,
                Status::Invalid,
                64,
                control.stop_reason(),
                vec![usage_issue(None, &msg)],
            )
        })?;
        if !seen_ids.insert(req.id.clone()) {
            return Err(output::notify(
                signals,
                Status::Invalid,
                64,
                control.stop_reason(),
                vec![usage_issue(
                    Some(&req.id),
                    &format!("duplicate request id `{}`", req.id),
                )],
            ));
        }
        parsed.push(req);
    }
    Ok(parsed)
}

pub(super) fn parse_single_ask(ask: &str) -> Result<ParsedShigureRequest, String> {
    let Some(eq_pos) = ask.find('=') else {
        return Err(format!(
            "invalid SHIGURE request `{ask}`: expected `ID=shigure_<kind>(DeclName[, snapshot=SnapshotId])`"
        ));
    };
    let id = ask[..eq_pos].trim();
    if !is_ident(id) {
        return Err(format!(
            "invalid request id `{id}` in `{ask}`: expected ASCII identifier"
        ));
    }
    let rhs = ask[eq_pos + 1..].trim();
    let Some(open_pos) = rhs.find('(') else {
        return Err(format!(
            "invalid SHIGURE request `{ask}`: expected `(` after query kind"
        ));
    };
    if !rhs.ends_with(')') {
        return Err(format!(
            "invalid SHIGURE request `{ask}`: expected closing `)`"
        ));
    }
    let kind_str = rhs[..open_pos].trim();
    let query = match kind_str {
        "shigure_preservation" => ShigureCliQuery::Task(ShigureQueryKind::SemanticPreservation),
        "shigure_solve" => ShigureCliQuery::Task(ShigureQueryKind::ConditionalSolutionSpace),
        "shigure_interaction" => ShigureCliQuery::Task(ShigureQueryKind::InteractionAnalysis),
        "shigure_diagram" => ShigureCliQuery::Diagram,
        "shigure_path" => ShigureCliQuery::Path,
        "shigure_transfer" => ShigureCliQuery::Transfer,
        other => {
            return Err(format!(
                "unknown SHIGURE query kind `{other}` in `{ask}`; expected `shigure_preservation`, `shigure_solve`, `shigure_interaction`, `shigure_diagram`, `shigure_path`, or `shigure_transfer`"
            ));
        }
    };
    let inner = rhs[open_pos + 1..rhs.len() - 1].trim();
    if inner.is_empty() {
        return Err(format!(
            "missing SHIGURE declaration name in `{ask}`; expected `{kind_str}(DeclName[, snapshot=SnapshotId])`"
        ));
    }
    let mut parts = inner.split(',');
    let head = parts.next().expect("non-empty split").trim();
    if !is_qname(head) {
        return Err(format!(
            "invalid SHIGURE declaration name `{head}` in `{ask}`: expected identifier or qualified `Reading.Decl` name"
        ));
    }
    let mut snapshot: Option<String> = None;
    for raw_arg in parts {
        let arg = raw_arg.trim();
        if arg.is_empty() {
            return Err(format!(
                "empty argument in SHIGURE request `{ask}` (trailing or duplicate comma)"
            ));
        }
        let Some(arg_eq) = arg.find('=') else {
            return Err(format!(
                "invalid argument `{arg}` in `{ask}`: expected `snapshot=SnapshotId`"
            ));
        };
        let key = arg[..arg_eq].trim();
        let val = arg[arg_eq + 1..].trim();
        match key {
            "snapshot" => {
                if snapshot.is_some() {
                    return Err(format!("duplicate argument `snapshot` in `{ask}`"));
                }
                if !is_snapshot_id(val) {
                    return Err(format!(
                        "invalid snapshot id `{val}` in `{ask}`: expected non-empty ArchMap snapshot identifier"
                    ));
                }
                snapshot = Some(val.to_owned());
            }
            other => {
                return Err(format!(
                    "unknown argument `{other}` in SHIGURE request `{ask}`; only optional `snapshot=SnapshotId` is supported"
                ));
            }
        }
    }
    Ok(ParsedShigureRequest {
        id: id.to_owned(),
        text: ask.to_owned(),
        query,
        task_name: head.to_owned(),
        snapshot,
    })
}

fn is_ident(s: &str) -> bool {
    let mut bytes = s.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !archsig_common::names::is_reserved(s)
}

fn is_qname(s: &str) -> bool {
    !s.is_empty() && s.split('.').all(is_ident)
}

fn is_snapshot_id(s: &str) -> bool {
    let mut bytes = s.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && bytes.all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
}
