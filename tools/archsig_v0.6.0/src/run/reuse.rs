//! 候補を現在の検査済み導出へ照合し、推論は採用せず全再計算する。
use crate::canonical::Json;
use crate::json::{JNode, JValue};
use crate::result::ResultIssue;
use crate::{
    control::{CheckFailure, Checkpoint, Control},
    observed::ObservedEvaluation,
    result::Signal,
};
use std::{
    collections::BTreeMap,
    io::Read,
    path::{Path, PathBuf},
};

pub(super) struct Candidate {
    path: PathBuf,
    document: Option<JNode>,
    rejected: Vec<Json>,
}
impl Candidate {
    fn reject(&mut self, message: String) {
        self.rejected.push(
            ResultIssue::Usage {
                argument: "--reuse".into(),
                message: format!("--reuse candidate {}: {message}", self.path.display()),
            }
            .wire(),
        );
    }
    /// JSONは照合だけに使う。候補の値・束縛を評価器へ渡さない。
    pub(super) fn verify(
        mut self,
        evaluation: &ObservedEvaluation,
        control: &mut Control,
    ) -> (Vec<Json>, Option<Signal>) {
        if let Some(document) = &self.document
            && matches!(evaluation.status(), "complete" | "partial")
        {
            match verify(document, evaluation, control) {
                Ok(()) => {}
                Err(Failure::Rejected(message)) => self.reject(message),
                Err(Failure::Stopped(reason)) => return (self.rejected, Some(reason)),
            }
        }
        (self.rejected, None)
    }
}
pub(super) fn inspect(path: Option<&Path>, control: &mut Control) -> Result<Candidate, Signal> {
    let mut candidate = Candidate {
        path: path.unwrap_or_else(|| Path::new("")).to_owned(),
        document: None,
        rejected: Vec::new(),
    };
    let Some(path) = path else {
        return Ok(candidate);
    };
    control.checkpoint(Checkpoint::Reuse)?;
    // componentsは末尾のslash/dotを除く。NOFOLLOWを意図した最終directoryへ適用する。
    // 親pathのOS解決は通常の明示pathと同じであり、候補から追加pathを探索しない。
    let normalized: PathBuf = path.components().collect();
    let read = || -> std::io::Result<Vec<u8>> {
        use rustix::fs::{Mode, OFlags, openat};
        let directory = openat(
            rustix::fs::CWD,
            &normalized,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW,
            Mode::empty(),
        )?;
        let file = openat(
            &directory,
            "result.json",
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK,
            Mode::empty(),
        )?;
        let mut file = std::fs::File::from(file);
        if !file.metadata()?.is_file() {
            return Err(std::io::Error::other("result.json is not a regular file"));
        }
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        Ok(bytes)
    };
    let read = read();
    control.checkpoint(Checkpoint::Reuse)?;
    let bytes = match read {
        Ok(bytes) => bytes,
        Err(error) => {
            candidate.reject(format!("cannot read result.json: {error}"));
            return Ok(candidate);
        }
    };
    let document = match crate::json::parse_inner::<CheckFailure<Box<crate::issue::Issue>>>(
        &bytes,
        control,
        Checkpoint::Reuse,
    ) {
        Ok(document) => document,
        Err(CheckFailure::Stopped(reason)) => return Err(reason),
        Err(CheckFailure::Input(issue)) => {
            candidate.reject(format!("invalid JSON: {}", issue.message));
            return Ok(candidate);
        }
    };
    match header(&document, control) {
        Ok(()) => candidate.document = Some(document),
        Err(Failure::Rejected(message)) => candidate.reject(message),
        Err(Failure::Stopped(reason)) => return Err(reason),
    }
    Ok(candidate)
}
enum Failure {
    Rejected(String),
    Stopped(Signal),
}
impl From<Signal> for Failure {
    fn from(reason: Signal) -> Self {
        Self::Stopped(reason)
    }
}
type Checked<T> = Result<T, Failure>;
fn invalid(message: impl Into<String>) -> Failure {
    Failure::Rejected(message.into())
}
fn fields(node: &JNode) -> Checked<&[(String, JNode)]> {
    match &node.value {
        JValue::Obj(fields) => Ok(fields),
        _ => Err(invalid("expected an object")),
    }
}
fn field<'a>(node: &'a JNode, name: &str) -> Checked<&'a JNode> {
    fields(node)?
        .iter()
        .find(|(key, _)| key == name)
        .map(|(_, v)| v)
        .ok_or_else(|| invalid(format!("missing {name}")))
}
fn text(node: &JNode) -> Checked<&str> {
    match &node.value {
        JValue::Str(s) => Ok(s),
        _ => Err(invalid("expected a string")),
    }
}
fn array(node: &JNode) -> Checked<&[JNode]> {
    match &node.value {
        JValue::Arr(a) => Ok(a),
        _ => Err(invalid("expected an array")),
    }
}
fn record(node: &JNode, required: &[&str], optional: &[&str]) -> Checked<()> {
    for name in required {
        field(node, name)?;
    }
    for (name, _) in fields(node)? {
        if !required.contains(&name.as_str()) && !optional.contains(&name.as_str()) {
            return Err(invalid(format!("unknown field: {name}")));
        }
    }
    Ok(())
}
fn nat(node: &JNode) -> Checked<()> {
    match &node.value {
        JValue::Num(s) if crate::archmap::nat_value(s).is_some() => Ok(()),
        _ => Err(invalid("Nat must be an integer in 0..9007199254740991")),
    }
}
fn header(document: &JNode, control: &mut Control) -> Checked<()> {
    control.checkpoint(Checkpoint::Reuse)?;
    if text(field(document, "format")?)? != crate::result::RESULT_FORMAT
        || text(field(document, "semantics")?)? != crate::law::SEMANTICS
    {
        return Err(invalid("format/semantics does not match the supported version"));
    }
    if text(field(document, "command")?)? != "run" {
        return Err(invalid("reuse candidate must be a saved run result"));
    }
    record(
        document,
        &[
            "format",
            "semantics",
            "command",
            "status",
            "exit_code",
            "inputs",
            "requests",
            "answers",
            "nodes",
            "issues",
        ],
        &["warnings"],
    )?;
    nat(field(document, "exit_code")?)?;
    if let Some((_, warnings)) = fields(document)?.iter().find(|(key, _)| key == "warnings") {
        for issue in array(warnings)? { issue_shape(issue, control)?; }
    }
    Ok(())
}
fn issue_shape(issue: &JNode, control: &mut Control) -> Checked<()> {
    control.checkpoint(Checkpoint::Reuse)?;
    record(
        issue,
        &["code", "message", "dependencies", "missing", "details"],
        &["request", "location"],
    )?;
    if text(field(issue, "message")?)?.is_empty() {
        return Err(invalid("Issue.message is empty"));
    }
    array(field(issue, "dependencies")?)?;
    array(field(issue, "missing")?)?;
    let details = field(issue, "details")?;
    // 旧候補の補助通知は意味上の入力にしない。現行の候補拒否通知はusageだけを生成する。
    // それ以外の旧通知を含む候補は採用対象へ広げず、全再計算する。
    if text(field(issue, "code")?)? != "usage" {
        return Err(invalid("cannot verify the candidate's previous rejection notice"));
    }
    record(details, &["argument"], &[])?;
    text(field(details, "argument")?)?;
    if !array(field(issue, "dependencies")?)?.is_empty()
        || !array(field(issue, "missing")?)?.is_empty()
    {
        return Err(invalid("candidate usage dependencies must be empty"));
    }
    if fields(issue)?
        .iter()
        .any(|(name, _)| name == "location" || name == "request")
    {
        return Err(invalid("invalid candidate usage location"));
    }
    Ok(())
}
fn wire_field<'a>(node: &'a Json, name: &str) -> Checked<&'a Json> {
    match node {
        Json::Obj(fields) => fields
            .get(name)
            .ok_or_else(|| invalid(format!("missing recomputed {name}"))),
        _ => Err(invalid("recomputed output is not an object")),
    }
}
fn normalized_candidate(
    node: &JNode,
    ids: &BTreeMap<String, String>,
    control: &mut Control,
) -> Checked<Json> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(Checkpoint::Reuse)?;
        Ok(match &node.value {
            JValue::Bool(b) => Json::Bool(*b),
            JValue::Num(s) => Json::Nat(
                crate::archmap::nat_value(s).ok_or_else(|| invalid("value is outside the Nat range or is not an integer"))?,
            ),
            JValue::Str(s) => Json::str(s),
            JValue::Arr(items) => Json::Arr(
                items
                    .iter()
                    .map(|n| normalized_candidate(n, ids, control))
                    .collect::<Checked<_>>()?,
            ),
            JValue::Obj(items) if items.iter().any(|(key, _)| key == "node") => {
                record(node, &["node"], &[])?;
                let id = text(field(node, "node")?)?;
                let key = ids
                    .get(id)
                    .ok_or_else(|| invalid(format!("undefined or nonpreceding Ref: {id}")))?;
                Json::obj([("node", Json::str(key))])
            }
            JValue::Obj(items) => Json::Obj(
                items
                    .iter()
                    .map(|(key, value)| {
                        Ok((key.clone(), normalized_candidate(value, ids, control)?))
                    })
                    .collect::<Checked<_>>()?,
            ),
            JValue::Null => return Err(invalid("null is not allowed")),
        })
    })
}
fn normalized_wire(
    node: &Json,
    ids: &BTreeMap<String, String>,
    control: &mut Control,
) -> Checked<Json> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(Checkpoint::Reuse)?;
        Ok(match node {
            Json::Bool(b) => Json::Bool(*b),
            Json::Nat(n) => Json::Nat(*n),
            Json::Str(s) => Json::str(s),
            Json::Arr(items) => Json::Arr(
                items
                    .iter()
                    .map(|n| normalized_wire(n, ids, control))
                    .collect::<Checked<_>>()?,
            ),
            Json::Obj(items) if items.contains_key("node") => {
                let Json::Str(id) = items
                    .get("node")
                    .ok_or_else(|| invalid("missing recomputed Ref"))?
                else {
                    return Err(invalid("recomputed Ref is not a string"));
                };
                let key = ids
                    .get(id)
                    .ok_or_else(|| invalid("recomputed Ref does not precede its use"))?;
                Json::obj([("node", Json::str(key))])
            }
            Json::Obj(items) => Json::Obj(
                items
                    .iter()
                    .map(|(key, value)| Ok((key.clone(), normalized_wire(value, ids, control)?)))
                    .collect::<Checked<_>>()?,
            ),
        })
    })
}
fn encoding(json: &Json, control: &mut Control) -> Checked<String> {
    match json
        .canonical_controlled::<CheckFailure<Box<crate::issue::Issue>>>(control, Checkpoint::Reuse)
    {
        Ok(s) => Ok(s),
        Err(CheckFailure::Stopped(reason)) => Err(Failure::Stopped(reason)),
        Err(CheckFailure::Input(issue)) => Err(invalid(issue.message)),
    }
}
fn node_content(mut node: Json, control: &mut Control) -> Checked<String> {
    let Json::Obj(fields) = &mut node else {
        return Err(invalid("node must be an object"));
    };
    fields.remove("id");
    encoding(&node, control)
}
fn verify(document: &JNode, evaluation: &ObservedEvaluation, control: &mut Control) -> Checked<()> {
    control.checkpoint(Checkpoint::Reuse)?;
    let replay = evaluation.result_wire_controlled(control, Checkpoint::Reuse)?;
    let empty = BTreeMap::new();
    // 元byte列のidentityと解決済み要求を照合する。宣言・型は現在の三入力から再検査する。
    // 候補が別の入力/問いのものでも、通常評価は既に現在入力から実行済みである。
    let mut inputs = normalized_candidate(field(document, "inputs")?, &empty, control)?;
    let Json::Arr(identities) = &mut inputs else {
        return Err(invalid("inputs must be an array"));
    };
    for identity in identities {
        control.checkpoint(Checkpoint::Reuse)?;
        let Json::Obj(fields) = identity else {
            return Err(invalid("InputIdentity must be an object"));
        };
        let Some(Json::Str(id)) = fields.get("id") else {
            return Err(invalid("missing InputIdentity.id"));
        };
        let expected = match id.as_str() {
            "law" => "inputs/law.law".to_owned(),
            "archmap" => "inputs/archmap.json".to_owned(),
            id => format!(
                "inputs/definitions/{}.json",
                id.strip_prefix("definition")
                    .ok_or_else(|| invalid("unknown input id"))?
            ),
        };
        if fields.get("path") != Some(&Json::str(expected)) {
            return Err(invalid("invalid fixed path for input copy"));
        }
        fields.remove("path");
    }
    if inputs != *wire_field(&replay, "inputs")? {
        return Err(invalid("current input identity does not match"));
    }
    for name in ["requests", "status"] {
        let candidate = normalized_candidate(field(document, name)?, &empty, control)?;
        if candidate != *wire_field(&replay, name)? {
            return Err(invalid(format!("cannot verify {name} against the current checked result")));
        }
    }
    let mut native_ids = BTreeMap::new();
    let mut verified = BTreeMap::new();
    let Json::Arr(nodes) = wire_field(&replay, "nodes")? else {
        return Err(invalid("missing recomputed nodes"));
    };
    for (index, node) in nodes.iter().enumerate() {
        control.checkpoint(Checkpoint::Reuse)?;
        let content = node_content(normalized_wire(node, &native_ids, control)?, control)?;
        let next = format!("v{}", verified.len());
        let key = verified.entry(content).or_insert(next).clone();
        native_ids.insert(format!("n{index}"), key);
    }
    let mut candidate_ids = BTreeMap::new();
    for (index, node) in array(field(document, "nodes")?)?.iter().enumerate() {
        control.checkpoint(Checkpoint::Reuse)?;
        let id = text(field(node, "id")?)?;
        if id != format!("n{index}") {
            return Err(invalid(format!("node.id must be n{index}")));
        }
        let content = node_content(
            normalized_candidate(node, &candidate_ids, control)?,
            control,
        )?;
        let key = verified.get(&content).ok_or_else(|| {
            invalid(format!(
                "cannot verify nodes[{index}] type, payload, provenance, conditions, or evidence against the current derivation"
            ))
        })?;
        candidate_ids.insert(id.to_owned(), key.clone());
    }
    // node番号・順序・共有を意味にしない。各Refを検査済みの導出内容へ正規化する。
    // digest一致で済ませず、payload・型・全依存・元位置を含むcanonical全文を照合する。
    let answers = normalized_candidate(field(document, "answers")?, &candidate_ids, control)?;
    if answers != normalized_wire(wire_field(&replay, "answers")?, &native_ids, control)? {
        return Err(invalid("cannot verify answers against the current checked derivation"));
    }
    let issues = normalized_candidate(field(document, "issues")?, &candidate_ids, control)?;
    if issues != normalized_wire(wire_field(&replay, "issues")?, &native_ids, control)? {
        return Err(invalid("cannot verify issues against the current checked derivation"));
    }
    let code = match evaluation.status() {
        "partial" => 2,
        "complete" => u64::from(
            evaluation
                .answers
                .iter()
                .any(|a| a.status == crate::observed::result::Decision::Refuted),
        ),
        _ => return Err(invalid("candidate verification is not finalized")),
    };
    if normalized_candidate(field(document, "exit_code")?, &empty, control)? != Json::Nat(code) {
        return Err(invalid("cannot verify exit_code against the computation result"));
    }
    control.checkpoint(Checkpoint::Reuse)?;
    Ok(())
}
