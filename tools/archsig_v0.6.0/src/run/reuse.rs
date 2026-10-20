//! 候補を現在の検査済み導出へ照合し、推論は採用せず全再計算する。
use crate::canonical::Json;
use crate::json::{JNode, JValue};
use crate::observed::{
    ObservedEvaluation,
    control::{CheckFailure, Checkpoint, Control, StopReason},
};
use crate::result::ResultIssue;
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
                message: format!("再利用候補 {}: {message}", self.path.display()),
            }
            .wire(),
        );
    }
    /// JSONは照合だけに使う。候補の値・束縛を評価器へ渡さない。
    pub(super) fn verify(
        mut self,
        evaluation: &ObservedEvaluation,
        control: &mut Control,
    ) -> (Vec<Json>, Option<StopReason>) {
        if let Some(document) = &self.document {
            if matches!(evaluation.status(), "complete" | "partial") {
                match verify(document, evaluation, control) {
                    Ok(()) => {}
                    Err(Failure::Rejected(message)) => self.reject(message),
                    Err(Failure::Stopped(reason)) => return (self.rejected, Some(reason)),
                }
            }
        }
        (self.rejected, None)
    }
}
pub(super) fn inspect(path: Option<&Path>, control: &mut Control) -> Result<Candidate, StopReason> {
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
            return Err(std::io::Error::other("result.jsonは通常ファイルではない"));
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
            candidate.reject(format!("result.jsonを読めない: {error}"));
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
            candidate.reject(format!("JSONが不正: {}", issue.message));
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
    Stopped(StopReason),
}
impl From<StopReason> for Failure {
    fn from(reason: StopReason) -> Self {
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
        _ => Err(invalid("objectが必要")),
    }
}
fn field<'a>(node: &'a JNode, name: &str) -> Checked<&'a JNode> {
    fields(node)?
        .iter()
        .find(|(key, _)| key == name)
        .map(|(_, v)| v)
        .ok_or_else(|| invalid(format!("{name}が必要")))
}
fn text(node: &JNode) -> Checked<&str> {
    match &node.value {
        JValue::Str(s) => Ok(s),
        _ => Err(invalid("文字列が必要")),
    }
}
fn array(node: &JNode) -> Checked<&[JNode]> {
    match &node.value {
        JValue::Arr(a) => Ok(a),
        _ => Err(invalid("arrayが必要")),
    }
}
fn record(node: &JNode, required: &[&str], optional: &[&str]) -> Checked<()> {
    for name in required {
        field(node, name)?;
    }
    for (name, _) in fields(node)? {
        if !required.contains(&name.as_str()) && !optional.contains(&name.as_str()) {
            return Err(invalid(format!("未知の欄: {name}")));
        }
    }
    Ok(())
}
fn decimal(node: &JNode) -> Checked<()> {
    let s = text(node)?;
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) || (s.len() > 1 && s.starts_with('0'))
    {
        return Err(invalid("DecimalNatが必要"));
    }
    Ok(())
}
fn nat(node: &JNode) -> Checked<()> {
    match &node.value {
        JValue::Num(s) if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) => Ok(()),
        _ => Err(invalid("Natが必要")),
    }
}
fn header(document: &JNode, control: &mut Control) -> Checked<()> {
    control.checkpoint(Checkpoint::Reuse)?;
    if text(field(document, "format")?)? != "archsig.result/2"
        || text(field(document, "semantics")?)? != crate::law::SEMANTICS
    {
        return Err(invalid("format/semanticsが対応版と異なる"));
    }
    record(
        document,
        &[
            "format",
            "semantics",
            "producer",
            "command",
            "status",
            "exit_code",
            "inputs",
            "declarations",
            "vocabularies",
            "requests",
            "answers",
            "nodes",
            "issues",
            "reuse",
            "usage",
            "limits",
        ],
        &[],
    )?;
    if text(field(document, "command")?)? != "run" && text(field(document, "command")?)? != "check"
    {
        return Err(invalid("commandが不正"));
    }
    record(field(document, "producer")?, &["version", "build"], &[])?;
    for name in ["version", "build"] {
        text(field(field(document, "producer")?, name)?)?;
    }
    record(
        field(document, "usage")?,
        &["elapsed_ms", "peak_bytes"],
        &[],
    )?;
    record(field(document, "limits")?, &[], &["time_ms", "memory_mib"])?;
    for group in ["usage", "limits"] {
        for (_, value) in fields(field(document, group)?)? {
            control.checkpoint(Checkpoint::Reuse)?;
            decimal(value)?;
        }
    }
    let reuse = field(document, "reuse")?;
    record(
        reuse,
        &[
            "requested",
            "accepted_nodes",
            "recomputed_nodes",
            "rejected",
        ],
        &[],
    )?;
    if !matches!(field(reuse, "requested")?.value, JValue::Bool(_)) {
        return Err(invalid("reuse.requestedはBool"));
    }
    for name in ["accepted_nodes", "recomputed_nodes"] {
        nat(field(reuse, name)?)?;
    }
    // 全再計算するため旧実行の性能や採用件数を証明には使わない。拒否理由の外形は検査する。
    for issue in array(field(reuse, "rejected")?)? {
        issue_shape(issue, control)?;
    }
    nat(field(document, "exit_code")?)?;
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
        return Err(invalid("Issue.messageが空"));
    }
    array(field(issue, "dependencies")?)?;
    array(field(issue, "missing")?)?;
    let details = field(issue, "details")?;
    // 旧候補の補助通知は意味上の入力にしない。現行の候補拒否通知はusageだけを生成する。
    // それ以外の旧通知を含む候補は採用対象へ広げず、全再計算する。
    if text(field(issue, "code")?)? != "usage" {
        return Err(invalid("候補の以前の拒否通知を照合できない"));
    }
    record(details, &["argument"], &[])?;
    text(field(details, "argument")?)?;
    if !array(field(issue, "dependencies")?)?.is_empty()
        || !array(field(issue, "missing")?)?.is_empty()
    {
        return Err(invalid("候補usageの依存は空"));
    }
    if fields(issue)?
        .iter()
        .any(|(name, _)| name == "location" || name == "request")
    {
        return Err(invalid("候補usageの位置が不正"));
    }
    Ok(())
}
fn wire_field<'a>(node: &'a Json, name: &str) -> Checked<&'a Json> {
    match node {
        Json::Obj(fields) => fields
            .get(name)
            .ok_or_else(|| invalid(format!("再計算した{name}がない"))),
        _ => Err(invalid("再計算表示がobjectでない")),
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
            JValue::Num(s) => Json::Nat(s.parse().map_err(|_| invalid("再計算結果にないNat"))?),
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
                    .ok_or_else(|| invalid(format!("未定義または先行していないRef: {id}")))?;
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
            JValue::Null => return Err(invalid("nullは使えない")),
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
                    .ok_or_else(|| invalid("再計算Refがない"))?
                else {
                    return Err(invalid("再計算Refが文字列でない"));
                };
                let key = ids
                    .get(id)
                    .ok_or_else(|| invalid("再計算Refが先行していない"))?;
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
        return Err(invalid("nodeはobject"));
    };
    fields.remove("id");
    encoding(&node, control)
}
fn verify(document: &JNode, evaluation: &ObservedEvaluation, control: &mut Control) -> Checked<()> {
    control.checkpoint(Checkpoint::Reuse)?;
    let replay = evaluation.wire_controlled(control, Checkpoint::Reuse)?;
    let empty = BTreeMap::new();
    // 元byte列・全宣言・語彙・解決済み要求を現在の三表へ照合する。
    // 候補が別の入力/問いのものでも、通常評価は既に現在入力から実行済みである。
    let mut inputs = normalized_candidate(field(document, "inputs")?, &empty, control)?;
    let Json::Arr(identities) = &mut inputs else {
        return Err(invalid("inputsはarray"));
    };
    for identity in identities {
        control.checkpoint(Checkpoint::Reuse)?;
        let Json::Obj(fields) = identity else {
            return Err(invalid("InputIdentityはobject"));
        };
        let Some(Json::Str(id)) = fields.get("id") else {
            return Err(invalid("InputIdentity.idが必要"));
        };
        let expected = match id.as_str() {
            "law" => "inputs/law.law".to_owned(),
            "archmap" => "inputs/archmap.json".to_owned(),
            id => format!(
                "inputs/definitions/{}.json",
                id.strip_prefix("definition")
                    .ok_or_else(|| invalid("未知の入力id"))?
            ),
        };
        if fields.get("path") != Some(&Json::str(expected)) {
            return Err(invalid("入力copyの固定pathが不正"));
        }
        fields.remove("path");
    }
    if inputs != *wire_field(&replay, "inputs")? {
        return Err(invalid("現在の入力identityと一致しない"));
    }
    for name in ["declarations", "vocabularies", "requests", "status"] {
        let candidate = normalized_candidate(field(document, name)?, &empty, control)?;
        if candidate != *wire_field(&replay, name)? {
            return Err(invalid(format!("{name}を現在の検査済み結果へ照合できない")));
        }
    }
    let mut native_ids = BTreeMap::new();
    let mut verified = BTreeMap::new();
    let Json::Arr(nodes) = wire_field(&replay, "nodes")? else {
        return Err(invalid("再計算nodesがない"));
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
            return Err(invalid(format!("node.idはn{index}が必要")));
        }
        let content = node_content(
            normalized_candidate(node, &candidate_ids, control)?,
            control,
        )?;
        let key = verified.get(&content).ok_or_else(|| {
            invalid(format!(
                "nodes[{index}]の型・payload・由来・条件・証拠を現在の導出へ照合できない"
            ))
        })?;
        candidate_ids.insert(id.to_owned(), key.clone());
    }
    // node番号・順序・共有を意味にしない。各Refを検査済みの導出内容へ正規化する。
    // digest一致で済ませず、payload・型・全依存・元位置を含むcanonical全文を照合する。
    let answers = normalized_candidate(field(document, "answers")?, &candidate_ids, control)?;
    if answers != normalized_wire(wire_field(&replay, "answers")?, &native_ids, control)? {
        return Err(invalid("回答を現在の検査済み導出へ照合できない"));
    }
    let issues = normalized_candidate(field(document, "issues")?, &candidate_ids, control)?;
    if issues != normalized_wire(wire_field(&replay, "issues")?, &native_ids, control)? {
        return Err(invalid("issuesを現在の検査済み導出へ照合できない"));
    }
    let code = match evaluation.status() {
        "partial" => 2,
        "complete" => u64::from(
            evaluation
                .answers
                .iter()
                .any(|a| a.status == crate::observed::result::Decision::Refuted),
        ),
        _ => return Err(invalid("確定していない候補照合")),
    };
    if field(document, "exit_code")?.value != JValue::Num(code.to_string()) {
        return Err(invalid("exit_codeを計算結果へ照合できない"));
    }
    control.checkpoint(Checkpoint::Reuse)?;
    Ok(())
}
