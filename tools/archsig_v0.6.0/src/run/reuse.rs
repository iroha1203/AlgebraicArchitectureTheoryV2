//! 候補を現在の検査済み導出へ照合し、推論は採用せず全再計算する。
use archsig_common::canonical::Json;
use archsig_common::control::{CheckFailure, Checkpoint, Control};
use archsig_common::json::{JNode, JValue, Span};
use archsig_computation::observed::{DeliveryEvaluation, PreparedObserved};
use archsig_input::result::ResultIssue;
use archsig_input::result::Signal;
use std::{
    collections::{BTreeMap, BTreeSet},
    io::Read,
    path::{Path, PathBuf},
};

pub(super) struct Candidate {
    path: PathBuf,
    pending: Option<Comparison>,
    rejected: Vec<Json>,
}
struct Comparison {
    bytes: Vec<u8>,
    nodes: Option<Vec<Span>>,
    status: JNode,
    exit_code: JNode,
    answers: JNode,
    issues: JNode,
}

/// 照合通知と、現在入力から生成済みの保存表示。
#[derive(Default)]
pub(super) struct Verification {
    pub rejected: Vec<Json>,
    pub stop: Option<Signal>,
    pub replay: Option<Json>,
}
impl Candidate {
    fn reject(&mut self, mut message: String) {
        // JSON keys and reference IDs can appear in diagnostics. Keep the
        // reason and a short excerpt even for an arbitrarily large old key.
        const MAX_REASON_BYTES: usize = 1024;
        if message.len() > MAX_REASON_BYTES {
            message.truncate(message.floor_char_boundary(MAX_REASON_BYTES));
            message.push('…');
        }
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
        evaluation: &DeliveryEvaluation,
        control: &Control,
    ) -> Verification {
        let mut replay = None;
        let mut stop = None;
        if matches!(evaluation.status(), "complete" | "partial")
            && let Some(candidate) = self.pending.take()
        {
            let checked = (|| {
                control.checkpoint(Checkpoint::Reuse)?;
                let current = evaluation.result_wire_controlled(control, Checkpoint::Reuse)?;
                let result = verify(candidate, &current, evaluation, control);
                replay = Some(current);
                result
            })();
            match checked {
                Ok(()) => {}
                Err(Failure::Rejected(message)) => self.reject(message),
                Err(Failure::Stopped(reason)) => stop = Some(reason),
            }
        }
        Verification {
            rejected: self.rejected,
            stop,
            replay,
        }
    }
}
pub(super) fn inspect(
    path: Option<&Path>,
    prepared: &PreparedObserved,
    control: &Control,
) -> Result<Candidate, Signal> {
    let mut candidate = Candidate {
        path: path.unwrap_or_else(|| Path::new("")).to_owned(),
        pending: None,
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
    let mut bytes = match read {
        Ok(bytes) => bytes,
        Err(error) => {
            candidate.reject(format!("cannot read result.json: {error}"));
            return Ok(candidate);
        }
    };
    let (mut document, mut nodes) = match archsig_common::json::parse_deferred_root_array::<
        CheckFailure<Box<archsig_common::issue::Issue>>,
    >(&bytes, "nodes", control, Checkpoint::Reuse)
    {
        Ok(parsed) => parsed,
        Err(CheckFailure::Stopped(reason)) => return Err(reason),
        Err(CheckFailure::Input(issue)) => {
            candidate.reject(format!("invalid JSON: {}", issue.message));
            return Ok(candidate);
        }
    };
    match header(&document, control) {
        Ok(()) => {}
        Err(Failure::Rejected(message)) => {
            candidate.reject(message);
            return Ok(candidate);
        }
        Err(Failure::Stopped(reason)) => return Err(reason),
    }
    match preflight(&document, prepared, control) {
        Ok(()) => {
            retain_node_bytes(
                &mut bytes,
                nodes.as_deref_mut().unwrap_or_default(),
                control,
            )?;
            let JValue::Obj(fields) = &mut document.value else {
                unreachable!("checked reuse header")
            };
            let mut take = |name: &str| {
                let (_, node) = fields
                    .iter_mut()
                    .find(|(key, _)| key == name)
                    .expect("required reuse field");
                std::mem::replace(
                    node,
                    JNode {
                        value: JValue::Null,
                    },
                )
            };
            candidate.pending = Some(Comparison {
                bytes,
                nodes,
                status: take("status"),
                exit_code: take("exit_code"),
                answers: take("answers"),
                issues: take("issues"),
            });
        }
        Err(Failure::Rejected(message)) => candidate.reject(message),
        Err(Failure::Stopped(reason)) => return Err(reason),
    }
    Ok(candidate)
}
/// Keep exactly the serialized entries to be compared. Compact forward so
/// inspected headers and insignificant whitespace do not span evaluation.
fn retain_node_bytes(
    bytes: &mut Vec<u8>,
    nodes: &mut [Span],
    control: &Control,
) -> Result<(), Signal> {
    const COPY_BLOCK_BYTES: usize = 16 * 1024;
    let mut retained = 0;
    for (start, end) in nodes {
        let output_start = retained;
        let mut quoted = false;
        let mut escaped = false;
        for block in (*start..*end).step_by(COPY_BLOCK_BYTES) {
            control.checkpoint(Checkpoint::Reuse)?;
            for read in block..(block + COPY_BLOCK_BYTES).min(*end) {
                let byte = bytes[read];
                if quoted || !matches!(byte, b' ' | b'\t' | b'\n' | b'\r') {
                    bytes[retained] = byte;
                    retained += 1;
                }
                if escaped {
                    escaped = false;
                } else if quoted && byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    quoted = !quoted;
                }
            }
        }
        *start = output_start;
        *end = retained;
    }
    bytes.truncate(retained);
    bytes.shrink_to_fit();
    control.checkpoint(Checkpoint::Reuse)
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
        JValue::Num(s) if archsig_input::archmap::nat_value(s).is_some() => Ok(()),
        _ => Err(invalid("Nat must be an integer in 0..9007199254740991")),
    }
}
fn header(document: &JNode, control: &Control) -> Checked<()> {
    control.checkpoint(Checkpoint::Reuse)?;
    if text(field(document, "format")?)? != archsig_input::result::RESULT_FORMAT
        || text(field(document, "semantics")?)? != archsig_input::law::SEMANTICS
    {
        return Err(invalid(
            "format/semantics does not match the supported version",
        ));
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
        for issue in array(warnings)? {
            issue_shape(issue, control)?;
        }
    }
    Ok(())
}
fn issue_shape(issue: &JNode, control: &Control) -> Checked<()> {
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
        return Err(invalid(
            "cannot verify the candidate's previous rejection notice",
        ));
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
    control: &Control,
) -> Checked<Json> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(Checkpoint::Reuse)?;
        Ok(match &node.value {
            JValue::Bool(b) => Json::Bool(*b),
            JValue::Num(s) => {
                Json::Nat(archsig_input::archmap::nat_value(s).ok_or_else(|| {
                    invalid("value is outside the Nat range or is not an integer")
                })?)
            }
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
    control: &Control,
) -> Checked<Json> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(Checkpoint::Reuse)?;
        Ok(match node {
            Json::Bool(b) => Json::Bool(*b),
            Json::Nat(n) => Json::Nat(*n),
            Json::Str(s) => Json::str(s),
            Json::NodeReferences(items) => {
                let mut normalized = Vec::with_capacity(items.len());
                for index in items {
                    control.checkpoint(Checkpoint::Reuse)?;
                    let id = format!("n{index}");
                    let key = ids
                        .get(&id)
                        .ok_or_else(|| invalid("recomputed Ref does not precede its use"))?;
                    // Normalized refs contain canonical keys, not numeric node ids.
                    normalized.push(Json::obj([("node", Json::str(key))]));
                }
                Json::Arr(normalized)
            }
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
fn encoding(json: &Json, control: &Control) -> Checked<String> {
    match json.canonical_controlled::<CheckFailure<Box<archsig_common::issue::Issue>>>(
        control,
        Checkpoint::Reuse,
    ) {
        Ok(s) => Ok(s),
        Err(CheckFailure::Stopped(reason)) => Err(Failure::Stopped(reason)),
        Err(CheckFailure::Input(issue)) => Err(invalid(issue.message)),
    }
}
fn node_content(mut node: Json, control: &Control) -> Checked<String> {
    let Json::Obj(fields) = &mut node else {
        return Err(invalid("node must be an object"));
    };
    fields.remove("id");
    if matches!(fields.get("type"), Some(Json::Str(ty)) if ty == "ObservationPlan") {
        let Some(Json::Obj(plan)) = fields.get_mut("value") else {
            return Err(invalid("ObservationPlan.value must be an object"));
        };
        let Some(Json::Arr(requirements)) = plan.get_mut("requirements") else {
            return Err(invalid("ObservationPlan.requirements must be an array"));
        };
        for requirement in requirements {
            control.checkpoint(Checkpoint::Reuse)?;
            let Json::Obj(requirement) = requirement else {
                return Err(invalid("ObservationPlan requirement must be an object"));
            };
            let Some(Json::Arr(dependents)) = requirement.get_mut("dependents") else {
                return Err(invalid("ObservationPlan.dependents must be an array"));
            };
            // 参照は既に検査した導出のキーに解決済み。旧表示の重複だけをまとめる。
            let mut seen = BTreeSet::new();
            for dependent in std::mem::take(dependents) {
                control.checkpoint(Checkpoint::Reuse)?;
                let Json::Str(key) = wire_field(&dependent, "node")? else {
                    return Err(invalid("ObservationPlan dependent must be a Ref"));
                };
                if seen.insert(key.clone()) {
                    dependents.push(dependent);
                }
            }
        }
    }
    encoding(&node, control)
}
fn preflight(document: &JNode, prepared: &PreparedObserved, control: &Control) -> Checked<()> {
    let empty = BTreeMap::new();
    // 元byte列のidentityと解決済み要求を照合する。宣言・型は現在の三入力から再検査する。
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
    if inputs != archsig_input::result::input_identities_wire(prepared.inputs().inputs()) {
        return Err(invalid("current input identity does not match"));
    }
    let requests = prepared
        .requests()
        .requests()
        .iter()
        .map(|request| {
            control.checkpoint(Checkpoint::Reuse)?;
            Ok(request.wire())
        })
        .collect::<Checked<Vec<_>>>()?;
    if normalized_candidate(field(document, "requests")?, &empty, control)? != Json::Arr(requests) {
        return Err(invalid(
            "cannot verify requests against the current checked result",
        ));
    }
    Ok(())
}

fn verify(
    candidate: Comparison,
    replay: &Json,
    evaluation: &DeliveryEvaluation,
    control: &Control,
) -> Checked<()> {
    let empty = BTreeMap::new();
    if normalized_candidate(&candidate.status, &empty, control)? != *wire_field(replay, "status")? {
        return Err(invalid(
            "cannot verify status against the current checked result",
        ));
    }
    let Comparison {
        bytes,
        nodes: candidate_nodes,
        answers,
        issues,
        exit_code,
        ..
    } = candidate;
    let mut native_ids = BTreeMap::new();
    let mut verified = BTreeMap::new();
    let Json::Arr(nodes) = wire_field(replay, "nodes")? else {
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
    for (index, (start, end)) in candidate_nodes
        .ok_or_else(|| invalid("expected an array"))?
        .into_iter()
        .enumerate()
    {
        control.checkpoint(Checkpoint::Reuse)?;
        let node = archsig_common::json::parse_inner::<
            CheckFailure<Box<archsig_common::issue::Issue>>,
        >(&bytes[start..end], control, Checkpoint::Reuse)
        .map_err(|error| match error {
            CheckFailure::Stopped(reason) => Failure::Stopped(reason),
            CheckFailure::Input(issue) => invalid(format!("invalid JSON: {}", issue.message)),
        })?;
        let id = text(field(&node, "id")?)?;
        if id != format!("n{index}") {
            return Err(invalid(format!("node.id must be n{index}")));
        }
        let content = node_content(
            normalized_candidate(&node, &candidate_ids, control)?,
            control,
        )?;
        let key = verified.get(&content).ok_or_else(|| {
            invalid(format!(
                "cannot verify nodes[{index}] type, payload, provenance, conditions, or evidence against the current derivation"
            ))
        })?;
        candidate_ids.insert(id.to_owned(), key.clone());
    }
    drop(bytes);
    // node番号・順序・共有を意味にしない。各Refを検査済みの導出内容へ正規化する。
    // digest一致で済ませず、payload・型・全依存・元位置を含むcanonical全文を照合する。
    let answers = normalized_candidate(&answers, &candidate_ids, control)?;
    if answers != normalized_wire(wire_field(replay, "answers")?, &native_ids, control)? {
        return Err(invalid(
            "cannot verify answers against the current checked derivation",
        ));
    }
    let issues = normalized_candidate(&issues, &candidate_ids, control)?;
    if issues != normalized_wire(wire_field(replay, "issues")?, &native_ids, control)? {
        return Err(invalid(
            "cannot verify issues against the current checked derivation",
        ));
    }
    let code = match evaluation.status() {
        "partial" => 2,
        "complete" => u64::from(evaluation.has_refuted_answer()),
        _ => return Err(invalid("candidate verification is not finalized")),
    };
    if normalized_candidate(&exit_code, &empty, control)? != Json::Nat(code) {
        return Err(invalid(
            "cannot verify exit_code against the computation result",
        ));
    }
    control.checkpoint(Checkpoint::Reuse)?;
    Ok(())
}

#[cfg(test)]
mod reference_array_tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};
    #[test]
    fn candidate_keeps_only_entry_bytes_and_rebases_each_range() {
        let mut bytes = br#"  {"nodes": [ true, {"x":[1,2]} ],"other":[0]} "#.to_vec();
        let control = Control::unlimited();
        let (_, spans) = archsig_common::json::parse_deferred_root_array::<
            Box<archsig_common::issue::Issue>,
        >(&bytes, "nodes", &control, Checkpoint::Reuse)
        .unwrap();
        let mut spans = spans.unwrap();
        retain_node_bytes(&mut bytes, &mut spans, &control).unwrap();
        assert_eq!(bytes, br#"true{"x":[1,2]}"#);
        assert_eq!(spans, [(0, 4), (4, 15)]);
        retain_node_bytes(&mut bytes, &mut [], &control).unwrap();
        assert!(bytes.is_empty());
    }

    #[test]
    fn whitespace_inside_each_node_is_elided_only_outside_json_strings() {
        let mut raw = br#"{"nodes":[{ "#.to_vec();
        raw.extend(std::iter::repeat_n(b' ', 40_000));
        raw.extend_from_slice(br#""text" : [ "keep space \t", "a\" b", "\\", " c " ] }]}"#);
        let control = Control::unlimited();
        let (_, spans) = archsig_common::json::parse_deferred_root_array::<
            Box<archsig_common::issue::Issue>,
        >(&raw, "nodes", &control, Checkpoint::Reuse)
        .unwrap();
        let mut spans = spans.unwrap();
        let original = archsig_common::json::parse(&raw[spans[0].0..spans[0].1]).unwrap();
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let stop = Control::new(move |_| {
            seen.set(seen.get() + 1);
            (seen.get() == 2).then_some(Signal::Term)
        });
        assert!(matches!(
            retain_node_bytes(&mut raw.clone(), &mut spans.clone(), &stop),
            Err(Signal::Term)
        ));
        retain_node_bytes(&mut raw, &mut spans, &control).unwrap();
        assert_eq!(raw, br#"{"text":["keep space \t","a\" b","\\"," c "]}"#);
        assert_eq!(spans, [(0, raw.len())]);
        assert_eq!(archsig_common::json::parse(&raw).unwrap(), original);
    }

    #[test]
    fn compact_refs_reuse_the_same_canonical_keys_and_reject_nonprior_ids() {
        let ids = BTreeMap::from([("n1".into(), "v0".into()), ("n2".into(), "v1".into())]);
        let compact = Json::NodeReferences(vec![2, 1, 2]);
        let candidate =
            archsig_common::json::parse(br#"[{"node":"n2"},{"node":"n1"},{"node":"n2"}]"#)
                .unwrap_or_else(|_| panic!("reference normalization failed"));
        let expected = normalized_candidate(&candidate, &ids, &Control::unlimited())
            .unwrap_or_else(|_| panic!("reference normalization failed"));
        assert_eq!(
            normalized_wire(&compact, &ids, &Control::unlimited())
                .unwrap_or_else(|_| panic!("reference normalization failed")),
            expected
        );
        assert_eq!(
            expected.canonical(),
            r#"[{"node":"v1"},{"node":"v0"},{"node":"v1"}]"#
        );
        assert!(
            normalized_wire(&Json::NodeReferences(vec![3]), &ids, &Control::unlimited()).is_err()
        );
        for bad in [
            br#"[{"node":"n01"}]"#.as_slice(),
            br#"[{"node":"n1","extra":true}]"#.as_slice(),
        ] {
            let candidate = archsig_common::json::parse(bad)
                .unwrap_or_else(|_| panic!("reference normalization failed"));
            assert!(normalized_candidate(&candidate, &ids, &Control::unlimited()).is_err());
        }
        let calls = Rc::new(Cell::new(0));
        let seen = calls.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        });
        normalized_wire(&compact, &ids, &control)
            .unwrap_or_else(|_| panic!("reference normalization failed"));
        for at in 1..=calls.get() {
            let mut visits = 0;
            let control = Control::new(move |_| {
                visits += 1;
                (visits == at).then_some(Signal::Int)
            });
            assert!(matches!(
                normalized_wire(&compact, &ids, &control),
                Err(Failure::Stopped(Signal::Int))
            ));
        }
    }
}
