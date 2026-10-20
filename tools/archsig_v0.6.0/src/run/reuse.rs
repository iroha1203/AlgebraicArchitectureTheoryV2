//! 再利用候補の構造検査。推論を採用せず、現在の三入力から常に全再計算する。

use crate::canonical::Json;
use crate::json::{JNode, JValue};
use crate::observed::control::{CheckFailure, Checkpoint, Control, StopReason};
use crate::result::ResultIssue;
use num_integer::Integer;
use std::collections::BTreeSet;
use std::io::Read;
use std::path::Path;

/// 候補はヒントなので、不正でも現在入力の評価を続ける。停止は同じControlへ伝播する。
pub(super) fn inspect(path: Option<&Path>, control: &mut Control) -> Result<Vec<Json>, StopReason> {
    let Some(path) = path else {
        return Ok(Vec::new());
    };
    control.checkpoint(Checkpoint::Reuse)?;
    let reject = |message: String| {
        vec![
            ResultIssue::Usage {
                argument: "--reuse".into(),
                message: format!("再利用候補 {}: {message}", path.display()),
            }
            .wire(),
        ]
    };
    let read = || -> std::io::Result<Vec<u8>> {
        use rustix::fs::{Mode, OFlags, openat};
        // directoryのhandleを固定し、metadata確認後のsymlink差替えも辿らない。
        let directory = openat(
            rustix::fs::CWD,
            path,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW,
            Mode::empty(),
        )?;
        let input = openat(
            &directory,
            "result.json",
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK,
            Mode::empty(),
        )?;
        let mut input = std::fs::File::from(input);
        if !input.metadata()?.is_file() {
            return Err(std::io::Error::other("result.jsonは通常ファイルではない"));
        }
        let mut bytes = Vec::new();
        input.read_to_end(&mut bytes)?;
        Ok(bytes)
    };
    let bytes = read();
    control.checkpoint(Checkpoint::Reuse)?;
    let bytes = match bytes {
        Ok(bytes) => bytes,
        Err(error) => return Ok(reject(format!("result.jsonを読めない: {error}"))),
    };
    let candidate = match crate::json::parse_inner::<CheckFailure<Box<crate::issue::Issue>>>(
        &bytes,
        control,
        Checkpoint::Reuse,
    ) {
        Ok(candidate) => candidate,
        Err(CheckFailure::Stopped(reason)) => return Err(reason),
        Err(CheckFailure::Input(issue)) => {
            return Ok(reject(format!("JSONが不正: {}", issue.message)));
        }
    };
    let result = validate(&candidate, control);
    control.checkpoint(Checkpoint::Reuse)?;
    match result {
        Ok(()) => Ok(Vec::new()),
        Err(Failure::Rejected(message)) => Ok(reject(message)),
        Err(Failure::Stopped(reason)) => Err(reason),
    }
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
fn object(node: &JNode) -> Checked<&[(String, JNode)]> {
    match &node.value {
        JValue::Obj(fields) => Ok(fields),
        _ => Err(invalid("objectが必要")),
    }
}
fn field<'a>(node: &'a JNode, name: &str) -> Checked<&'a JNode> {
    object(node)?
        .iter()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value)
        .ok_or_else(|| invalid(format!("{name}が必要")))
}
fn text(node: &JNode) -> Checked<&str> {
    match &node.value {
        JValue::Str(value) => Ok(value),
        _ => Err(invalid("文字列が必要")),
    }
}
fn array(node: &JNode) -> Checked<&[JNode]> {
    match &node.value {
        JValue::Arr(values) => Ok(values),
        _ => Err(invalid("arrayが必要")),
    }
}
fn record(node: &JNode, required: &[&str], optional: &[&str]) -> Checked<()> {
    for name in required {
        field(node, name)?;
    }
    for (name, _) in object(node)? {
        if !required.contains(&name.as_str()) && !optional.contains(&name.as_str()) {
            return Err(invalid(format!("未知の欄: {name}")));
        }
    }
    Ok(())
}

fn validate(candidate: &JNode, control: &mut Control) -> Checked<()> {
    // 未知版の新しい欄を先にschemaエラーとしない。
    if text(field(candidate, "format")?)? != "archsig.result/2"
        || text(field(candidate, "semantics")?)? != crate::law::SEMANTICS
    {
        return Err(invalid("format/semanticsが対応版と異なる"));
    }
    record(
        candidate,
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
    for name in [
        "inputs",
        "declarations",
        "vocabularies",
        "requests",
        "answers",
        "issues",
    ] {
        array(field(candidate, name)?)?;
    }
    for (name, allowed) in [
        ("command", &["check", "run"][..]),
        (
            "status",
            &[
                "complete",
                "partial",
                "invalid",
                "unsupported",
                "interrupted",
                "error",
            ][..],
        ),
    ] {
        if !allowed.contains(&text(field(candidate, name)?)?) {
            return Err(invalid(format!("{name}が不正")));
        }
    }
    record(field(candidate, "producer")?, &["version", "build"], &[])?;
    for name in ["version", "build"] {
        text(field(field(candidate, "producer")?, name)?)?;
    }
    record(
        field(candidate, "reuse")?,
        &[
            "requested",
            "accepted_nodes",
            "recomputed_nodes",
            "rejected",
        ],
        &[],
    )?;
    if !matches!(
        field(field(candidate, "reuse")?, "requested")?.value,
        JValue::Bool(_)
    ) {
        return Err(invalid("reuse.requestedはBool"));
    }
    array(field(field(candidate, "reuse")?, "rejected")?)?;
    record(
        field(candidate, "usage")?,
        &["elapsed_ms", "peak_bytes"],
        &[],
    )?;
    record(field(candidate, "limits")?, &[], &["time_ms", "memory_mib"])?;
    for group in ["usage", "limits"] {
        for (_, value) in object(field(candidate, group)?)? {
            let value = text(value)?;
            if value.is_empty()
                || !value.bytes().all(|b| b.is_ascii_digit())
                || (value.len() > 1 && value.starts_with('0'))
            {
                return Err(invalid(format!("{group}はDecimalNat")));
            }
        }
    }
    for value in [
        field(candidate, "exit_code")?,
        field(field(candidate, "reuse")?, "accepted_nodes")?,
        field(field(candidate, "reuse")?, "recomputed_nodes")?,
    ] {
        if !matches!(value.value, JValue::Num(_)) {
            return Err(invalid("exit_codeとnode数はNat"));
        }
    }
    let mut prior = BTreeSet::new();
    for (index, node) in array(field(candidate, "nodes")?)?.iter().enumerate() {
        control.checkpoint(Checkpoint::Reuse)?;
        record(
            node,
            &[
                "id",
                "type",
                "state",
                "rule",
                "arguments",
                "support",
                "conditions",
                "evidence",
                "scope",
                "reasons",
            ],
            &["value", "partial", "judgment"],
        )?;
        for name in ["arguments", "conditions", "evidence"] {
            for reference in array(field(node, name)?)? {
                record(reference, &["node"], &[])?;
                text(field(reference, "node")?)?;
            }
        }
        for name in ["support", "reasons"] {
            array(field(node, name)?)?;
        }
        object(field(node, "rule")?)?;
        object(field(node, "scope")?)?;
        let id = text(field(node, "id")?)?;
        if id.is_empty() || prior.contains(id) {
            return Err(invalid(format!("nodes[{index}]のidが空または重複: {id}")));
        }
        validate_type(field(node, "type")?, control)?;
        let state = text(field(node, "state")?)?;
        let value = object(node)?
            .iter()
            .find(|(name, _)| name == "value")
            .map(|(_, v)| v);
        match (state, value) {
            ("value", Some(value)) => scalar_shape(field(node, "type")?, value, control)?,
            ("blocked", None) => {}
            _ => return Err(invalid(format!("nodes[{index}]のstate/valueが不整合"))),
        }
        // payload内の入れ子も含め、参照は検査済みの先行nodeだけに限る。
        walk(node, &prior, control)?;
        prior.insert(id.to_owned());
    }
    let mut answer_ids = BTreeSet::new();
    for answer in array(field(candidate, "answers")?)? {
        control.checkpoint(Checkpoint::Reuse)?;
        record(
            answer,
            &["id", "status", "outputs", "evidence", "reasons", "scope"],
            &["claim"],
        )?;
        let id = text(field(answer, "id")?)?;
        if id.is_empty() || !answer_ids.insert(id) {
            return Err(invalid("回答idが空または重複"));
        }
        if !["established", "refuted", "undetermined"].contains(&text(field(answer, "status")?)?) {
            return Err(invalid("回答statusが不正"));
        }
        for (_, reference) in object(field(answer, "outputs")?)? {
            record(reference, &["node"], &[])?;
        }
        array(field(answer, "evidence")?)?;
        array(field(answer, "reasons")?)?;
        object(field(answer, "scope")?)?;
    }
    for (name, value) in object(candidate)? {
        if name != "nodes" {
            walk(value, &prior, control)?;
        }
    }
    Ok(())
}

fn walk(root: &JNode, prior: &BTreeSet<String>, control: &mut Control) -> Checked<()> {
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        control.checkpoint(Checkpoint::Reuse)?;
        match &node.value {
            JValue::Null => return Err(invalid("nullは使えない")),
            JValue::Num(number) if !number.bytes().all(|b| b.is_ascii_digit()) => {
                return Err(invalid("JSON numberはNatに限る"));
            }
            JValue::Obj(fields) if fields.iter().any(|(key, _)| key == "node") => {
                if fields.len() != 1 {
                    return Err(invalid("Refはnodeだけを持つ"));
                }
                let id = text(&fields[0].1)?;
                if !prior.contains(id) {
                    return Err(invalid(format!("未定義または先行していないRef: {id}")));
                }
            }
            JValue::Obj(fields) => pending.extend(fields.iter().map(|(_, value)| value)),
            JValue::Arr(values) => pending.extend(values),
            _ => {}
        }
    }
    Ok(())
}

fn validate_type(ty: &JNode, control: &mut Control) -> Checked<()> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(Checkpoint::Reuse)?;
        match &ty.value {
            JValue::Str(name)
                if [
                    "Unit",
                    "Bool",
                    "Z",
                    "Q",
                    "Text",
                    "Expression",
                    "Evaluation",
                    "LawInstance",
                    "Proposition",
                    "Evidence",
                    "Domain",
                ]
                .contains(&name.as_str()) =>
            {
                Ok(())
            }
            JValue::Arr(parts) => {
                let tag = parts.first().ok_or_else(|| invalid("空の型"))?;
                match (text(tag)?, parts.len()) {
                    ("Fp", 2) => {
                        let modulus = integer(&parts[1])?
                            .to_biguint()
                            .ok_or_else(|| invalid("Fpの法は正の素数"))?;
                        match crate::prime::is_prime_controlled::<
                            CheckFailure<Box<crate::issue::Issue>>,
                        >(&modulus, control, Checkpoint::Reuse)
                        {
                            Ok(true) => {}
                            Ok(false) => return Err(invalid("Fpの法は素数")),
                            Err(CheckFailure::Stopped(reason)) => {
                                return Err(Failure::Stopped(reason));
                            }
                            Err(CheckFailure::Input(issue)) => return Err(invalid(issue.message)),
                        }
                    }
                    ("Ref" | "Data", 2) => {
                        text(&parts[1])?;
                    }
                    ("Path", 3) => {
                        text(&parts[1])?;
                        text(&parts[2])?;
                    }
                    ("Tuple", _) => {
                        for part in &parts[1..] {
                            validate_type(part, control)?;
                        }
                    }
                    ("List" | "Set" | "Option", 2) => validate_type(&parts[1], control)?,
                    ("Map", 3) => {
                        validate_type(&parts[1], control)?;
                        validate_type(&parts[2], control)?;
                    }
                    ("Term", 3) => {
                        for part in array(&parts[1])? {
                            validate_type(part, control)?;
                        }
                        validate_type(&parts[2], control)?;
                    }
                    _ => return Err(invalid("型の構成が不正")),
                }
                Ok(())
            }
            _ => Err(invalid("未知または不正なnode型")),
        }
    })
}

fn integer(node: &JNode) -> Checked<num_bigint::BigInt> {
    let spelling = text(node)?;
    let value = spelling
        .parse::<num_bigint::BigInt>()
        .map_err(|_| invalid("整数の綴りが不正"))?;
    if value.to_string() != spelling {
        return Err(invalid("整数は正規化した十進表記"));
    }
    Ok(value)
}

/// 候補の値の形だけを検査する。証拠の意味検査・推論採用は行わない。
fn scalar_shape(ty: &JNode, value: &JNode, control: &mut Control) -> Checked<()> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.checkpoint(Checkpoint::Reuse)?;
        let valid = match &ty.value {
            JValue::Str(name) => match name.as_str() {
                "Bool" => matches!(value.value, JValue::Bool(_)),
                "Z" => integer(value).is_ok(),
                "Text" => matches!(value.value, JValue::Str(_)),
                "Unit" => array(value)?.is_empty(),
                "Q" => {
                    let parts = array(value)?;
                    if parts.len() != 2 {
                        false
                    } else {
                        let n = integer(&parts[0])?;
                        let d = integer(&parts[1])?;
                        d > 0.into() && n.gcd(&d) == 1.into()
                    }
                }
                _ => matches!(value.value, JValue::Obj(_)),
            },
            JValue::Arr(parts) => match text(&parts[0])? {
                "Tuple" => {
                    let values = array(value)?;
                    if values.len() != parts.len() - 1 {
                        false
                    } else {
                        for (ty, value) in parts[1..].iter().zip(values) {
                            scalar_shape(ty, value, control)?;
                        }
                        true
                    }
                }
                "List" | "Set" => {
                    for value in array(value)? {
                        scalar_shape(&parts[1], value, control)?;
                    }
                    true
                }
                "Ref" => {
                    let values = array(value)?;
                    values.len() == 2 && values.iter().all(|v| text(v).is_ok())
                }
                "Fp" => {
                    let n = integer(value)?;
                    n >= 0.into() && n < integer(&parts[1])?
                }
                "Map" => {
                    for pair in array(value)? {
                        let pair = array(pair)?;
                        if pair.len() != 2 {
                            return Err(invalid("Mapのpairが不正"));
                        }
                        scalar_shape(&parts[1], &pair[0], control)?;
                        scalar_shape(&parts[2], &pair[1], control)?;
                    }
                    true
                }
                "Option" => {
                    let fields = object(value)?;
                    if fields.len() != 1 {
                        false
                    } else {
                        match fields[0].0.as_str() {
                            "none" => matches!(fields[0].1.value, JValue::Bool(true)),
                            "some" => {
                                scalar_shape(&parts[1], &fields[0].1, control)?;
                                true
                            }
                            _ => false,
                        }
                    }
                }
                _ => matches!(value.value, JValue::Obj(_)),
            },
            _ => false,
        };
        if valid {
            Ok(())
        } else {
            Err(invalid("node型とpayloadの形が一致しない"))
        }
    })
}
