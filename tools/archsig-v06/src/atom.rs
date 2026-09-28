use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// 第3章の Atom。JSON の一行に当たる。
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq)]
pub struct Atom {
    pub kind: String,
    pub subject: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub object: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub when: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub meaning: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub params: Option<BTreeMap<String, String>>,
    #[serde(rename = "type", default, skip_serializing_if = "Option::is_none")]
    pub ty: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub uses: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub by: Option<String>,
}

pub const STRUCTURE_KINDS: &[&str] = &[
    "defines", "calls", "reads", "writes", "passes", "sends", "receives", "returns", "imports", "resolves",
];
const OTHER_KINDS: &[&str] = &["meaning", "observed", "plan", "corresponds", "removes"];

/// `at` を分けたもの。`パス:行@版` または `plan:<名前>`。
#[derive(Clone, Debug, PartialEq)]
pub struct Location {
    pub path: String,
    pub line: Option<u32>,
    pub version: Option<String>,
}

impl Atom {
    pub fn is_structure(&self) -> bool {
        STRUCTURE_KINDS.contains(&self.kind.as_str())
    }

    /// 観測の範囲。構造 Atom は `structure`、意味 Atom は `meaning:<名前>`。
    pub fn scope_name(&self) -> Option<String> {
        if self.is_structure() {
            Some("structure".to_string())
        } else if self.kind == "meaning" {
            self.meaning.as_ref().map(|m| format!("meaning:{m}"))
        } else if self.kind == "observed" {
            self.scope.clone()
        } else {
            None
        }
    }

    pub fn location(&self) -> Option<Location> {
        self.at.as_deref().and_then(parse_location)
    }

    pub fn validate(&self) -> Result<(), String> {
        if !STRUCTURE_KINDS.contains(&self.kind.as_str()) && !OTHER_KINDS.contains(&self.kind.as_str()) {
            return Err(format!("未知の kind `{}`", self.kind));
        }
        if self.subject.is_empty() {
            return Err("subject がない".to_string());
        }
        let need_object = matches!(
            self.kind.as_str(),
            "calls" | "reads" | "imports" | "resolves" | "writes" | "passes" | "sends" | "receives" | "corresponds"
        );
        if need_object && self.object.is_none() {
            return Err(format!("{} に object がない: {}", self.kind, self.subject));
        }
        let need_value = matches!(self.kind.as_str(), "defines" | "writes" | "passes" | "sends" | "receives" | "returns");
        if need_value && self.value.is_none() {
            return Err(format!("{} に value がない: {}", self.kind, self.subject));
        }
        if self.kind == "meaning" && self.meaning.is_none() {
            return Err(format!("meaning に meaning がない: {}", self.subject));
        }
        if self.kind == "observed" && self.scope.is_none() {
            return Err(format!("observed に scope がない: {}", self.subject));
        }
        Ok(())
    }
}

pub fn parse_location(at: &str) -> Option<Location> {
    if let Some(rest) = at.strip_prefix("plan:") {
        return Some(Location { path: format!("plan:{rest}"), line: None, version: None });
    }
    let (loc, version) = match at.rsplit_once('@') {
        Some((l, v)) => (l, Some(v.to_string())),
        None => (at, None),
    };
    let (path, line) = match loc.rsplit_once(':') {
        Some((p, l)) if !l.is_empty() && l.chars().all(|c| c.is_ascii_digit() || c == '-') => {
            let start = l.split('-').next().and_then(|s| s.parse().ok());
            (p.to_string(), start)
        }
        _ => (loc.to_string(), None),
    };
    Some(Location { path, line, version })
}

pub fn parse_jsonl(text: &str, origin: &str) -> Result<Vec<Atom>, String> {
    let mut atoms = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let atom: Atom = serde_json::from_str(line).map_err(|e| format!("{origin}:{}: {e}", i + 1))?;
        atom.validate().map_err(|e| format!("{origin}:{}: {e}", i + 1))?;
        atoms.push(atom);
    }
    Ok(atoms)
}

pub fn to_jsonl(atoms: &[Atom]) -> String {
    let mut out = String::new();
    for a in atoms {
        out.push_str(&serde_json::to_string(a).expect("Atom は JSON にできる"));
        out.push('\n');
    }
    out
}
