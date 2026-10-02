use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// 第3章の Atom。JSON の一行に当たる。
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq)]
pub struct Atom {
    pub kind: String,
    pub subject: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub object: Option<String>,
    /// `writes` の書き込み先までにたどるフィールドの列。場所は `[via…, object]`(設計 §3.5)。
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub via: Option<Vec<String>>,
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

/// `at` を分けたもの。`パス:行@版`。
#[derive(Clone, Debug, PartialEq)]
pub struct Location {
    pub path: String,
    /// 行。`10` か `10-14`。
    pub lines: Option<String>,
    pub version: Option<String>,
}

impl Location {
    pub fn to_at(&self) -> String {
        let mut at = self.path.clone();
        if let Some(l) = &self.lines {
            at.push(':');
            at.push_str(l);
        }
        if let Some(v) = &self.version {
            at.push('@');
            at.push_str(v);
        }
        at
    }
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
}

pub fn parse_location(at: &str) -> Option<Location> {
    let (loc, version) = match at.rsplit_once('@') {
        Some((l, v)) if is_version(v) => (l, Some(v.to_string())),
        _ => (at, None),
    };
    let (path, lines) = match loc.rsplit_once(':') {
        Some((p, l)) if !l.is_empty() && l.chars().all(|c| c.is_ascii_digit() || c == '-') => (p.to_string(), Some(l.to_string())),
        _ => (loc.to_string(), None),
    };
    Some(Location { path, lines, version })
}

/// 版は `blob:<hex>` か `<hex>`(7文字以上)。パスの中の `@` と区別する。
fn is_version(v: &str) -> bool {
    let hex = v.strip_prefix("blob:").unwrap_or(v);
    hex.len() >= 7 && hex.chars().all(|c| c.is_ascii_hexdigit())
}

pub fn parse_jsonl(text: &str, origin: &str) -> Result<Vec<Atom>, String> {
    let mut atoms = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let atom: Atom = serde_json::from_str(line).map_err(|e| format!("{origin}:{}: {e}", i + 1))?;
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
