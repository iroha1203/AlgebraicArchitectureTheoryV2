//! 検査済み ArchMap のデータ型。原始値・欠測・参照・由来を保持する。

use super::value::Value;
use crate::definition::model::Binding;
use crate::issue::Issue;
use crate::types::Type;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Observed,
    Proposed,
    Specification,
}

impl Mode {
    pub fn wire(self) -> &'static str {
        match self {
            Mode::Observed => "observed",
            Mode::Proposed => "proposed",
            Mode::Specification => "specification",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    pub id: String,
    pub uri: String,
    pub revision: String,
    pub digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLocation {
    pub source: String,
    pub path: String,
    pub span: Option<(u64, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    pub id: String,
    pub mode: Mode,
    pub method: String,
    pub locations: Vec<SourceLocation>,
    pub note: Option<String>,
}

/// subject の一つの field の slot。Atom がなければ欠測で、identity と型を保持する。
#[derive(Debug, PartialEq)]
pub enum Slot {
    Known {
        atom: String,
        origin: String,
        value: Value,
        pointer: String,
    },
    Missing,
}

#[derive(Debug, PartialEq)]
pub struct Field {
    /// field の完全名。
    pub name: String,
    pub ty: Type,
    pub slot: Slot,
}

#[derive(Debug, PartialEq)]
pub struct Subject {
    pub snapshot: String,
    pub id: String,
    /// 宣言の完全名。
    pub ty: String,
    pub origin: String,
    /// 宣言順(括弧内、body の順)の全 field。
    pub fields: Vec<Field>,
    pub pointer: String,
}

#[derive(Debug, PartialEq)]
pub struct Snapshot {
    pub id: String,
    pub origin: String,
    pub subjects: Vec<Subject>,
}

/// 検査を通った ArchMap。
#[derive(Debug)]
pub struct CheckedArchMap {
    pub bytes_digest: String,
    pub model_digest: String,
    pub vocabularies: BTreeMap<String, Binding>,
    pub sources: Vec<Source>,
    pub origins: Vec<Origin>,
    pub snapshots: Vec<Snapshot>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchMapFailure {
    pub issue: Issue,
    pub bytes_digest: String,
}
