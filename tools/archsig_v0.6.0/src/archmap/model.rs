//! 検査済み ArchMap のデータ型。原始値・欠測・参照・由来を保持する。

use super::value::Value;
use crate::canonical::Json;
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
/// 原始観測の位置。fieldだけを持つものはslot、atomも持つものは既知のfield Atom。
pub struct Fact {
    pub snapshot: String,
    pub subject: String,
    pub field: Option<String>,
    pub atom: Option<String>,
}
impl Fact {
    pub(crate) fn wire(&self) -> Json {
        let mut f = BTreeMap::from([
            ("snapshot".into(), Json::str(&self.snapshot)),
            ("subject".into(), Json::str(&self.subject)),
        ]);
        if let Some(s) = &self.field {
            f.insert("field".into(), Json::str(s));
        }
        if let Some(s) = &self.atom {
            f.insert("atom".into(), Json::str(s));
        }
        Json::Obj(f)
    }
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

/// 検査を通った ArchMap。`check_archmap` / controlled版で構築し、共有参照で読み取る。
///
/// ```compile_fail,E0616
/// fn alter(map: &mut archsig::archmap::CheckedArchMap) { map.bytes_digest.clear(); }
/// ```
/// ```compile_fail,E0616
/// fn alter(map: &mut archsig::archmap::CheckedArchMap) { map.model_digest.clear(); }
/// ```
/// ```compile_fail,E0596
/// fn alter(map: &mut archsig::archmap::CheckedArchMap) { map.vocabularies().clear(); }
/// ```
/// ```compile_fail,E0596
/// fn alter(map: &mut archsig::archmap::CheckedArchMap) { map.sources().first_mut(); }
/// ```
/// ```compile_fail,E0596
/// fn alter(map: &mut archsig::archmap::CheckedArchMap) { map.origins().first_mut(); }
/// ```
/// ```compile_fail,E0596
/// fn alter(map: &mut archsig::archmap::CheckedArchMap) { map.snapshots().first_mut(); }
/// ```
/// ```compile_fail,E0451
/// use archsig::archmap::CheckedArchMap;
/// let forged = CheckedArchMap {
///     bytes_digest: String::new(), model_digest: String::new(),
///     vocabularies: Default::default(), sources: vec![], origins: vec![], snapshots: vec![],
/// };
/// ```
#[derive(Debug)]
pub struct CheckedArchMap {
    pub(crate) bytes_digest: String,
    pub(crate) model_digest: String,
    pub(crate) vocabularies: BTreeMap<String, Binding>,
    pub(crate) sources: Vec<Source>,
    pub(crate) origins: Vec<Origin>,
    pub(crate) snapshots: Vec<Snapshot>,
}
impl CheckedArchMap {
    pub fn bytes_digest(&self) -> &str {
        &self.bytes_digest
    }
    pub fn model_digest(&self) -> &str {
        &self.model_digest
    }
    pub fn vocabularies(&self) -> &BTreeMap<String, Binding> {
        &self.vocabularies
    }
    pub fn sources(&self) -> &[Source] {
        &self.sources
    }
    pub fn origins(&self) -> &[Origin] {
        &self.origins
    }
    pub fn snapshots(&self) -> &[Snapshot] {
        &self.snapshots
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchMapFailure {
    pub issue: Issue,
    pub bytes_digest: String,
}
