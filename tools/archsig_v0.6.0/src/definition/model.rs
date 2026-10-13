//! 共通原始定義。意味・依存・入力位置を Law の構文木から独立して保持する。
use crate::{canonical::Json, issue::Location, types::Type};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub namespace: String,
    pub version: String,
    pub digest: String,
    pub location: Location,
}
impl Binding {
    pub fn wire(&self) -> Json {
        Json::obj([
            ("namespace", Json::str(&self.namespace)),
            ("version", Json::str(&self.version)),
            ("digest", Json::str(&self.digest)),
        ])
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub name: String,
    pub ty: Type,
    pub meaning: String,
    pub location: Location,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    pub name: String,
    pub arguments: Vec<Type>,
    pub meaning: String,
    pub location: Location,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alignment {
    pub source: String,
    pub target: String,
    pub meaning: String,
    pub location: Location,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrimitiveSignature {
    Entity {
        parameters: Vec<Field>,
        fields: Vec<Field>,
        owner: Option<String>,
    },
    Arrow {
        parameters: Vec<Field>,
        fields: Vec<Field>,
        owner: String,
        endpoint: String,
    },
    Correspondence {
        parameters: Vec<Field>,
        fields: Vec<Field>,
        from: String,
        to: String,
        maps: Vec<(String, String, String)>,
        alignments: Vec<Alignment>,
        implicit: Vec<(String, String)>,
    },
    Data {
        constructors: Vec<Constructor>,
    },
}
impl PrimitiveSignature {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Entity { .. } => "entity",
            Self::Arrow { .. } => "arrow",
            Self::Correspondence { .. } => "correspondence",
            Self::Data { .. } => "data",
        }
    }
    pub fn record_fields(&self) -> Option<(&[Field], &[Field])> {
        match self {
            Self::Entity {
                parameters, fields, ..
            }
            | Self::Arrow {
                parameters, fields, ..
            }
            | Self::Correspondence {
                parameters, fields, ..
            } => Some((parameters, fields)),
            _ => None,
        }
    }
    pub fn field(&self, name: &str) -> Option<&Field> {
        let (p, f) = self.record_fields()?;
        p.iter().chain(f).find(|f| f.name == name)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveDeclaration {
    pub name: String,
    pub namespace: String,
    pub meaning: String,
    pub signature: PrimitiveSignature,
    pub location: Location,
    /// 元の QName 文字列の位置と解決先。
    pub references: Vec<(Location, String)>,
    pub dependencies: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vocabulary {
    pub namespace: String,
    pub version: String,
    pub dependencies: Vec<Binding>,
    pub manifest: Json,
    pub digest: String,
    pub location: Location,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionIdentity {
    pub input: String,
    pub bytes_digest: String,
    pub model_digest: Option<String>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckedDefinitions {
    pub declarations: BTreeMap<String, PrimitiveDeclaration>,
    pub vocabularies: BTreeMap<String, Vocabulary>,
    pub inputs: Vec<DefinitionIdentity>,
}

/// data の引数から推移的に計算した原始型の性質。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DataProperties {
    pub term_or_path: bool,
    pub reference: bool,
}
