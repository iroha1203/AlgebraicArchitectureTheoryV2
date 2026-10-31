//! 共通原始定義。意味・依存・入力位置を Law の構文木から独立して保持する。
use crate::control::{Checkpoint, Control};
use crate::json::InputError;
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
        self.field_controlled::<Box<crate::issue::Issue>>(
            name,
            &mut Control::unlimited(),
            Checkpoint::DefinitionSemantics,
        )
        .expect("通常の field 探索は中断しない")
    }
    pub(crate) fn field_controlled<E: InputError>(
        &self,
        name: &str,
        control: &mut Control,
        point: Checkpoint,
    ) -> Result<Option<&Field>, E> {
        self.field_checked_controlled::<E, _>(name, control, point, |field, _| Ok(field))
    }
    /// Interpret the completed search before sampling its post checkpoint.
    /// A required use constructs its original Issue here; optional lookup keeps None.
    pub(crate) fn field_checked_controlled<'a, E: InputError, T>(
        &'a self,
        name: &str,
        control: &mut Control,
        point: Checkpoint,
        check: impl FnOnce(Option<&'a Field>, &mut Control) -> Result<T, E>,
    ) -> Result<T, E> {
        E::checkpoint(control, point)?;
        let result = match self.record_fields() {
            Some((parameters, fields)) => find_field_checked_controlled::<E, _>(
                parameters.iter().chain(fields),
                name,
                control,
                point,
                check,
            ),
            None => check(None, control),
        };
        E::finish(result, control, point)
    }
}

pub(crate) fn find_field_controlled<'a, E: InputError>(
    fields: impl IntoIterator<Item = &'a Field>,
    name: &str,
    control: &mut Control,
    point: Checkpoint,
) -> Result<Option<&'a Field>, E> {
    find_field_checked_controlled::<E, _>(fields, name, control, point, |field, _| Ok(field))
}

pub(crate) fn find_field_checked_controlled<'a, E: InputError, T>(
    fields: impl IntoIterator<Item = &'a Field>,
    name: &str,
    control: &mut Control,
    point: Checkpoint,
    check: impl FnOnce(Option<&'a Field>, &mut Control) -> Result<T, E>,
) -> Result<T, E> {
    E::checkpoint(control, point)?;
    let result = (|| {
        let mut fields = fields.into_iter().peekable();
        while let Some(field) = fields.next() {
            E::checkpoint(control, point)?;
            let found = field.name == name;
            if found {
                return E::finish(check(Some(field), control), control, point);
            }
            if fields.peek().is_none() {
                return E::finish(check(None, control), control, point);
            }
            E::checkpoint(control, point)?;
        }
        check(None, control)
    })();
    E::finish(result, control, point)
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
/// `check_definitions` で検査した共通定義。公開の参照から内容を読み取れる。
///
/// ```
/// use archsig::definition::check_definitions;
/// let checked = check_definitions(&[]).unwrap();
/// assert!(checked.declarations().is_empty());
/// assert!(checked.vocabularies().is_empty());
/// assert!(checked.inputs().is_empty());
/// ```
///
/// 構築と更新は検査を通す。
///
/// ```compile_fail,E0451
/// use archsig::definition::CheckedDefinitions;
/// let forged = CheckedDefinitions {
///     declarations: Default::default(),
///     vocabularies: Default::default(),
///     inputs: Vec::new(),
/// };
/// ```
///
/// ```compile_fail,E0599
/// use archsig::definition::CheckedDefinitions;
/// let forged = CheckedDefinitions::default();
/// ```
///
/// ```compile_fail,E0596
/// let mut checked = archsig::definition::check_definitions(&[]).unwrap();
/// checked.declarations().clear();
/// ```
///
/// ```compile_fail,E0596
/// let mut checked = archsig::definition::check_definitions(&[]).unwrap();
/// checked.vocabularies().values_mut().next().unwrap().dependencies.clear();
/// ```
///
/// ```compile_fail,E0594
/// let mut checked = archsig::definition::check_definitions(&[]).unwrap();
/// checked.inputs()[0].model_digest = None;
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedDefinitions {
    pub(crate) declarations: BTreeMap<String, PrimitiveDeclaration>,
    pub(crate) vocabularies: BTreeMap<String, Vocabulary>,
    pub(crate) inputs: Vec<DefinitionIdentity>,
}

impl CheckedDefinitions {
    pub(crate) fn empty() -> Self {
        Self {
            declarations: BTreeMap::new(),
            vocabularies: BTreeMap::new(),
            inputs: Vec::new(),
        }
    }
    pub fn declarations(&self) -> &BTreeMap<String, PrimitiveDeclaration> {
        &self.declarations
    }
    pub fn vocabularies(&self) -> &BTreeMap<String, Vocabulary> {
        &self.vocabularies
    }
    pub fn inputs(&self) -> &[DefinitionIdentity] {
        &self.inputs
    }
}

/// data の引数から推移的に計算した原始型の性質。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DataProperties {
    pub term_or_path: bool,
    pub reference: bool,
}

#[cfg(test)]
mod field_control_tests {
    use super::*;
    use crate::control::{CheckFailure, Limits, StopReason, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};
    type Failure = CheckFailure<Box<crate::issue::Issue>>;
    #[test]
    fn field_lookup_checks_each_candidate_and_its_success_and_absence_exit() {
        let fields: Vec<_> = ["first", "second", "last"]
            .into_iter()
            .map(|name| Field {
                name: name.into(),
                ty: Type::Bool,
                meaning: String::new(),
                location: Location::Law { span: (0, 1) },
            })
            .collect();
        let signature = PrimitiveSignature::Entity {
            parameters: vec![fields[0].clone()],
            fields: fields[1..].to_vec(),
            owner: None,
        };
        for name in ["last", "absent"] {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut control = Control::new(Limits::default(), move |_| {
                seen.set(seen.get() + 1);
                Usage::default()
            });
            let hit = signature
                .field_controlled::<Failure>(name, &mut control, Checkpoint::DefinitionSemantics)
                .unwrap();
            assert_eq!(hit, signature.field(name));
            assert!(count.get() >= 8);
            for at in 1..=count.get() {
                let mut visits = 0;
                let mut control = Control::new(Limits::default(), move |_| {
                    visits += 1;
                    Usage {
                        signal: (visits == at).then_some(Signal::Term),
                        ..Usage::default()
                    }
                });
                assert!(matches!(
                    signature.field_controlled::<Failure>(
                        name,
                        &mut control,
                        Checkpoint::DefinitionSemantics
                    ),
                    Err(Failure::Stopped(StopReason::Cancelled(Signal::Term)))
                ));
            }
        }
    }
}
