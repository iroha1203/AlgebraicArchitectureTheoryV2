//! 選択reading内のkind・短名と、移送後の署名による宣言対応。
use super::*;
use crate::{law::model::DeclarationInfo, types::Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclarationConditionFailure {
    Missing {
        name: String,
    },
    Kind {
        expected: &'static str,
        actual: &'static str,
    },
    Arity {
        source: usize,
        target: usize,
    },
    Parameter {
        position: usize,
        expected: Type,
        actual: Type,
    },
    Return {
        expected: Type,
        actual: Option<Type>,
    },
}
/// 署名適合を確認したLaw/view/local/change/relationの対応。式・値の保存は別途検査する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationPair {
    source: String,
    target: String,
    parameters: Vec<(String, String)>,
}
impl DeclarationPair {
    pub fn source(&self) -> &str {
        &self.source
    }
    pub fn target(&self) -> &str {
        &self.target
    }
    pub fn parameters(&self) -> &[(String, String)] {
        &self.parameters
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationCandidate {
    source: DeclarationInfo,
    target: Option<DeclarationInfo>,
    failures: Vec<DeclarationConditionFailure>,
    pair: Option<DeclarationPair>,
}
impl DeclarationCandidate {
    pub fn source(&self) -> &DeclarationInfo {
        &self.source
    }
    pub fn target(&self) -> Option<&DeclarationInfo> {
        self.target.as_ref()
    }
    pub fn failures(&self) -> &[DeclarationConditionFailure] {
        &self.failures
    }
    pub fn pair(&self) -> Option<&DeclarationPair> {
        self.pair.as_ref()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclarationCorrespondence {
    operation: ConfigurationOperation,
    types: Vec<(String, String)>,
    candidates: Vec<DeclarationCandidate>,
}
impl DeclarationCorrespondence {
    pub fn operation(&self) -> &ConfigurationOperation {
        &self.operation
    }
    pub fn types(&self) -> &[(String, String)] {
        &self.types
    }
    pub fn candidates(&self) -> &[DeclarationCandidate] {
        &self.candidates
    }
    pub fn all_signatures_compatible(&self) -> bool {
        self.candidates.iter().all(|c| c.pair.is_some())
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self != &declaration_correspondence(inputs, self.operation.map(), control)? {
            return Err(ConstructionFailure::Inconsistent(
                "宣言候補・署名の対応が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::DeclarationCorrespondence)
        .map_err(Into::into)
}
pub(crate) fn moved_type(
    ty: &Type,
    mu: &BTreeMap<String, String>,
    alpha: &BTreeMap<String, String>,
    control: &mut Control,
) -> Result<Type, ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        tick(control)?;
        let name = |n: &String| mu.get(n).cloned().unwrap_or_else(|| n.clone());
        let ty = match ty {
            Type::Ref(n) => Type::Ref(name(n)),
            Type::Owned(n, owner) => Type::Owned(
                name(n),
                alpha.get(owner).cloned().unwrap_or_else(|| owner.clone()),
            ),
            Type::Tuple(items) => {
                let mut moved = Vec::new();
                for t in items {
                    tick(control)?;
                    moved.push(moved_type(t, mu, alpha, control)?);
                }
                Type::Tuple(moved)
            }
            Type::List(t) => Type::List(Box::new(moved_type(t, mu, alpha, control)?)),
            Type::Set(t) => Type::Set(Box::new(moved_type(t, mu, alpha, control)?)),
            Type::Option(t) => Type::Option(Box::new(moved_type(t, mu, alpha, control)?)),
            Type::Map(a, b) => Type::Map(
                Box::new(moved_type(a, mu, alpha, control)?),
                Box::new(moved_type(b, mu, alpha, control)?),
            ),
            Type::Term(args, ret) => {
                let mut moved = Vec::new();
                for t in args {
                    tick(control)?;
                    moved.push(moved_type(t, mu, alpha, control)?);
                }
                Type::Term(moved, Box::new(moved_type(ret, mu, alpha, control)?))
            }
            Type::Path(a, b) => Type::Path(name(a), name(b)),
            t => t.clone(),
        };
        tick(control)?;
        Ok(ty)
    })
}
fn metadata(
    inputs: &CheckedInputs,
    name: &str,
    control: &mut Control,
) -> Result<DeclarationInfo, ConstructionFailure> {
    for info in &inputs.law().infos {
        tick(control)?;
        if info.name == name {
            return Ok(info.clone());
        }
    }
    Err(ConstructionFailure::Inconsistent(
        "元宣言のmetadataがない".into(),
    ))
}
/// 保存済み原始対応を使い、選択readingの全宣言候補の署名を検査する。
pub fn declaration_correspondence(
    inputs: &CheckedInputs,
    map: &ConfigurationMap,
    control: &mut Control,
) -> Result<DeclarationCorrespondence, ConstructionFailure> {
    tick(control)?;
    let MapOrigin::Correspondence(raw) = &map.candidate.origin else {
        return Err(ConstructionFailure::InvalidSelection(
            "宣言対応は原始correspondenceの保存済みmapを要求する".into(),
        ));
    };
    let operation = ConfigurationOperation::from_map(inputs, map, control)?;
    let holder = subject(inputs, &raw.snapshot, &raw.subject, control)?;
    let declaration = inputs
        .definitions()
        .declarations
        .get(&holder.ty)
        .ok_or_else(|| ConstructionFailure::Inconsistent("原始対応の定義がない".into()))?;
    let PrimitiveSignature::Correspondence { from, to, maps, .. } = &declaration.signature else {
        return Err(ConstructionFailure::Inconsistent(
            "原始対応の型が違う".into(),
        ));
    };
    let mut mu = BTreeMap::new();
    mu.insert(from.clone(), to.clone());
    for (_, a, b) in maps {
        tick(control)?;
        mu.insert(a.clone(), b.clone());
    }
    let c = map.candidate();
    let prefix = format!("{}.", c.reading());
    let mut candidates = Vec::new();
    for declaration in inputs.law().declarations.values() {
        tick(control)?;
        let kind = declaration.signature.kind();
        if declaration.reading != c.reading()
            || !matches!(kind, "law" | "view" | "local" | "change" | "relation")
        {
            continue;
        }
        let short = declaration
            .name
            .strip_prefix(&prefix)
            .ok_or_else(|| ConstructionFailure::Inconsistent("宣言名とreadingが違う".into()))?;
        let name = format!("{}.{short}", c.to_reading());
        let source = metadata(inputs, &declaration.name, control)?;
        let target = if inputs
            .law()
            .declarations
            .get(&name)
            .is_some_and(|d| d.reading == c.to_reading())
        {
            Some(metadata(inputs, &name, control)?)
        } else {
            None
        };
        let mut failures = Vec::new();
        let mut parameters = Vec::new();
        if let Some(target) = &target {
            if target.kind != kind {
                failures.push(DeclarationConditionFailure::Kind {
                    expected: kind,
                    actual: target.kind,
                });
            } else {
                if source.parameters.len() != target.parameters.len() {
                    failures.push(DeclarationConditionFailure::Arity {
                        source: source.parameters.len(),
                        target: target.parameters.len(),
                    });
                }
                let mut alpha = BTreeMap::new();
                for ((s, _), (t, _)) in source.parameters.iter().zip(&target.parameters) {
                    tick(control)?;
                    alpha.insert(s.clone(), t.clone());
                }
                for (position, ((s, ty), (t, actual))) in
                    source.parameters.iter().zip(&target.parameters).enumerate()
                {
                    tick(control)?;
                    let expected = moved_type(ty, &mu, &alpha, control)?;
                    if &expected != actual {
                        failures.push(DeclarationConditionFailure::Parameter {
                            position,
                            expected,
                            actual: actual.clone(),
                        });
                    }
                    parameters.push((s.clone(), t.clone()));
                }
                if kind == "view" {
                    let returns = source.returns.as_ref().ok_or_else(|| {
                        ConstructionFailure::Inconsistent("viewの元戻り型がない".into())
                    })?;
                    let expected = moved_type(returns, &mu, &alpha, control)?;
                    if target.returns.as_ref() != Some(&expected) {
                        failures.push(DeclarationConditionFailure::Return {
                            expected,
                            actual: target.returns.clone(),
                        });
                    }
                }
            }
        } else {
            failures.push(DeclarationConditionFailure::Missing { name });
        }
        let pair = if failures.is_empty() {
            Some(DeclarationPair {
                source: source.name.clone(),
                target: target
                    .as_ref()
                    .ok_or_else(|| {
                        ConstructionFailure::Inconsistent("確認済みの終域宣言がない".into())
                    })?
                    .name
                    .clone(),
                parameters,
            })
        } else {
            None
        };
        candidates.push(DeclarationCandidate {
            source,
            target,
            failures,
            pair,
        });
    }
    let mut types = Vec::new();
    for pair in mu {
        tick(control)?;
        types.push(pair);
    }
    tick(control)?;
    Ok(DeclarationCorrespondence {
        operation,
        types,
        candidates,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn type_transport_keeps_value_identities_and_moves_all_structural_reference_positions() {
        let mu = BTreeMap::from([
            ("L.Root".into(), "R.Root".into()),
            ("L.Child".into(), "R.Child".into()),
        ]);
        let alpha = BTreeMap::from([("a".into(), "x".into())]);
        let source = Type::Tuple(vec![
            Type::Ref("L.Root".into()),
            Type::Owned("L.Child".into(), "a".into()),
            Type::List(Box::new(Type::Option(Box::new(Type::Ref(
                "L.Child".into(),
            ))))),
            Type::Set(Box::new(Type::Ref("Shared.External".into()))),
            Type::Map(
                Box::new(Type::Owned("L.Child".into(), "a".into())),
                Box::new(Type::Ref("Shared.External".into())),
            ),
            Type::Path("L.Child".into(), "L.Root".into()),
            Type::Term(
                vec![Type::Z, Type::Bool],
                Box::new(Type::Option(Box::new(Type::Q))),
            ),
            Type::Data("Shared.Tree".into()),
            Type::Fp("5".into()),
            Type::Text,
            Type::Unit,
        ]);
        let expected = Type::Tuple(vec![
            Type::Ref("R.Root".into()),
            Type::Owned("R.Child".into(), "x".into()),
            Type::List(Box::new(Type::Option(Box::new(Type::Ref(
                "R.Child".into(),
            ))))),
            Type::Set(Box::new(Type::Ref("Shared.External".into()))),
            Type::Map(
                Box::new(Type::Owned("R.Child".into(), "x".into())),
                Box::new(Type::Ref("Shared.External".into())),
            ),
            Type::Path("R.Child".into(), "R.Root".into()),
            Type::Term(
                vec![Type::Z, Type::Bool],
                Box::new(Type::Option(Box::new(Type::Q))),
            ),
            Type::Data("Shared.Tree".into()),
            Type::Fp("5".into()),
            Type::Text,
            Type::Unit,
        ]);
        assert_eq!(
            moved_type(&source, &mu, &alpha, &mut Control::unlimited()).unwrap(),
            expected
        );
    }
    fn inputs(law: &str) -> CheckedInputs {
        let left = include_bytes!("../../../tests/fixtures/configuration-map-left.atoms.json");
        let right = include_bytes!("../../../tests/fixtures/configuration-map-right.atoms.json");
        let defs =
            crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &defs.vocabularies["Left"].digest;
        let rd = &defs.vocabularies["Right"].digest;
        let bridge = include_str!("../../../tests/fixtures/configuration-map-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd);
        let defs = crate::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let map = include_str!("../../../tests/fixtures/configuration-map-bridge.archmap.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest);
        crate::observed::input::check_inputs(
            crate::observed::input::InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                law.replace("@LEFT_DIGEST@", ld)
                    .replace("@RIGHT_DIGEST@", rd)
                    .into_bytes(),
                map.into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    fn build(i: &CheckedInputs) -> DeclarationCorrespondence {
        let m = correspondence(
            i,
            "v",
            "m",
            "Before",
            Some("After"),
            &mut Control::unlimited(),
        )
        .unwrap();
        declaration_correspondence(i, m.map().unwrap(), &mut Control::unlimited()).unwrap()
    }
    #[test]
    fn recheck_rejects_forged_types_metadata_names_parameters_pairs_and_conditions() {
        let law = include_str!("../../../tests/fixtures/declaration-correspondence.law");
        let i = inputs(law);
        let original = build(&i);
        let owner = original
            .candidates
            .iter()
            .position(|c| c.source.name == "Before.owned")
            .unwrap();
        let amount = original
            .candidates
            .iter()
            .position(|c| c.source.name == "Before.amount")
            .unwrap();
        for kind in 0..8 {
            let mut forged = original.clone();
            match kind {
                0 => {
                    forged.types.swap(0, 1);
                }
                1 => {
                    forged.candidates.pop();
                }
                2 => {
                    forged.candidates[owner].source.parameters.pop();
                }
                3 => {
                    forged.candidates[amount].target.as_mut().unwrap().name = "Decoy.amount".into();
                }
                4 => {
                    forged.candidates[owner]
                        .pair
                        .as_mut()
                        .unwrap()
                        .parameters
                        .swap(0, 1);
                }
                5 => {
                    forged.candidates[owner].pair = None;
                }
                6 => {
                    forged.candidates[amount]
                        .failures
                        .push(DeclarationConditionFailure::Missing {
                            name: "After.amount".into(),
                        });
                }
                _ => {
                    forged.candidates[amount].source.references.clear();
                    forged.candidates[amount].source.dependencies.clear();
                }
            }
            assert!(
                forged.recheck(&i, &mut Control::unlimited()).is_err(),
                "{kind}"
            );
        }
        let bad = inputs(&law.replace(
            "view owned(x: Root, y: Root, k: Child[x])",
            "view owned(x: Root, y: Root, k: Child[y])",
        ));
        let mut forged = build(&bad);
        assert!(forged.candidates[owner].pair.is_none());
        forged.candidates[owner].failures.clear();
        forged.candidates[owner].pair = original.candidates[owner].pair.clone();
        assert!(forged.recheck(&bad, &mut Control::unlimited()).is_err());
    }
}
