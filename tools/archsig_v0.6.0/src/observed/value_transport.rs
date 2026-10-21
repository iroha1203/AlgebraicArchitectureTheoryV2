//! 既存の有限域核を使い、宣言の値型全域で移送の順逆を検査する。
use super::{
    control::{Checkpoint, Control},
    data, finite,
    input::CheckedInputs,
    result::{Fact, Scalar, ValidationFailure},
};
use crate::{
    canonical::Json,
    construction::{
        ConstructionFailure,
        maps::{ConfigurationOperation, DeclarationCorrespondence},
    },
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationValuePosition {
    Parameter(usize),
    Return,
}
/// 型付きの全域値または候補像。像の終域所属は結果の検査で判定する。
#[derive(Clone, Debug, Eq)]
pub struct FiniteTransportValue {
    value: Scalar,
}
impl PartialEq for FiniteTransportValue {
    fn eq(&self, other: &Self) -> bool {
        // 型域外の候補にも用いる。重複を含む改変による一方向の包含を等値にしない。
        self.value == other.value && other.value == self.value
    }
}
impl FiniteTransportValue {
    pub fn ty(&self) -> Type {
        self.value.ty()
    }
    pub fn wire(&self) -> Json {
        self.value.wire()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FiniteValueConditionFailure {
    OutsideTarget {
        source: usize,
        detail: String,
    },
    Collision {
        image: FiniteTransportValue,
        target: Option<usize>,
        sources: Vec<usize>,
    },
    Unreached {
        target: usize,
    },
}
/// source/target の全値順に対応する添字。双方の合成を全域で検査済み。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteValueBijection {
    forward: Vec<usize>,
    inverse: Vec<usize>,
}
impl FiniteValueBijection {
    pub fn forward(&self) -> &[usize] {
        &self.forward
    }
    pub fn inverse(&self) -> &[usize] {
        &self.inverse
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteValueTransport {
    declarations: DeclarationCorrespondence,
    declaration: String,
    position: DeclarationValuePosition,
    source_type: Type,
    target_type: Type,
    source: Vec<FiniteTransportValue>,
    target: Vec<FiniteTransportValue>,
    images: Vec<FiniteTransportValue>,
    support: Vec<Fact>,
    snapshots: BTreeSet<String>,
    modes: BTreeSet<String>,
    failures: Vec<FiniteValueConditionFailure>,
    bijection: Option<FiniteValueBijection>,
}
impl FiniteValueTransport {
    pub fn operation(&self) -> &ConfigurationOperation {
        self.declarations.operation()
    }
    pub fn declaration(&self) -> &str {
        &self.declaration
    }
    pub fn position(&self) -> DeclarationValuePosition {
        self.position
    }
    pub fn source_type(&self) -> &Type {
        &self.source_type
    }
    pub fn target_type(&self) -> &Type {
        &self.target_type
    }
    pub fn source(&self) -> &[FiniteTransportValue] {
        &self.source
    }
    pub fn target(&self) -> &[FiniteTransportValue] {
        &self.target
    }
    pub fn images(&self) -> &[FiniteTransportValue] {
        &self.images
    }
    pub fn support(&self) -> &[Fact] {
        &self.support
    }
    pub fn snapshots(&self) -> &BTreeSet<String> {
        &self.snapshots
    }
    pub fn modes(&self) -> &BTreeSet<String> {
        &self.modes
    }
    pub fn failures(&self) -> &[FiniteValueConditionFailure] {
        &self.failures
    }
    pub fn bijection(&self) -> Option<&FiniteValueBijection> {
        self.bijection.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self
            != &finite_declaration_value_transport(
                inputs,
                &self.declarations,
                &self.declaration,
                self.position,
                control,
            )?
        {
            return Err(ConstructionFailure::Inconsistent(
                "有限値域・候補像・順逆検査が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::FiniteValueTransport)
        .map_err(Into::into)
}
fn failure(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
        f => ConstructionFailure::Inconsistent(format!("有限値計算の不整合: {f:?}")),
    }
}
fn selected_types(
    declarations: &DeclarationCorrespondence,
    name: &str,
    position: DeclarationValuePosition,
    control: &mut Control,
) -> Result<(Type, Type), ConstructionFailure> {
    for c in declarations.candidates() {
        tick(control)?;
        if c.source().name != name {
            continue;
        }
        let target = c.target().filter(|_| c.pair().is_some()).ok_or_else(|| {
            ConstructionFailure::InvalidSelection("値型の選択は署名対応済み宣言を要求する".into())
        })?;
        let pair = match position {
            DeclarationValuePosition::Parameter(p) => c
                .source()
                .parameters
                .get(p)
                .zip(target.parameters.get(p))
                .map(|(a, b)| (a.1.clone(), b.1.clone())),
            DeclarationValuePosition::Return => c
                .source()
                .returns
                .as_ref()
                .zip(target.returns.as_ref())
                .map(|(a, b)| (a.clone(), b.clone())),
        };
        return pair.ok_or_else(|| {
            ConstructionFailure::InvalidSelection("宣言に指定の値型位置がない".into())
        });
    }
    Err(ConstructionFailure::InvalidSelection(format!(
        "選択readingの宣言候補にない: {name}"
    )))
}
fn domain(
    inputs: &CheckedInputs,
    ty: &Type,
    control: &mut Control,
) -> Result<finite::Enumeration, ConstructionFailure> {
    if !finite::supported(ty, inputs.law(), control).map_err(failure)? {
        return Err(ConstructionFailure::InvalidSelection(
            "有限値域APIの適用域でない型".into(),
        ));
    }
    let shared = control.clone();
    finite::values(
        ty,
        inputs.law(),
        &shared,
        &mut |name| {
            let mut result = finite::Enumeration::default();
            for snapshot in &inputs.archmap().snapshots {
                control.checkpoint(Checkpoint::FiniteValueTransport)?;
                result.scope.snapshots.insert(snapshot.id.clone());
                for origin in &inputs.archmap().origins {
                    control.checkpoint(Checkpoint::FiniteValueTransport)?;
                    if origin.id == snapshot.origin {
                        result.scope.modes.insert(origin.mode.wire().into());
                    }
                }
                for subject in &snapshot.subjects {
                    control.checkpoint(Checkpoint::FiniteValueTransport)?;
                    if subject.ty == name {
                        result.values.push(Scalar::Subject {
                            snapshot: snapshot.id.clone(),
                            subject: subject.id.clone(),
                            entity: name.into(),
                        });
                        result.support.push(Fact {
                            snapshot: snapshot.id.clone(),
                            subject: subject.id.clone(),
                            field: None,
                            atom: None,
                        });
                        for origin in &inputs.archmap().origins {
                            control.checkpoint(Checkpoint::FiniteValueTransport)?;
                            if origin.id == subject.origin {
                                result.scope.modes.insert(origin.mode.wire().into());
                            }
                        }
                    }
                }
            }
            // 元入力順によらず同じ有限域順にする。
            let mut rows: Vec<_> = result.values.into_iter().zip(result.support).collect();
            rows.sort_by(|a, b| a.1.cmp(&b.1));
            (result.values, result.support) = rows.into_iter().unzip();
            Ok(result)
        },
        &mut |_| {},
    )
    .map_err(failure)
}
fn moved_type(
    ty: &Type,
    mu: &BTreeMap<String, String>,
    control: &mut Control,
) -> Result<Type, ConstructionFailure> {
    crate::construction::maps::moved_declaration_type(ty, mu, &BTreeMap::new(), control)
}
fn same(a: &Scalar, b: &Scalar, control: &mut Control) -> Result<bool, ConstructionFailure> {
    tick(control)?;
    if a.ty() != b.ty() {
        return Ok(false);
    }
    data::equal(a, b, control).map_err(failure)
}
fn same_candidate(
    a: &Scalar,
    b: &Scalar,
    control: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(control)?;
    data::candidate_equal(a, b, control).map_err(failure)
}

/// 候補値の型検査の不成立を、計算自身の失敗と分ける。
fn shape(
    value: &Scalar,
    inputs: &CheckedInputs,
    control: &mut Control,
) -> Result<Option<String>, ConstructionFailure> {
    match data::check(value, inputs.law(), control) {
        Ok(()) => Ok(None),
        Err(ValidationFailure::Internal(s)) => Ok(Some(s)),
        Err(f) => Err(failure(f)),
    }
}
fn image(
    value: &Scalar,
    inputs: &CheckedInputs,
    mu: &BTreeMap<String, String>,
    action: &BTreeMap<Fact, Fact>,
    control: &mut Control,
) -> Result<Scalar, ConstructionFailure> {
    stacker::maybe_grow(64 * 1024, 4 * 1024 * 1024, || {
        tick(control)?;
        Ok(match value {
            Scalar::Subject {
                snapshot,
                subject,
                entity,
            } => {
                let original = Fact {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: None,
                    atom: None,
                };
                if let Some(to) = action.get(&original) {
                    let target_type = mu.get(entity).unwrap_or(entity);
                    // F内の外部参照も原始mapで固定される。実subjectの型を保持する。
                    let mut actual = None;
                    for s in &inputs.archmap().snapshots {
                        tick(control)?;
                        if s.id == to.snapshot {
                            for a in &s.subjects {
                                tick(control)?;
                                if a.id == to.subject {
                                    actual = Some(a.ty.clone());
                                }
                            }
                        }
                    }
                    Scalar::Subject {
                        snapshot: to.snapshot.clone(),
                        subject: to.subject.clone(),
                        entity: actual.ok_or_else(|| {
                            ConstructionFailure::Inconsistent(format!(
                                "参照値の像がない: {target_type}"
                            ))
                        })?,
                    }
                } else {
                    value.clone()
                }
            }
            Scalar::Tuple(items) => {
                let mut moved = Vec::new();
                for a in items {
                    moved.push(image(a, inputs, mu, action, control)?);
                }
                Scalar::Tuple(moved)
            }
            Scalar::Option { element, value } => Scalar::Option {
                element: moved_type(element, mu, control)?,
                value: match value {
                    Some(v) => Some(Box::new(image(v, inputs, mu, action, control)?)),
                    None => None,
                },
            },
            Scalar::Set { element, items } => {
                let mut moved = Vec::new();
                for a in items {
                    let b = image(a, inputs, mu, action, control)?;
                    let mut duplicate = false;
                    for prior in &moved {
                        tick(control)?;
                        if same_candidate(prior, &b, control)? {
                            duplicate = true;
                            break;
                        }
                    }
                    if !duplicate {
                        moved.push(b);
                    }
                }
                Scalar::Set {
                    element: moved_type(element, mu, control)?,
                    items: moved,
                }
            }
            Scalar::Map {
                domain,
                codomain,
                pairs,
            } => {
                let mut moved: Vec<(Scalar, Scalar)> = Vec::new();
                for (a, b) in pairs {
                    let a = image(a, inputs, mu, action, control)?;
                    let b = image(b, inputs, mu, action, control)?;
                    let mut duplicate = false;
                    for (key, value) in &moved {
                        tick(control)?;
                        if same_candidate(key, &a, control)? && same_candidate(value, &b, control)?
                        {
                            duplicate = true;
                            break;
                        }
                    }
                    // 同じkey・異なる像は消さずに候補へ残し、型域検査で反証する。
                    if !duplicate {
                        moved.push((a, b));
                    }
                }
                Scalar::Map {
                    domain: moved_type(domain, mu, control)?,
                    codomain: moved_type(codomain, mu, control)?,
                    pairs: moved,
                }
            }
            Scalar::Data {
                family,
                constructor,
                args,
            } => {
                let mut moved = Vec::new();
                for a in args {
                    moved.push(image(a, inputs, mu, action, control)?);
                }
                Scalar::Data {
                    family: family.clone(),
                    constructor: constructor.clone(),
                    args: moved,
                }
            }
            Scalar::Unit | Scalar::Bool(_) | Scalar::Fp { .. } => value.clone(),
            _ => {
                return Err(ConstructionFailure::Inconsistent(
                    "有限値域に適用外の値が入った".into(),
                ));
            }
        })
    })
}
/// 対応済み宣言の有限な値型を、既存核で全列挙して順逆対応を検査する。
/// 適用域外はこのnative有限APIの選択エラーであり、公開問いの算法判定ではない。
pub fn finite_declaration_value_transport(
    inputs: &CheckedInputs,
    declarations: &DeclarationCorrespondence,
    declaration: &str,
    position: DeclarationValuePosition,
    control: &mut Control,
) -> Result<FiniteValueTransport, ConstructionFailure> {
    tick(control)?;
    declarations.recheck(inputs, control)?;
    let (source_type, target_type) = selected_types(declarations, declaration, position, control)?;
    let source = domain(inputs, &source_type, control)?;
    let target = domain(inputs, &target_type, control)?;
    let mut snapshots = source.scope.snapshots.clone();
    snapshots.extend(target.scope.snapshots);
    let mut modes = source.scope.modes.clone();
    modes.extend(target.scope.modes);
    let mut support = source.support;
    support.extend(target.support);
    support.sort();
    support.dedup();
    let mu: BTreeMap<_, _> = declarations.types().iter().cloned().collect();
    let map = declarations.operation().map().candidate();
    let mut action = BTreeMap::new();
    for fact in map.source_configuration().family() {
        tick(control)?;
        if fact.field.is_none() {
            action.insert(
                fact.clone(),
                map.image(fact)
                    .ok_or_else(|| {
                        ConstructionFailure::Inconsistent("参照の候補作用がない".into())
                    })?
                    .clone(),
            );
        }
    }
    let mut images: Vec<FiniteTransportValue> = Vec::new();
    let mut failures = Vec::new();
    let mut forward = Vec::new();
    let mut fibers: Vec<Vec<usize>> = vec![Vec::new(); target.values.len()];
    let mut candidate_fibers: Vec<(usize, Option<usize>, Vec<usize>)> = Vec::new();
    for (index, value) in source.values.iter().enumerate() {
        tick(control)?;
        let moved = image(value, inputs, &mu, &action, control)?;
        let mut found = None;
        let invalid = shape(&moved, inputs, control)?;
        if invalid.is_none() {
            for (j, target) in target.values.iter().enumerate() {
                tick(control)?;
                if same(&moved, target, control)? {
                    found = Some(j);
                    break;
                }
            }
        }
        if let Some(j) = found {
            fibers[j].push(index);
            forward.push(j);
        } else {
            failures.push(FiniteValueConditionFailure::OutsideTarget {
                source: index,
                detail: invalid.unwrap_or_else(|| "候補像が終域の全値に含まれない".into()),
            });
        }
        let mut found_fiber = false;
        for (representative, _, sources) in &mut candidate_fibers {
            tick(control)?;
            if same_candidate(&images[*representative].value, &moved, control)? {
                sources.push(index);
                found_fiber = true;
                break;
            }
        }
        if !found_fiber {
            candidate_fibers.push((index, found, vec![index]));
        }
        images.push(FiniteTransportValue { value: moved });
    }
    for (representative, target, sources) in candidate_fibers {
        tick(control)?;
        if sources.len() > 1 {
            failures.push(FiniteValueConditionFailure::Collision {
                image: images[representative].clone(),
                target,
                sources,
            });
        }
    }
    for (j, sources) in fibers.iter().enumerate() {
        tick(control)?;
        if sources.is_empty() {
            failures.push(FiniteValueConditionFailure::Unreached { target: j });
        }
    }
    let bijection = if failures.is_empty() {
        let mut inverse = Vec::new();
        for fiber in &fibers {
            tick(control)?;
            inverse.push(fiber[0]);
        }
        for (a, b) in forward.iter().enumerate() {
            tick(control)?;
            if inverse.get(*b) != Some(&a) {
                return Err(ConstructionFailure::Inconsistent(
                    "有限値の逆順合成が恒等でない".into(),
                ));
            }
        }
        for (b, a) in inverse.iter().enumerate() {
            tick(control)?;
            if forward.get(*a) != Some(&b) {
                return Err(ConstructionFailure::Inconsistent(
                    "有限値の順合成が恒等でない".into(),
                ));
            }
        }
        Some(FiniteValueBijection { forward, inverse })
    } else {
        None
    };
    let result = FiniteValueTransport {
        declarations: declarations.clone(),
        declaration: declaration.into(),
        position,
        source_type,
        target_type,
        source: source
            .values
            .into_iter()
            .map(|value| FiniteTransportValue { value })
            .collect(),
        target: target
            .values
            .into_iter()
            .map(|value| FiniteTransportValue { value })
            .collect(),
        images,
        support,
        snapshots,
        modes,
        failures,
        bijection,
    };
    tick(control)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::construction::maps::{correspondence, declaration_correspondence};
    use crate::observed::input::{InputSources, check_inputs};
    const L: &str = include_str!("../../tests/fixtures/finite-value-transport.law");
    const A: &str = include_str!("../../tests/fixtures/reference-type.archmap.json");
    fn inputs(a: &str) -> CheckedInputs {
        with_left(
            include_bytes!("../../tests/fixtures/finite-value-left.atoms.json"),
            a,
        )
    }
    fn with_left(left: &[u8], a: &str) -> CheckedInputs {
        let right = include_bytes!("../../tests/fixtures/configuration-map-right.atoms.json");
        let defs =
            crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &defs.vocabularies["Left"].digest;
        let rd = &defs.vocabularies["Right"].digest;
        let bridge = include_str!("../../tests/fixtures/configuration-map-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd);
        let defs = crate::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let a = a
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest);
        check_inputs(
            InputSources::from_bytes(
                vec![left.to_vec(), right.to_vec(), bridge.into_bytes()],
                L.replace("@LEFT_DIGEST@", ld)
                    .replace("@RIGHT_DIGEST@", rd)
                    .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
                    .into_bytes(),
                a.into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues()))
    }
    fn declarations(i: &CheckedInputs) -> DeclarationCorrespondence {
        let r = correspondence(
            i,
            "v",
            "m",
            "Before",
            Some("After"),
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(r.counterexamples().is_empty(), "{:?}", r.counterexamples());
        assert!(r.missing().is_empty(), "{:?}", r.missing());
        declaration_correspondence(i, r.map().unwrap(), &mut Control::unlimited()).unwrap()
    }

    #[test]
    fn forged_whole_value_domains_images_and_bijections_are_rejected() {
        let i = inputs(A);
        let d = declarations(&i);
        let r = finite_declaration_value_transport(
            &i,
            &d,
            "Before.axes",
            DeclarationValuePosition::Parameter(5),
            &mut Control::unlimited(),
        )
        .unwrap();
        let failed = finite_declaration_value_transport(
            &i,
            &d,
            "Before.axes",
            DeclarationValuePosition::Parameter(10),
            &mut Control::unlimited(),
        )
        .unwrap();
        let mut cases = Vec::new();
        let mut v = r.clone();
        v.source.pop();
        cases.push(v);
        let mut v = r.clone();
        v.target.pop();
        cases.push(v);
        let mut v = r.clone();
        v.images[0].value = Scalar::Bool(false);
        cases.push(v);
        let mut v = r.clone();
        v.source_type = Type::Bool;
        cases.push(v);
        let mut v = r.clone();
        v.target_type = Type::Bool;
        cases.push(v);
        let mut v = r.clone();
        v.position = DeclarationValuePosition::Parameter(1);
        cases.push(v);
        let mut v = r.clone();
        v.support.clear();
        cases.push(v);
        let mut v = r.clone();
        v.snapshots.clear();
        cases.push(v);
        let mut v = r.clone();
        v.modes.clear();
        cases.push(v);
        let mut v = r.clone();
        v.bijection.as_mut().unwrap().forward[0] = 1;
        cases.push(v);
        let mut v = r.clone();
        v.bijection.as_mut().unwrap().inverse[0] = 1;
        cases.push(v);
        let mut v = r.clone();
        v.bijection = None;
        cases.push(v);
        let mut v = failed.clone();
        v.failures.clear();
        cases.push(v);
        let mut v = failed.clone();
        v.bijection = r.bijection.clone();
        cases.push(v);
        for v in cases {
            assert!(matches!(
                v.recheck(&i, &mut Control::unlimited()),
                Err(ConstructionFailure::Inconsistent(_))
            ));
        }
        r.recheck(&i, &mut Control::unlimited()).unwrap();
        failed.recheck(&i, &mut Control::unlimited()).unwrap();
    }
    #[test]
    fn candidate_equality_keeps_partial_type_mismatches_and_conflicting_map_relations() {
        let i = inputs(A);
        let d = declarations(&i);
        let r = finite_declaration_value_transport(
            &i,
            &d,
            "Before.axes",
            DeclarationValuePosition::Parameter(10),
            &mut Control::unlimited(),
        )
        .unwrap();
        let invalid = &r.images[0].value;
        let valid = &r.source[0].value;
        assert!(data::candidate_equal(invalid, invalid, &Control::unlimited()).unwrap());
        assert!(!data::candidate_equal(invalid, valid, &Control::unlimited()).unwrap());
        assert!(matches!(
            data::equal(invalid, valid, &Control::unlimited()),
            Err(ValidationFailure::Internal(_))
        ));
        let value = |id: &str, ty: &str| Scalar::Subject {
            snapshot: "v".into(),
            subject: id.into(),
            entity: ty.into(),
        };
        let map = |reverse: bool| {
            let mut pairs = vec![
                (value("q", "Right.Child"), value("p", "Left.Child")),
                (value("q", "Right.Child"), value("r", "Left.Child")),
            ];
            if reverse {
                pairs.reverse();
            }
            Scalar::Map {
                domain: Type::Ref("Right.Child".into()),
                codomain: Type::Ref("Left.Child".into()),
                pairs,
            }
        };
        let a = map(false);
        let b = map(true);
        assert!(data::candidate_equal(&a, &a, &Control::unlimited()).unwrap());
        assert!(data::candidate_equal(&a, &b, &Control::unlimited()).unwrap());
        assert!(data::candidate_equal(&b, &a, &Control::unlimited()).unwrap());
        assert!(matches!(
            data::check(&a, i.law(), &Control::unlimited()),
            Err(ValidationFailure::Internal(_))
        ));
    }
    #[test]
    fn duplicate_set_image_forgery_cannot_keep_an_established_bijection() {
        let base = inputs(A);
        let sources = base.sources();
        let law = std::str::from_utf8(sources.law().bytes())
            .unwrap()
            .replace("members: Set<Left.Child>", "members: Set<Bool>")
            .replace("members: Set<Right.Child>", "members: Set<Bool>");
        let i = check_inputs(
            InputSources::from_bytes(
                sources
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                law.into_bytes(),
                sources.archmap().bytes().to_vec(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap();
        let d = declarations(&i);
        let mut r = finite_declaration_value_transport(
            &i,
            &d,
            "Before.axes",
            DeclarationValuePosition::Parameter(6),
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(r.bijection().is_some());
        assert_eq!(r.images.len(), 4);
        if let Scalar::Set { items, .. } = &mut r.images[3].value {
            assert_eq!(items.len(), 2);
            items[1] = items[0].clone();
        } else {
            panic!("Set fixture");
        }
        assert_ne!(r.images[3], r.target[3]);
        assert!(matches!(
            r.recheck(&i, &mut Control::unlimited()),
            Err(ConstructionFailure::Inconsistent(_))
        ));
    }
}
