//! 担当別の原始モデルと明示対応から、同じ型付き構成を生成する。
use super::{data, result::*, value_transport};
use crate::construction::{self, ConfigurationConstruction, ConstructionFailure};
use archsig_common::{
    control::{Checkpoint, Control},
    issue::Location,
    types::Type,
};
use archsig_input::{
    archmap::{Slot, Subject},
    input::CheckedInputs,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub(super) enum Preparation {
    Ready(Model),
    Missing(Vec<Fact>),
    Unsupported(Unsupported),
    Rejected(Rejection),
}
#[derive(Clone, Debug)]
pub(super) struct Unsupported {
    pub detail: String,
    pub location: Location,
    pub operand_types: Vec<Type>,
    pub position: Option<Fact>,
}
fn unsupported(s: &Subject, f: &archsig_input::archmap::Field, detail: String) -> Preparation {
    match &f.slot {
        Slot::Known { pointer, .. } => Preparation::Unsupported(Unsupported {
            detail,
            location: Location::ArchMap {
                pointer: pointer.clone(),
                span: None,
            },
            operand_types: vec![f.ty.erase()],
            position: Some(observed_fact(s, f)),
        }),
        Slot::Missing => Preparation::Missing(vec![field_fact(s, f)]),
    }
}
#[derive(Debug)]
pub(super) struct Rejection {
    pub detail: String,
    pub facts: Vec<Fact>,
    pub values: Option<(Scalar, Scalar)>,
}
pub(super) fn rejected(detail: impl Into<String>, facts: Vec<Fact>) -> Preparation {
    Preparation::Rejected(Rejection {
        detail: detail.into(),
        facts,
        values: None,
    })
}
fn observed_fact(s: &Subject, f: &archsig_input::archmap::Field) -> Fact {
    let mut fact = field_fact(s, f);
    if let Slot::Known { atom, .. } = &f.slot {
        fact.atom = Some(atom.clone());
    }
    fact
}
fn counterexample_facts(rows: &[crate::construction::maps::Counterexample]) -> Vec<Fact> {
    use crate::construction::maps::Counterexample as C;
    let mut facts = Vec::new();
    for row in rows {
        match row {
            C::Field {
                source,
                target_subject,
                ..
            } => facts.extend([source.clone(), target_subject.clone()]),
            C::ReferenceStructure { source, target }
            | C::Family {
                source,
                image: target,
            } => facts.extend([source.clone(), target.clone()]),
            C::ReferenceConstraints {
                fields,
                unresolved_fields,
            } => {
                for (a, b) in fields {
                    facts.extend([a.clone(), b.clone()]);
                }
                facts.extend(unresolved_fields.iter().cloned());
            }
            C::Relation {
                source: (a, b),
                image: (x, y),
            }
            | C::Identification {
                source: (a, b),
                image: (x, y),
            } => facts.extend([a.clone(), b.clone(), x.clone(), y.clone()]),
        }
    }
    facts.sort();
    facts.dedup();
    facts
}
#[derive(Debug)]
pub(super) struct Model {
    pub construction: std::sync::Arc<ConfigurationConstruction>,
    pub fragments: Vec<ConfigurationConstruction>,
    pub overrides: std::sync::Arc<Vec<(Fact, Scalar)>>,
    pub support: Vec<Fact>,
    pub inclusions: Vec<crate::construction::maps::ConfigurationTransport>,
    pub restrictions: Vec<crate::construction::maps::ConfigurationMap>,
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::ConfigurationMap)?;
    Ok(())
}
fn failure(e: ConstructionFailure) -> ValidationFailure {
    match e {
        ConstructionFailure::Stopped(s) => s.into(),
        e => ValidationFailure::Internal(e.internal_context(format!("局所モデル組立て: {e:?}"))),
    }
}
fn subject<'a>(inputs: &'a CheckedInputs, fact: &Fact) -> Result<&'a Subject, ValidationFailure> {
    inputs
        .archmap()
        .snapshots()
        .iter()
        .find(|s| s.id == fact.snapshot)
        .and_then(|s| s.subjects.iter().find(|s| s.id == fact.subject))
        .ok_or_else(|| internal!("組立ての型付き参照先がない").into())
}
fn field_fact(s: &Subject, field: &archsig_input::archmap::Field) -> Fact {
    Fact::from(archsig_input::archmap::FactData {
        snapshot: s.snapshot.clone(),
        subject: s.id.clone(),
        field: Some(field.name.clone()),
        atom: None,
    })
}
/// 同値類のrootだけを保持し、全対・全域の積を作らない。
fn representative(
    parent: &mut BTreeMap<Fact, Fact>,
    fact: &Fact,
    c: &Control,
) -> Result<Fact, ValidationFailure> {
    let mut root = fact.clone();
    while let Some(next) = parent.get(&root) {
        tick(c)?;
        if next == &root {
            break;
        }
        root = next.clone();
    }
    let mut at = fact.clone();
    while let Some(next) = parent.get(&at).cloned() {
        tick(c)?;
        if next == at || next == root {
            break;
        }
        parent.insert(at, root.clone());
        at = next;
    }
    Ok(root)
}
pub(super) fn compile(
    inputs: &std::sync::Arc<CheckedInputs>,
    reading: &str,
    target: &Fact,
    roots: &[Fact],
    pairs: &[(Fact, Fact)],
    c: &Control,
) -> Result<Preparation, ValidationFailure> {
    tick(c)?;
    if roots.is_empty() {
        return Ok(rejected("担当rootの集合が空", vec![target.clone()]));
    }
    let root_subject = subject(inputs, target)?;
    let target_construction =
        construction::construct(inputs, reading, &target.snapshot, &target.subject, c)
            .map_err(failure)?;
    if !target_construction.local_domain().is_complete() {
        return Ok(Preparation::Missing(
            target_construction.base().blocking_slots().to_vec(),
        ));
    }
    if target_construction.local_domain().known().len() != 1 {
        return Ok(rejected(
            "組立て先rootに既存または所属未決の個体がある",
            target_construction.local_domain().known().to_vec(),
        ));
    }
    let mut fragments = Vec::new();
    let mut membership = BTreeMap::new();
    let mut parent = BTreeMap::new();
    let mut roots_seen = BTreeSet::new();
    let mut missing = BTreeSet::new();
    let mut support = BTreeSet::new();
    for (i, root) in roots.iter().enumerate() {
        tick(c)?;
        if root == target
            || !roots_seen.insert(root)
            || root.snapshot != target.snapshot
            || subject(inputs, root)?.ty != root_subject.ty
        {
            return Ok(rejected(
                "担当rootは同一snapshot・同一型の異なるrootを要求する",
                vec![root.clone(), target.clone()],
            ));
        }
        let local = construction::construct(inputs, reading, &root.snapshot, &root.subject, c)
            .map_err(failure)?;
        missing.extend(local.base().blocking_slots().iter().cloned());
        support.extend(local.base().known().family().iter().cloned());
        parent.insert(root.clone(), target.clone());
        for fact in local.local_domain().known() {
            tick(c)?;
            if fact != root {
                membership.insert(fact.clone(), i);
                parent.insert(fact.clone(), fact.clone());
            }
        }
        fragments.push(local);
    }
    // 原始のscalar欠測も含め、完成した局所記述だけを対象にする。
    for fact in fragments
        .iter()
        .flat_map(|f| f.local_domain().known())
        .chain(std::iter::once(target))
    {
        let s = subject(inputs, fact)?;
        for field in &s.fields {
            tick(c)?;
            if matches!(field.slot, Slot::Missing) {
                missing.insert(field_fact(s, field));
            }
        }
    }
    if !missing.is_empty() {
        return Ok(Preparation::Missing(missing.into_iter().collect()));
    }
    for (a, b) in pairs {
        tick(c)?;
        let (Some(ia), Some(ib)) = (membership.get(a), membership.get(b)) else {
            return Ok(rejected(
                "共有対の個体が担当rootに所属しない",
                vec![a.clone(), b.clone()],
            ));
        };
        if ia == ib || subject(inputs, a)?.ty != subject(inputs, b)?.ty {
            return Ok(rejected(
                "共有対は異なる担当の同じ型の個体を要求する",
                vec![a.clone(), b.clone()],
            ));
        }
        let a = representative(&mut parent, a, c)?;
        let b = representative(&mut parent, b, c)?;
        let (small, large) = if a.wire().canonical() < b.wire().canonical() {
            (a, b)
        } else {
            (b, a)
        };
        parent.insert(large, small);
    }
    // 一度だけ平坦化し、以後の参照輸送・後続評価で同じ対応を使う。
    let mut transport = BTreeMap::new();
    let keys: Vec<_> = parent.keys().cloned().collect();
    for fact in keys {
        tick(c)?;
        transport.insert(fact.clone(), representative(&mut parent, &fact, c)?);
    }
    for local in &fragments {
        let mut images = BTreeSet::new();
        for fact in local
            .base()
            .known()
            .family()
            .iter()
            .filter(|f| f.field.is_none())
        {
            tick(c)?;
            if !images.insert(transport.get(fact).unwrap_or(fact)) {
                return Ok(rejected(
                    "共有対応の推移閉包が局所の異なる個体を同一視する",
                    local
                        .base()
                        .known()
                        .family()
                        .iter()
                        .filter(|f| f.field.is_none())
                        .cloned()
                        .collect(),
                ));
            }
        }
    }
    let mut members = BTreeSet::from([target.clone()]);
    members.extend(membership.keys().map(|f| transport[f].clone()));
    let mut overrides = Vec::new();
    for (from, to) in &transport {
        tick(c)?;
        let a = subject(inputs, from)?;
        let b = subject(inputs, to)?;
        for af in &a.fields {
            tick(c)?;
            let bf = b
                .fields
                .iter()
                .find(|f| f.name == af.name)
                .ok_or(internal!("同じ型の組立てfieldがない"))?;
            let (Slot::Known { value: av, .. }, Slot::Known { value: bv, .. }) =
                (&af.slot, &bf.slot)
            else {
                return Err(internal!("組立ての既知field検査が失われた").into());
            };
            let (Some(av), Some(bv)) = (
                data::from_input(av, &af.ty.erase(), inputs.law(), c)?,
                data::from_input(bv, &bf.ty.erase(), inputs.law(), c)?,
            ) else {
                return Ok(unsupported(
                    a,
                    af,
                    format!("field `{}` の型付き値輸送に未対応", af.name),
                ));
            };
            if contains_term(&av, c)? || contains_term(&bv, c)? {
                return Ok(unsupported(
                    a,
                    af,
                    format!("field `{}` は関数値を含む", af.name),
                ));
            }
            let moved_a = value_transport::transport_references(&av, inputs, &transport, c)
                .map_err(failure)?;
            let moved_b = value_transport::transport_references(&bv, inputs, &transport, c)
                .map_err(failure)?;
            if !data::equal(&moved_a, &moved_b, c)? {
                return Ok(Preparation::Rejected(Rejection {
                    detail: format!("共有個体のfield `{}` が参照輸送後に一致しない", af.name),
                    facts: vec![observed_fact(a, af), observed_fact(b, bf)],
                    values: Some((moved_a, moved_b)),
                }));
            }
            if from == to && !data::equal(&bv, &moved_b, c)? {
                overrides.push((field_fact(b, bf), moved_b));
            }
        }
    }
    // targetrootはparentのkeyでない。rootの輸送後値も明示する。
    for field in &root_subject.fields {
        tick(c)?;
        let Slot::Known { value, .. } = &field.slot else {
            return Err(internal!("組立て先rootの既知fieldがない").into());
        };
        let Some(value) = data::from_input(value, &field.ty.erase(), inputs.law(), c)? else {
            return Ok(unsupported(
                root_subject,
                field,
                format!("root field `{}` に未対応", field.name),
            ));
        };
        let moved = value_transport::transport_references(&value, inputs, &transport, c)
            .map_err(failure)?;
        if !data::equal(&value, &moved, c)? {
            overrides.push((field_fact(root_subject, field), moved));
        }
    }
    support.extend(target_construction.base().known().family().iter().cloned());
    let construction = construction::construct_assembled(
        inputs.clone(),
        target_construction,
        &members.into_iter().collect::<Vec<_>>(),
        transport,
        c,
    )
    .map_err(failure)?;
    let construction = std::sync::Arc::new(construction);
    let global_arrows = std::sync::Arc::new(
        construction::maps::internal_arrows_constructed(inputs, construction.clone(), c)
            .map_err(|e| failure(e.cause().clone()))?,
    );
    if !global_arrows.all_preserved() {
        return Ok(rejected(
            "組立て対象の生成操作がconfigurationを保存しない",
            global_arrows
                .arrows()
                .iter()
                .flat_map(|row| counterexample_facts(row.counterexamples()))
                .collect(),
        ));
    }
    let mut inclusions = Vec::new();
    let mut restrictions = Vec::new();
    for local in &fragments {
        tick(c)?;
        let mut forward = BTreeMap::new();
        let mut inverse = BTreeMap::new();
        let mut local_image = Vec::new();
        for fact in local
            .base()
            .known()
            .family()
            .iter()
            .filter(|f| f.field.is_none())
        {
            tick(c)?;
            let image = construction.transported_subject(fact).clone();
            forward.insert(fact.clone(), image.clone());
            inverse.insert(image, fact.clone());
        }
        for fact in local.local_domain().known() {
            local_image.push(construction.transported_subject(fact).clone());
        }
        let local = std::sync::Arc::new(local.clone());
        let Some(inclusion) = construction::maps::assembled_map(
            inputs,
            local.clone(),
            construction.clone(),
            forward,
            c,
        )
        .map_err(failure)?
        else {
            return Ok(rejected(
                "局所の包含がconfigurationを保存しない",
                local.base().known().family().to_vec(),
            ));
        };
        let local_arrows = std::sync::Arc::new(
            construction::maps::internal_arrows_constructed(inputs, local.clone(), c)
                .map_err(|e| failure(e.cause().clone()))?,
        );
        let inclusion = construction::maps::configuration_transport_constructed(
            inputs,
            &inclusion,
            local_arrows,
            global_arrows.clone(),
            c,
        )
        .map_err(|e| failure(e.cause().clone()))?;
        if !inclusion.all_preserved() {
            return Ok(rejected(
                "局所の包含が生成操作を保存しない",
                inclusion
                    .generators()
                    .iter()
                    .flat_map(|g| [g.source().clone(), g.target().clone()])
                    .collect(),
            ));
        }
        let restricted =
            construction::restrict_assembled(&construction, local_image, c).map_err(failure)?;
        let Some(restriction) = construction::maps::assembled_map(
            inputs,
            std::sync::Arc::new(restricted),
            local.clone(),
            inverse,
            c,
        )
        .map_err(failure)?
        else {
            return Ok(rejected(
                "全体からの再制限が局所のconfigurationへ戻らない",
                local.base().known().family().to_vec(),
            ));
        };
        let action = inclusion.action();
        for fact in local.base().known().family() {
            tick(c)?;
            let image = action
                .image(fact)
                .ok_or(internal!("包含の作用に原始位置がない"))?;
            if restriction.candidate().image(image) != Some(fact) {
                return Ok(rejected(
                    "再制限と包含の合成が局所で恒等でない",
                    vec![fact.clone(), image.clone()],
                ));
            }
        }
        inclusions.push(inclusion);
        restrictions.push(restriction);
    }
    tick(c)?;
    Ok(Preparation::Ready(Model {
        construction,
        fragments,
        overrides: std::sync::Arc::new(overrides),
        support: support.into_iter().collect(),
        inclusions,
        restrictions,
    }))
}
fn contains_term(value: &Scalar, c: &Control) -> Result<bool, ValidationFailure> {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        tick(c)?;
        match value {
            Scalar::Term(_) => return Ok(true),
            Scalar::Tuple(items)
            | Scalar::List { items, .. }
            | Scalar::Set { items, .. }
            | Scalar::Data { args: items, .. } => pending.extend(items),
            Scalar::Option { value: Some(v), .. } => pending.push(v),
            Scalar::Map { pairs, .. } => {
                for (k, v) in pairs {
                    pending.push(k);
                    pending.push(v);
                }
            }
            _ => {}
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_common::canonical::Json;
    use archsig_input::input::check_inputs;
    use std::sync::Arc;
    mod fixture {
        include!("../../../../tests/common/model_assembly_data.rs");
    }
    fn inputs(edit: impl FnOnce(String) -> String) -> Arc<CheckedInputs> {
        Arc::new(check_inputs(fixture::input(edit), &Control::unlimited()).unwrap())
    }
    fn fact(id: &str) -> Fact {
        Fact::from(archsig_input::archmap::FactData {
            snapshot: "v".into(),
            subject: id.into(),
            field: None,
            atom: None,
        })
    }
    fn build(inputs: &Arc<CheckedInputs>, pairs: &[(Fact, Fact)]) -> Preparation {
        compile(
            inputs,
            "Assembly",
            &fact("G"),
            &[fact("A"), fact("B")],
            pairs,
            &Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn empty_interface_tuple_keeps_distinct_fragments_and_binding_errors_are_rejected() {
        let source = fixture::input(|s| s);
        let law = String::from_utf8(source.law().bytes().to_vec())
            .unwrap()
            .replace(
                "List<(Part,Part)> = list<(Part,Part)>[(ma,mb)]",
                "Unit = unit",
            );
        let source = archsig_input::input::InputSources::from_bytes(
            vec![source.definitions()[0].bytes().to_vec()],
            law.into_bytes(),
            source.archmap().bytes().to_vec(),
        );
        let checked = check_inputs(source.clone(), &Control::unlimited()).unwrap();
        let result = crate::observed::evaluate_observed_bytes(
            source,
            &[fixture::ASSEMBLE],
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(
            result.answers[0].status,
            Decision::Established,
            "{:?}",
            result.issues
        );
        for ask in [
            fixture::ASSEMBLE.replace(",mb=@v/mb", ""),
            fixture::ASSEMBLE.replace("along=Assembly.interfaces", "along=Assembly.amount"),
            fixture::ASSEMBLE.replace("on=@v/G", "on=@v/a"),
        ] {
            assert!(
                crate::observed::request::resolve_observed_requests_controlled(
                    checked.law(),
                    checked.archmap(),
                    &[&ask],
                    &Control::unlimited()
                )
                .is_err(),
                "{ask}"
            );
        }
    }
    #[test]
    fn stopped_assembly_keeps_prior_answer_without_publishing_partial_model() {
        use std::{cell::Cell, rc::Rc};
        let i = fixture::input(|s| s);
        let asks = ["v=evaluate(Assembly.amount,p=@v/a)", fixture::ASSEMBLE];
        for signal in [
            archsig_common::control::Signal::Int,
            archsig_common::control::Signal::Term,
        ] {
            let reached = Rc::new(Cell::new(0));
            let count = reached.clone();
            let c = Control::new(move |phase| {
                if phase == Checkpoint::ConfigurationMap {
                    count.set(count.get() + 1);
                }
                (count.get() >= 12).then_some(signal)
            });
            let result = crate::observed::evaluate_observed_bytes(i.clone(), &asks, &c).unwrap();
            assert!(reached.get() >= 12);
            assert_eq!(result.answers[0].status, Decision::Established);
            assert!(
                result
                    .answers
                    .iter()
                    .skip(1)
                    .all(|a| a.status != Decision::Established
                        && !a.outputs.contains_key("object")
                        && !a.outputs.contains_key("assembly"))
            );
            assert!(
                result
                    .issues
                    .iter()
                    .any(|r| matches!(r.kind, ReasonKind::Stop(_)))
            );
        }
    }
    #[test]
    fn local_roots_generate_a_new_global_domain_and_transport_known_owners() {
        let i = inputs(|x| x);
        let result = build(&i, &[(fact("ma"), fact("mb"))]);
        let Preparation::Ready(m) = result else {
            panic!("{result:?}")
        };
        let names: BTreeSet<_> = m
            .construction
            .local_domain()
            .known()
            .iter()
            .map(|f| f.subject.as_str())
            .collect();
        assert_eq!(
            names,
            BTreeSet::from(["G", "a", "b", "left", "ma", "right"])
        );
        assert_eq!(m.construction.components().len(), 3);
        assert_eq!(m.inclusions.len(), 2);
        assert_eq!(m.restrictions.len(), 2);
        assert_eq!(m.construction.transported_subject(&fact("mb")), &fact("ma"));
        let owner = m
            .overrides
            .iter()
            .find(|(f, _)| {
                f.subject == "b" && f.field.as_ref().is_some_and(|n| n.short() == "owner")
            })
            .unwrap();
        assert!(matches!(&owner.1,Scalar::Subject{subject,..} if subject=="G"));
        let b = subject(&i, &fact("b")).unwrap();
        assert!(
            matches!(&b.fields.iter().find(|f|f.name.is_owner()).unwrap().slot,Slot::Known{value:archsig_input::archmap::Value::Ref{subject,..},..} if subject=="B")
        );
        assert!(
            m.construction
                .base()
                .known()
                .relations()
                .iter()
                .any(|(a, b)| a.subject == "right"
                    && a.field.as_ref().is_some_and(|n| n.short() == "from")
                    && b == &fact("ma"))
        );
        let readings = crate::construction::readings::object_reading_instances(
            &i,
            &m.construction,
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(readings.objects().len(), 4);
        let arrows = crate::construction::maps::internal_arrows_constructed(
            &i,
            m.construction.clone(),
            &Control::unlimited(),
        )
        .unwrap();
        assert!(arrows.all_preserved(), "{arrows:?}");
        assert_eq!(arrows.arrows().len(), 2);
        let operation = |name: &str| {
            let row = arrows
                .arrows()
                .iter()
                .find(|a| a.arrow().subject == name)
                .unwrap();
            crate::construction::maps::ConfigurationOperation::from_map(
                &i,
                row.map().unwrap(),
                &Control::unlimited(),
            )
            .unwrap()
        };
        let left = operation("left");
        let right = operation("right");
        let composed = left.compose(&i, &right, &Control::unlimited()).unwrap();
        assert_eq!(composed.source().subject(), &fact("a"));
        assert_eq!(composed.target().subject(), &fact("b"));
        assert_eq!(composed.word(), &[fact("left"), fact("right")]);
        composed.recheck(&i, &Control::unlimited()).unwrap();
        let id = crate::construction::maps::identity(
            &i,
            "Assembly",
            "v",
            "G",
            None,
            &Control::unlimited(),
        )
        .unwrap();
        assert!(id.operation().is_some());

        assert_eq!(m.fragments[0].local_domain().known().len(), 4);
        assert_eq!(m.fragments[1].local_domain().known().len(), 4);
        assert!(
            m.support
                .iter()
                .any(|f| f.subject == "mb" && f.field.is_some())
        );
    }
    #[test]
    fn transitive_overlap_cannot_collapse_distinct_local_individuals() {
        let i = inputs(|x| x);
        let result = build(&i, &[(fact("a"), fact("mb")), (fact("ma"), fact("mb"))]);
        assert!(
            matches!(result,Preparation::Rejected(reason) if reason.detail.contains("推移閉包"))
        );
    }
    #[test]
    fn shared_values_are_checked_after_transport_and_unshared_instances_remain_distinct() {
        let i = inputs(|x| x);
        let result = build(&i, &[]);
        let Preparation::Ready(m) = result else {
            panic!("{result:?}")
        };
        assert_eq!(m.construction.components().len(), 4);
        let i = inputs(|map| fixture::atom(map, "mb-quantity", Some(Json::str("1"))));
        let Preparation::Rejected(reason) = build(&i, &[(fact("ma"), fact("mb"))]) else {
            panic!("不一致の実値を要求する")
        };
        assert!(reason.detail.contains("quantity"));
        let (a, b) = reason.values.unwrap();
        assert_eq!(
            BTreeSet::from([a.wire().canonical(), b.wire().canonical()]),
            BTreeSet::from([
                Scalar::Z(0.into()).wire().canonical(),
                Scalar::Z(1.into()).wire().canonical()
            ])
        );
        assert!(
            reason
                .facts
                .iter()
                .any(|f| f.subject == "ma" && f.atom.as_deref() == Some("ma-quantity"))
        );
        assert!(
            reason
                .facts
                .iter()
                .any(|f| f.subject == "mb" && f.atom.as_deref() == Some("mb-quantity"))
        );
    }
    #[test]
    fn public_assembly_keeps_the_transported_owner_in_later_checks() {
        let i = inputs(|x| x);
        let asks = [
            fixture::ASSEMBLE,
            "c=check(Assembly.zero,on=$a.object)",
            "o=evaluate(Assembly.ownerOf,on=$a.object,p=@v/b)",
            "m=check(Assembly.zero,on=$a.assembly.inclusions[0].map.candidate.target)",
            "x=compose($a.assembly.inclusions[0].generators[0].target,then=$a.assembly.inclusions[1].generators[0].target)",
            "l=localize($a.object,law=Assembly.zero)",
            "u=evaluate(Assembly.singleton,p=@v/b)",
            "p=prepare(Assembly.zero,using=Assembly.choose,on=$a.object)",
            "s=solve($p.problem,within=$u.value)",
            "k=candidate($s.solutions,index=0)",
            "v=apply($k.assignment,in=$s.solutions)",
            "t=check(Assembly.zero,on=$v.object)",
            "z=evaluate(Assembly.ownerOf,on=$v.object,p=@v/b)",
        ];
        let control = Control::unlimited();
        let result = crate::observed::evaluate_observed_bytes(i.sources().clone(), &asks, &control)
            .unwrap_or_else(|e| panic!("{:?}", e.wire()));
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            result.issues
        );
        for answer in &result.answers {
            assert_eq!(
                answer.status,
                Decision::Established,
                "{} {:?}",
                answer.id,
                result.issues
            );
        }
        assert!(result.answers[0].outputs.contains_key("assembly"));
        let node = &result.nodes[result.answers[2].outputs["value"].0];
        let value = match node.payload.as_ref() {
            Some(Payload::Scalar(v)) => Some(v),
            Some(Payload::Construction(v)) => v.scalar(),
            _ => None,
        };
        assert!(matches!(value,Some(Scalar::Subject{subject,..}) if subject=="G"));
        let witness = |answer: usize| {
            let Some(Payload::Construction(v)) =
                &result.nodes[result.answers[answer].outputs["object"].0].payload
            else {
                panic!("native object")
            };
            let crate::observed::construction_result::Witness::Architecture(w) = &v.witness else {
                panic!("architecture witness")
            };
            w
        };
        let original = witness(0);
        let applied = witness(10);
        assert_eq!(
            applied.construction().local_domain().known().len(),
            6,
            "元の空rootへ戻さない"
        );
        assert!(
            Arc::ptr_eq(
                &original.shared_construction(),
                &applied.shared_construction()
            ),
            "構成は後続の変更でも共有する"
        );
        assert!(
            std::ptr::eq(original.readings(), applied.readings()),
            "同じ読取りinstanceを深く複製しない"
        );
        let supports: Vec<_> = result
            .nodes
            .iter()
            .filter_map(|n| {
                let Some(Payload::Construction(v)) = &n.payload else {
                    return None;
                };
                let (
                    crate::observed::construction_result::ConstructionData::ConstructedField {
                        ..
                    },
                    crate::observed::construction_result::Witness::Architecture(w),
                ) = (&v.data, &v.witness)
                else {
                    return None;
                };
                Arc::ptr_eq(w, original).then_some(&n.support)
            })
            .collect();
        assert!(supports.len() >= 2);
        assert_eq!(
            supports[0].as_ptr(),
            supports[1].as_ptr(),
            "同じ支持の配列を輸送値ごとに持たない"
        );
    }
    #[test]
    fn original_missing_positions_overlap_conflicts_and_operation_failure_stay_distinct() {
        let missing = inputs(|map| fixture::atom(map, "mb-quantity", None));
        assert!(
            matches!(build(&missing,&[(fact("ma"),fact("mb"))]),Preparation::Missing(facts) if facts.len()==1 && facts[0].subject=="mb" && facts[0].field.as_ref().is_some_and(|f|f.short()=="quantity"))
        );
        let broken = inputs(|map| {
            fixture::atom(
                map,
                "a-links",
                Some(Json::Arr(vec![Json::Arr(vec![
                    Json::str("v"),
                    Json::str("a"),
                ])])),
            )
        });
        assert!(
            matches!(build(&broken,&[(fact("ma"),fact("mb"))]),Preparation::Rejected(detail) if detail.detail.contains("生成操作"))
        );
        let collapsed = inputs(|map| {
            fixture::atom(
                map,
                "a-links",
                Some(Json::Arr(vec![
                    Json::Arr(vec![Json::str("v"), Json::str("ma")]),
                    Json::Arr(vec![Json::str("v"), Json::str("mb")]),
                ])),
            )
        });
        assert!(
            matches!(build(&collapsed,&[(fact("ma"),fact("mb"))]),Preparation::Rejected(detail) if detail.detail.contains("同一視"))
        );
        let conflict = inputs(|map| fixture::atom(map, "mb-quantity", Some(Json::str("1"))));
        for (input, status) in [
            (&missing, Decision::Undetermined),
            (&conflict, Decision::Refuted),
            (&broken, Decision::Refuted),
        ] {
            let result = crate::observed::evaluate_observed_bytes(
                input.sources().clone(),
                &[fixture::ASSEMBLE],
                &Control::unlimited(),
            )
            .unwrap();
            assert_eq!(result.answers[0].status, status, "{:?}", result.issues);
            assert!(!result.answers[0].outputs.contains_key("object"));
            assert!(!result.answers[0].outputs.contains_key("assembly"));
            assert!(
                result
                    .issues
                    .iter()
                    .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
                "{:?}",
                result.issues
            );
            if status == Decision::Undetermined {
                assert!(
                    result
                        .issues
                        .iter()
                        .any(|r| matches!(r.kind, ReasonKind::Missing)
                            && !r.dependencies.is_empty()
                            && r.missing.iter().any(|f| f.subject == "mb"))
                );
            } else {
                assert!(result.issues.iter().any(|r| matches!(
                    r.kind,
                    ReasonKind::ConditionFailed {
                        construction: "model_assembly",
                        ..
                    }
                )));
            }
        }
    }
    #[test]
    fn opaque_fields_report_the_actual_position_type_and_source_without_constructing_a_model() {
        let input = fixture::with_term();
        let result = crate::observed::evaluate_observed_bytes(
            input,
            &[fixture::ASSEMBLE],
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(
            result.answers[0].status,
            Decision::Undetermined,
            "{:?}",
            result.issues
        );
        assert!(!result.answers[0].outputs.contains_key("object"));
        assert!(result.issues.iter().any(|r|matches!(&r.kind,ReasonKind::UnsupportedAlgorithm{question:crate::observed::request::QuestionKind::Assemble,operand_types,method} if method=="finite_local_model_assembly" && matches!(operand_types.as_slice(),[Type::Term(..)])) && matches!(r.location,Some(Location::ArchMap{..})) && !r.dependencies.is_empty()),"{:?}",result.issues);
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_)))
        );
    }
}
