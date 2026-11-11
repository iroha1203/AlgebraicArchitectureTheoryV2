//! 担当別の原始モデルと明示対応から、同じ型付き構成を生成する。
use super::{data, environment::InputIndexes, result::*, value_transport};
use crate::construction::{self, ConfigurationConstruction, ConstructionFailure};
use archsig_common::{
    control::{Checkpoint, Control},
    issue::Location,
    types::Type,
};
use archsig_input::{
    archmap::{Slot, Subject, Value},
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
    pub affects_layout: bool,
    pub detail: String,
    pub location: Location,
    pub operand_types: Vec<Type>,
    pub position: Option<Fact>,
}
fn unsupported(s: &Subject, f: &archsig_input::archmap::Field, detail: String) -> Preparation {
    match &f.slot {
        Slot::Known { pointer, .. } => Preparation::Unsupported(Unsupported {
            affects_layout: false,
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
    pub affects_layout: bool,
    pub detail: String,
    pub facts: Vec<Fact>,
    pub values: Option<(Scalar, Scalar)>,
    pub repaired: [Option<Fact>; 2],
    pub location: Option<Location>,
}
pub(super) fn rejected(detail: impl Into<String>, facts: Vec<Fact>) -> Preparation {
    Preparation::Rejected(rejection(detail, facts, false))
}
fn rejection(detail: impl Into<String>, facts: Vec<Fact>, affects_layout: bool) -> Rejection {
    Rejection {
        affects_layout,
        detail: detail.into(),
        facts,
        values: None,
        repaired: [None, None],
        location: None,
    }
}
fn rejected_layout(detail: impl Into<String>, facts: Vec<Fact>) -> Preparation {
    Preparation::Rejected(rejection(detail, facts, true))
}
pub(super) fn layout_root_condition(
    indexes: &InputIndexes<'_>,
    target: &Fact,
    roots: &[Fact],
    c: &Control,
) -> Result<Option<Rejection>, ValidationFailure> {
    if roots.is_empty() {
        return Ok(Some(rejection("担当集合が空", vec![target.clone()], true)));
    }
    let root_subject = indexes.subject(&target.snapshot, &target.subject)?;
    let mut seen = BTreeSet::new();
    for root in roots {
        tick(c)?;
        if root == target
            || !seen.insert(root)
            || indexes.subject(&root.snapshot, &root.subject)?.ty != root_subject.ty
        {
            return Ok(Some(rejection(
                "担当rootは同一snapshot・同一型の異なるrootを要求する",
                vec![root.clone(), target.clone()],
                true,
            )));
        }
    }
    Ok(None)
}
pub(super) fn observed_fact(s: &Subject, f: &archsig_input::archmap::Field) -> Fact {
    let mut fact = field_fact(s, f);
    if let Slot::Known { atom, .. } = &f.slot {
        fact.atom = Some(atom.clone());
    }
    fact
}
pub(super) fn counterexample_facts(
    rows: &[crate::construction::maps::Counterexample],
) -> Vec<Fact> {
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
    pub fragments: Vec<std::sync::Arc<ConfigurationConstruction>>,
    pub overrides: std::sync::Arc<Vec<(Fact, Scalar)>>,
    pub repaired_values: Vec<(Fact, Scalar)>,
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
pub(super) fn subject<'a>(
    inputs: &'a CheckedInputs,
    fact: &Fact,
) -> Result<&'a Subject, ValidationFailure> {
    inputs
        .archmap()
        .snapshots()
        .iter()
        .find(|s| s.id == fact.snapshot)
        .and_then(|s| s.subjects.iter().find(|s| s.id == fact.subject))
        .ok_or_else(|| internal!("組立ての型付き参照先がない").into())
}
pub(super) fn field_fact(s: &Subject, field: &archsig_input::archmap::Field) -> Fact {
    Fact::from(archsig_input::archmap::FactData {
        snapshot: s.snapshot.clone(),
        subject: s.id.clone(),
        field: Some(field.name.clone()),
        atom: None,
    })
}
/// 同値類のrootだけを保持し、全対・全域の積を作らない。
pub(super) fn link_shared(
    parent: &mut BTreeMap<Fact, Fact>,
    a: &Fact,
    b: &Fact,
    c: &Control,
) -> Result<(), ValidationFailure> {
    let a = representative(parent, a, c)?;
    let b = representative(parent, b, c)?;
    let (small, large) = if a.wire().canonical() < b.wire().canonical() {
        (a, b)
    } else {
        (b, a)
    };
    parent.insert(large, small);
    Ok(())
}

pub(super) fn representative(
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
fn selected_field(
    inputs: &CheckedInputs,
    subject: &Subject,
    field: &archsig_input::archmap::Field,
    selected: &BTreeMap<Fact, Scalar>,
    c: &Control,
) -> Result<Option<Scalar>, ValidationFailure> {
    if let Some(value) = selected.get(&field_fact(subject, field)) {
        return Ok(Some(value.clone()));
    }
    let Slot::Known { value, .. } = &field.slot else {
        return Err(internal!("組立ての既知field検査が失われた").into());
    };
    data::from_input(value, &field.ty.erase(), inputs.law(), c)
}

pub(super) fn foreign_snapshot(
    inputs: &CheckedInputs,
    fact: &Fact,
    detail: &str,
) -> Result<Preparation, ValidationFailure> {
    Ok(Preparation::Unsupported(snapshot_problem(
        inputs, fact, detail,
    )?))
}

fn snapshot_problem(
    inputs: &CheckedInputs,
    fact: &Fact,
    detail: &str,
) -> Result<Unsupported, ValidationFailure> {
    let endpoint = subject(inputs, fact)?;
    Ok(Unsupported {
        affects_layout: true,
        detail: detail.into(),
        location: Location::ArchMap {
            pointer: endpoint.pointer.clone(),
            span: None,
        },
        operand_types: vec![Type::Ref(endpoint.ty.to_string())],
        position: None,
    })
}

pub(super) fn layout_snapshot(
    indexes: &InputIndexes<'_>,
    reading: &str,
    target: &Fact,
    roots: &[Fact],
    pairs: &[(Fact, Fact)],
    c: &Control,
) -> Result<Option<Unsupported>, ValidationFailure> {
    let inputs = indexes.inputs;
    let mut root_ids = BTreeSet::from([target.subject.as_str()]);
    for root in roots {
        tick(c)?;
        if root.snapshot != target.snapshot {
            return Ok(Some(snapshot_problem(
                inputs,
                root,
                "担当rootのsnapshotが組立て標識と異なる",
            )?));
        }
        root_ids.insert(root.subject.as_str());
    }
    for member in pairs.iter().flat_map(|(left, right)| [left, right]) {
        tick(c)?;
        if member.snapshot != target.snapshot {
            return Ok(Some(snapshot_problem(
                inputs,
                member,
                "共有対の個体が別snapshotに属する",
            )?));
        }
        let holder = indexes.subject(&member.snapshot, &member.subject)?;
        if let Some((field, _)) =
            construction::owner_slot_for(inputs, holder, None, c).map_err(failure)?
            && matches!(&field.slot, Slot::Known {
                value: Value::Ref { snapshot, .. }, ..
            } if snapshot != &target.snapshot)
        {
            return Ok(Some(snapshot_problem(
                inputs,
                member,
                "共有個体のownerが別snapshotに属する",
            )?));
        }
    }
    let foreign =
        construction::foreign_owned_member(inputs, reading, &target.snapshot, &root_ids, c)
            .map_err(failure)?;
    foreign
        .map(|member| {
            snapshot_problem(
                inputs,
                &member,
                "組立て先または担当の所属個体が別snapshotに属する",
            )
        })
        .transpose()
}

/// Construct a layout after the shared snapshot and root checks.
pub(super) fn compile_same_snapshot(
    inputs: &std::sync::Arc<CheckedInputs>,
    reading: &str,
    target: &Fact,
    roots: &[Fact],
    pairs: &[(Fact, Fact)],
    selected: &BTreeMap<Fact, Scalar>,
    c: &Control,
) -> Result<Preparation, ValidationFailure> {
    tick(c)?;
    let root_subject = subject(inputs, target)?;
    let target_construction =
        construction::construct(inputs, reading, &target.snapshot, &target.subject, c)
            .map_err(failure)?;
    if target_construction.local_domain().known().len() != 1 {
        return Ok(rejected_layout(
            "組立て先rootに既存の所属個体がある",
            target_construction.local_domain().known().to_vec(),
        ));
    }
    if !target_construction.local_domain().is_complete() {
        return Ok(Preparation::Missing(
            target_construction.base().blocking_slots().to_vec(),
        ));
    }
    let mut fragments = Vec::new();
    let mut membership = BTreeMap::new();
    let mut parent = BTreeMap::new();
    let mut missing = BTreeSet::new();
    let mut support = BTreeSet::new();
    for (i, root) in roots.iter().enumerate() {
        tick(c)?;
        let local = construction::construct_fragment(
            inputs,
            &target_construction,
            &root.snapshot,
            &root.subject,
            c,
        )
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
        fragments.push(std::sync::Arc::new(local));
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
            return Ok(rejected_layout(
                "共有対の個体が担当rootに所属しない",
                vec![a.clone(), b.clone()],
            ));
        };
        if ia == ib || subject(inputs, a)?.ty != subject(inputs, b)?.ty {
            return Ok(rejected_layout(
                "共有対は異なる担当の同じ型の個体を要求する",
                vec![a.clone(), b.clone()],
            ));
        }
        link_shared(&mut parent, a, b, c)?;
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
                return Ok(rejected_layout(
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
        for af in &a.fields {
            tick(c)?;
            let Some(av) = selected_field(inputs, a, af, selected, c)? else {
                return Ok(unsupported(
                    a,
                    af,
                    format!("field `{}` の型付き値輸送に未対応", af.name),
                ));
            };
            if contains_term(&av, c)? {
                return Ok(unsupported(
                    a,
                    af,
                    format!("field `{}` は関数値を含む", af.name),
                ));
            }
            let moved_a = value_transport::transport_references(&av, inputs, &transport, c)
                .map_err(failure)?;
            if from == to {
                let position = field_fact(a, af);
                if selected.contains_key(&position) || !data::equal(&av, &moved_a, c)? {
                    overrides.push((position, moved_a));
                }
                continue;
            }
            // 以後は異なる個体間の共有整合だけを調べる。原値はもう保持しない。
            drop(av);
            let b = subject(inputs, to)?;
            let bf = b
                .fields
                .iter()
                .find(|f| f.name == af.name)
                .ok_or(internal!("同じ型の組立てfieldがない"))?;
            let Some(bv) = selected_field(inputs, b, bf, selected, c)? else {
                return Ok(unsupported(
                    a,
                    af,
                    format!("field `{}` の型付き値輸送に未対応", af.name),
                ));
            };
            if contains_term(&bv, c)? {
                return Ok(unsupported(
                    a,
                    af,
                    format!("field `{}` は関数値を含む", af.name),
                ));
            }
            let moved_b = value_transport::transport_references(&bv, inputs, &transport, c)
                .map_err(failure)?;
            drop(bv);
            if !data::equal(&moved_a, &moved_b, c)? {
                let mut facts = Vec::new();
                let mut repaired = [None, None];
                for (index, (subject, field)) in [(a, af), (b, bf)].into_iter().enumerate() {
                    let position = field_fact(subject, field);
                    if selected.contains_key(&position) {
                        repaired[index] = Some(position);
                    } else {
                        facts.push(observed_fact(subject, field));
                    }
                }
                return Ok(Preparation::Rejected(Rejection {
                    affects_layout: false,
                    detail: format!("共有個体のfield `{}` が参照輸送後に一致しない", af.name),
                    facts,
                    values: Some((moved_a, moved_b)),
                    repaired,
                    location: None,
                }));
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
        let local = local.clone();
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
    let repaired_values = overrides
        .iter()
        .filter(|(slot, _)| selected.contains_key(slot))
        .cloned()
        .collect();
    Ok(Preparation::Ready(Model {
        construction,
        fragments,
        repaired_values,
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
        compile_same_snapshot(
            inputs,
            "Assembly",
            &fact("G"),
            &[fact("A"), fact("B")],
            pairs,
            &BTreeMap::new(),
            &Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn identity_subject_transports_list_order_duplicates_and_self_reference() {
        let i = inputs(|s| {
            fixture::without_arrows(fixture::atom(
                s,
                "b-links",
                Some(Json::Arr(
                    ["mb", "b", "mb"]
                        .into_iter()
                        .map(|id| Json::Arr(vec![Json::str("v"), Json::str(id)]))
                        .collect(),
                )),
            ))
        });
        let preparation = build(&i, &[(fact("ma"), fact("mb"))]);
        let Preparation::Ready(model) = preparation else {
            panic!("組立て成立: {preparation:?}")
        };
        let (_, value) = model
            .overrides
            .iter()
            .find(|(slot, _)| {
                slot.subject == "b" && slot.field.as_deref() == Some("Assemble.Part.links")
            })
            .unwrap();
        let Scalar::List { items, .. } = value else {
            panic!("List")
        };
        let subjects = items
            .iter()
            .map(|v| match v {
                Scalar::Subject { subject, .. } => subject.as_str(),
                _ => panic!("Part参照"),
            })
            .collect::<Vec<_>>();
        assert_eq!(subjects, ["ma", "b", "ma"]);
        let original = subject(&i, &fact("b")).unwrap();
        let field = original
            .fields
            .iter()
            .find(|f| f.name == "Assemble.Part.links")
            .unwrap();
        let Slot::Known { value, .. } = &field.slot else {
            panic!("既知原値")
        };
        let raw = data::from_input(value, &field.ty.erase(), i.law(), &Control::unlimited())
            .unwrap()
            .unwrap();
        let Scalar::List { items, .. } = &raw else {
            panic!("原始List")
        };
        assert!(matches!(&items[0], Scalar::Subject {subject,..} if subject == "mb"));
    }
    #[test]
    fn profiles_construct_and_recheck_the_current_domain_once_each() {
        let i = inputs(|s| s);
        let c = Control::unlimited();
        let seen = std::rc::Rc::new(std::cell::Cell::new(0));
        let counter = seen.clone();
        let _observer =
            construction::observe_constructions(move |_| counter.set(counter.get() + 1));
        let profiles =
            construction::profiles::construct_profiles(&i, "Assembly", "v", "A", &c).unwrap();
        assert_eq!(seen.get(), 1);
        assert!(profiles.is_complete());
        seen.set(0);
        profiles.recheck(&i, &c).unwrap();
        assert_eq!(seen.get(), 1);
    }
    #[test]
    fn cross_snapshot_fragments_and_shared_endpoints_are_outside_the_algorithm_not_refuted() {
        for (ask, foreign_owner) in [
            (
                fixture::ASSEMBLE
                    .replace("b=@v/B", "b=@w/B")
                    .replace("mb=@v/mb", "mb=@w/mb"),
                None,
            ),
            (fixture::ASSEMBLE.replace("mb=@v/mb", "mb=@w/mb"), None),
            (fixture::ASSEMBLE.to_owned(), Some("A")),
            (fixture::ASSEMBLE.to_owned(), Some("G")),
        ] {
            let mut input = fixture::with_second_snapshot();
            if let Some(owner) = foreign_owner {
                let map = std::str::from_utf8(input.archmap().bytes()).unwrap();
                let mixed = map.replacen(
                    r#""subject":"a","value":["w","A"]"#,
                    &format!(r#""subject":"a","value":["v","{owner}"]"#),
                    1,
                );
                let mixed = mixed.replace(
                    r#""subject":"left","value":["w","a"]"#,
                    r#""subject":"left","value":["w","ma"]"#,
                );
                assert_ne!(mixed, map);
                input = archsig_input::input::InputSources::from_bytes(
                    vec![input.definitions()[0].bytes().to_vec()],
                    input.law().bytes().to_vec(),
                    mixed.into_bytes(),
                );
            }
            let result =
                crate::observed::evaluate_observed_bytes(input, &[&ask], &Control::unlimited())
                    .unwrap();
            assert_eq!(
                result.answers[0].status,
                Decision::Undetermined,
                "{:?}",
                result.issues
            );
            assert!(!result.answers[0].outputs.contains_key("object"));
            assert!(!result.answers[0].outputs.contains_key("assembly"));
            assert!(result.issues.iter().any(|r| matches!(
                r.kind,
                ReasonKind::UnsupportedAlgorithm { .. }
            ) && !r.dependencies.is_empty()
                && matches!(r.location, Some(Location::ArchMap { .. }))));
            assert!(result.issues.iter().all(|r| !matches!(
                r.kind,
                ReasonKind::Internal(_) | ReasonKind::ConditionFailed { .. }
            )));
        }
    }
    #[test]
    fn unavailable_parameter_handles_block_assembly_before_reading_views() {
        let source = fixture::input(|s| fixture::atom(s, "ma-quantity", None));
        let law = String::from_utf8(source.law().bytes().to_vec())
            .unwrap()
            .replace(
                "view singleton",
                "view pick(p:Part,q:Part):Part=if p.quantity=0 then p else q;\n  view singleton",
            );
        let source = archsig_input::input::InputSources::from_bytes(
            vec![source.definitions()[0].bytes().to_vec()],
            law.into_bytes(),
            source.archmap().bytes().to_vec(),
        );
        let ask = fixture::ASSEMBLE.replace("ma=@v/ma", "ma=$n.value");
        let result = crate::observed::evaluate_observed_bytes(
            source,
            &["n=evaluate(Assembly.pick,p=@v/ma,q=@v/b)", &ask],
            &Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.answers[0].status, Decision::Undetermined);
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_))),
            "{:?}",
            result.issues
        );
        assert!(
            result.answers[1]
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
        );
        assert!(!result.answers[1].outputs.contains_key("object"));
    }
    #[test]
    fn restrictions_share_native_values_and_support_but_keep_exact_slot_provenance() {
        let c = Control::unlimited();
        let inputs = inputs(|s| s);
        let requests = crate::observed::request::resolve_observed_requests_controlled(
            inputs.law(),
            inputs.archmap(),
            &[fixture::ASSEMBLE],
            &c,
        )
        .unwrap();
        let p = crate::observed::PreparedObserved {
            inputs,
            requests,
            object: None,
        };
        let env = crate::observed::environment::Environment::with_prepared(&p, &c).unwrap();
        let mut g = Graph::new(&c);
        g.requests = p.requests().requests().to_vec();
        let answer = crate::observed::build_result::evaluate(
            &p,
            &env,
            &mut g,
            &p.requests().requests()[0],
            &c,
        )
        .unwrap();
        env.validate_answer(&g, &p.requests().requests()[0], &answer)
            .unwrap();
        let Some(Payload::Construction(global)) = &g.get(answer.outputs["object"]).unwrap().payload
        else {
            panic!("native全体を要求する")
        };
        let crate::observed::construction_result::Witness::Architecture(parent) = &global.witness
        else {
            panic!("全体の由来を要求する")
        };
        let crate::observed::construction_result::ConstructionData::Architecture {
            overrides, ..
        } = &global.data
        else {
            panic!("完成対象を要求する")
        };
        assert!(overrides.len() > 1);
        let mut restrictions = Vec::new();
        for node in &g.nodes {
            let Some(Payload::Construction(v)) = &node.payload else {
                continue;
            };
            let crate::observed::construction_result::Witness::Architecture(w) = &v.witness else {
                continue;
            };
            let crate::observed::construction_result::ConstructionData::Architecture {
                overrides: local,
                ..
            } = &v.data
            else {
                continue;
            };
            if w.override_parent().is_some() {
                assert!(Arc::ptr_eq(local, overrides));
                assert_eq!(w.support().as_ptr(), parent.support().as_ptr());
                assert_eq!(node.support.as_ptr(), parent.support().as_ptr());
                restrictions.push(node);
            }
        }
        assert_eq!(restrictions.len(), 2);
        assert_eq!(g.nodes.iter().filter(|n|matches!(&n.payload,Some(Payload::Construction(v)) if matches!(v.data,crate::observed::construction_result::ConstructionData::ConstructedField {..}))).count(),overrides.len());
        // Equal owner values from another slot still cannot replace this slot's proof.
        assert_eq!(
            g.scalar(overrides[0].2).unwrap(),
            g.scalar(overrides[1].2).unwrap()
        );
        let mut forged = restrictions[0].clone();
        let Some(Payload::Construction(v)) = &mut forged.payload else {
            unreachable!()
        };
        let crate::observed::construction_result::ConstructionData::Architecture {
            overrides: changed,
            ..
        } = &mut v.data
        else {
            unreachable!()
        };
        Arc::make_mut(changed)[0].2 = overrides[1].2;
        forged.arguments = v.arguments();
        let error = env.validate(&g, &forged).unwrap_err();
        assert!(format!("{error:?}").contains("輸送値が別由来"), "{error:?}");
    }
    #[test]
    fn unsupported_algebra_keeps_following_object_consumers_dependency_blocked() {
        let source = fixture::input(|s| s);
        let law = String::from_utf8(source.law().bytes().to_vec())
            .unwrap()
            .replace(
                "law required zero",
                "law required sizeLaw(p:Part):count(Part[p.owner])>=1;\n  law required zero",
            );
        let expression = "count(Part[p.owner])>=1";
        let begin = law.find(expression).unwrap();
        let location = Location::Law {
            span: (begin, begin + expression.len()),
        };
        let source = archsig_input::input::InputSources::from_bytes(
            vec![source.definitions()[0].bytes().to_vec()],
            law.into_bytes(),
            source.archmap().bytes().to_vec(),
        );
        let asks = [fixture::ASSEMBLE, "c=check(Assembly.zero,on=$a.object)"];
        let c = Control::unlimited();
        let result = crate::observed::evaluate_observed_bytes(source, &asks, &c).unwrap();
        let reason = result.answers[0].reasons.iter().find(|r| matches!(&r.kind,
            ReasonKind::UnsupportedAlgorithm { method, operand_types, .. }
                if method == "integer_order_equation_presentation" && operand_types == &[Type::Z, Type::Z])).unwrap();
        assert_eq!(reason.location, Some(location.clone()));
        assert!(!reason.dependencies.is_empty());
        let mut found = false;
        for dependency in &reason.dependencies {
            if let Some(Payload::Construction(value)) = &result.nodes[dependency.0].payload
                && let super::super::construction_result::ConstructionData::PolynomialLaw(data) =
                    &value.data
                && let archsig_common::canonical::Json::Obj(ref fields) = data.wire()
                && fields.get("kind") == Some(&archsig_common::canonical::Json::str("source"))
            {
                assert_eq!(
                    fields["location"],
                    archsig_input::result::location_wire(&location)
                );
                let archsig_common::canonical::Json::Arr(bindings) = &fields["bindings"] else {
                    panic!("元束縛")
                };
                let binding = bindings
                    .iter()
                    .find_map(|binding| match binding {
                        archsig_common::canonical::Json::Obj(fields)
                            if fields.get("name")
                                == Some(&archsig_common::canonical::Json::str("p")) =>
                        {
                            Some(fields["value"].exact_node_reference().unwrap())
                        }
                        _ => None,
                    })
                    .expect("未対応となった元個体の束縛");
                let bound = &result.nodes[binding];
                assert_eq!(bound.ty, NodeType::Value(Type::Ref("Assemble.Part".into())));
                let scalar = match &bound.payload {
                    Some(Payload::Scalar(value)) => value,
                    Some(Payload::Construction(value)) => value.scalar().unwrap(),
                    _ => panic!("元subject"),
                };
                assert!(
                    matches!(scalar, Scalar::Subject { snapshot, subject, entity }
                    if snapshot == "v" && ["a", "b", "ma"].contains(&subject.as_str()) && entity == "Assemble.Part")
                );

                found = true;
            }
        }
        assert!(found, "未対応となった元Lawの型付き出現を保持する");
        assert!(
            result.answers[1]
                .reasons
                .iter()
                .any(|r| r.kind == reason.kind
                    && r.location == reason.location
                    && r.dependencies == reason.dependencies)
        );
        assert_eq!(result.answers[1].status, Decision::Undetermined);
        assert!(
            result
                .issues
                .iter()
                .all(|r| !matches!(r.kind, ReasonKind::Internal(_)))
        );
        assert!(
            result.answers[1]
                .reasons
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::DependencyBlocked { .. }))
        );
    }
    #[test]
    fn interface_views_can_read_known_arrow_endpoints() {
        let source = fixture::input(|s| s);
        let law = String::from_utf8(source.law().bytes().to_vec()).unwrap()
            .replace("ma:Part,mb:Part)", "ma:Part,mb:Part,ea:Step,eb:Step)")
            .replace("List<(Part,Part)> = list<(Part,Part)>[(ma,mb)]", "(List<(Part,Part)>,List<(Step,Step)>) = (list<(Part,Part)>[(ea.from,eb.from),(ma,mb)],list<(Step,Step)>[(ea,eb)])");
        let input = archsig_input::input::InputSources::from_bytes(
            vec![source.definitions()[0].bytes().to_vec()],
            law.into_bytes(),
            source.archmap().bytes().to_vec(),
        );
        let ask = fixture::ASSEMBLE.replace("mb=@v/mb)", "mb=@v/b,ea=@v/left,eb=@v/right)");
        let result = crate::observed::evaluate_observed_bytes(input, &[
            "v=evaluate(Assembly.interfaces,a=@v/A,b=@v/B,ma=@v/ma,mb=@v/b,ea=@v/left,eb=@v/right)",
            &ask, "c=check(Assembly.zero,on=$a.object)", "o=evaluate(Assembly.ownerOf,on=$a.object,p=@v/b)"
        ], &Control::unlimited()).unwrap();
        assert!(
            result
                .answers
                .iter()
                .all(|a| a.status == Decision::Established),
            "{:?}",
            result.issues
        );
        let assembly = &result.nodes[result.answers[1].outputs["assembly"].0];
        let Some(Payload::Construction(v)) = &assembly.payload else {
            panic!("native組立てを要求する")
        };
        let crate::observed::construction_result::ConstructionData::Build(d) = &v.data else {
            panic!("組立ての元planを要求する")
        };
        let (interfaces, _) = d
            .assembly_project(&[crate::observed::projection::ProjectionStep::Field(
                "interfaces".into(),
            )])
            .unwrap();
        let scalar = |at: NodeRef| match result.nodes[at.0].payload.as_ref() {
            Some(Payload::Scalar(v)) => v,
            Some(Payload::Construction(v)) => v.scalar().unwrap(),
            _ => panic!("型付き値を要求する"),
        };
        assert!(
            data::equal(
                scalar(result.answers[0].outputs["value"]),
                scalar(interfaces),
                &Control::unlimited()
            )
            .unwrap()
        );
        for atom in ["left-from", "right-from"] {
            assert!(
                result.nodes[interfaces.0]
                    .support
                    .iter()
                    .any(|f| f.atom.as_deref() == Some(atom))
            );
        }
        assert!(
            result.nodes[interfaces.0]
                .support
                .iter()
                .all(|f| f.field.is_none() || f.atom.is_some())
        );
        assert!(
            matches!(scalar(result.answers[3].outputs["value"]),Scalar::Subject {subject,..} if subject=="G")
        );
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
        for (checkpoint, at) in [
            (Checkpoint::ConfigurationMap, 12),
            (Checkpoint::NativeResultNode, 101),
            (Checkpoint::NativeResultNode, 601),
        ] {
            for signal in [
                archsig_common::control::Signal::Int,
                archsig_common::control::Signal::Term,
            ] {
                let reached = Rc::new(Cell::new(0));
                let count = reached.clone();
                let c = Control::new(move |phase| {
                    if phase == checkpoint {
                        count.set(count.get() + 1);
                    }
                    (count.get() >= at).then_some(signal)
                });
                let result =
                    crate::observed::evaluate_observed_bytes(i.clone(), &asks, &c).unwrap();
                assert!(reached.get() >= at);
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
    }

    #[test]
    fn local_roots_generate_a_new_global_domain_and_transport_known_owners() {
        let i = inputs(|x| x);
        let counts = std::rc::Rc::new(std::cell::RefCell::new(BTreeMap::new()));
        let seen = counts.clone();
        let result = {
            let _observer = construction::observe_constructions(move |root| {
                *seen.borrow_mut().entry(root.to_owned()).or_insert(0usize) += 1
            });
            build(&i, &[(fact("ma"), fact("mb"))])
        };
        assert_eq!(
            *counts.borrow(),
            BTreeMap::from([("A".into(), 1), ("B".into(), 1), ("G".into(), 1)])
        );
        let Preparation::Ready(m) = result else {
            panic!("{result:?}")
        };
        for (index, inclusion) in m.inclusions.iter().enumerate() {
            assert!(
                inclusion
                    .operation()
                    .map()
                    .candidate()
                    .source_configuration()
                    .shares_storage_with(m.fragments[index].base().known())
            );
            assert!(
                inclusion
                    .operation()
                    .map()
                    .candidate()
                    .target_configuration()
                    .shares_storage_with(m.construction.base().known())
            );
            assert!(
                m.restrictions[index]
                    .candidate()
                    .target_configuration()
                    .shares_storage_with(m.fragments[index].base().known())
            );
            assert_eq!(
                inclusion.action().universe().as_ptr(),
                m.construction.universe().as_ptr()
            );
            assert_eq!(
                m.restrictions[index].candidate().universe().as_ptr(),
                m.construction.universe().as_ptr()
            );
            assert_eq!(
                m.fragments[index].universe().as_ptr(),
                m.construction.universe().as_ptr()
            );
        }
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
        let model = result
            .nodes
            .iter()
            .find_map(|n| match &n.payload {
                Some(Payload::Construction(v)) => match &v.data {
                    crate::observed::construction_result::ConstructionData::Build(d) => {
                        d.assembly_model()
                    }
                    _ => None,
                },
                _ => None,
            })
            .unwrap();
        for (index, fragment) in model.fragments.iter().enumerate() {
            assert!(Arc::ptr_eq(
                fragment,
                &model.inclusions[index]
                    .operation()
                    .map()
                    .candidate()
                    .source_construction()
                    .unwrap()
            ));
            assert!(result.nodes.iter().any(|n| matches!(&n.payload, Some(Payload::Construction(v)) if matches!(&v.witness, crate::observed::construction_result::Witness::Architecture(w) if Arc::ptr_eq(fragment, &w.shared_construction())))));
        }
        let cores: Vec<_> = result
            .nodes
            .iter()
            .filter_map(|n| match &n.payload {
                Some(Payload::Construction(v)) => match &v.data {
                    crate::observed::construction_result::ConstructionData::InternalArrows(d) => {
                        Some(d.shared_core())
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();
        assert!(
            cores
                .iter()
                .any(|c| Arc::ptr_eq(c, &model.inclusions[0].shared_target()))
        );
        for inclusion in &model.inclusions {
            assert!(
                cores
                    .iter()
                    .any(|c| Arc::ptr_eq(c, &inclusion.shared_source()))
            );
        }
        let lazy: Vec<_> = result
            .nodes
            .iter()
            .filter_map(|n| match &n.payload {
                Some(Payload::Construction(v)) => match &v.data {
                    crate::observed::construction_result::ConstructionData::Build(d) => {
                        d.assembly_action_is_lazy()
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();
        assert_eq!(
            lazy,
            vec![true; 2 * model.fragments.len()],
            "作用表のJSONを描画前に保持しない"
        );
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
    #[test]
    fn changed_integer_and_count_laws_keep_original_occurrences_and_object_references() {
        let mut previous = None;
        let asks = [
            fixture::ASSEMBLE,
            "raw=evaluate(Assembly.sizeOf,p=@v/a)",
            "global=evaluate(Assembly.sizeOf,on=$a.object,p=@v/a)",
        ];
        for clause in [
            "law required zero(p:Part):p.quantity=0;",
            "law required parameter(r:Root,n:Z):n=n;",
            "law required size(p:Part):count(Part[p.owner])>=1;",
            "law required zero(p:Part):p.quantity=0;",
        ] {
            let raw = fixture::input(|s| s);
            let law = String::from_utf8(raw.law().bytes().to_vec())
                .unwrap()
                .replace(
                    "law required zero(p:Part):p.quantity=0;",
                    &format!("{clause} view sizeOf(p:Part):Z=count(Part[p.owner]);"),
                );
            let input = archsig_input::input::InputSources::from_bytes(
                raw.definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                law.into_bytes(),
                raw.archmap().bytes().to_vec(),
            );
            let result = match previous.as_ref() {
                Some(old) => crate::observed::reevaluate_observed_bytes(
                    old,
                    input.clone(),
                    &asks,
                    &Control::unlimited(),
                )
                .unwrap(),
                None => crate::observed::evaluate_observed_bytes(
                    input.clone(),
                    &asks,
                    &Control::unlimited(),
                )
                .unwrap(),
            };
            let cold =
                crate::observed::evaluate_observed_bytes(input, &asks, &Control::unlimited())
                    .unwrap();
            assert_eq!(result.result_wire(), cold.result_wire(), "{clause}");
            let scalar = |answer: usize| match result.nodes
                [result.answers[answer].outputs["value"].0]
                .payload
                .as_ref()
                .unwrap()
            {
                Payload::Scalar(v) => v,
                Payload::Construction(v) => v.scalar().unwrap(),
                _ => panic!("scalar"),
            };
            assert_eq!(scalar(1), &Scalar::Z(2.into()));
            assert_eq!(scalar(2), &Scalar::Z(3.into()));
            assert_eq!(
                result.answers[0].status,
                Decision::Established,
                "{clause}: {:?}",
                result.issues
            );
            assert!(result.answers[0].outputs.contains_key("object"));
            assert!(result.issues.is_empty(), "{clause}: {:?}", result.issues);
            previous = Some(result);
        }
    }
}
