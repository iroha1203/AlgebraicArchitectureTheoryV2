//! owner slotの参照候補を入力制約で全検査する。Graphや評価環境を構築しない。
use archsig_common::{
    canonical::Json,
    control::{CheckFailure, Checkpoint, Control, Signal},
    issue::{Code, Issue},
    types::Type,
};
use archsig_input::{
    archmap::{Fact, FieldAssignment, Slot},
    input::CheckedInputs,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Scope {
    pub snapshots: BTreeSet<String>,
    pub modes: BTreeSet<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeterminedOwners {
    owners: Vec<(Fact, Fact)>,
    scope: Scope,
    support: Vec<Fact>,
}
impl DeterminedOwners {
    pub(crate) fn owners(&self) -> &[(Fact, Fact)] {
        &self.owners
    }
    pub(crate) fn scope(&self) -> &Scope {
        &self.scope
    }
    pub(crate) fn support(&self) -> &[Fact] {
        &self.support
    }
}
#[derive(Debug)]
pub(crate) enum Failure {
    Invalid(String),
    Kernel(String),
    Stopped(Signal),
}
impl From<Signal> for Failure {
    fn from(signal: Signal) -> Self {
        Self::Stopped(signal)
    }
}
fn tick(c: &Control) -> Result<(), Failure> {
    c.checkpoint(Checkpoint::FiniteIteration)?;
    Ok(())
}
fn kernel(message: &str) -> Failure {
    Failure::Kernel(message.into())
}

pub(crate) fn determined_owners(
    inputs: &CheckedInputs,
    fields: &[Fact],
    c: &Control,
) -> Result<Option<DeterminedOwners>, Failure> {
    if fields.is_empty()
        || fields.iter().any(|field| {
            field.atom.is_some() || !field.field.as_ref().is_some_and(|name| name.is_owner())
        })
    {
        return Err(Failure::Invalid("owner補完の元slotが違う".into()));
    }
    let mut modes = BTreeMap::new();
    for origin in inputs.archmap().origins() {
        tick(c)?;
        modes.insert(origin.id.as_str(), origin.mode.wire());
        tick(c)?;
    }
    let mode = |id: &str| {
        modes
            .get(id)
            .copied()
            .ok_or_else(|| kernel("origin が見つからない"))
    };
    let mut field_index = BTreeMap::new();
    tick(c)?;
    for snapshot in inputs.archmap().snapshots() {
        tick(c)?;
        for subject in &snapshot.subjects {
            tick(c)?;
            for field in &subject.fields {
                tick(c)?;
                field_index.insert(
                    (
                        snapshot.id.as_str(),
                        subject.id.as_str(),
                        field.name.as_str(),
                    ),
                    field,
                );
                tick(c)?;
            }
            tick(c)?;
        }
        tick(c)?;
    }
    tick(c)?;
    let mut entities = Vec::new();
    tick(c)?;
    for fact in fields {
        tick(c)?;
        let field = field_index
            .get(&(
                fact.snapshot.as_str(),
                fact.subject.as_str(),
                fact.field
                    .as_ref()
                    .ok_or_else(|| kernel("補完slotに元field名がない"))?
                    .as_str(),
            ))
            .ok_or_else(|| kernel("field がない"))?;
        if field.slot != Slot::Missing {
            return Err(kernel("補完slotが元の有限型の欠測fieldでない"));
        }
        let Type::Ref(ref entity) = field.ty.erase() else {
            return Err(kernel("補完slotが元の有限型の欠測fieldでない"));
        };
        tick(c)?;
        entities.push(entity.clone());
        tick(c)?;
    }
    let mut scope = Scope::default();
    let mut support = Vec::new();
    let mut candidates = vec![Vec::new()];
    for entity in &entities {
        tick(c)?;
        let mut family = Vec::new();
        for snapshot in inputs.archmap().snapshots() {
            tick(c)?;
            scope.snapshots.insert(snapshot.id.clone());
            scope.modes.insert(mode(&snapshot.origin)?.into());
            for subject in &snapshot.subjects {
                tick(c)?;
                if subject.ty == entity.as_str() {
                    let fact = Fact {
                        snapshot: snapshot.id.clone(),
                        subject: subject.id.clone(),
                        field: None,
                        atom: None,
                    };
                    family.push(fact.clone());
                    support.push(fact);
                    scope.modes.insert(mode(&subject.origin)?.into());
                }
                tick(c)?;
            }
            tick(c)?;
        }
        let mut next = Vec::new();
        for prefix in &candidates {
            for value in &family {
                tick(c)?;
                let mut row = prefix.clone();
                row.push(value.clone());
                next.push(row);
                tick(c)?;
            }
        }
        candidates = next;
    }
    // 既知Map/ownerの参照制約も候補を制限するため、全入力の支持を保持する。
    for snapshot in inputs.archmap().snapshots() {
        tick(c)?;
        scope.snapshots.insert(snapshot.id.clone());
        scope.modes.insert(mode(&snapshot.origin)?.into());
        for subject in &snapshot.subjects {
            tick(c)?;
            scope.modes.insert(mode(&subject.origin)?.into());
            support.push(Fact {
                snapshot: snapshot.id.clone(),
                subject: subject.id.clone(),
                field: None,
                atom: None,
            });
            for field in &subject.fields {
                tick(c)?;
                if let Slot::Known { atom, origin, .. } = &field.slot {
                    scope.modes.insert(mode(origin)?.into());
                    support.push(Fact {
                        snapshot: snapshot.id.clone(),
                        subject: subject.id.clone(),
                        field: Some(field.name.clone()),
                        atom: Some(atom.clone()),
                    });
                }
            }
        }
    }
    support.sort();
    support.dedup();
    tick(c)?;
    let mut kept = Vec::new();
    for values in candidates {
        tick(c)?;
        let mut pinned = Vec::new();
        for (field, value) in fields.iter().zip(&values) {
            tick(c)?;
            pinned.push(FieldAssignment {
                snapshot: field.snapshot.clone(),
                subject: field.subject.clone(),
                field: field
                    .field
                    .clone()
                    .ok_or_else(|| kernel("補完に元fieldがない"))?
                    .into(),
                value: Json::Arr(vec![Json::str(&value.snapshot), Json::str(&value.subject)]),
            });
        }
        tick(c)?;
        match archsig_input::archmap::check_completion_with_values::<CheckFailure<Box<Issue>>>(
            &inputs.archmap().snapshots(),
            &inputs.law().definitions(),
            &pinned,
            c,
        ) {
            Ok(()) => kept.push(values),
            Err(CheckFailure::Input(issue)) if issue.code == Code::InconsistentObservation => (),
            Err(CheckFailure::Stopped(signal)) => return Err(Failure::Stopped(signal)),
            Err(CheckFailure::Input(issue)) => {
                return Err(Failure::Kernel(format!(
                    "参照補完候補の元入力検査: {}",
                    issue.message
                )));
            }
        }
        tick(c)?;
    }
    if kept.is_empty() {
        return Err(kernel("検査済み入力の参照補完全域が空になった"));
    }
    tick(c)?;
    if kept.len() != 1 {
        return Ok(None);
    }
    let mut owners = Vec::new();
    for (field, value) in fields.iter().zip(kept.remove(0)) {
        c.checkpoint(Checkpoint::Completion)?;
        owners.push((field.clone(), value));
    }
    Ok(Some(DeterminedOwners {
        owners,
        scope,
        support,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_input::input::{InputSources, check_inputs};
    #[allow(dead_code)]
    mod fixture {

        include!("../../../tests/common/reference_completions.rs");
    }
    fn example(unique: bool, multiple: bool, peer: bool) -> InputSources {
        let input = fixture::input(fixture::SCRIPT, peer, false);
        let mut map = String::from_utf8(input.archmap().bytes().to_vec()).unwrap();
        map = map.replace(r#"{"id":"item-owner","subject":"item","field":"Refs.Sample.owner","value":["v","A"],"origin":"v"},"#, "");
        if multiple {
            map = map.replace(r#"{"id":"other-owner","subject":"other","field":"Refs.Sample.owner","value":["v","A"],"origin":"v"}"#, "");
        }
        if unique {
            map = map.replace(r#"{"id":"B","type":"Refs.Root","origin":"v"},"#, "");
        }
        InputSources::from_bytes(
            input
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            input.law().bytes().to_vec(),
            map.into_bytes(),
        )
    }
    fn fields(inputs: &CheckedInputs) -> Vec<Fact> {
        inputs
            .archmap()
            .snapshots()
            .iter()
            .flat_map(|s| &s.subjects)
            .flat_map(|s| {
                s.fields
                    .iter()
                    .filter(|f| f.name.is_owner() && f.slot == Slot::Missing)
                    .map(|f| Fact {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        field: Some(f.name.clone()),
                        atom: None,
                    })
            })
            .collect()
    }
    #[test]
    fn input_only_owner_completion_matches_previous_environment_route() {
        for (sources, unique, count) in [
            (example(true, false, false), true, 1),
            (example(true, true, false), true, 2),
            (example(false, false, false), false, 1),
            (example(false, true, true), false, 2),
            (fixture::constrained(true), true, 1),
        ] {
            let inputs = check_inputs(sources, &Control::unlimited()).unwrap();
            let fields = fields(&inputs);
            assert_eq!(fields.len(), count);
            let new = determined_owners(&inputs, &fields, &Control::unlimited()).unwrap();
            let old = crate::observed::owner_completion_legacy::determined_owners(
                &inputs,
                &fields,
                &Control::unlimited(),
            )
            .unwrap();
            assert_eq!(new.is_some(), unique);
            assert_eq!(old.is_some(), unique);
            if let (Some(new), Some(old)) = (new, old) {
                assert_eq!(new.owners(), old.owners());
                assert_eq!(new.support(), old.support());
                assert_eq!(new.scope.snapshots, old.scope().snapshots);
                assert_eq!(new.scope.modes, old.scope().modes);
                assert!(old.scope().readings.is_empty());
                assert!(old.scope().quantifiers.is_empty());
                assert!(old.scope().completions);
                assert!(!old.scope().assignments);
                for (field, owner) in new.owners() {
                    assert!(field.field.as_ref().unwrap().is_owner());
                    assert!(owner.field.is_none() && owner.atom.is_none());
                }
            }
        }
    }
    #[test]
    fn every_owner_completion_checkpoint_propagates_both_signals() {
        use std::{cell::Cell, rc::Rc};
        let inputs = check_inputs(example(true, true, false), &Control::unlimited()).unwrap();
        let fields = fields(&inputs);
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        });
        determined_owners(&inputs, &fields, &control).unwrap();
        assert!(count.get() > fields.len());
        for stop in 1..=count.get() {
            for signal in [Signal::Int, Signal::Term] {
                let count = Rc::new(Cell::new(0));
                let seen = count.clone();
                let control = Control::new(move |_| {
                    seen.set(seen.get() + 1);
                    (seen.get() == stop).then_some(signal)
                });
                assert!(
                    matches!(determined_owners(&inputs, &fields, &control), Err(Failure::Stopped(found)) if found == signal)
                );
                assert_eq!(count.get(), stop);
            }
        }
    }
}
