//! 検査済み入力から構築する索引と固定した評価入力。
use super::*;

pub(crate) struct InputIndexes<'a> {
    pub inputs: &'a CheckedInputs,
    pub(super) object: Option<std::sync::Arc<crate::observed::object_evaluate::ObjectDomain>>,
    pub(super) object_instance: Option<&'a crate::construction::readings::ObjectInstance>,
    pub(super) object_values: Option<&'a crate::observed::object_view_family::FiniteViewAssignment>,
    pub(super) original_requests: Option<&'a [Request]>,
    pub(super) subjects: BTreeMap<(String, String), &'a Subject>,
    pub(super) fields:
        BTreeMap<(String, String, crate::names::QualifiedName), &'a crate::archmap::Field>,
    pub(super) atoms: BTreeMap<String, Fact>,
    pub(super) modes: BTreeMap<String, &'static str>,
    pub(super) snapshot_origins: BTreeMap<String, String>,
    // 候補ごとに独立したEnvironmentへ一度だけ設定し、観測cacheと共有しない。
    pub(super) primitive_valuation: Option<BTreeMap<Fact, Scalar>>,
    // 整数changeの式を読む内部環境。観測slotと元parameterを区別する。
    pub(super) affine_valuation: BTreeMap<Fact, crate::observed::affine::Form>,
    pub(super) primitive_input_valuation: Option<BTreeMap<Fact, Value>>,
}

impl<'a> InputIndexes<'a> {
    pub fn subject(&self, snapshot: &str, id: &str) -> Result<&'a Subject, String> {
        self.subjects
            .get(&(snapshot.into(), id.into()))
            .copied()
            .ok_or_else(|| "検査済み subject が見つからない".into())
    }
    pub fn origin_mode(&self, id: &str) -> Result<&'static str, String> {
        self.modes
            .get(id)
            .copied()
            .ok_or_else(|| "origin が見つからない".into())
    }
    pub fn field(
        &self,
        state: &EvaluationState,
        snapshot: &str,
        subject: &str,
        name: &str,
    ) -> Result<&'a crate::archmap::Field, String> {
        let field = self
            .fields
            .get(&(snapshot.into(), subject.into(), name.into()))
            .copied()
            .ok_or_else(|| String::from("field がない"))?;
        if matches!(field.slot, Slot::Missing)
            && state
                .architecture_value(&Fact {
                    snapshot: snapshot.into(),
                    subject: subject.into(),
                    field: Some(field.name.clone()),
                    atom: None,
                })
                .is_none()
        {
            if let Some(reads) = state.missing_slot_reads.borrow_mut().as_mut() {
                reads.insert(Fact {
                    snapshot: snapshot.into(),
                    subject: subject.into(),
                    field: Some(field.name.clone()),
                    atom: None,
                });
            }
        }
        if let Some(reads) = state.primitive_reads.borrow_mut().as_mut() {
            reads.insert(Fact {
                snapshot: snapshot.into(),
                subject: subject.into(),
                field: Some(field.name.clone()),
                atom: None,
            });
        }
        Ok(field)
    }
    pub fn scope(
        &self,
        s: &Subject,
        reading: &str,
        atom_origin: Option<&str>,
    ) -> Result<Scope, String> {
        let mut scope = self.subject_scope(s)?;
        scope.readings.insert(reading.into());
        if let Some(origin) = atom_origin {
            scope.modes.insert(self.origin_mode(origin)?.into());
        }
        Ok(scope)
    }
    pub(in crate::observed) fn subject_scope(&self, s: &Subject) -> Result<Scope, String> {
        let mut scope = Scope::default();
        scope.snapshots.insert(s.snapshot.clone());
        scope.modes.insert(self.origin_mode(&s.origin)?.into());
        let origin = self
            .snapshot_origins
            .get(&s.snapshot)
            .ok_or("snapshot がない")?;
        scope.modes.insert(self.origin_mode(origin)?.into());
        Ok(scope)
    }
}

impl<'a> InputIndexes<'a> {
    pub fn new(inputs: &'a CheckedInputs, control: &Control) -> Result<Self, Signal> {
        let mut subjects = BTreeMap::new();
        let mut fields = BTreeMap::new();
        let mut atoms = BTreeMap::new();
        let mut modes = BTreeMap::new();
        let mut snapshot_origins = BTreeMap::new();
        for origin in inputs.archmap().origins() {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            modes.insert(origin.id.clone(), origin.mode.wire());
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        for snapshot in inputs.archmap().snapshots() {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            snapshot_origins.insert(snapshot.id.clone(), snapshot.origin.clone());
            for s in &snapshot.subjects {
                control.checkpoint(Checkpoint::FiniteIteration)?;
                subjects.insert((s.snapshot.clone(), s.id.clone()), s);
                for field in &s.fields {
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                    fields.insert(
                        (s.snapshot.clone(), s.id.clone(), field.name.clone()),
                        field,
                    );
                    if let Slot::Known { atom, pointer, .. } = &field.slot {
                        atoms.insert(
                            pointer.clone(),
                            Fact {
                                snapshot: s.snapshot.clone(),
                                subject: s.id.clone(),
                                field: Some(field.name.clone()),
                                atom: Some(atom.clone()),
                            },
                        );
                    }
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                }
                control.checkpoint(Checkpoint::FiniteIteration)?;
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        Ok(Self {
            inputs,
            object: None,
            object_instance: None,
            object_values: None,
            subjects,
            fields,
            atoms,
            original_requests: None,
            modes,
            snapshot_origins,
            primitive_valuation: None,
            affine_valuation: BTreeMap::new(),
            primitive_input_valuation: None,
        })
    }
}

impl InputIndexes<'_> {
    pub(super) fn reference_roster(
        &self,
        control: &Control,
        entity: &str,
        observer: &mut dyn FnMut(usize),
    ) -> Result<crate::observed::finite::Enumeration, ValidationFailure> {
        use crate::definition::PrimitiveSignature;
        if !matches!(
            self.inputs
                .law()
                .definitions()
                .declarations()
                .get(entity)
                .map(|d| &d.signature),
            Some(
                PrimitiveSignature::Entity { .. }
                    | PrimitiveSignature::Arrow { .. }
                    | PrimitiveSignature::Correspondence { .. }
            )
        ) {
            return Err("plain参照族の元完全型名が原始参照型でない".into());
        }
        let mut family = crate::observed::finite::Enumeration::default();
        for (index, snapshot) in self.inputs.archmap().snapshots().iter().enumerate() {
            observer(index);
            control.checkpoint(Checkpoint::FiniteIteration)?;
            family.scope.snapshots.insert(snapshot.id.clone());
            family
                .scope
                .modes
                .insert(self.origin_mode(&snapshot.origin)?.into());
            for subject in &snapshot.subjects {
                control.checkpoint(Checkpoint::FiniteIteration)?;
                if subject.ty == entity {
                    family.values.push(Scalar::Subject {
                        snapshot: snapshot.id.clone(),
                        subject: subject.id.clone(),
                        entity: entity.into(),
                    });
                    family
                        .scope
                        .modes
                        .insert(self.origin_mode(&subject.origin)?.into());
                    family.support.push(Fact {
                        snapshot: snapshot.id.clone(),
                        subject: subject.id.clone(),
                        field: None,
                        atom: None,
                    });
                }
                control.checkpoint(Checkpoint::FiniteIteration)?;
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        Ok(family)
    }
}
