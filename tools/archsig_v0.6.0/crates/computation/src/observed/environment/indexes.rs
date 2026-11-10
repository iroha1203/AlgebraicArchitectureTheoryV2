//! 検査済み入力から構築する索引と固定した評価入力。
use super::*;
use archsig_common::internal::InternalError;
use std::collections::HashMap;

/// 候補値を元入力で読むか、選択対象への明示変更として読むか。
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ValuationDomain {
    Input,
    Object,
}

pub(crate) struct InputIndexes<'a> {
    pub inputs: &'a CheckedInputs,
    pub(super) object: Option<std::sync::Arc<crate::observed::object_evaluate::ObjectDomain>>,
    pub(super) object_instance: Option<&'a crate::construction::readings::ObjectInstance>,
    pub(super) object_values: Option<&'a crate::observed::object_view_family::FiniteViewAssignment>,
    pub(super) original_requests: Option<&'a [Request]>,
    fixed: std::sync::Arc<FixedInputIndexes<'a>>,
    // 検査済み入力の Map 値を入力内の値ごとに共有する。
    observed_maps: data::InputMapCache,
    // 候補ごとに独立したEnvironmentへ一度だけ設定し、観測cacheと共有しない。
    pub(super) primitive_valuation: Option<std::sync::Arc<BTreeMap<Fact, Scalar>>>,
    pub(super) valuation_domain: ValuationDomain,
    pub(super) fixed_primitive_valuation: bool,
    // 整数changeの式を読む内部環境。観測slotと元parameterを区別する。
    pub(super) affine_valuation: BTreeMap<Fact, crate::observed::affine::Form>,
    // 参照構造とprobeの再検査に必要なdecoded値。完成候補の純leafは保存しない。
    // None（候補でない）とSome(empty)は区別する。
    pub(super) primitive_input_valuation: Option<BTreeMap<Fact, Value>>,
}

/// 同じCheckedInputsの全候補で変わらない索引。可変の候補値・評価cacheを含めない。
pub(crate) struct FixedInputIndexes<'a> {
    pub(super) subjects: BTreeMap<(&'a str, &'a str), &'a Subject>,
    pub(super) subjects_by_type: HashMap<(&'a str, &'a str), Vec<(usize, &'a Subject)>>,
    pub(super) fields: HashMap<(&'a str, &'a str, &'a str), &'a archsig_input::archmap::Field>,
    pub(super) atoms: HashMap<(&'a str, &'a str), Fact>,
    pub(super) modes: BTreeMap<String, &'static str>,
    pub(super) snapshot_origins: BTreeMap<String, String>,
    pub(super) roster: archsig_input::archmap::value::Roster<'a>,
}
impl<'a> std::ops::Deref for InputIndexes<'a> {
    type Target = FixedInputIndexes<'a>;
    fn deref(&self) -> &Self::Target {
        &self.fixed
    }
}
impl<'a> InputIndexes<'a> {
    /// 不変索引だけを共有し、候補値・対象選択は元の空状態から始める。
    pub(super) fn fresh(&self) -> Self {
        Self {
            inputs: self.inputs,
            valuation_domain: self.valuation_domain,
            fixed: self.fixed.clone(),
            observed_maps: RefCell::default(),
            object: None,
            object_instance: None,
            object_values: None,
            original_requests: None,
            primitive_valuation: None,
            fixed_primitive_valuation: false,
            affine_valuation: BTreeMap::new(),
            primitive_input_valuation: None,
        }
    }
}

impl<'a> InputIndexes<'a> {
    pub fn subject(&self, snapshot: &str, id: &str) -> Result<&'a Subject, InternalError> {
        self.subjects
            .get(&(snapshot, id))
            .copied()
            .ok_or_else(|| internal!("検査済み subject が見つからない"))
    }
    pub fn origin_mode(&self, id: &str) -> Result<&'static str, InternalError> {
        self.modes
            .get(id)
            .copied()
            .ok_or_else(|| internal!("origin が見つからない"))
    }
    pub fn field(
        &self,
        state: &EvaluationState,
        snapshot: &str,
        subject: &str,
        name: &str,
    ) -> Result<&'a archsig_input::archmap::Field, InternalError> {
        let field = self
            .fields
            .get(&(snapshot, subject, name))
            .copied()
            .ok_or_else(|| internal!("field がない"))?;
        if matches!(field.slot, Slot::Missing)
            && state
                .architecture_value_reference(&Fact::from(archsig_input::archmap::FactData {
                    snapshot: snapshot.into(),
                    subject: subject.into(),
                    field: Some(field.name.clone()),
                    atom: None,
                }))
                .is_none()
        {
            if let Some(reads) = state.missing_slot_reads.borrow_mut().as_mut() {
                reads.insert(Fact::from(archsig_input::archmap::FactData {
                    snapshot: snapshot.into(),
                    subject: subject.into(),
                    field: Some(field.name.clone()),
                    atom: None,
                }));
            }
        }
        if let Some(reads) = state.primitive_reads.borrow_mut().as_mut() {
            reads.insert(Fact::from(archsig_input::archmap::FactData {
                snapshot: snapshot.into(),
                subject: subject.into(),
                field: Some(field.name.clone()),
                atom: None,
            }));
        }
        Ok(field)
    }
    pub(in crate::observed) fn observed_scalar(
        &self,
        field: &'a archsig_input::archmap::Field,
        control: &Control,
    ) -> Result<Option<Scalar>, ValidationFailure> {
        let Slot::Known { value, .. } = &field.slot else {
            return Err(internal!("既知の原始slotがない").into());
        };
        match value {
            Value::Bool(_) | Value::Ref { .. } => {
                scalar_from(value, &field.ty, self.inputs.law(), control)
            }
            _ => self.raw_observed_scalar(field, control),
        }
    }

    pub(super) fn raw_observed_scalar(
        &self,
        field: &'a archsig_input::archmap::Field,
        control: &Control,
    ) -> Result<Option<Scalar>, ValidationFailure> {
        let Slot::Known { value, .. } = &field.slot else {
            return Err(internal!("既知の原始slotがない").into());
        };
        data::from_input_with_maps(
            value,
            &field.ty.erase(),
            self.inputs.law(),
            control,
            Some(&self.observed_maps),
        )
    }
    pub fn scope(
        &self,
        s: &Subject,
        reading: &str,
        atom_origin: Option<&str>,
    ) -> Result<Scope, InternalError> {
        let mut scope = self.subject_scope(s)?;
        scope.readings.insert(reading.into());
        if let Some(origin) = atom_origin {
            scope.modes.insert(self.origin_mode(origin)?.into());
        }
        Ok(scope)
    }
    pub(in crate::observed) fn subject_scope(&self, s: &Subject) -> Result<Scope, InternalError> {
        let mut scope = Scope::default();
        scope.snapshots.insert(s.snapshot.clone());
        scope.modes.insert(self.origin_mode(&s.origin)?.into());
        let origin = self
            .snapshot_origins
            .get(&s.snapshot)
            .ok_or(internal!("snapshot がない"))?;
        scope.modes.insert(self.origin_mode(origin)?.into());
        Ok(scope)
    }
}

impl<'a> InputIndexes<'a> {
    pub fn new(inputs: &'a CheckedInputs, control: &Control) -> Result<Self, Signal> {
        let mut subjects = BTreeMap::new();
        let mut subjects_by_type = HashMap::<_, Vec<_>>::new();
        let mut fields = HashMap::new();
        let mut atoms = HashMap::new();
        let mut modes = BTreeMap::new();
        let mut snapshot_origins = BTreeMap::new();
        let mut roster_types = HashMap::new();
        for origin in inputs.archmap().origins() {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            modes.insert(origin.id.clone(), origin.mode.wire());
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        control.checkpoint(Checkpoint::FiniteIteration)?;
        for snapshot in inputs.archmap().snapshots() {
            control.checkpoint(Checkpoint::FiniteIteration)?;
            snapshot_origins.insert(snapshot.id.clone(), snapshot.origin.clone());
            for (position, s) in snapshot.subjects.iter().enumerate() {
                control.checkpoint(Checkpoint::FiniteIteration)?;
                subjects_by_type
                    .entry((s.snapshot.as_str(), s.ty.as_str()))
                    .or_default()
                    .push((position, s));
                subjects.insert((s.snapshot.as_str(), s.id.as_str()), s);
                roster_types.insert((s.snapshot.as_str(), s.id.as_str()), s.ty.as_str());
                for field in &s.fields {
                    control.checkpoint(Checkpoint::FiniteIteration)?;
                    fields.insert(
                        (s.snapshot.as_str(), s.id.as_str(), field.name.as_str()),
                        field,
                    );
                    if let Slot::Known { atom, pointer, .. } = &field.slot {
                        atoms.insert(
                            (s.snapshot.as_str(), pointer.as_str()),
                            Fact::from(archsig_input::archmap::FactData {
                                snapshot: s.snapshot.clone(),
                                subject: s.id.clone(),
                                field: Some(field.name.clone()),
                                atom: Some(atom.clone()),
                            }),
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
            valuation_domain: ValuationDomain::Input,
            object: None,
            object_instance: None,
            object_values: None,
            fixed: std::sync::Arc::new(FixedInputIndexes {
                subjects,
                subjects_by_type,
                fields,
                atoms,
                modes,
                snapshot_origins,
                roster: archsig_input::archmap::value::Roster {
                    types: roster_types,
                },
            }),
            observed_maps: RefCell::default(),
            original_requests: None,
            primitive_valuation: None,
            fixed_primitive_valuation: false,
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
        use archsig_input::definition::PrimitiveSignature;
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
            return Err(internal!("plain参照族の元完全型名が原始参照型でない").into());
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
                    family
                        .support
                        .push(Fact::from(archsig_input::archmap::FactData {
                            snapshot: snapshot.id.clone(),
                            subject: subject.id.clone(),
                            field: None,
                            atom: None,
                        }));
                }
                control.checkpoint(Checkpoint::FiniteIteration)?;
            }
            control.checkpoint(Checkpoint::FiniteIteration)?;
        }
        Ok(family)
    }
}

#[cfg(test)]
mod tests;
