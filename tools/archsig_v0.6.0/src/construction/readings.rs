//! 標準対象域に適用されるLaw/viewの参照束縛と、未代入の全域値parameter。
use super::*;
use crate::law::model::{DeclarationInfo, Param, Signature};
use crate::observed::input::InputBytes;
pub use crate::observed::object_evaluate::{
    ObjectEvaluation, ObjectEvaluationFailure, ObjectEvaluationOutcome, evaluate_object_instance,
};
use maps::ObjectIdentity;

/// 同じ原始owner slotには同じ値を要求する。条件の成立はまだ観測していない。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MembershipCondition {
    slot: FactPointer,
    owner: FactPointer,
}
impl MembershipCondition {
    pub fn slot(&self) -> &FactPointer {
        &self.slot
    }
    pub fn owner(&self) -> &FactPointer {
        &self.owner
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadingObject {
    identity: ObjectIdentity,
    conditions: Vec<MembershipCondition>,
}
impl ReadingObject {
    pub fn identity(&self) -> &ObjectIdentity {
        &self.identity
    }
    pub fn conditions(&self) -> &[MembershipCondition] {
        &self.conditions
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceBinding {
    parameter: Param,
    subject: FactPointer,
}
impl ReferenceBinding {
    pub fn parameter(&self) -> &Param {
        &self.parameter
    }
    pub fn subject(&self) -> &FactPointer {
        &self.subject
    }
}
/// 適用の構成条件。Applicableは式の評価やLaw成立を意味しない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstanceApplication {
    NotApplicable,
    Applicable {
        conditions: Vec<MembershipCondition>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectInstance {
    declaration: DeclarationInfo,
    bindings: Vec<ReferenceBinding>,
    parameters: Vec<Param>,
    applications: Vec<InstanceApplication>,
}
impl ObjectInstance {
    pub fn declaration(&self) -> &DeclarationInfo {
        &self.declaration
    }
    pub fn bindings(&self) -> &[ReferenceBinding] {
        &self.bindings
    }
    /// 各parameterの全型域を保持する。列挙例や評価値ではない。
    pub fn parameters(&self) -> &[Param] {
        &self.parameters
    }
    /// objects()と同じ順序。適用外と条件付きの適用を区別する。
    pub fn applications(&self) -> &[InstanceApplication] {
        &self.applications
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectReadingInstances {
    construction: ConfigurationConstruction,
    source_law: InputBytes,
    local_types: BTreeSet<String>,
    objects: Vec<ReadingObject>,
    declarations: Vec<DeclarationInfo>,
    instances: Vec<ObjectInstance>,
}
impl ObjectReadingInstances {
    pub(crate) fn local_types(&self) -> &BTreeSet<String> {
        &self.local_types
    }
    pub fn construction(&self) -> &ConfigurationConstruction {
        &self.construction
    }
    /// 式・guard・helperの元byte列。metadataのspanはこの入力内の出現を指す。
    pub fn source_law(&self) -> &InputBytes {
        &self.source_law
    }
    pub fn objects(&self) -> &[ReadingObject] {
        &self.objects
    }
    /// 選択scopeの元宣言。独立軸にしないhelperもここに保持する。
    pub fn declarations(&self) -> &[DeclarationInfo] {
        &self.declarations
    }
    pub fn instances(&self) -> &[ObjectInstance] {
        &self.instances
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let actual = object_reading_instances(inputs, &self.construction, control)?;
        if self != &actual {
            return Err(ConstructionFailure::Inconsistent(
                "対象別instanceが現在の入力・原宣言・参照束縛と違う".into(),
            ));
        }
        checkpoint(control)
    }
}
fn checkpoint(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ObjectInstances)
        .map_err(Into::into)
}
fn subject<'a>(
    inputs: &'a CheckedInputs,
    fact: &FactPointer,
    control: &mut Control,
) -> Result<&'a Subject, ConstructionFailure> {
    for snapshot in &inputs.archmap().snapshots {
        checkpoint(control)?;
        if snapshot.id != fact.snapshot {
            continue;
        }
        for subject in &snapshot.subjects {
            checkpoint(control)?;
            if subject.id == fact.subject {
                return Ok(subject);
            }
        }
    }
    Err(ConstructionFailure::Inconsistent(
        "instanceの原始subjectがない".into(),
    ))
}
/// 条件は同じslotごとに共有する。互いに違う値を要求する連言は採用しない。
fn merge_conditions(
    left: &[MembershipCondition],
    right: &[MembershipCondition],
    control: &mut Control,
) -> Result<Option<Vec<MembershipCondition>>, ConstructionFailure> {
    let mut values = BTreeMap::new();
    for condition in left.iter().chain(right) {
        checkpoint(control)?;
        if values
            .get(&condition.slot)
            .is_some_and(|owner| owner != &condition.owner)
        {
            return Ok(None);
        }
        values.insert(condition.slot.clone(), condition.owner.clone());
    }
    checkpoint(control)?;
    Ok(Some(
        values
            .into_iter()
            .map(|(slot, owner)| MembershipCondition { slot, owner })
            .collect(),
    ))
}
#[derive(Clone)]
struct ReferenceChoice {
    subject: FactPointer,
    conditions: Vec<MembershipCondition>,
}
fn owner_condition(
    candidate: &Subject,
    owner: &FactPointer,
    control: &mut Control,
) -> Result<Option<Vec<MembershipCondition>>, ConstructionFailure> {
    // LawのOwned型はownerと同じsnapshotの個体を要求する。
    if candidate.snapshot != owner.snapshot {
        return Ok(None);
    }
    for field in &candidate.fields {
        checkpoint(control)?;
        if field.name.rsplit('.').next() != Some("owner") {
            continue;
        }
        return match &field.slot {
            Slot::Known {
                value: Value::Ref { snapshot, subject },
                ..
            } => Ok((snapshot == &owner.snapshot && subject == &owner.subject).then(Vec::new)),
            Slot::Missing => Ok(Some(vec![MembershipCondition {
                slot: slot(candidate, &field.name),
                owner: owner.clone(),
            }])),
            _ => Err(ConstructionFailure::Inconsistent(
                "Owned instanceのownerが原始参照でない".into(),
            )),
        };
    }
    Err(ConstructionFailure::Inconsistent(
        "Owned instanceのowner slotがない".into(),
    ))
}
fn choices(
    inputs: &CheckedInputs,
    ty: &str,
    local: bool,
    domain: &SubjectDomain,
    control: &mut Control,
) -> Result<Vec<ReferenceChoice>, ConstructionFailure> {
    let mut result = Vec::new();
    if local {
        for fact in domain.known() {
            checkpoint(control)?;
            if subject(inputs, fact, control)?.ty == ty {
                result.push(ReferenceChoice {
                    subject: fact.clone(),
                    conditions: vec![],
                });
            }
        }
        for member in domain.conditional() {
            checkpoint(control)?;
            if subject(inputs, member.subject(), control)?.ty == ty {
                result.push(ReferenceChoice {
                    subject: member.subject().clone(),
                    conditions: vec![MembershipCondition {
                        slot: member.owner_slot().clone(),
                        owner: member.owner().clone(),
                    }],
                });
            }
        }
    } else {
        for snapshot in &inputs.archmap().snapshots {
            checkpoint(control)?;
            for member in &snapshot.subjects {
                checkpoint(control)?;
                if member.ty == ty {
                    result.push(ReferenceChoice {
                        subject: exists(member),
                        conditions: vec![],
                    });
                }
            }
        }
    }
    result.sort_by(|a, b| a.subject.cmp(&b.subject));
    checkpoint(control)?;
    Ok(result)
}
struct Row {
    bindings: Vec<ReferenceBinding>,
    conditions: Vec<MembershipCondition>,
}

/// 対象別読取りの入力を構成する。評価結果・全域延長・ObjectAlgebraの成立は返さない。
pub fn object_reading_instances(
    inputs: &CheckedInputs,
    construction: &ConfigurationConstruction,
    control: &mut Control,
) -> Result<ObjectReadingInstances, ConstructionFailure> {
    checkpoint(control)?;
    let root = construction.root();
    construction.recheck(
        inputs,
        construction.reading(),
        &root.snapshot,
        &root.subject,
        control,
    )?;
    let root_ty = &subject(inputs, root, control)?.ty;
    let visible_namespaces = namespaces(inputs, construction.reading(), control)?;
    let mut local_types = BTreeSet::from([root_ty.clone()]);
    for declaration in inputs.definitions().declarations.values() {
        checkpoint(control)?;
        if visible(inputs, &declaration.name, &visible_namespaces)
            && matches!(&declaration.signature,
            PrimitiveSignature::Entity { owner: Some(owner), .. } | PrimitiveSignature::Arrow { owner, .. }
            if owner == root_ty)
        {
            local_types.insert(declaration.name.clone());
        }
    }
    let mut objects = vec![ReadingObject {
        identity: ObjectIdentity::selected(construction.reading(), root, root),
        conditions: vec![],
    }];
    for component in construction.components() {
        checkpoint(control)?;
        objects.push(ReadingObject {
            identity: ObjectIdentity::selected(construction.reading(), root, component.subject()),
            conditions: vec![],
        });
    }
    for member in construction.local_domain().conditional() {
        checkpoint(control)?;
        if member.is_entity() {
            objects.push(ReadingObject {
                identity: ObjectIdentity::selected(construction.reading(), root, member.subject()),
                conditions: vec![MembershipCondition {
                    slot: member.owner_slot().clone(),
                    owner: root.clone(),
                }],
            });
        }
    }
    // baseを先頭にし、部分対象は原始identity順。未確定所属の候補も別行に保つ。
    objects
        .get_mut(1..)
        .ok_or_else(|| ConstructionFailure::Inconsistent("base対象がない".into()))?
        .sort_by(|a, b| a.identity.subject().cmp(b.identity.subject()));
    checkpoint(control)?;
    let mut declarations = Vec::new();
    let mut instances = Vec::new();
    for declaration in inputs.law().declarations.values() {
        checkpoint(control)?;
        if declaration.reading != construction.reading() {
            continue;
        }
        let params = match &declaration.signature {
            Signature::Law { params, .. } | Signature::View { params, .. } => params,
            _ => continue,
        };
        let metadata = inputs
            .law()
            .infos
            .iter()
            .find(|info| info.name == declaration.name)
            .ok_or_else(|| ConstructionFailure::Inconsistent("元Law/view metadataがない".into()))?
            .clone();
        declarations.push(metadata.clone());
        let mut anchored = false;
        let mut parameters = Vec::new();
        for param in params {
            checkpoint(control)?;
            match &param.ty {
                Type::Ref(ty) | Type::Owned(ty, _) => anchored |= local_types.contains(ty),
                _ => parameters.push(param.clone()),
            }
        }
        // root/owned参照へ適用しないhelperを独立の軸にはしない。
        if !anchored {
            continue;
        }
        let mut rows = vec![Row {
            bindings: vec![],
            conditions: vec![],
        }];
        for param in params {
            checkpoint(control)?;
            let (ty, owner) = match &param.ty {
                Type::Ref(ty) => (ty, None),
                Type::Owned(ty, owner) => (ty, Some(owner)),
                _ => continue,
            };
            let roster = choices(
                inputs,
                ty,
                local_types.contains(ty),
                construction.local_domain(),
                control,
            )?;
            let mut next = Vec::new();
            for row in rows {
                checkpoint(control)?;
                for choice in &roster {
                    checkpoint(control)?;
                    let Some(mut conditions) =
                        merge_conditions(&row.conditions, &choice.conditions, control)?
                    else {
                        continue;
                    };
                    if let Some(owner) = owner {
                        let owner = row
                            .bindings
                            .iter()
                            .find(|b| &b.parameter.name == owner)
                            .ok_or_else(|| {
                                ConstructionFailure::Inconsistent(
                                    "Owned parameterの先行参照ownerがない".into(),
                                )
                            })?;
                        let Some(required) = owner_condition(
                            subject(inputs, &choice.subject, control)?,
                            &owner.subject,
                            control,
                        )?
                        else {
                            continue;
                        };
                        let Some(merged) = merge_conditions(&conditions, &required, control)?
                        else {
                            continue;
                        };
                        conditions = merged;
                    }
                    let mut bindings = row.bindings.clone();
                    bindings.push(ReferenceBinding {
                        parameter: param.clone(),
                        subject: choice.subject.clone(),
                    });
                    next.push(Row {
                        bindings,
                        conditions,
                    });
                }
            }
            rows = next;
        }
        for row in rows {
            checkpoint(control)?;
            let mut applications = Vec::new();
            for object in &objects {
                checkpoint(control)?;
                let base = object.identity.subject() == root;
                let mut applies = true;
                for binding in &row.bindings {
                    checkpoint(control)?;
                    let (Type::Ref(ty) | Type::Owned(ty, _)) = &binding.parameter.ty else {
                        return Err(ConstructionFailure::Inconsistent(
                            "参照束縛の元parameterが参照型でない".into(),
                        ));
                    };
                    if local_types.contains(ty)
                        && !base
                        && &binding.subject != object.identity.subject()
                    {
                        applies = false;
                    }
                }
                let conditions = if applies {
                    merge_conditions(&row.conditions, &object.conditions, control)?
                } else {
                    None
                };
                applications.push(match conditions {
                    Some(conditions) => InstanceApplication::Applicable { conditions },
                    None => InstanceApplication::NotApplicable,
                });
            }
            instances.push(ObjectInstance {
                declaration: metadata.clone(),
                bindings: row.bindings,
                parameters: parameters.clone(),
                applications,
            });
        }
    }
    let result = ObjectReadingInstances {
        construction: construction.clone(),
        source_law: inputs.sources().law().clone(),
        local_types,
        objects,
        declarations,
        instances,
    };
    checkpoint(control)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn inputs() -> CheckedInputs {
        let d = include_bytes!("../../tests/fixtures/object-instances.atoms.json");
        let l = include_str!("../../tests/fixtures/object-instances.law");
        let a = include_str!("../../tests/fixtures/object-instances.archmap.json");
        let definitions = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &definitions.vocabularies["Instances"].digest;
        crate::observed::input::check_inputs(
            crate::observed::input::InputSources::from_bytes(
                vec![d.to_vec()],
                l.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
                a.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn recheck_rejects_forged_instances_domains_metadata_and_shared_conditions() {
        let i = inputs();
        let c = construct(&i, "Selected", "v", "A", &mut Control::unlimited()).unwrap();
        let original = object_reading_instances(&i, &c, &mut Control::unlimited()).unwrap();
        original.recheck(&i, &mut Control::unlimited()).unwrap();
        for mutation in 0..13 {
            let mut forged = original.clone();
            match mutation {
                0 => {
                    forged.instances.pop();
                }
                1 => {
                    forged.objects.pop();
                }
                2 => {
                    forged.declarations.pop();
                }
                3 => {
                    forged
                        .instances
                        .first_mut()
                        .unwrap()
                        .bindings
                        .first_mut()
                        .unwrap()
                        .subject
                        .subject = "q".into();
                }
                4 => {
                    forged.instances.first_mut().unwrap().applications.pop();
                }
                5 => {
                    forged.instances.first_mut().unwrap().applications[0] =
                        InstanceApplication::NotApplicable;
                }
                6 => {
                    forged
                        .instances
                        .iter_mut()
                        .find(|r| r.declaration.name == "Selected.values")
                        .unwrap()
                        .parameters
                        .remove(0);
                }
                7 => {
                    forged
                        .instances
                        .iter_mut()
                        .find(|r| r.declaration.name == "Selected.values")
                        .unwrap()
                        .parameters[0]
                        .ty = Type::Q;
                }
                8 => {
                    forged
                        .instances
                        .iter_mut()
                        .find(|r| r.declaration.name == "Selected.root")
                        .unwrap()
                        .declaration
                        .dependencies
                        .clear();
                }
                9 => {
                    let row = forged
                        .instances
                        .iter_mut()
                        .find(|r| r.declaration.name == "Selected.sharing")
                        .unwrap();
                    let InstanceApplication::Applicable { conditions } = &mut row.applications[0]
                    else {
                        panic!("sharing")
                    };
                    conditions.clear();
                }
                10 => {
                    let row = forged
                        .instances
                        .iter_mut()
                        .find(|r| r.declaration.name == "Selected.sharing")
                        .unwrap();
                    let InstanceApplication::Applicable { conditions } = &mut row.applications[0]
                    else {
                        panic!("sharing")
                    };
                    conditions[0].owner.subject = "A".into();
                }
                11 => {
                    forged.source_law = InputBytes::new("law", b"changed source law".to_vec());
                }
                _ => forged.local_types.clear(),
            }
            assert_ne!(
                forged, original,
                "mutation {mutation} must change actual data"
            );
            assert!(
                matches!(
                    forged.recheck(&i, &mut Control::unlimited()),
                    Err(ConstructionFailure::Inconsistent(_))
                ),
                "mutation {mutation}"
            );
        }
    }
}
