//! 検査済み三入力から、共通AtomUniverseと対象のConfigurationを生成する。
pub use crate::observed::result::Fact as FactPointer;
use crate::{
    archmap::{Slot, Subject, Value},
    canonical::Json,
    definition::model::PrimitiveSignature,
    observed::{
        control::{Checkpoint, Control, StopReason},
        input::CheckedInputs,
    },
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};
pub mod maps;
pub mod profiles;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Configuration {
    family: Vec<FactPointer>,
    requirements: Vec<FactPointer>,
    relations: Vec<(FactPointer, FactPointer)>,
    identifications: Vec<(FactPointer, FactPointer)>,
}
impl Configuration {
    pub fn family(&self) -> &[FactPointer] {
        &self.family
    }
    pub fn requirements(&self) -> &[FactPointer] {
        &self.requirements
    }
    pub fn relations(&self) -> &[(FactPointer, FactPointer)] {
        &self.relations
    }
    pub fn identifications(&self) -> &[(FactPointer, FactPointer)] {
        &self.identifications
    }
    pub fn wire(&self) -> Json {
        let pairs = |items: &[(FactPointer, FactPointer)]| {
            Json::Arr(
                items
                    .iter()
                    .map(|(a, b)| Json::Arr(vec![a.wire(), b.wire()]))
                    .collect(),
            )
        };
        Json::obj([
            (
                "family",
                Json::Arr(self.family.iter().map(FactPointer::wire).collect()),
            ),
            (
                "requirements",
                Json::Arr(self.requirements.iter().map(FactPointer::wire).collect()),
            ),
            ("relations", pairs(&self.relations)),
            ("identifications", pairs(&self.identifications)),
        ])
    }
}
/// 未観測の所属/参照があるときknownは確定している断片であり、完成した対象ではない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationCandidate {
    known: Configuration,
    blocking_slots: Vec<FactPointer>,
}
impl ConfigurationCandidate {
    pub fn known(&self) -> &Configuration {
        &self.known
    }
    pub fn blocking_slots(&self) -> &[FactPointer] {
        &self.blocking_slots
    }
    pub fn configuration(&self) -> Option<&Configuration> {
        self.blocking_slots.is_empty().then_some(&self.known)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectComponent {
    subject: FactPointer,
    candidate: ConfigurationCandidate,
}
impl ObjectComponent {
    pub fn subject(&self) -> &FactPointer {
        &self.subject
    }
    pub fn candidate(&self) -> &ConfigurationCandidate {
        &self.candidate
    }
}
/// このsubjectのowner slotが選択rootを指す、という所属条件。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionalSubject {
    subject: FactPointer,
    owner_slot: FactPointer,
    owner: FactPointer,
    entity: bool,
}
impl ConditionalSubject {
    pub fn subject(&self) -> &FactPointer {
        &self.subject
    }
    pub fn owner_slot(&self) -> &FactPointer {
        &self.owner_slot
    }
    pub fn owner(&self) -> &FactPointer {
        &self.owner
    }
    pub fn is_entity(&self) -> bool {
        self.entity
    }
}
/// Fの外部参照先を含めず、原始所属から作る読取り適用域。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubjectDomain {
    known: Vec<FactPointer>,
    conditional: Vec<ConditionalSubject>,
}
impl SubjectDomain {
    pub fn known(&self) -> &[FactPointer] {
        &self.known
    }
    pub fn conditional(&self) -> &[ConditionalSubject] {
        &self.conditional
    }
    pub fn is_complete(&self) -> bool {
        self.conditional.is_empty()
    }
}
/// build/mapが共用する原始構成。LawやObjectAlgebraの成立を表す型とは区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationConstruction {
    reading: String,
    root: FactPointer,
    universe: Vec<FactPointer>,
    base: ConfigurationCandidate,
    components: Vec<ObjectComponent>,
    local_domain: SubjectDomain,
}
impl ConfigurationConstruction {
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn root(&self) -> &FactPointer {
        &self.root
    }
    pub fn universe(&self) -> &[FactPointer] {
        &self.universe
    }
    pub fn base(&self) -> &ConfigurationCandidate {
        &self.base
    }
    pub fn local_domain(&self) -> &SubjectDomain {
        &self.local_domain
    }
    pub fn components(&self) -> &[ObjectComponent] {
        &self.components
    }
    /// 表示や保存を経由せず、現在の三入力・reading/rootから全構成を再照合する。
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        reading: &str,
        snapshot: &str,
        root: &str,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let expected = construct(inputs, reading, snapshot, root, control)?;
        if self != &expected {
            return Err(ConstructionFailure::Inconsistent(
                "Configuration/Uが現在の入力・reading/rootと違う".into(),
            ));
        }
        tick(control)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructionFailure {
    InvalidSelection(String),
    Inconsistent(String),
    Stopped(StopReason),
}
impl From<StopReason> for ConstructionFailure {
    fn from(reason: StopReason) -> Self {
        Self::Stopped(reason)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::Configuration)
        .map_err(Into::into)
}
fn exists(subject: &Subject) -> FactPointer {
    FactPointer {
        snapshot: subject.snapshot.clone(),
        subject: subject.id.clone(),
        field: None,
        atom: None,
    }
}
fn slot(subject: &Subject, field: &str) -> FactPointer {
    FactPointer {
        field: Some(field.into()),
        ..exists(subject)
    }
}
fn canonical_facts(
    items: BTreeSet<FactPointer>,
    control: &mut Control,
) -> Result<Vec<FactPointer>, ConstructionFailure> {
    let mut keyed = Vec::new();
    for item in items {
        tick(control)?;
        keyed.push((item.wire().canonical(), item));
    }
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    tick(control)?;
    Ok(keyed.into_iter().map(|(_, item)| item).collect())
}
fn canonical_pairs(
    items: BTreeSet<(FactPointer, FactPointer)>,
    control: &mut Control,
) -> Result<Vec<(FactPointer, FactPointer)>, ConstructionFailure> {
    let mut keyed = Vec::new();
    for (a, b) in items {
        tick(control)?;
        keyed.push((Json::Arr(vec![a.wire(), b.wire()]).canonical(), (a, b)));
    }
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    tick(control)?;
    Ok(keyed.into_iter().map(|(_, item)| item).collect())
}
fn namespaces(
    inputs: &CheckedInputs,
    reading: &str,
    control: &mut Control,
) -> Result<BTreeSet<String>, ConstructionFailure> {
    let mut selected = None;
    for info in &inputs.law().infos {
        tick(control)?;
        if info.kind == "reading" && info.name == reading {
            selected = Some(info);
        }
    }
    let info = selected.ok_or_else(|| {
        ConstructionFailure::InvalidSelection(format!("reading `{reading}` がない"))
    })?;
    let mut pending = Vec::new();
    for vocabulary in &info.vocabularies {
        tick(control)?;
        pending.push(vocabulary.namespace.clone());
    }
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop() {
        tick(control)?;
        if !seen.insert(name.clone()) {
            continue;
        }
        let vocabulary = inputs
            .definitions()
            .vocabularies
            .get(&name)
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent(format!("検査済み定義 `{name}` がない"))
            })?;
        for dependency in &vocabulary.dependencies {
            tick(control)?;
            pending.push(dependency.namespace.clone());
        }
    }
    Ok(seen)
}
fn visible(inputs: &CheckedInputs, ty: &str, namespaces: &BTreeSet<String>) -> bool {
    inputs
        .definitions()
        .declarations
        .get(ty)
        .is_some_and(|d| namespaces.contains(&d.namespace))
}
fn has_reference(
    inputs: &CheckedInputs,
    ty: &Type,
    control: &mut Control,
) -> Result<bool, ConstructionFailure> {
    let mut pending = vec![ty];
    let mut seen = BTreeSet::new();
    while let Some(ty) = pending.pop() {
        tick(control)?;
        match ty {
            Type::Ref(_) | Type::Owned(..) => return Ok(true),
            Type::Tuple(items) => pending.extend(items),
            Type::List(t) | Type::Set(t) | Type::Option(t) => pending.push(t),
            Type::Map(k, v) => {
                pending.push(k);
                pending.push(v);
            }
            Type::Data(name) if seen.insert(name) => {
                let Some(PrimitiveSignature::Data { constructors }) = inputs
                    .definitions()
                    .declarations
                    .get(name)
                    .map(|d| &d.signature)
                else {
                    return Err(ConstructionFailure::Inconsistent(
                        "dataの元定義がない".into(),
                    ));
                };
                for constructor in constructors {
                    tick(control)?;
                    pending.extend(&constructor.arguments);
                }
            }
            _ => {}
        }
    }
    Ok(false)
}
fn references<'a>(
    value: &'a Value,
    control: &mut Control,
) -> Result<Vec<(&'a str, &'a str)>, ConstructionFailure> {
    let mut pending = vec![value];
    let mut result = Vec::new();
    while let Some(value) = pending.pop() {
        tick(control)?;
        match value {
            Value::Ref { snapshot, subject } => result.push((snapshot.as_str(), subject.as_str())),
            Value::Tuple(items)
            | Value::List(items)
            | Value::Set(items)
            | Value::Data { args: items, .. } => pending.extend(items),
            Value::Option(Some(v)) => pending.push(v),
            Value::Map(pairs) => {
                for (k, v) in pairs {
                    tick(control)?;
                    pending.push(k);
                    pending.push(v);
                }
            }
            _ => {}
        }
    }
    Ok(result)
}
fn configuration(
    inputs: &CheckedInputs,
    subjects: &[&Subject],
    index: &BTreeMap<(&str, &str), &Subject>,
    mut blocking: BTreeSet<FactPointer>,
    control: &mut Control,
) -> Result<ConfigurationCandidate, ConstructionFailure> {
    let mut family = BTreeSet::new();
    let mut relations = BTreeSet::new();
    for subject in subjects {
        tick(control)?;
        let existence = exists(subject);
        family.insert(existence.clone());
        for field in &subject.fields {
            tick(control)?;
            match &field.slot {
                Slot::Known { atom, value, .. } => {
                    let fact = FactPointer {
                        atom: Some(atom.clone()),
                        ..slot(subject, &field.name)
                    };
                    family.insert(fact.clone());
                    relations.insert((existence.clone(), fact.clone()));
                    for (snapshot, id) in references(value, control)? {
                        tick(control)?;
                        let target = index.get(&(snapshot, id)).ok_or_else(|| {
                            ConstructionFailure::Inconsistent("参照先の存在事実がない".into())
                        })?;
                        let target = exists(target);
                        family.insert(target.clone());
                        relations.insert((fact.clone(), target));
                    }
                }
                Slot::Missing if has_reference(inputs, &field.ty, control)? => {
                    blocking.insert(slot(subject, &field.name));
                }
                Slot::Missing => {}
            }
        }
    }
    let mut requirements = BTreeSet::new();
    // 外部参照先は存在事実だけをFに含める。そのfield値やRを走査しない。
    for fact in &family {
        tick(control)?;
        if fact.field.is_none() {
            let subject = index
                .get(&(fact.snapshot.as_str(), fact.subject.as_str()))
                .ok_or_else(|| ConstructionFailure::Inconsistent("Fのsubjectがない".into()))?;
            for field in &subject.fields {
                tick(control)?;
                requirements.insert(slot(subject, &field.name));
            }
        }
    }
    let mut identifications = BTreeSet::new();
    for fact in &family {
        tick(control)?;
        identifications.insert((fact.clone(), fact.clone()));
    }
    Ok(ConfigurationCandidate {
        known: Configuration {
            family: canonical_facts(family, control)?,
            requirements: canonical_facts(requirements, control)?,
            relations: canonical_pairs(relations, control)?,
            identifications: canonical_pairs(identifications, control)?,
        },
        blocking_slots: canonical_facts(blocking, control)?,
    })
}
/// rootとreadingを選んで標準構成を生成する。値や所属の補完を入力として受け取らない。
pub fn construct(
    inputs: &CheckedInputs,
    reading: &str,
    snapshot: &str,
    root: &str,
    control: &mut Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    tick(control)?;
    let namespaces = namespaces(inputs, reading, control)?;
    let mut index = BTreeMap::new();
    let mut universe = BTreeSet::new();
    for snap in &inputs.archmap().snapshots {
        tick(control)?;
        for subject in &snap.subjects {
            tick(control)?;
            index.insert((subject.snapshot.as_str(), subject.id.as_str()), subject);
            universe.insert(exists(subject));
            for field in &subject.fields {
                tick(control)?;
                if let Slot::Known { atom, .. } = &field.slot {
                    universe.insert(FactPointer {
                        atom: Some(atom.clone()),
                        ..slot(subject, &field.name)
                    });
                }
            }
        }
    }
    let selected = *index.get(&(snapshot, root)).ok_or_else(|| {
        ConstructionFailure::InvalidSelection(format!("root `@{snapshot}/{root}` がない"))
    })?;
    if !visible(inputs, &selected.ty, &namespaces) {
        return Err(ConstructionFailure::InvalidSelection(format!(
            "root型 `{}` がreading `{reading}` の定義にない",
            selected.ty
        )));
    }
    if !matches!(
        inputs
            .definitions()
            .declarations
            .get(&selected.ty)
            .map(|d| &d.signature),
        Some(PrimitiveSignature::Entity { owner: None, .. })
    ) {
        return Err(ConstructionFailure::InvalidSelection(
            "rootはownerを持たないentityを要求する".into(),
        ));
    }
    let mut subjects = vec![selected];
    let mut parts = Vec::new();
    let mut conditional = BTreeMap::new();
    let mut blocking = BTreeSet::new();
    for subject in index.values() {
        tick(control)?;
        if !visible(inputs, &subject.ty, &namespaces) {
            continue;
        }
        let signature = inputs
            .definitions()
            .declarations
            .get(&subject.ty)
            .ok_or_else(|| ConstructionFailure::Inconsistent("subjectの元定義がない".into()))?;
        let (owner, is_entity) = match &signature.signature {
            PrimitiveSignature::Entity {
                owner: Some(owner), ..
            } => (owner, true),
            PrimitiveSignature::Arrow { owner, .. } => (owner, false),
            _ => continue,
        };
        if owner != &selected.ty {
            continue;
        }
        let mut owner_field = None;
        for field in &subject.fields {
            tick(control)?;
            if field.name.rsplit('.').next() == Some("owner") {
                owner_field = Some(field);
            }
        }
        let field = owner_field.ok_or_else(|| {
            ConstructionFailure::Inconsistent("owned subjectのowner slotがない".into())
        })?;
        match &field.slot {
            Slot::Known {
                value:
                    Value::Ref {
                        snapshot: actual_snapshot,
                        subject: actual,
                    },
                ..
            } if actual_snapshot == snapshot && actual == root => {
                subjects.push(subject);
                if is_entity {
                    parts.push(*subject);
                }
            }
            Slot::Missing => {
                blocking.insert(slot(subject, &field.name));
                conditional.insert(
                    exists(subject),
                    ConditionalSubject {
                        subject: exists(subject),
                        owner_slot: slot(subject, &field.name),
                        owner: exists(selected),
                        entity: is_entity,
                    },
                );
            }
            Slot::Known {
                value: Value::Ref { .. },
                ..
            } => {}
            _ => {
                return Err(ConstructionFailure::Inconsistent(
                    "owner slotが原始参照でない".into(),
                ));
            }
        }
    }
    let mut known = BTreeSet::new();
    for subject in &subjects {
        tick(control)?;
        known.insert(exists(subject));
    }
    let mut conditions = Vec::new();
    let condition_order = canonical_facts(conditional.keys().cloned().collect(), control)?;
    for subject in condition_order {
        tick(control)?;
        conditions.push(
            conditional.remove(&subject).ok_or_else(|| {
                ConstructionFailure::Inconsistent("所属条件のsubjectがない".into())
            })?,
        );
    }
    let local_domain = SubjectDomain {
        known: canonical_facts(known, control)?,
        conditional: conditions,
    };
    let base = configuration(inputs, &subjects, &index, blocking, control)?;
    let mut components = Vec::new();
    for subject in parts {
        tick(control)?;
        components.push(ObjectComponent {
            subject: exists(subject),
            candidate: configuration(inputs, &[subject], &index, BTreeSet::new(), control)?,
        });
    }
    components.sort_by_key(|p| p.subject.wire().canonical());
    let result = ConfigurationConstruction {
        reading: reading.into(),
        root: exists(selected),
        universe: canonical_facts(universe, control)?,
        base,
        components,
        local_domain,
    };
    tick(control)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::input::{InputSources, check_inputs};
    fn inputs(missing: bool) -> CheckedInputs {
        let definition = include_bytes!("../tests/fixtures/configuration.atoms.json");
        let definitions =
            crate::definition::check_definitions(&[("definition0", definition)]).unwrap();
        let digest = &definitions.vocabularies["Mesh"].digest;
        let law =
            include_str!("../tests/fixtures/configuration.law").replace("@MESH_DIGEST@", digest);
        let map = include_str!("../tests/fixtures/configuration.archmap.json")
            .replace("@MESH_DIGEST@", digest);
        let map = if missing {
            map.lines()
                .filter(|line| !line.contains("\"id\": \"A-links\""))
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            map
        };
        check_inputs(
            InputSources::from_bytes(
                vec![definition.to_vec()],
                law.into_bytes(),
                map.into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn recheck_rejects_forged_families_relations_slots_universe_components_and_conditions() {
        let inputs = inputs(false);
        let original = construct(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
        for kind in [
            "family",
            "requirements",
            "relations",
            "identifications",
            "universe",
            "component",
            "domain",
            "reading",
            "root",
        ] {
            let mut forged = original.clone();
            match kind {
                "family" => {
                    forged.base.known.family.pop();
                }
                "requirements" => {
                    forged.base.known.requirements.pop();
                }
                "relations" => {
                    forged.base.known.relations.pop();
                }
                "identifications" => {
                    forged.base.known.identifications.pop();
                }
                "universe" => {
                    forged.universe.pop();
                }
                "component" => {
                    forged.components[0].subject.subject = "q".into();
                }
                "domain" => {
                    forged.local_domain.known.pop();
                }
                "reading" => {
                    forged.reading = "other".into();
                }
                "root" => {
                    forged.root.subject = "B".into();
                }
                _ => unreachable!(),
            }
            assert!(
                matches!(
                    forged.recheck(&inputs, "MeshRead", "v", "A", &mut Control::unlimited()),
                    Err(ConstructionFailure::Inconsistent(_))
                ),
                "{kind}"
            );
        }
        assert!(matches!(
            original.recheck(&inputs, "MeshRead", "v", "B", &mut Control::unlimited()),
            Err(ConstructionFailure::Inconsistent(_))
        ));
        let missing = self::inputs(true);
        let mut forged =
            construct(&missing, "MeshRead", "v", "A", &mut Control::unlimited()).unwrap();
        assert!(forged.base.configuration().is_none());
        forged.base.blocking_slots.clear();
        assert!(
            matches!(
                forged.recheck(&missing, "MeshRead", "v", "A", &mut Control::unlimited()),
                Err(ConstructionFailure::Inconsistent(_))
            ),
            "未観測の構成条件を消せない"
        );
    }
}
