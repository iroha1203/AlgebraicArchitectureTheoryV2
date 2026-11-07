//! 検査済み三入力から、共通AtomUniverseと対象のConfigurationを生成する。
use archsig_common::internal::InternalError;
use archsig_common::{
    canonical::Json,
    control::{Checkpoint, Control},
    types::Type,
};
use archsig_input::archmap::Fact as FactPointer;
use archsig_input::{
    archmap::{Slot, Subject, Value},
    definition::model::PrimitiveSignature,
    input::CheckedInputs,
    result::Signal,
};
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
type ConstructionProbe = Box<dyn FnMut(&str)>;
#[cfg(test)]
thread_local! { static CONSTRUCTION_PROBE: std::cell::RefCell<Option<ConstructionProbe>> = const {std::cell::RefCell::new(None)}; }
#[cfg(test)]
pub(crate) struct ConstructionObserver(Option<ConstructionProbe>);
#[cfg(test)]
impl Drop for ConstructionObserver {
    fn drop(&mut self) {
        CONSTRUCTION_PROBE.with(|p| p.replace(self.0.take()));
    }
}
#[cfg(test)]
pub(crate) fn observe_constructions(probe: impl FnMut(&str) + 'static) -> ConstructionObserver {
    ConstructionObserver(CONSTRUCTION_PROBE.with(|p| p.replace(Some(Box::new(probe)))))
}
pub mod maps;
pub mod profiles;
pub mod readings;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Configuration {
    data: std::sync::Arc<ConfigurationData>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct ConfigurationData {
    family: Vec<FactPointer>,
    requirements: Vec<FactPointer>,
    relations: Vec<(FactPointer, FactPointer)>,
    identifications: Vec<(FactPointer, FactPointer)>,
}
impl Configuration {
    fn new(
        family: Vec<FactPointer>,
        requirements: Vec<FactPointer>,
        relations: Vec<(FactPointer, FactPointer)>,
        identifications: Vec<(FactPointer, FactPointer)>,
    ) -> Self {
        Self {
            data: std::sync::Arc::new(ConfigurationData {
                family,
                requirements,
                relations,
                identifications,
            }),
        }
    }
    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.data, &other.data)
    }

    pub fn family(&self) -> &[FactPointer] {
        &self.data.family
    }
    pub fn requirements(&self) -> &[FactPointer] {
        &self.data.requirements
    }
    pub fn relations(&self) -> &[(FactPointer, FactPointer)] {
        &self.data.relations
    }
    pub fn identifications(&self) -> &[(FactPointer, FactPointer)] {
        &self.data.identifications
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
                Json::Arr(self.data.family.iter().map(FactPointer::wire).collect()),
            ),
            (
                "requirements",
                Json::Arr(
                    self.data
                        .requirements
                        .iter()
                        .map(FactPointer::wire)
                        .collect(),
                ),
            ),
            ("relations", pairs(&self.data.relations)),
            ("identifications", pairs(&self.data.identifications)),
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
    universe: std::sync::Arc<Vec<FactPointer>>,
    base: ConfigurationCandidate,
    components: Vec<ObjectComponent>,
    local_domain: SubjectDomain,
    owner_resolution: Option<crate::owner_completion::DeterminedOwners>,
    assembly: Option<std::sync::Arc<AssemblyOrigin>>,
}
/// 計算済みの組立てに閉じた不変な由来。外部入力から直接生成しない。
#[derive(Debug)]
struct AssemblyOrigin {
    inputs: std::sync::Arc<CheckedInputs>,
    members: Vec<FactPointer>,
    transport: std::sync::Arc<BTreeMap<FactPointer, FactPointer>>,
}
impl PartialEq for AssemblyOrigin {
    fn eq(&self, other: &Self) -> bool {
        self.members == other.members
            && self.transport == other.transport
            && (std::sync::Arc::ptr_eq(&self.inputs, &other.inputs)
                || self.inputs.sources() == other.inputs.sources())
    }
}
impl Eq for AssemblyOrigin {}
impl ConfigurationConstruction {
    /// 構成した対象の参照輸送。元の観測値と欠測補完を変更しない。
    pub(crate) fn transported_subject<'a>(&'a self, fact: &'a FactPointer) -> &'a FactPointer {
        self.transport().and_then(|m| m.get(fact)).unwrap_or(fact)
    }
    pub(crate) fn transport(&self) -> Option<&BTreeMap<FactPointer, FactPointer>> {
        self.assembly.as_deref().map(|a| a.transport.as_ref())
    }
    pub(crate) fn resolved_owners(&self) -> &[(FactPointer, FactPointer)] {
        self.owner_resolution
            .as_ref()
            .map(|r| r.owners())
            .unwrap_or(&[])
    }
    pub(crate) fn owner_support(&self) -> &[FactPointer] {
        self.owner_resolution
            .as_ref()
            .map(|r| r.support())
            .unwrap_or(&[])
    }
    pub(crate) fn owner_scope(&self) -> Option<&crate::owner_completion::Scope> {
        self.owner_resolution.as_ref().map(|r| r.scope())
    }
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn root(&self) -> &FactPointer {
        &self.root
    }
    pub(crate) fn shared_universe(&self) -> std::sync::Arc<Vec<FactPointer>> {
        self.universe.clone()
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
        control: &Control,
    ) -> Result<(), ConstructionFailure> {
        let expected = if let Some(origin) = &self.assembly {
            if !std::ptr::eq(inputs, origin.inputs.as_ref())
                && inputs.sources() != origin.inputs.sources()
            {
                return Err(ConstructionFailure::Inconsistent(internal!(
                    "組立て構成の元三入力が違う"
                )));
            }
            let target = construct(inputs, reading, snapshot, root, control)?;
            assemble_from_origin(
                target.reading(),
                target.root(),
                target.shared_universe(),
                origin.clone(),
                control,
            )?
        } else if self.owner_resolution.is_none() {
            construct(inputs, reading, snapshot, root, control)?
        } else {
            construct_resolving_owners(inputs, reading, snapshot, root, control)?
        };
        if self != &expected {
            return Err(ConstructionFailure::Inconsistent(internal!(
                "Configuration/Uが現在の入力・reading/rootと違う"
            )));
        }
        tick(control)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructionFailure {
    InvalidSelection(String),
    Inconsistent(InternalError),
    Stopped(Signal),
}
impl ConstructionFailure {
    #[track_caller]
    pub(crate) fn internal_context(&self, message: String) -> InternalError {
        match self {
            Self::Inconsistent(error) => error.with_message(message),
            _ => internal!(message),
        }
    }
}
impl From<Signal> for ConstructionFailure {
    fn from(reason: Signal) -> Self {
        Self::Stopped(reason)
    }
}
fn tick(control: &Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::Configuration)
        .map_err(Into::into)
}
fn exists(subject: &Subject) -> FactPointer {
    FactPointer::from(archsig_input::archmap::FactData {
        snapshot: subject.snapshot.clone(),
        subject: subject.id.clone(),
        field: None,
        atom: None,
    })
}
fn slot(subject: &Subject, field: &archsig_common::names::QualifiedName) -> FactPointer {
    {
        let aat_field_0 = Some(field.clone());
        let mut aat_fact = exists(subject);
        aat_fact.field = aat_field_0;
        aat_fact
    }
}
fn canonical_facts(
    items: BTreeSet<FactPointer>,
    control: &Control,
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
    control: &Control,
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
    control: &Control,
) -> Result<BTreeSet<String>, ConstructionFailure> {
    reading_namespaces(inputs.law(), reading, control)
}
pub(crate) fn reading_namespaces(
    law: &archsig_input::law::CheckedLaw,
    reading: &str,
    control: &Control,
) -> Result<BTreeSet<String>, ConstructionFailure> {
    let mut selected = None;
    for info in law.infos() {
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
        let vocabulary = law.definitions().vocabularies().get(&name).ok_or_else(|| {
            ConstructionFailure::Inconsistent(internal!(format!("検査済み定義 `{name}` がない")))
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
        .declarations()
        .get(ty)
        .is_some_and(|d| namespaces.contains(&d.namespace))
}
pub(crate) fn has_reference(
    inputs: &CheckedInputs,
    ty: &Type,
    control: &Control,
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
                    .declarations()
                    .get(name)
                    .map(|d| &d.signature)
                else {
                    return Err(ConstructionFailure::Inconsistent(internal!(
                        "dataの元定義がない"
                    )));
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
    control: &Control,
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
    blocking: BTreeSet<FactPointer>,
    control: &Control,
) -> Result<ConfigurationCandidate, ConstructionFailure> {
    configuration_with_owners(inputs, subjects, index, blocking, &[], control)
}
fn configuration_with_owners(
    inputs: &CheckedInputs,
    subjects: &[&Subject],
    index: &BTreeMap<(&str, &str), &Subject>,
    blocking: BTreeSet<FactPointer>,
    owners: &[(FactPointer, FactPointer)],
    control: &Control,
) -> Result<ConfigurationCandidate, ConstructionFailure> {
    configuration_transported(inputs, subjects, index, blocking, owners, None, control)
}
fn configuration_transported(
    inputs: &CheckedInputs,
    subjects: &[&Subject],
    index: &BTreeMap<(&str, &str), &Subject>,
    mut blocking: BTreeSet<FactPointer>,
    owners: &[(FactPointer, FactPointer)],
    transport: Option<&BTreeMap<FactPointer, FactPointer>>,
    control: &Control,
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
                    let fact = {
                        let aat_field_0 = Some(atom.clone());
                        let mut aat_fact = slot(subject, &field.name);
                        aat_fact.atom = aat_field_0;
                        aat_fact
                    };
                    family.insert(fact.clone());
                    relations.insert((existence.clone(), fact.clone()));
                    for (snapshot, id) in references(value, control)? {
                        tick(control)?;
                        let target = index.get(&(snapshot, id)).ok_or_else(|| {
                            ConstructionFailure::Inconsistent(internal!("参照先の存在事実がない"))
                        })?;
                        let target = exists(target);
                        let target = transport.and_then(|m| m.get(&target)).unwrap_or(&target);
                        family.insert(target.clone());
                        relations.insert((fact.clone(), target.clone()));
                    }
                }
                Slot::Missing
                    if owners
                        .iter()
                        .any(|(fact, _)| *fact == slot(subject, &field.name)) => {}
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
                .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("Fのsubjectがない")))?;
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
        known: Configuration::new(
            canonical_facts(family, control)?,
            canonical_facts(requirements, control)?,
            canonical_pairs(relations, control)?,
            canonical_pairs(identifications, control)?,
        ),
        blocking_slots: canonical_facts(blocking, control)?,
    })
}
/// rootとreadingを選んで標準構成を生成する。値や所属の補完を入力として受け取らない。
pub fn construct(
    inputs: &CheckedInputs,
    reading: &str,
    snapshot: &str,
    root: &str,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    construct_with_owners(inputs, reading, snapshot, root, &[], control)
}
/// 観測から列挙した整合owner補完が一元のときだけ所属を確定する。
/// 原始Atomの集合と値は観測のまま保持する。
pub(crate) fn construct_resolving_owners(
    inputs: &CheckedInputs,
    reading: &str,
    snapshot: &str,
    root: &str,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    let observed = construct(inputs, reading, snapshot, root, control)?;
    let fields = observed
        .local_domain
        .conditional
        .iter()
        .map(|m| m.owner_slot.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if fields.is_empty() {
        return Ok(observed);
    }
    let Some(resolution) = crate::owner_completion::determined_owners(inputs, &fields, control)
        .map_err(|failure| match failure {
            crate::owner_completion::Failure::Invalid(message) => {
                ConstructionFailure::Inconsistent(internal!(message))
            }
            crate::owner_completion::Failure::Kernel(message) => ConstructionFailure::Inconsistent(
                message.with_message(format!("owner補完の構成検査: Internal({message:?})")),
            ),
            crate::owner_completion::Failure::Stopped(reason) => {
                ConstructionFailure::Stopped(reason)
            }
        })?
    else {
        return Ok(observed);
    };
    let owners = resolution.owners();
    let mut candidate = construct_with_owners(inputs, reading, snapshot, root, owners, control)?;
    // この構成経路はownerだけの欠測を扱う。通常の構成器の欠測規則は保つ。
    for requirement in candidate.base.known.requirements() {
        tick(control)?;
        let subject = inputs
            .archmap()
            .snapshots()
            .iter()
            .flat_map(|s| &s.subjects)
            .find(|s| s.snapshot == requirement.snapshot && s.id == requirement.subject)
            .ok_or_else(|| {
                ConstructionFailure::Inconsistent(internal!("構成要求のsubjectがない"))
            })?;
        if subject.fields.iter().any(|field| {
            Some(&field.name) == requirement.field.as_ref()
                && matches!(field.slot, Slot::Missing)
                && !owners.iter().any(|(slot, _)| slot == requirement)
        }) {
            return Ok(observed);
        }
    }
    candidate.owner_resolution = Some(resolution);
    Ok(candidate)
}
fn construct_with_owners(
    inputs: &CheckedInputs,
    reading: &str,
    snapshot: &str,
    root: &str,
    owners: &[(FactPointer, FactPointer)],
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    construct_inner(inputs, reading, snapshot, root, owners, None, control)
}
/// Same checked input and reading as the ambient construction; share its carrier.
pub(crate) fn construct_fragment(
    inputs: &CheckedInputs,
    ambient: &ConfigurationConstruction,
    snapshot: &str,
    root: &str,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    construct_inner(
        inputs,
        ambient.reading(),
        snapshot,
        root,
        &[],
        Some(ambient.shared_universe()),
        control,
    )
}
fn construct_inner(
    inputs: &CheckedInputs,
    reading: &str,
    snapshot: &str,
    root: &str,
    owners: &[(FactPointer, FactPointer)],
    shared_universe: Option<std::sync::Arc<Vec<FactPointer>>>,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    tick(control)?;
    #[cfg(test)]
    CONSTRUCTION_PROBE.with(|p| {
        if let Some(probe) = p.borrow_mut().as_mut() {
            probe(root);
        }
    });

    let namespaces = namespaces(inputs, reading, control)?;
    let mut index = BTreeMap::new();
    let mut universe = BTreeSet::new();
    for snap in inputs.archmap().snapshots() {
        tick(control)?;
        for subject in &snap.subjects {
            tick(control)?;
            index.insert((subject.snapshot.as_str(), subject.id.as_str()), subject);
            if shared_universe.is_none() {
                universe.insert(exists(subject));
                for field in &subject.fields {
                    tick(control)?;
                    if let Slot::Known { atom, .. } = &field.slot {
                        universe.insert({
                            let aat_field_0 = Some(atom.clone());
                            let mut aat_fact = slot(subject, &field.name);
                            aat_fact.atom = aat_field_0;
                            aat_fact
                        });
                    }
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
            .declarations()
            .get(selected.ty.as_str())
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
            .declarations()
            .get(subject.ty.as_str())
            .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("subjectの元定義がない")))?;
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
            if field.name.is_owner() {
                owner_field = Some(field);
            }
        }
        let field = owner_field.ok_or_else(|| {
            ConstructionFailure::Inconsistent(internal!("owned subjectのowner slotがない"))
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
            Slot::Missing
                if owners.iter().any(|(fact, owner)| {
                    *fact == slot(subject, &field.name)
                        && owner.snapshot == snapshot
                        && owner.subject == root
                }) =>
            {
                subjects.push(subject);
                if is_entity {
                    parts.push(*subject);
                }
            }
            Slot::Missing
                if owners
                    .iter()
                    .any(|(fact, _)| *fact == slot(subject, &field.name)) => {}
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
                return Err(ConstructionFailure::Inconsistent(internal!(
                    "owner slotが原始参照でない"
                )));
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
        conditions.push(conditional.remove(&subject).ok_or_else(|| {
            ConstructionFailure::Inconsistent(internal!("所属条件のsubjectがない"))
        })?);
    }
    let local_domain = SubjectDomain {
        known: canonical_facts(known, control)?,
        conditional: conditions,
    };
    let base = configuration_with_owners(inputs, &subjects, &index, blocking, owners, control)?;
    let mut components = Vec::new();
    for subject in parts {
        tick(control)?;
        components.push(ObjectComponent {
            subject: exists(subject),
            candidate: configuration_with_owners(
                inputs,
                &[subject],
                &index,
                BTreeSet::new(),
                owners,
                control,
            )?,
        });
    }
    components.sort_by_key(|p| p.subject.wire().canonical());
    let result = ConfigurationConstruction {
        reading: reading.into(),
        root: exists(selected),
        universe: if let Some(universe) = shared_universe {
            universe
        } else {
            std::sync::Arc::new(canonical_facts(universe, control)?)
        },
        base,
        components,
        local_domain,
        owner_resolution: None,
        assembly: None,
    };
    tick(control)?;
    Ok(result)
}

/// 検査済みの局所組立てが決めた個体と参照輸送から、既存のF/R/E規則を適用する。
/// 対応の値整合と局所単射は呼出し側の型付き組立てで先に検査する。
pub(crate) fn construct_assembled(
    inputs: std::sync::Arc<CheckedInputs>,
    target: ConfigurationConstruction,
    members: &[FactPointer],
    transport: BTreeMap<FactPointer, FactPointer>,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    let origin = std::sync::Arc::new(AssemblyOrigin {
        inputs,
        members: members.to_vec(),
        transport: std::sync::Arc::new(transport),
    });
    assemble_from_origin(
        target.reading(),
        target.root(),
        target.shared_universe(),
        origin,
        control,
    )
}
pub(crate) fn restrict_assembled(
    source: &ConfigurationConstruction,
    members: Vec<FactPointer>,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    let origin = source.assembly.as_ref().ok_or_else(|| {
        ConstructionFailure::InvalidSelection("再制限元が組立て対象でない".into())
    })?;
    let origin = std::sync::Arc::new(AssemblyOrigin {
        inputs: origin.inputs.clone(),
        members,
        transport: origin.transport.clone(),
    });
    assemble_from_origin(
        source.reading(),
        source.root(),
        source.shared_universe(),
        origin,
        control,
    )
}
fn assemble_from_origin(
    reading: &str,
    root: &FactPointer,
    universe: std::sync::Arc<Vec<FactPointer>>,
    origin: std::sync::Arc<AssemblyOrigin>,
    control: &Control,
) -> Result<ConfigurationConstruction, ConstructionFailure> {
    let inputs = &origin.inputs;
    let members = &origin.members;
    let transport = origin.transport.as_ref();
    tick(control)?;
    let mut index = BTreeMap::new();
    for snapshot in inputs.archmap().snapshots() {
        for subject in &snapshot.subjects {
            tick(control)?;
            index.insert((subject.snapshot.as_str(), subject.id.as_str()), subject);
        }
    }
    let mut subjects = Vec::new();
    let mut components = Vec::new();
    for fact in members {
        tick(control)?;
        let subject = *index
            .get(&(fact.snapshot.as_str(), fact.subject.as_str()))
            .ok_or_else(|| ConstructionFailure::Inconsistent(internal!("組立て個体がない")))?;
        subjects.push(subject);
        if fact != root
            && matches!(
                inputs.definitions().declarations()[subject.ty.as_str()].signature,
                PrimitiveSignature::Entity { .. }
            )
        {
            components.push(ObjectComponent {
                subject: fact.clone(),
                candidate: configuration_transported(
                    inputs,
                    &[subject],
                    &index,
                    BTreeSet::new(),
                    &[],
                    Some(transport),
                    control,
                )?,
            });
        }
    }
    let base = configuration_transported(
        inputs,
        &subjects,
        &index,
        BTreeSet::new(),
        &[],
        Some(transport),
        control,
    )?;
    components.sort_by_key(|p| p.subject.wire().canonical());
    let local_domain = SubjectDomain {
        known: canonical_facts(members.iter().cloned().collect(), control)?,
        conditional: vec![],
    };
    tick(control)?;
    Ok(ConfigurationConstruction {
        reading: reading.into(),
        root: root.clone(),
        universe,
        base,
        components,
        local_domain,
        owner_resolution: None,
        assembly: Some(origin),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use archsig_input::input::{InputSources, check_inputs};
    fn inputs(missing: bool) -> CheckedInputs {
        let definition = include_bytes!("../../../tests/fixtures/configuration.atoms.json");
        let definitions =
            archsig_input::definition::check_definitions(&[("definition0", definition)]).unwrap();
        let digest = &definitions.vocabularies()["Mesh"].digest;
        let law = include_str!("../../../tests/fixtures/configuration.law")
            .replace("@MESH_DIGEST@", digest);
        let map = include_str!("../../../tests/fixtures/configuration.archmap.json")
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
            &Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn recheck_rejects_forged_families_relations_slots_universe_components_and_conditions() {
        let inputs = inputs(false);
        let original = construct(&inputs, "MeshRead", "v", "A", &Control::unlimited()).unwrap();
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
                    std::sync::Arc::make_mut(&mut forged.base.known.data)
                        .family
                        .pop();
                }
                "requirements" => {
                    std::sync::Arc::make_mut(&mut forged.base.known.data)
                        .requirements
                        .pop();
                }
                "relations" => {
                    std::sync::Arc::make_mut(&mut forged.base.known.data)
                        .relations
                        .pop();
                }
                "identifications" => {
                    std::sync::Arc::make_mut(&mut forged.base.known.data)
                        .identifications
                        .pop();
                }
                "universe" => {
                    std::sync::Arc::make_mut(&mut forged.universe).pop();
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
                    forged.recheck(&inputs, "MeshRead", "v", "A", &Control::unlimited()),
                    Err(ConstructionFailure::Inconsistent(_))
                ),
                "{kind}"
            );
        }
        assert!(matches!(
            original.recheck(&inputs, "MeshRead", "v", "B", &Control::unlimited()),
            Err(ConstructionFailure::Inconsistent(_))
        ));
        let missing = self::inputs(true);
        let mut forged = construct(&missing, "MeshRead", "v", "A", &Control::unlimited()).unwrap();
        assert!(forged.base.configuration().is_none());
        forged.base.blocking_slots.clear();
        assert!(
            matches!(
                forged.recheck(&missing, "MeshRead", "v", "A", &Control::unlimited()),
                Err(ConstructionFailure::Inconsistent(_))
            ),
            "未観測の構成条件を消せない"
        );
    }
}
