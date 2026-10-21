//! 原始correspondenceと内部arrowの実作用・Configuration保存を現在の入力から検査する。
use super::*;
use crate::archmap::Field;

mod declarations;
mod internal;
mod operations;
mod references;
mod transport;
pub use crate::observed::numeric_transport::{
    NumericTransportValue, NumericValueMap, NumericValueTransport,
    numeric_declaration_value_transport,
};
pub use crate::observed::object_law_transport::{
    FiniteLawFamily, LawApplication, LawBooleanReading, LawConditionFailure,
    LawParameterComparison, LawTransportOutcome, ObjectLawTransport, ObjectLawTransportFailure,
    ObjectLawTransportPartial, object_law_transport,
};
pub use crate::observed::object_view_transport::{
    ObjectViewTransport, ObjectViewTransportFailure, ObjectViewTransportPartial,
    ViewConditionFailure, ViewTransportOutcome, ViewTransportValue, ViewValueEquivalence,
    object_view_transport,
};
pub use crate::observed::value_transport::{
    DeclarationValuePosition, FiniteTransportValue, FiniteValueBijection,
    FiniteValueConditionFailure, FiniteValueTransport, finite_declaration_value_transport,
};
pub(crate) use declarations::moved_type as moved_declaration_type;
pub use declarations::{
    DeclarationCandidate, DeclarationConditionFailure, DeclarationCorrespondence, DeclarationPair,
    declaration_correspondence,
};
pub use internal::{
    InternalArrowResult, InternalArrows, InternalArrowsFailure, internal_arrow, internal_arrows,
};
pub use operations::{
    ActionDifference, ConfigurationOperation, IdentityConstruction, OperationFailure,
    OperationStep, identity,
};
pub use references::{
    ReferenceBijection, ReferenceConditionFailure, ReferenceTypeTransport, reference_type_transport,
};
pub use transport::{
    ConfigurationTransport, ConfigurationTransportFailure, ConfigurationTransportPartial,
    GeneratorTransport, Naturality, ObjectTransport, TransportConditionFailure,
    configuration_transport,
};

type SubjectKey = (String, String);
#[derive(Clone, Debug, PartialEq, Eq)]
enum MapOrigin {
    Derived(operations::DerivedOrigin),
    Correspondence(FactPointer),
    InternalArrow {
        root: FactPointer,
        arrow: FactPointer,
    },
}
/// 同じConfigurationでも、root・reading・subjectの異なる対象を同一視しない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectIdentity {
    reading: String,
    root: FactPointer,
    subject: FactPointer,
}
impl ObjectIdentity {
    pub(super) fn selected(reading: &str, root: &FactPointer, subject: &FactPointer) -> Self {
        Self {
            reading: reading.into(),
            root: root.clone(),
            subject: subject.clone(),
        }
    }
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn root(&self) -> &FactPointer {
        &self.root
    }
    pub fn subject(&self) -> &FactPointer {
        &self.subject
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapCandidate {
    origin: MapOrigin,
    source_root: FactPointer,
    target_root: FactPointer,
    reading: String,
    to_reading: String,
    source_configuration: Configuration,
    target_configuration: Configuration,
    universe: Vec<FactPointer>,
    images: Vec<FactPointer>,
}
impl MapCandidate {
    pub fn subject(&self) -> Option<&FactPointer> {
        match &self.origin {
            MapOrigin::Correspondence(subject) => Some(subject),
            MapOrigin::InternalArrow { arrow, .. } => Some(arrow),
            MapOrigin::Derived(_) => None,
        }
    }
    pub fn correspondence(&self) -> Option<&FactPointer> {
        match &self.origin {
            MapOrigin::Correspondence(subject) => Some(subject),
            MapOrigin::InternalArrow { .. } | MapOrigin::Derived(_) => None,
        }
    }
    pub fn source_object(&self) -> ObjectIdentity {
        let root = match &self.origin {
            MapOrigin::Derived(origin) => return origin.source.clone(),
            MapOrigin::Correspondence(_) => self.source_root.clone(),
            MapOrigin::InternalArrow { root, .. } => root.clone(),
        };
        ObjectIdentity {
            reading: self.reading.clone(),
            root,
            subject: self.source_root.clone(),
        }
    }
    pub fn target_object(&self) -> ObjectIdentity {
        let root = match &self.origin {
            MapOrigin::Derived(origin) => return origin.target.clone(),
            MapOrigin::Correspondence(_) => self.target_root.clone(),
            MapOrigin::InternalArrow { root, .. } => root.clone(),
        };
        ObjectIdentity {
            reading: self.to_reading.clone(),
            root,
            subject: self.target_root.clone(),
        }
    }
    pub fn source_root(&self) -> &FactPointer {
        &self.source_root
    }
    pub fn target_root(&self) -> &FactPointer {
        &self.target_root
    }
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn to_reading(&self) -> &str {
        &self.to_reading
    }
    pub fn source_configuration(&self) -> &Configuration {
        &self.source_configuration
    }
    pub fn target_configuration(&self) -> &Configuration {
        &self.target_configuration
    }
    /// 候補作用の再照合。保存の成立はConfigurationMapの再照合で検査する。
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let (candidate, _) = self.recompute(inputs, control)?;
        if candidate.as_ref() != Some(self) {
            return Err(ConstructionFailure::Inconsistent(
                "候補作用が現在の入力・readingと違う".into(),
            ));
        }
        check(control)
    }
    fn recompute(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(Option<MapCandidate>, Option<ConfigurationMap>), ConstructionFailure> {
        match &self.origin {
            MapOrigin::Derived(origin) => {
                let map = operations::recompute(inputs, &origin.steps, control)?;
                Ok((Some(map.candidate.clone()), Some(map)))
            }
            MapOrigin::Correspondence(subject) => {
                let result = correspondence(
                    inputs,
                    &subject.snapshot,
                    &subject.subject,
                    &self.reading,
                    Some(&self.to_reading),
                    control,
                )?;
                Ok((result.candidate, result.map))
            }
            MapOrigin::InternalArrow { root, arrow } => {
                let result = internal_arrow(
                    inputs,
                    &self.reading,
                    &root.snapshot,
                    &root.subject,
                    &arrow.snapshot,
                    &arrow.subject,
                    control,
                )?;
                Ok((result.candidate, result.map))
            }
        }
    }
    pub fn universe(&self) -> &[FactPointer] {
        &self.universe
    }
    pub fn images(&self) -> &[FactPointer] {
        &self.images
    }
    pub fn image(&self, fact: &FactPointer) -> Option<&FactPointer> {
        self.universe
            .iter()
            .position(|f| f == fact)
            .map(|i| &self.images[i])
    }
}
/// 現在の候補作用がF/R/Eと参照構造を保存することを確認した値。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationMap {
    candidate: MapCandidate,
}
impl ConfigurationMap {
    pub fn candidate(&self) -> &MapCandidate {
        &self.candidate
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let (_, map) = self.candidate.recompute(inputs, control)?;
        if map.as_ref() != Some(self) {
            return Err(ConstructionFailure::Inconsistent(
                "保存済みmapが現在の入力・readingと違う".into(),
            ));
        }
        check(control)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Counterexample {
    Field {
        source: FactPointer,
        target_subject: FactPointer,
        target_field: String,
    },
    ReferenceStructure {
        source: FactPointer,
        target: FactPointer,
    },
    /// これらの位置を一つの型付き対応表で同時に保存する補完がない。
    /// 各位置が単独でも不成立である、という主張とは区別する。
    ReferenceConstraints {
        fields: Vec<(FactPointer, FactPointer)>,
        /// holderの像に依存する位置。終域位置を仮定せず、各型付き補完で検査する。
        unresolved_fields: Vec<FactPointer>,
    },
    Family {
        source: FactPointer,
        image: FactPointer,
    },
    Relation {
        source: (FactPointer, FactPointer),
        image: (FactPointer, FactPointer),
    },
    Identification {
        source: (FactPointer, FactPointer),
        image: (FactPointer, FactPointer),
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceFailure {
    cause: ConstructionFailure,
    partial: Option<Box<CorrespondenceResult>>,
}
impl CorrespondenceFailure {
    pub fn cause(&self) -> &ConstructionFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&CorrespondenceResult> {
        self.partial.as_deref()
    }
    pub(crate) fn into_parts(self) -> (ConstructionFailure, Option<Box<CorrespondenceResult>>) {
        (self.cause, self.partial)
    }
}
impl From<ConstructionFailure> for CorrespondenceFailure {
    fn from(cause: ConstructionFailure) -> Self {
        Self {
            cause,
            partial: None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CorrespondenceResult {
    correspondence: FactPointer,
    reading: String,
    to_reading: String,
    source: Option<ConfigurationConstruction>,
    target: Option<ConfigurationConstruction>,
    candidate: Option<MapCandidate>,
    map: Option<ConfigurationMap>,
    missing: Vec<FactPointer>,
    counterexamples: Vec<Counterexample>,
}
impl CorrespondenceResult {
    pub fn correspondence(&self) -> &FactPointer {
        &self.correspondence
    }
    pub fn source(&self) -> Option<&ConfigurationConstruction> {
        self.source.as_ref()
    }
    pub fn target(&self) -> Option<&ConfigurationConstruction> {
        self.target.as_ref()
    }
    pub fn candidate(&self) -> Option<&MapCandidate> {
        self.candidate.as_ref()
    }
    pub fn map(&self) -> Option<&ConfigurationMap> {
        self.map.as_ref()
    }
    pub fn missing(&self) -> &[FactPointer] {
        &self.missing
    }
    pub fn counterexamples(&self) -> &[Counterexample] {
        &self.counterexamples
    }
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn to_reading(&self) -> &str {
        &self.to_reading
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        snapshot: &str,
        subject: &str,
        reading: &str,
        to_reading: Option<&str>,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self != &correspondence(inputs, snapshot, subject, reading, to_reading, control)? {
            return Err(ConstructionFailure::Inconsistent(
                "対応候補・作用・保存結果が現在入力と違う".into(),
            ));
        }
        check(control)
    }
}
fn check(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ConfigurationMap)
        .map_err(Into::into)
}
fn field<'a>(
    subject: &'a Subject,
    name: &str,
    control: &mut Control,
) -> Result<Option<&'a Field>, ConstructionFailure> {
    for f in &subject.fields {
        check(control)?;
        if f.name == name || f.name.rsplit('.').next() == Some(name) {
            return Ok(Some(f));
        }
    }
    Ok(None)
}
fn subject<'a>(
    inputs: &'a CheckedInputs,
    snapshot: &str,
    id: &str,
    control: &mut Control,
) -> Result<&'a Subject, ConstructionFailure> {
    for s in &inputs.archmap().snapshots {
        check(control)?;
        if s.id == snapshot {
            for candidate in &s.subjects {
                check(control)?;
                if candidate.id == id {
                    return Ok(candidate);
                }
            }
        }
    }
    Err(ConstructionFailure::InvalidSelection(format!(
        "subject `@{snapshot}/{id}` がない"
    )))
}
fn key(value: &Value) -> Result<SubjectKey, ConstructionFailure> {
    if let Value::Ref { snapshot, subject } = value {
        Ok((snapshot.clone(), subject.clone()))
    } else {
        Err(ConstructionFailure::Inconsistent(
            "対応表の元が原始参照でない".into(),
        ))
    }
}
fn endpoint(
    holder: &Subject,
    name: &str,
    missing: &mut BTreeSet<FactPointer>,
    control: &mut Control,
) -> Result<Option<SubjectKey>, ConstructionFailure> {
    let f = field(holder, name, control)?
        .ok_or_else(|| ConstructionFailure::Inconsistent(format!("原始候補の{name} slotがない")))?;
    match &f.slot {
        Slot::Known { value, .. } => Ok(Some(key(value)?)),
        Slot::Missing => {
            missing.insert(slot(holder, &f.name));
            Ok(None)
        }
    }
}
// 参照へ至る構造だけを比較する。Map/Setの列挙順は意味に含めず、Listの順は保持する。
// 量だけの部分木はNoneとし、その値をconfiguration保存条件へ追加しない。
fn reference_shape(
    value: &Value,
    moved: &BTreeMap<SubjectKey, SubjectKey>,
    control: &mut Control,
) -> Result<Option<String>, ConstructionFailure> {
    enum Work<'a> {
        Visit(&'a Value),
        Join(String, usize, bool),
    }
    let mut work = vec![Work::Visit(value)];
    let mut values: Vec<Option<String>> = Vec::new();
    while let Some(item) = work.pop() {
        check(control)?;
        match item {
            Work::Visit(Value::Ref { snapshot, subject }) => {
                let k = (snapshot.clone(), subject.clone());
                let image = moved.get(&k).unwrap_or(&k);
                values.push(Some(
                    Json::Arr(vec![Json::str(&image.0), Json::str(&image.1)]).canonical(),
                ));
            }
            Work::Visit(Value::Tuple(items))
            | Work::Visit(Value::List(items))
            | Work::Visit(Value::Set(items)) => {
                let (tag, sort) = match item {
                    Work::Visit(Value::Tuple(_)) => ("tuple", false),
                    Work::Visit(Value::List(_)) => ("list", false),
                    _ => ("set", true),
                };
                work.push(Work::Join(tag.into(), items.len(), sort));
                for v in items.iter().rev() {
                    check(control)?;
                    work.push(Work::Visit(v));
                }
            }
            Work::Visit(Value::Option(Some(v))) => {
                work.push(Work::Join("some".into(), 1, false));
                work.push(Work::Visit(v));
            }
            Work::Visit(Value::Data { constructor, args }) => {
                work.push(Work::Join(format!("data:{constructor}"), args.len(), false));
                for v in args.iter().rev() {
                    check(control)?;
                    work.push(Work::Visit(v));
                }
            }
            Work::Visit(Value::Map(pairs)) => {
                work.push(Work::Join("map".into(), pairs.len(), true));
                for (k, v) in pairs.iter().rev() {
                    check(control)?;
                    work.push(Work::Join("entry".into(), 2, false));
                    work.push(Work::Visit(v));
                    work.push(Work::Visit(k));
                }
            }
            Work::Visit(_) => values.push(None),
            Work::Join(tag, n, sort) => {
                let at = values.len().checked_sub(n).ok_or_else(|| {
                    ConstructionFailure::Inconsistent("参照構造の構成stackが不足".into())
                })?;
                let mut children = values.split_off(at);
                if children.iter().all(Option::is_none) {
                    values.push(None);
                    continue;
                }
                if sort {
                    children.sort();
                }
                // Setは像集合、Mapは同じkey/valueの像を一行として扱う。
                // List/Tupleの位置・重複は縮約しない。
                if tag == "set" || tag == "map" {
                    children.dedup();
                }
                let mut out = format!("{}:{tag}:{}:", tag.len(), children.len());
                for child in children {
                    check(control)?;
                    let child = child.unwrap_or_else(|| "quantity".into());
                    out.push_str(&format!("{}:{child}", child.len()));
                }
                values.push(Some(out));
            }
        }
    }
    check(control)?;
    if values.len() != 1 {
        return Err(ConstructionFailure::Inconsistent(
            "参照構造の構成stackが不整合".into(),
        ));
    }
    Ok(values.pop().flatten())
}
// 像が未決のleafだけを変数として扱い、既知の参照構造を失わない。
// 保存できる補完では各参照像がtarget値に現れるため、その有限族を全列挙すれば
// 確定違反を検査できる。型/owner条件を緩めた族にも解がなければ全補完で反証される。
fn reference_violation(
    source: &Value,
    target: &Value,
    moved: &BTreeMap<SubjectKey, SubjectKey>,
    unknown: &BTreeSet<SubjectKey>,
    control: &mut Control,
) -> Result<bool, ConstructionFailure> {
    reference_constraints_violation(&[(source, target)], moved, unknown, control)
}
fn reference_constraints_violation(
    fields: &[(&Value, &Value)],
    moved: &BTreeMap<SubjectKey, SubjectKey>,
    unknown: &BTreeSet<SubjectKey>,
    control: &mut Control,
) -> Result<bool, ConstructionFailure> {
    let mut variables = BTreeSet::new();
    let mut target_shapes = Vec::new();
    for (source, target) in fields {
        check(control)?;
        for (snapshot, id) in references(source, control)? {
            check(control)?;
            let k = (snapshot.to_owned(), id.to_owned());
            if unknown.contains(&k) {
                variables.insert(k);
            }
        }
        target_shapes.push(reference_shape(target, &BTreeMap::new(), control)?);
    }
    let matches = |trial: &BTreeMap<SubjectKey, SubjectKey>,
                   control: &mut Control|
     -> Result<bool, ConstructionFailure> {
        for ((source, _), shape) in fields.iter().zip(&target_shapes) {
            check(control)?;
            if reference_shape(source, trial, control)? != *shape {
                return Ok(false);
            }
        }
        Ok(true)
    };
    if variables.is_empty() {
        return Ok(!matches(moved, control)?);
    }
    let mut trial = BTreeMap::new();
    for (from, to) in moved {
        check(control)?;
        trial.insert(from.clone(), to.clone());
    }
    // 順序付きの位置から決まる像を先に解決する。Listの長さ違反などに
    // 無用な補完全列挙をせず、同じ未知参照の反復にも同じ像を要求する。
    let mut pairs = Vec::new();
    for pair in fields {
        check(control)?;
        pairs.push(*pair);
    }
    while let Some((a, b)) = pairs.pop() {
        check(control)?;
        if references(a, control)?.is_empty() && references(b, control)?.is_empty() {
            continue;
        }
        match (a, b) {
            (
                Value::Ref { snapshot, subject },
                Value::Ref {
                    snapshot: ts,
                    subject: ti,
                },
            ) => {
                let k = (snapshot.clone(), subject.clone());
                let target = (ts.clone(), ti.clone());
                if unknown.contains(&k) {
                    if let Some(previous) = trial.insert(k, target.clone()) {
                        if previous != target {
                            return Ok(true);
                        }
                    }
                } else if trial.get(&k).unwrap_or(&k) != &target {
                    return Ok(true);
                }
            }
            (Value::List(a), Value::List(b)) | (Value::Tuple(a), Value::Tuple(b)) => {
                if a.len() != b.len() {
                    return Ok(true);
                }
                for pair in a.iter().zip(b) {
                    check(control)?;
                    pairs.push(pair);
                }
            }
            (Value::Option(Some(a)), Value::Option(Some(b))) => pairs.push((a, b)),
            (
                Value::Data {
                    constructor: a,
                    args: aa,
                },
                Value::Data {
                    constructor: b,
                    args: ba,
                },
            ) => {
                if a != b || aa.len() != ba.len() {
                    return Ok(true);
                }
                for pair in aa.iter().zip(ba) {
                    check(control)?;
                    pairs.push(pair);
                }
            }
            (Value::Map(_), Value::Map(_)) | (Value::Set(_), Value::Set(_)) => {}
            _ => return Ok(true),
        }
    }
    variables.retain(|k| !trial.contains_key(k));
    if variables.is_empty() {
        return Ok(!matches(&trial, control)?);
    }
    let mut domain = BTreeSet::new();
    for (_, target) in fields {
        check(control)?;
        for (snapshot, id) in references(target, control)? {
            check(control)?;
            domain.insert((snapshot.to_owned(), id.to_owned()));
        }
    }
    if domain.is_empty() {
        return Ok(true);
    }
    let domain: Vec<_> = domain.into_iter().collect();
    let variables: Vec<_> = variables.into_iter().collect();
    let mut positions = vec![0; variables.len()];
    loop {
        check(control)?;
        for (variable, position) in variables.iter().zip(&positions) {
            check(control)?;
            trial.insert(variable.clone(), domain[*position].clone());
        }
        if matches(&trial, control)? {
            return Ok(false);
        }
        let mut next = false;
        for position in positions.iter_mut().rev() {
            check(control)?;
            if *position < domain.len() - 1 {
                *position += 1;
                next = true;
                break;
            }
            *position = 0;
        }
        if !next {
            check(control)?;
            return Ok(true);
        }
    }
}
// 欠測Mapの各keyは、終域の型/ownerに適合する像か、始域外で固定する場合を持つ。
// 完成候補のMap値は原始入力の補完仮説であり、結果JSONの逆取込みには使わない。
struct MappingVariable {
    source: SubjectKey,
    field: String,
    images: Vec<Option<SubjectKey>>,
}
fn typed_reference_constraints_violation(
    inputs: &CheckedInputs,
    holder: &Subject,
    maps: &[(String, String, String)],
    to: &SubjectKey,
    moved: &BTreeMap<SubjectKey, SubjectKey>,
    unknown: &BTreeSet<SubjectKey>,
    fields: &[(&Value, &Value)],
    unresolved_fields: &[FactPointer],
    field_map: &BTreeMap<&str, &str>,
    control: &mut Control,
) -> Result<bool, ConstructionFailure> {
    if reference_constraints_violation(fields, moved, unknown, control)? {
        return Ok(true);
    }
    let mut variables = Vec::new();
    for k in unknown {
        check(control)?;
        let source = subject(inputs, &k.0, &k.1, control)?;
        let mut selected = None;
        for (name, source_type, target_type) in maps {
            check(control)?;
            if source_type == &source.ty {
                selected = Some((name, target_type));
                break;
            }
        }
        let (name, target_type) = selected
            .ok_or_else(|| ConstructionFailure::Inconsistent("未決subjectの型対応がない".into()))?;
        let map_field = field(holder, name, control)?
            .ok_or_else(|| ConstructionFailure::Inconsistent("原始Map slotがない".into()))?;
        let mut images = Vec::new();
        if matches!(map_field.slot, Slot::Known { .. }) {
            // 既知全域表のkeyにないsubjectは、ownerが未観測でも始域外。
            images.push(None);
        } else {
            let owner = field(source, "owner", control)?
                .ok_or_else(|| ConstructionFailure::Inconsistent("始域owner slotがない".into()))?;
            if owner.slot == Slot::Missing {
                images.push(None);
            }
            for snapshot in &inputs.archmap().snapshots {
                check(control)?;
                for target in &snapshot.subjects {
                    check(control)?;
                    if &target.ty != target_type {
                        continue;
                    }
                    let owner = field(target, "owner", control)?.ok_or_else(|| {
                        ConstructionFailure::Inconsistent("終域owner slotがない".into())
                    })?;
                    if matches!(&owner.slot, Slot::Known { value, .. } if &key(value)? != to) {
                        continue;
                    }
                    images.push(Some((target.snapshot.clone(), target.id.clone())));
                }
            }
        }
        if images.is_empty() {
            return Ok(true);
        }
        variables.push(MappingVariable {
            source: k.clone(),
            field: map_field.name.clone(),
            images,
        });
    }
    // 一つの像だけで既知の位置に違反する選択を先に除き、無関係なkeyの
    // 組合せを列挙する前に型付きの確定違反を返す。
    for variable in &mut variables {
        check(control)?;
        let mut remaining = BTreeSet::new();
        for k in unknown {
            check(control)?;
            if k != &variable.source {
                remaining.insert(k.clone());
            }
        }
        let mut admissible = Vec::new();
        for image in &variable.images {
            check(control)?;
            let mut trial = BTreeMap::new();
            for (source, target) in moved {
                check(control)?;
                trial.insert(source.clone(), target.clone());
            }
            trial.insert(
                variable.source.clone(),
                image.as_ref().unwrap_or(&variable.source).clone(),
            );
            if !reference_constraints_violation(fields, &trial, &remaining, control)? {
                admissible.push(image.clone());
            }
        }
        if admissible.is_empty() {
            return Ok(true);
        }
        variable.images = admissible;
    }
    let mut target_shapes = Vec::new();
    for (_, target) in fields {
        check(control)?;
        target_shapes.push(reference_shape(target, &BTreeMap::new(), control)?);
    }
    let mut positions = vec![0; variables.len()];
    loop {
        check(control)?;
        let mut trial = BTreeMap::new();
        let mut inside = BTreeSet::new();
        for (source, target) in moved {
            check(control)?;
            trial.insert(source.clone(), target.clone());
        }
        for (variable, position) in variables.iter().zip(&positions) {
            check(control)?;
            if variable.images[*position].is_some() {
                inside.insert(variable.source.clone());
            }
            trial.insert(
                variable.source.clone(),
                variable.images[*position]
                    .as_ref()
                    .unwrap_or(&variable.source)
                    .clone(),
            );
        }
        let mut matches = true;
        for ((source, _), target_shape) in fields.iter().zip(&target_shapes) {
            check(control)?;
            if reference_shape(source, &trial, control)? != *target_shape {
                matches = false;
                break;
            }
        }
        if matches {
            for fact in unresolved_fields {
                check(control)?;
                let k = (fact.snapshot.clone(), fact.subject.clone());
                if !inside.contains(&k) {
                    continue;
                }
                let source = subject(inputs, &k.0, &k.1, control)?;
                let image = trial.get(&k).ok_or_else(|| {
                    ConstructionFailure::Inconsistent("補完したholderの像がない".into())
                })?;
                let target = subject(inputs, &image.0, &image.1, control)?;
                let source_field = fact.field.as_deref().ok_or_else(|| {
                    ConstructionFailure::Inconsistent("参照条件にfieldがない".into())
                })?;
                let name = field_map
                    .get(source_field)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| {
                        format!(
                            "{}.{}",
                            target.ty,
                            source_field.rsplit('.').next().unwrap_or(source_field)
                        )
                    });
                let Some(tf) = field(target, &name, control)? else {
                    matches = false;
                    break;
                };
                let Some(sf) = field(source, source_field, control)? else {
                    return Err(ConstructionFailure::Inconsistent(
                        "参照条件の元fieldがない".into(),
                    ));
                };
                if let (Slot::Known { value: a, .. }, Slot::Known { value: b, .. }) =
                    (&sf.slot, &tf.slot)
                {
                    if reference_shape(a, &trial, control)?
                        != reference_shape(b, &BTreeMap::new(), control)?
                    {
                        matches = false;
                        break;
                    }
                }
            }
        }
        if matches {
            let mut assignments = Vec::new();
            for (name, _, _) in maps {
                check(control)?;
                let map_field = field(holder, name, control)?.ok_or_else(|| {
                    ConstructionFailure::Inconsistent("原始Map slotがない".into())
                })?;
                if map_field.slot != Slot::Missing {
                    continue;
                }
                let mut rows = Vec::new();
                for (variable, position) in variables.iter().zip(&positions) {
                    check(control)?;
                    if variable.field == map_field.name {
                        if let Some(image) = &variable.images[*position] {
                            rows.push(Json::Arr(vec![
                                Json::Arr(vec![
                                    Json::str(&variable.source.0),
                                    Json::str(&variable.source.1),
                                ]),
                                Json::Arr(vec![Json::str(&image.0), Json::str(&image.1)]),
                            ]));
                        }
                    }
                }
                assignments.push(crate::archmap::FieldAssignment {
                    snapshot: holder.snapshot.clone(),
                    subject: holder.id.clone(),
                    field: map_field.name.clone(),
                    value: Json::Arr(rows),
                });
            }
            use crate::observed::control::CheckFailure;
            match crate::archmap::check_completion_with_values::<
                CheckFailure<Box<crate::issue::Issue>>,
            >(
                &inputs.archmap().snapshots,
                inputs.definitions(),
                &assignments,
                control,
            ) {
                Ok(()) => return Ok(false),
                Err(CheckFailure::Input(issue))
                    if issue.code == crate::issue::Code::InconsistentObservation => {}
                Err(CheckFailure::Input(issue)) => {
                    return Err(ConstructionFailure::Inconsistent(issue.message));
                }
                Err(CheckFailure::Stopped(reason)) => return Err(reason.into()),
            }
        }
        let mut next = false;
        for (position, variable) in positions.iter_mut().zip(&variables).rev() {
            check(control)?;
            if *position < variable.images.len() - 1 {
                *position += 1;
                next = true;
                break;
            }
            *position = 0;
        }
        if !next {
            check(control)?;
            return Ok(true);
        }
    }
}
fn preservation_counterexamples(
    source_config: &Configuration,
    target_config: &Configuration,
    target_complete: bool,
    action: &BTreeMap<FactPointer, FactPointer>,
    control: &mut Control,
) -> Result<Vec<Counterexample>, ConstructionFailure> {
    let mut counterexamples = Vec::new();
    let target_family: BTreeSet<_> = target_config.family().iter().collect();
    let target_relations: BTreeSet<_> = target_config.relations().iter().collect();
    let target_identifications: BTreeSet<_> = target_config.identifications().iter().collect();
    for source in source_config.family() {
        check(control)?;
        let Some(image) = action.get(source).cloned() else {
            continue;
        };
        if target_complete && !target_family.contains(&image) {
            counterexamples.push(Counterexample::Family {
                source: source.clone(),
                image,
            });
        }
    }
    for (identifications, pairs) in [
        (false, source_config.relations()),
        (true, source_config.identifications()),
    ] {
        for pair in pairs {
            check(control)?;
            let (Some(left), Some(right)) = (action.get(&pair.0), action.get(&pair.1)) else {
                continue;
            };
            let image = (left.clone(), right.clone());
            let preserved = if identifications {
                target_identifications.contains(&image)
            } else {
                target_relations.contains(&image)
            };
            if target_complete && !preserved {
                counterexamples.push(if identifications {
                    Counterexample::Identification {
                        source: pair.clone(),
                        image,
                    }
                } else {
                    Counterexample::Relation {
                        source: pair.clone(),
                        image,
                    }
                });
            }
        }
    }
    Ok(counterexamples)
}
/// readingを推測せず、現在の原始correspondence instanceから全U上の作用と保存を検査する。
pub fn correspondence(
    inputs: &CheckedInputs,
    snapshot: &str,
    id: &str,
    reading: &str,
    to_reading: Option<&str>,
    control: &mut Control,
) -> Result<CorrespondenceResult, ConstructionFailure> {
    correspondence_retained(inputs, snapshot, id, reading, to_reading, control)
        .map_err(|failure| failure.cause)
}
/// 停止時にも、この呼出しで検査済みの候補・保存結果・反例を保持する。
pub fn correspondence_retained(
    inputs: &CheckedInputs,
    snapshot: &str,
    id: &str,
    reading: &str,
    to_reading: Option<&str>,
    control: &mut Control,
) -> Result<CorrespondenceResult, CorrespondenceFailure> {
    check(control)?;
    let holder = subject(inputs, snapshot, id, control)?;
    let declaration = inputs
        .definitions()
        .declarations
        .get(&holder.ty)
        .ok_or_else(|| ConstructionFailure::Inconsistent("対応の元定義がない".into()))?;
    let PrimitiveSignature::Correspondence {
        from,
        to,
        maps,
        alignments,
        implicit,
        ..
    } = &declaration.signature
    else {
        return Err(ConstructionFailure::InvalidSelection(
            "mapは原始correspondence instanceを要求する".into(),
        )
        .into());
    };
    let to_reading = to_reading.unwrap_or(reading);
    for (reading, ty) in [(reading, from), (to_reading, to)] {
        let namespaces = namespaces(inputs, reading, control)?;
        if !visible(inputs, ty, &namespaces) {
            return Err(ConstructionFailure::InvalidSelection(format!(
                "根型 `{ty}` はreading `{reading}` の定義にない"
            ))
            .into());
        }
    }
    let mut result = CorrespondenceResult {
        correspondence: exists(holder),
        reading: reading.into(),
        to_reading: to_reading.into(),
        source: None,
        target: None,
        candidate: None,
        map: None,
        missing: vec![],
        counterexamples: vec![],
    };
    let mut missing = BTreeSet::new();
    let computed = (|| -> Result<(), ConstructionFailure> {
        let from = endpoint(holder, "from", &mut missing, control)?;
        let to = endpoint(holder, "to", &mut missing, control)?;

        if let Some((s, id)) = &from {
            result.source = Some(construct(inputs, reading, s, id, control)?);
        }
        if let Some((s, id)) = &to {
            result.target = Some(construct(inputs, to_reading, s, id, control)?);
        }
        let mut moved = BTreeMap::new();
        if let (Some(from), Some(to)) = (&from, &to) {
            moved.insert(from.clone(), to.clone());
        }
        for (name, _, _) in maps {
            check(control)?;
            let f = field(holder, name, control)?
                .ok_or_else(|| ConstructionFailure::Inconsistent("対応表slotがない".into()))?;
            match &f.slot {
                Slot::Missing => {
                    missing.insert(slot(holder, &f.name));
                }
                Slot::Known {
                    value: Value::Map(pairs),
                    ..
                } => {
                    for (source, target) in pairs {
                        check(control)?;
                        moved.insert(key(source)?, key(target)?);
                    }
                }
                _ => {
                    return Err(ConstructionFailure::Inconsistent(
                        "原始対応表の型がMapでない".into(),
                    ));
                }
            }
        }
        for construction in [&result.source, &result.target].into_iter().flatten() {
            for f in construction.base().blocking_slots() {
                check(control)?;
                missing.insert(f.clone());
            }
        }
        let (Some(source), Some(target)) = (&result.source, &result.target) else {
            result.missing = canonical_facts(missing.clone(), control)?;
            check(control)?;
            return Ok(());
        };
        if source.universe() != target.universe() {
            return Err(ConstructionFailure::Inconsistent(
                "始終域の共通Uが違う".into(),
            ));
        }
        let source_config = source.base().known();
        let target_config = target.base().known();
        let target_complete = target.base().configuration().is_some();
        // 表の欠測や未観測ownerを「対象外だから固定」と読み替えない。
        let mut unknown_subjects = BTreeSet::new();
        for snapshot in &inputs.archmap().snapshots {
            check(control)?;
            for s in &snapshot.subjects {
                check(control)?;
                let k = (s.snapshot.clone(), s.id.clone());
                if moved.contains_key(&k) {
                    continue;
                }
                let mut in_domain = false;
                for (_, ty, _) in maps {
                    check(control)?;
                    in_domain |= ty == &s.ty;
                }
                if !in_domain {
                    continue;
                }
                let owner = field(s, "owner", control)?.ok_or_else(|| {
                    ConstructionFailure::Inconsistent("対応域のownerがない".into())
                })?;
                match &owner.slot {
                    Slot::Missing => {
                        unknown_subjects.insert(k);
                    }
                    Slot::Known { value, .. } if Some(key(value)?) == from => {
                        unknown_subjects.insert(k);
                    }
                    _ => {}
                }
            }
        }
        let family: BTreeSet<_> = source_config.family().iter().cloned().collect();
        let mut field_map = BTreeMap::new();
        for (s, t) in implicit {
            check(control)?;
            field_map.insert(s.as_str(), t.as_str());
        }
        for pair in alignments {
            check(control)?;
            field_map.insert(pair.source.as_str(), pair.target.as_str());
        }
        let mut unresolved_fields = Vec::new();
        let source_namespaces = namespaces(inputs, reading, control)?;
        for k in &unknown_subjects {
            check(control)?;
            let source = subject(inputs, &k.0, &k.1, control)?;
            if !visible(inputs, &source.ty, &source_namespaces) {
                continue;
            }
            for f in &source.fields {
                check(control)?;
                if let Slot::Known { atom, value, .. } = &f.slot {
                    if !references(value, control)?.is_empty() {
                        unresolved_fields.push(FactPointer {
                            atom: Some(atom.clone()),
                            ..slot(source, &f.name)
                        });
                    }
                }
            }
        }
        let mut images = Vec::new();
        let mut action = BTreeMap::new();
        let mut reference_fields = Vec::new();
        let mut reference_values = Vec::new();
        let mut absent = false;
        for fact in source.universe() {
            check(control)?;
            if !family.contains(fact) {
                images.push(target.root().clone());
                action.insert(fact.clone(), target.root().clone());
                continue;
            }
            let original = subject(inputs, &fact.snapshot, &fact.subject, control)?;
            let k = (fact.snapshot.clone(), fact.subject.clone());
            if unknown_subjects.contains(&k) {
                absent = true;
                continue;
            }
            let image_key = moved.get(&k).unwrap_or(&k);
            let image_subject = subject(inputs, &image_key.0, &image_key.1, control)?;
            if let Some(source_field) = &fact.field {
                let target_field = field_map
                    .get(source_field.as_str())
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| {
                        format!(
                            "{}.{}",
                            image_subject.ty,
                            source_field.rsplit('.').next().unwrap_or(source_field)
                        )
                    });
                let Some(tf) = field(image_subject, &target_field, control)? else {
                    result.counterexamples.push(Counterexample::Field {
                        source: fact.clone(),
                        target_subject: exists(image_subject),
                        target_field,
                    });
                    absent = true;
                    continue;
                };
                match &tf.slot {
                    Slot::Missing => {
                        missing.insert(slot(image_subject, &tf.name));
                        absent = true;
                    }
                    Slot::Known { atom, value, .. } => {
                        let image = FactPointer {
                            atom: Some(atom.clone()),
                            ..slot(image_subject, &tf.name)
                        };
                        let sf = field(original, source_field, control)?.ok_or_else(|| {
                            ConstructionFailure::Inconsistent("始域のfieldがない".into())
                        })?;
                        let Slot::Known {
                            value: source_value,
                            ..
                        } = &sf.slot
                        else {
                            return Err(ConstructionFailure::Inconsistent(
                                "始域のAtom値がない".into(),
                            ));
                        };
                        if reference_violation(
                            source_value,
                            value,
                            &moved,
                            &unknown_subjects,
                            control,
                        )? {
                            result
                                .counterexamples
                                .push(Counterexample::ReferenceStructure {
                                    source: fact.clone(),
                                    target: image.clone(),
                                });
                        }
                        let mut unresolved = false;
                        for (snapshot, id) in references(source_value, control)? {
                            check(control)?;
                            unresolved |= unknown_subjects.contains(&(snapshot.into(), id.into()));
                        }
                        if unresolved {
                            reference_fields.push((fact.clone(), image.clone()));
                            reference_values.push((source_value, value));
                        }
                        action.insert(fact.clone(), image.clone());
                        images.push(image);
                    }
                }
            } else {
                let image = exists(image_subject);
                action.insert(fact.clone(), image.clone());
                images.push(image);
            }
        }
        if (!reference_values.is_empty() || !unresolved_fields.is_empty())
            && !result
                .counterexamples
                .iter()
                .any(|c| matches!(c, Counterexample::ReferenceStructure { .. }))
            && typed_reference_constraints_violation(
                inputs,
                holder,
                maps,
                &(
                    target.root().snapshot.clone(),
                    target.root().subject.clone(),
                ),
                &moved,
                &unknown_subjects,
                &reference_values,
                &unresolved_fields,
                &field_map,
                control,
            )?
        {
            result
                .counterexamples
                .push(Counterexample::ReferenceConstraints {
                    fields: reference_fields,
                    unresolved_fields,
                });
        }
        result.missing = canonical_facts(missing.clone(), control)?;
        result.counterexamples.extend(preservation_counterexamples(
            source_config,
            target_config,
            target_complete,
            &action,
            control,
        )?);
        if !absent && result.missing.is_empty() {
            let candidate = MapCandidate {
                origin: MapOrigin::Correspondence(exists(holder)),
                source_root: source.root().clone(),
                target_root: target.root().clone(),
                reading: reading.into(),
                to_reading: to_reading.into(),
                source_configuration: source_config.clone(),
                target_configuration: target_config.clone(),
                universe: source.universe().to_vec(),
                images,
            };
            if result.counterexamples.is_empty() {
                result.map = Some(ConfigurationMap {
                    candidate: candidate.clone(),
                });
            }
            result.candidate = Some(candidate);
        }
        check(control)?;
        Ok(())
    })();
    match computed {
        Ok(()) => Ok(result),
        Err(cause) => {
            if result.missing.is_empty() {
                result.missing = missing.into_iter().collect();
            }
            Err(CorrespondenceFailure {
                cause,
                partial: Some(Box::new(result)),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::input::{InputSources, check_inputs};
    #[test]
    fn reference_projection_checks_map_image_collisions_and_shared_unknown_leaves() {
        let reference = |id: &str| Value::Ref {
            snapshot: "v".into(),
            subject: id.into(),
        };
        let moved = BTreeMap::from([
            (("v".into(), "p".into()), ("v".into(), "r".into())),
            (("v".into(), "q".into()), ("v".into(), "r".into())),
        ]);
        let source = Value::Map(vec![
            (reference("p"), reference("x")),
            (reference("q"), reference("x")),
        ]);
        let target = Value::Map(vec![(reference("r"), reference("x"))]);
        assert!(
            !reference_violation(
                &source,
                &target,
                &moved,
                &BTreeSet::new(),
                &mut Control::unlimited()
            )
            .unwrap()
        );
        let conflicting = Value::Map(vec![
            (reference("p"), reference("x")),
            (reference("q"), reference("y")),
        ]);
        assert!(
            reference_violation(
                &conflicting,
                &target,
                &moved,
                &BTreeSet::new(),
                &mut Control::unlimited()
            )
            .unwrap()
        );
        let unknown = BTreeSet::from([("v".into(), "p".into())]);
        let source = Value::Tuple(vec![
            reference("p"),
            Value::Option(Some(Box::new(reference("p")))),
        ]);
        let target = Value::Tuple(vec![
            reference("r"),
            Value::Option(Some(Box::new(reference("s")))),
        ]);
        assert!(
            reference_violation(
                &source,
                &target,
                &BTreeMap::new(),
                &unknown,
                &mut Control::unlimited()
            )
            .unwrap()
        );
    }
    fn inputs(bad: bool, missing: bool) -> CheckedInputs {
        let mut map = include_str!("../../tests/fixtures/reservations.archmap.json").to_owned();
        if bad {
            map = map
                .lines()
                .map(|line| {
                    if line.contains("\"id\": \"m-states\"") {
                        line.replace("[\"v\", \"r\"]", "[\"v\", \"temp\"]")
                            .replace("[\"v\", \"s\"]", "[\"v\", \"r\"]")
                            .replace("[\"v\", \"temp\"]", "[\"v\", \"s\"]")
                    } else {
                        line.to_owned()
                    }
                })
                .collect::<Vec<_>>()
                .join("\n");
        }
        if missing {
            map = map
                .lines()
                .filter(|line| !line.contains("\"id\": \"r-free\""))
                .collect::<Vec<_>>()
                .join("\n");
        }
        check_inputs(
            InputSources::from_bytes(
                vec![include_bytes!("../../tests/fixtures/reservations.atoms.json").to_vec()],
                include_bytes!("../../tests/fixtures/reservations.law").to_vec(),
                map.into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap_or_else(|f| panic!("{:?}", f.issues()))
    }
    #[test]
    fn recheck_rejects_forged_actions_preservation_counterexamples_and_missing_conditions() {
        let inputs = inputs(false, false);
        let original = correspondence(
            &inputs,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        original
            .recheck(
                &inputs,
                "v",
                "m",
                "Reservations",
                None,
                &mut Control::unlimited(),
            )
            .unwrap();
        for kind in [
            "action",
            "verified",
            "reading",
            "candidate",
            "correspondence",
        ] {
            let mut forged = original.clone();
            match kind {
                "action" => {
                    forged.candidate.as_mut().unwrap().images[0] =
                        original.candidate.as_ref().unwrap().source_root.clone()
                }
                "verified" => forged.map.as_mut().unwrap().candidate.images.swap(0, 1),
                "reading" => forged.to_reading = "other".into(),
                "candidate" => forged.candidate = None,
                "correspondence" => forged.correspondence.subject = "other".into(),
                _ => unreachable!(),
            }
            assert!(
                matches!(
                    forged.recheck(
                        &inputs,
                        "v",
                        "m",
                        "Reservations",
                        None,
                        &mut Control::unlimited()
                    ),
                    Err(ConstructionFailure::Inconsistent(_))
                ),
                "{kind}"
            );
        }
        let bad = self::inputs(true, false);
        let mut forged = correspondence(
            &bad,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(!forged.counterexamples.is_empty());
        assert!(forged.map.is_none());
        forged.counterexamples.clear();
        forged.map = Some(ConfigurationMap {
            candidate: forged.candidate.clone().unwrap(),
        });
        assert!(
            matches!(
                forged.recheck(
                    &bad,
                    "v",
                    "m",
                    "Reservations",
                    None,
                    &mut Control::unlimited()
                ),
                Err(ConstructionFailure::Inconsistent(_))
            ),
            "反例を消して検査済みmapを偽造できない"
        );
        let partial = self::inputs(false, true);
        let mut forged = correspondence(
            &partial,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        assert!(!forged.missing.is_empty());
        forged.missing.clear();
        forged.candidate = original.candidate.clone();
        forged.map = original.map.clone();
        assert!(
            matches!(
                forged.recheck(
                    &partial,
                    "v",
                    "m",
                    "Reservations",
                    None,
                    &mut Control::unlimited()
                ),
                Err(ConstructionFailure::Inconsistent(_))
            ),
            "未知の像を旧候補で埋めない"
        );
    }
}
