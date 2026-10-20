//! 原始correspondenceの実作用とConfiguration保存を、現在の入力から検査する。
use super::*;
use crate::archmap::Field;

type SubjectKey = (String, String);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapCandidate {
    correspondence: FactPointer,
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
    pub fn correspondence(&self) -> &FactPointer {
        &self.correspondence
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
        let result = correspondence(
            inputs,
            &self.correspondence.snapshot,
            &self.correspondence.subject,
            &self.reading,
            Some(&self.to_reading),
            control,
        )?;
        if result.candidate.as_ref() != Some(self) {
            return Err(ConstructionFailure::Inconsistent(
                "候補作用が現在の入力・readingと違う".into(),
            ));
        }
        check(control)
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
        let candidate = &self.candidate;
        let result = correspondence(
            inputs,
            &candidate.correspondence.snapshot,
            &candidate.correspondence.subject,
            &candidate.reading,
            Some(&candidate.to_reading),
            control,
        )?;
        if result.map.as_ref() != Some(self) {
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
    let f = field(holder, name, control)?.ok_or_else(|| {
        ConstructionFailure::Inconsistent(format!("correspondenceの{name} slotがない"))
    })?;
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
                let mut out = format!("{}:{tag}:{n}:", tag.len());
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
/// readingを推測せず、現在の原始correspondence instanceから全U上の作用と保存を検査する。
pub fn correspondence(
    inputs: &CheckedInputs,
    snapshot: &str,
    id: &str,
    reading: &str,
    to_reading: Option<&str>,
    control: &mut Control,
) -> Result<CorrespondenceResult, ConstructionFailure> {
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
        ));
    };
    let to_reading = to_reading.unwrap_or(reading);
    for (reading, ty) in [(reading, from), (to_reading, to)] {
        let namespaces = namespaces(inputs, reading, control)?;
        if !visible(inputs, ty, &namespaces) {
            return Err(ConstructionFailure::InvalidSelection(format!(
                "根型 `{ty}` はreading `{reading}` の定義にない"
            )));
        }
    }
    let mut missing = BTreeSet::new();
    let from = endpoint(holder, "from", &mut missing, control)?;
    let to = endpoint(holder, "to", &mut missing, control)?;
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
        result.missing = canonical_facts(missing, control)?;
        check(control)?;
        return Ok(result);
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
            let owner = field(s, "owner", control)?
                .ok_or_else(|| ConstructionFailure::Inconsistent("対応域のownerがない".into()))?;
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
    let mut images = Vec::new();
    let mut action = BTreeMap::new();
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
                    let mut known_references = true;
                    for (snapshot, id) in references(source_value, control)? {
                        check(control)?;
                        if unknown_subjects.contains(&(snapshot.into(), id.into())) {
                            known_references = false;
                        }
                    }
                    if known_references
                        && reference_shape(source_value, &moved, control)?
                            != reference_shape(value, &BTreeMap::new(), control)?
                    {
                        result
                            .counterexamples
                            .push(Counterexample::ReferenceStructure {
                                source: fact.clone(),
                                target: image.clone(),
                            });
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
    result.missing = canonical_facts(missing, control)?;
    let target_family: BTreeSet<_> = target_config.family().iter().collect();
    let target_relations: BTreeSet<_> = target_config.relations().iter().collect();
    let target_identifications: BTreeSet<_> = target_config.identifications().iter().collect();
    for source in source_config.family() {
        check(control)?;
        let Some(image) = action.get(source).cloned() else {
            continue;
        };
        if target_complete && !target_family.contains(&image) {
            result.counterexamples.push(Counterexample::Family {
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
                result.counterexamples.push(if identifications {
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
    if !absent && result.missing.is_empty() {
        let candidate = MapCandidate {
            correspondence: exists(holder),
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
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::input::{InputSources, check_inputs};
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
