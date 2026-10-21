//! 部分対象間の内部arrow。全候補を保持し、保存未確認のarrowを落とさない。
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InternalArrowResult {
    root: FactPointer,
    arrow: FactPointer,
    reading: String,
    source: Option<ObjectComponent>,
    target: Option<ObjectComponent>,
    pub(super) candidate: Option<MapCandidate>,
    pub(super) map: Option<ConfigurationMap>,
    missing: Vec<FactPointer>,
    counterexamples: Vec<Counterexample>,
}
impl InternalArrowResult {
    pub fn root(&self) -> &FactPointer {
        &self.root
    }
    pub fn arrow(&self) -> &FactPointer {
        &self.arrow
    }
    pub fn reading(&self) -> &str {
        &self.reading
    }
    pub fn source(&self) -> Option<&ObjectComponent> {
        self.source.as_ref()
    }
    pub fn target(&self) -> Option<&ObjectComponent> {
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
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let expected = internal_arrow(
            inputs,
            &self.reading,
            &self.root.snapshot,
            &self.root.subject,
            &self.arrow.snapshot,
            &self.arrow.subject,
            control,
        )?;
        if self != &expected {
            return Err(ConstructionFailure::Inconsistent(
                "内部arrowの構成・保存結果が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
/// rootで選んだ全内部arrowの検査結果。ObjectAlgebraの成立型とは区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InternalArrows {
    construction: ConfigurationConstruction,
    arrows: Vec<InternalArrowResult>,
    selected: Option<Vec<FactPointer>>,
    complete: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InternalArrowsFailure {
    cause: ConstructionFailure,
    partial: Option<Box<InternalArrows>>,
}
impl InternalArrowsFailure {
    pub fn cause(&self) -> &ConstructionFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&InternalArrows> {
        self.partial.as_deref()
    }
    pub(crate) fn into_parts(self) -> (ConstructionFailure, Option<Box<InternalArrows>>) {
        (self.cause, self.partial)
    }
}
impl From<ConstructionFailure> for InternalArrowsFailure {
    fn from(cause: ConstructionFailure) -> Self {
        Self {
            cause,
            partial: None,
        }
    }
}
impl InternalArrows {
    pub fn construction(&self) -> &ConfigurationConstruction {
        &self.construction
    }
    pub fn arrows(&self) -> &[InternalArrowResult] {
        &self.arrows
    }
    /// 所属未決・保存未決・反証のarrowが一つでもあればfalse。
    pub fn all_preserved(&self) -> bool {
        self.complete && self.arrows.iter().all(|a| a.map.is_some())
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    /// Noneは候補の列挙自体が未完了。Someは未処理のcanonicalな候補列。
    pub fn pending(&self) -> Option<&[FactPointer]> {
        self.selected
            .as_deref()
            .map(|rows| &rows[self.arrows.len()..])
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        let expected = internal_arrows(
            inputs,
            self.construction.reading(),
            &self.construction.root().snapshot,
            &self.construction.root().subject,
            control,
        )
        .map_err(|failure| failure.cause)?;
        if self != &expected {
            return Err(ConstructionFailure::Inconsistent(
                "内部arrow全件の構成が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::InternalArrow)
        .map_err(Into::into)
}
fn component(
    inputs: &CheckedInputs,
    key: &SubjectKey,
    index: &BTreeMap<(&str, &str), &Subject>,
    root: &FactPointer,
    confirmed_owner: bool,
    missing: &mut BTreeSet<FactPointer>,
    control: &mut Control,
) -> Result<Option<ObjectComponent>, ConstructionFailure> {
    tick(control)?;
    let selected = subject(inputs, &key.0, &key.1, control)?;
    let owner = endpoint(selected, "owner", missing, control)?;
    if owner
        .as_ref()
        .is_some_and(|(s, id)| s != &root.snapshot || id != &root.subject)
    {
        if confirmed_owner {
            return Err(ConstructionFailure::Inconsistent(
                "内部arrowの端点が別rootに属する".into(),
            ));
        }
        // arrowのowner未観測時には、このrootの対象だと仮定しない。
        return Ok(None);
    }
    let candidate = configuration(inputs, &[selected], index, BTreeSet::new(), control)?;
    for slot in candidate.blocking_slots() {
        tick(control)?;
        missing.insert(slot.clone());
    }
    Ok(Some(ObjectComponent {
        subject: exists(selected),
        candidate,
    }))
}
/// 選択rootの内部arrowを、原始from/toと同名field規則から検査する。
/// owner未観測の候補も未決として返し、完成した作用へ昇格させない。
pub fn internal_arrow(
    inputs: &CheckedInputs,
    reading: &str,
    root_snapshot: &str,
    root_id: &str,
    arrow_snapshot: &str,
    arrow_id: &str,
    control: &mut Control,
) -> Result<InternalArrowResult, ConstructionFailure> {
    tick(control)?;
    let construction = construct(inputs, reading, root_snapshot, root_id, control)?;
    let result = internal_arrow_checked(inputs, &construction, arrow_snapshot, arrow_id, control)?;
    tick(control)?;
    Ok(result)
}
fn internal_arrow_checked(
    inputs: &CheckedInputs,
    construction: &ConfigurationConstruction,
    arrow_snapshot: &str,
    arrow_id: &str,
    control: &mut Control,
) -> Result<InternalArrowResult, ConstructionFailure> {
    tick(control)?;
    let holder = subject(inputs, arrow_snapshot, arrow_id, control)?;
    let root = subject(
        inputs,
        &construction.root().snapshot,
        &construction.root().subject,
        control,
    )?;
    let signature = inputs
        .definitions()
        .declarations
        .get(&holder.ty)
        .ok_or_else(|| ConstructionFailure::Inconsistent("arrowの元定義がない".into()))?;
    let PrimitiveSignature::Arrow { owner, .. } = &signature.signature else {
        return Err(ConstructionFailure::InvalidSelection(
            "内部生成元は原始arrowを要求する".into(),
        ));
    };
    if owner != &root.ty
        || !visible(
            inputs,
            &holder.ty,
            &namespaces(inputs, construction.reading(), control)?,
        )
    {
        return Err(ConstructionFailure::InvalidSelection(
            "arrowの型・readingが選択rootに適合しない".into(),
        ));
    }
    let mut missing = BTreeSet::new();
    let owner = endpoint(holder, "owner", &mut missing, control)?;
    if owner
        .as_ref()
        .is_some_and(|(s, id)| s != &root.snapshot || id != &root.id)
    {
        return Err(ConstructionFailure::InvalidSelection(
            "arrowが選択rootに属さない".into(),
        ));
    }
    let from = endpoint(holder, "from", &mut missing, control)?;
    let to = endpoint(holder, "to", &mut missing, control)?;
    let mut index = BTreeMap::new();
    for snapshot in &inputs.archmap().snapshots {
        tick(control)?;
        for subject in &snapshot.subjects {
            tick(control)?;
            index.insert((subject.snapshot.as_str(), subject.id.as_str()), subject);
        }
    }
    let mut result = InternalArrowResult {
        root: construction.root().clone(),
        arrow: exists(holder),
        reading: construction.reading().into(),
        source: None,
        target: None,
        candidate: None,
        map: None,
        missing: vec![],
        counterexamples: vec![],
    };
    if let Some(from) = &from {
        result.source = component(
            inputs,
            from,
            &index,
            construction.root(),
            owner.is_some(),
            &mut missing,
            control,
        )?;
    }
    if let Some(to) = &to {
        result.target = component(
            inputs,
            to,
            &index,
            construction.root(),
            owner.is_some(),
            &mut missing,
            control,
        )?;
    }
    let (Some(from), Some(to), Some(source), Some(target)) =
        (&from, &to, &result.source, &result.target)
    else {
        result.missing = canonical_facts(missing, control)?;
        return Ok(result);
    };
    let moved = BTreeMap::from([(from.clone(), to.clone())]);
    let source_config = source.candidate().known();
    let target_config = target.candidate().known();
    let family: BTreeSet<_> = source_config.family().iter().collect();
    let mut images = Vec::new();
    let mut action = BTreeMap::new();
    let mut absent = false;
    for fact in construction.universe() {
        tick(control)?;
        if !family.contains(fact) {
            images.push(fact.clone());
            action.insert(fact.clone(), fact.clone());
            continue;
        }
        let key = (fact.snapshot.clone(), fact.subject.clone());
        let target_key = moved.get(&key).unwrap_or(&key);
        let target_subject = subject(inputs, &target_key.0, &target_key.1, control)?;
        let Some(source_field) = &fact.field else {
            let image = exists(target_subject);
            action.insert(fact.clone(), image.clone());
            images.push(image);
            continue;
        };
        let source_subject = subject(inputs, &fact.snapshot, &fact.subject, control)?;
        let name = source_field.rsplit('.').next().unwrap_or(source_field);
        let target_field = format!("{}.{}", target_subject.ty, name);
        let Some(tf) = field(target_subject, &target_field, control)? else {
            result.counterexamples.push(Counterexample::Field {
                source: fact.clone(),
                target_subject: exists(target_subject),
                target_field,
            });
            absent = true;
            continue;
        };
        let Slot::Known {
            atom,
            value: target_value,
            ..
        } = &tf.slot
        else {
            missing.insert(slot(target_subject, &tf.name));
            absent = true;
            continue;
        };
        let image = FactPointer {
            atom: Some(atom.clone()),
            ..slot(target_subject, &tf.name)
        };
        let sf = field(source_subject, source_field, control)?
            .ok_or_else(|| ConstructionFailure::Inconsistent("内部作用の始域fieldがない".into()))?;
        let Slot::Known {
            value: source_value,
            ..
        } = &sf.slot
        else {
            return Err(ConstructionFailure::Inconsistent(
                "内部作用の始域Atom値がない".into(),
            ));
        };
        if reference_violation(
            source_value,
            target_value,
            &moved,
            &BTreeSet::new(),
            control,
        )? {
            result
                .counterexamples
                .push(Counterexample::ReferenceStructure {
                    source: fact.clone(),
                    target: image.clone(),
                });
        }
        images.push(image.clone());
        action.insert(fact.clone(), image);
    }
    result.counterexamples.extend(preservation_counterexamples(
        source_config,
        target_config,
        target.candidate().configuration().is_some(),
        &action,
        control,
    )?);
    result.missing = canonical_facts(missing, control)?;
    if !absent && result.missing.is_empty() {
        let candidate = MapCandidate {
            origin: MapOrigin::InternalArrow {
                root: construction.root().clone(),
                arrow: exists(holder),
            },
            source_root: source.subject().clone(),
            target_root: target.subject().clone(),
            reading: construction.reading().into(),
            to_reading: construction.reading().into(),
            source_configuration: source_config.clone(),
            target_configuration: target_config.clone(),
            universe: construction.universe().to_vec(),
            images,
        };
        if result.counterexamples.is_empty() {
            result.map = Some(ConfigurationMap {
                candidate: candidate.clone(),
            });
        }
        result.candidate = Some(candidate);
    }
    Ok(result)
}
/// rootの全owned arrowをcanonical順で検査する。owner欠測の候補も結果表に残す。
pub fn internal_arrows(
    inputs: &CheckedInputs,
    reading: &str,
    root_snapshot: &str,
    root_id: &str,
    control: &mut Control,
) -> Result<InternalArrows, InternalArrowsFailure> {
    tick(control)?;
    let construction = construct(inputs, reading, root_snapshot, root_id, control)?;
    let mut result = InternalArrows {
        construction,
        arrows: vec![],
        selected: None,
        complete: false,
    };
    let computed = (|| -> Result<(), ConstructionFailure> {
        control.checkpoint(Checkpoint::InternalArrowRoster)?;
        let root = subject(inputs, root_snapshot, root_id, control)?;
        let namespaces = namespaces(inputs, reading, control)?;
        let mut arrows = Vec::new();
        for snapshot in &inputs.archmap().snapshots {
            tick(control)?;
            for holder in &snapshot.subjects {
                tick(control)?;
                if !visible(inputs, &holder.ty, &namespaces) {
                    continue;
                }
                let Some(PrimitiveSignature::Arrow { owner, .. }) = inputs
                    .definitions()
                    .declarations
                    .get(&holder.ty)
                    .map(|d| &d.signature)
                else {
                    continue;
                };
                if owner != &root.ty {
                    continue;
                }
                let f = field(holder, "owner", control)?.ok_or_else(|| {
                    ConstructionFailure::Inconsistent("内部arrowのowner slotがない".into())
                })?;
                let selected = match &f.slot {
                    Slot::Missing => true,
                    Slot::Known { value, .. } => {
                        key(value)? == (root_snapshot.into(), root_id.into())
                    }
                };
                if selected {
                    arrows.push(exists(holder));
                }
            }
        }
        result.selected = Some(canonical_facts(arrows.into_iter().collect(), control)?);
        while let Some(arrow) = result.pending().and_then(|rows| rows.first()).cloned() {
            tick(control)?;
            let row = internal_arrow_checked(
                inputs,
                &result.construction,
                &arrow.snapshot,
                &arrow.subject,
                control,
            )?;
            result.arrows.push(row);
            control.checkpoint(Checkpoint::InternalArrowRow)?;
        }
        result.complete = true;
        tick(control)?;
        Ok(())
    })();
    match computed {
        Ok(()) => Ok(result),
        Err(cause) => Err(InternalArrowsFailure {
            cause,
            partial: Some(Box::new(result)),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::input::{InputSources, check_inputs};
    fn inputs() -> CheckedInputs {
        let d = include_bytes!("../../../tests/fixtures/internal-arrow.atoms.json");
        let checked = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &checked.vocabularies["Flow"].digest;
        check_inputs(
            InputSources::from_bytes(
                vec![d.to_vec()],
                include_str!("../../../tests/fixtures/internal-arrow.law")
                    .replace("@FLOW_DIGEST@", digest)
                    .into_bytes(),
                include_str!("../../../tests/fixtures/internal-arrow.archmap.json")
                    .replace("@FLOW_DIGEST@", digest)
                    .into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn recheck_rejects_forged_internal_origin_objects_actions_and_dropped_arrows() {
        let inputs = inputs();
        let original =
            internal_arrows(&inputs, "FlowRead", "v", "A", &mut Control::unlimited()).unwrap();
        for kind in [
            "drop",
            "selected",
            "complete",
            "arrow",
            "root",
            "reading",
            "source",
            "action",
            "map",
            "missing",
            "counterexample",
        ] {
            let mut forged = original.clone();
            match kind {
                "drop" => {
                    forged.arrows.pop();
                }
                "selected" => forged.selected = None,
                "complete" => forged.complete = false,
                "arrow" => forged.arrows[0].arrow.subject = "f".into(),
                "root" => forged.arrows[0].root.subject = "B".into(),
                "reading" => forged.arrows[0].reading = "OtherRead".into(),
                "source" => forged.arrows[0].source.as_mut().unwrap().subject.subject = "q".into(),
                "action" => forged.arrows[0]
                    .candidate
                    .as_mut()
                    .unwrap()
                    .images
                    .swap(0, 1),
                "map" => forged.arrows[0].map = None,
                "missing" => forged.arrows[0]
                    .missing
                    .push(original.construction.root().clone()),
                "counterexample" => forged.arrows[0]
                    .counterexamples
                    .push(Counterexample::Family {
                        source: original.construction.root().clone(),
                        image: original.construction.root().clone(),
                    }),
                _ => unreachable!(),
            }
            assert!(
                matches!(
                    forged.recheck(&inputs, &mut Control::unlimited()),
                    Err(ConstructionFailure::Inconsistent(_))
                ),
                "{kind}"
            );
        }
        let candidate = original.arrows[0].candidate.as_ref().unwrap();
        for kind in ["action", "origin", "target", "reading"] {
            let mut forged = candidate.clone();
            match kind {
                "action" => forged.images.swap(0, 1),
                "origin" => {
                    if let MapOrigin::InternalArrow { arrow, .. } = &mut forged.origin {
                        arrow.subject = "f".into();
                    }
                }
                "target" => forged.target_root.subject = "p".into(),
                "reading" => forged.to_reading = "OtherRead".into(),
                _ => unreachable!(),
            }
            assert!(
                forged.recheck(&inputs, &mut Control::unlimited()).is_err(),
                "{kind}"
            );
            assert!(
                ConfigurationMap { candidate: forged }
                    .recheck(&inputs, &mut Control::unlimited())
                    .is_err(),
                "{kind}"
            );
        }
    }
}
