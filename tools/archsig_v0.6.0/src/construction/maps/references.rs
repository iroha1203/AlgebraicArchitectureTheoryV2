//! plain Ref の全有限域で、原始対応と固定外部参照から順逆写像を検査する。
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceConditionFailure {
    ImageType {
        source: FactPointer,
        image: FactPointer,
        expected: String,
        actual: String,
    },
    Collision {
        image: FactPointer,
        sources: Vec<FactPointer>,
    },
    Unreached {
        target: FactPointer,
    },
}
/// 全 source/target 域で両合成を検査した plain Ref の順逆写像。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceBijection {
    forward: BTreeMap<FactPointer, FactPointer>,
    inverse: BTreeMap<FactPointer, FactPointer>,
}
impl ReferenceBijection {
    pub fn forward(&self) -> &BTreeMap<FactPointer, FactPointer> {
        &self.forward
    }
    pub fn inverse(&self) -> &BTreeMap<FactPointer, FactPointer> {
        &self.inverse
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceTypeTransport {
    declarations: DeclarationCorrespondence,
    source_type: String,
    target_type: String,
    source: Vec<FactPointer>,
    target: Vec<FactPointer>,
    images: Vec<FactPointer>,
    failures: Vec<ReferenceConditionFailure>,
    bijection: Option<ReferenceBijection>,
}
impl ReferenceTypeTransport {
    pub fn operation(&self) -> &ConfigurationOperation {
        self.declarations.operation()
    }
    pub fn source_type(&self) -> &str {
        &self.source_type
    }
    pub fn target_type(&self) -> &str {
        &self.target_type
    }
    pub fn source(&self) -> &[FactPointer] {
        &self.source
    }
    pub fn target(&self) -> &[FactPointer] {
        &self.target
    }
    /// source() と同じ順の全候補像。失敗時も削除しない。
    pub fn images(&self) -> &[FactPointer] {
        &self.images
    }
    pub fn failures(&self) -> &[ReferenceConditionFailure] {
        &self.failures
    }
    pub fn bijection(&self) -> Option<&ReferenceBijection> {
        self.bijection.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self
            != &reference_type_transport(inputs, &self.declarations, &self.source_type, control)?
        {
            return Err(ConstructionFailure::Inconsistent(
                "参照値の全域・像・順逆検査が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ReferenceTypeTransport)
        .map_err(Into::into)
}
fn reference_type(inputs: &CheckedInputs, name: &str) -> Result<(), ConstructionFailure> {
    if matches!(
        inputs
            .definitions()
            .declarations
            .get(name)
            .map(|d| &d.signature),
        Some(
            PrimitiveSignature::Entity { .. }
                | PrimitiveSignature::Arrow { .. }
                | PrimitiveSignature::Correspondence { .. }
        )
    ) {
        Ok(())
    } else {
        Err(ConstructionFailure::InvalidSelection(format!(
            "plain Ref の原始参照型でない: {name}"
        )))
    }
}
/// Owned の所属添字・複合値や式の評価とは別に、plain Ref 型全域の同値を検査する。
pub fn reference_type_transport(
    inputs: &CheckedInputs,
    declarations: &DeclarationCorrespondence,
    source_type: &str,
    control: &mut Control,
) -> Result<ReferenceTypeTransport, ConstructionFailure> {
    tick(control)?;
    declarations.recheck(inputs, control)?;
    reference_type(inputs, source_type)?;
    let mut target_type = source_type.to_owned();
    for (source, target) in declarations.types() {
        tick(control)?;
        if source == source_type {
            target_type = target.clone();
        }
    }
    reference_type(inputs, &target_type)?;
    let mut types = BTreeMap::new();
    let mut source = Vec::new();
    let mut target = Vec::new();
    for snapshot in &inputs.archmap().snapshots {
        tick(control)?;
        for subject in &snapshot.subjects {
            tick(control)?;
            let fact = FactPointer {
                snapshot: snapshot.id.clone(),
                subject: subject.id.clone(),
                field: None,
                atom: None,
            };
            if subject.ty == source_type {
                source.push(fact.clone());
            }
            if subject.ty == target_type {
                target.push(fact.clone());
            }
            types.insert(fact, subject.ty.as_str());
        }
    }
    source.sort();
    target.sort();
    let map = declarations.operation().map().candidate();
    let mut action = BTreeMap::new();
    for (a, b) in map.universe().iter().zip(map.images()) {
        tick(control)?;
        action.insert(a, b);
    }
    let mut family = BTreeSet::new();
    for a in map.source_configuration().family() {
        tick(control)?;
        family.insert(a);
    }
    let mut images = Vec::new();
    let mut failures = Vec::new();
    let mut fibers: BTreeMap<FactPointer, Vec<FactPointer>> = BTreeMap::new();
    for a in &source {
        tick(control)?;
        // Atom の F 外を root に送る全域化を値の移送には使わない。
        let b = if family.contains(a) {
            action
                .get(a)
                .copied()
                .ok_or_else(|| ConstructionFailure::Inconsistent("参照の対応作用がない".into()))?
        } else {
            a
        };
        let actual = types.get(b).ok_or_else(|| {
            ConstructionFailure::Inconsistent("参照値の像が原始subjectでない".into())
        })?;
        if **actual != target_type {
            failures.push(ReferenceConditionFailure::ImageType {
                source: a.clone(),
                image: b.clone(),
                expected: target_type.clone(),
                actual: (*actual).into(),
            });
        }
        images.push(b.clone());
        fibers.entry(b.clone()).or_default().push(a.clone());
    }
    for (image, sources) in &fibers {
        tick(control)?;
        if sources.len() > 1 {
            failures.push(ReferenceConditionFailure::Collision {
                image: image.clone(),
                sources: sources.clone(),
            });
        }
    }
    for b in &target {
        tick(control)?;
        if !fibers.contains_key(b) {
            failures.push(ReferenceConditionFailure::Unreached { target: b.clone() });
        }
    }
    let bijection = if failures.is_empty() {
        let mut forward = BTreeMap::new();
        let mut inverse = BTreeMap::new();
        for (a, b) in source.iter().zip(&images) {
            tick(control)?;
            forward.insert(a.clone(), b.clone());
            inverse.insert(b.clone(), a.clone());
        }
        for a in &source {
            tick(control)?;
            if forward.get(a).and_then(|b| inverse.get(b)) != Some(a) {
                return Err(ConstructionFailure::Inconsistent(
                    "参照の逆順合成が恒等でない".into(),
                ));
            }
        }
        for b in &target {
            tick(control)?;
            if inverse.get(b).and_then(|a| forward.get(a)) != Some(b) {
                return Err(ConstructionFailure::Inconsistent(
                    "参照の順合成が恒等でない".into(),
                ));
            }
        }
        Some(ReferenceBijection { forward, inverse })
    } else {
        None
    };
    let result = ReferenceTypeTransport {
        declarations: declarations.clone(),
        source_type: source_type.into(),
        target_type,
        source,
        target,
        images,
        failures,
        bijection,
    };
    tick(control)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn forged_domains_images_failures_and_inverses_cannot_pass_current_input_recheck() {
        let d = include_bytes!("../../../tests/fixtures/cross-kind-transport.atoms.json");
        let defs = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &defs.vocabularies["V"].digest;
        let i = crate::observed::input::check_inputs(
            crate::observed::input::InputSources::from_bytes(
                vec![d.to_vec()],
                include_str!("../../../tests/fixtures/cross-kind-transport.law")
                    .replace("@DIGEST@", digest)
                    .into_bytes(),
                include_str!("../../../tests/fixtures/cross-kind-transport.archmap.json")
                    .replace("@DIGEST@", digest)
                    .into_bytes(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap();
        let map = correspondence(&i, "v", "m", "Read", None, &mut Control::unlimited()).unwrap();
        let declarations =
            declaration_correspondence(&i, map.map().unwrap(), &mut Control::unlimited()).unwrap();
        let external =
            reference_type_transport(&i, &declarations, "V.M", &mut Control::unlimited()).unwrap();
        let failed =
            reference_type_transport(&i, &declarations, "V.S", &mut Control::unlimited()).unwrap();
        let mut forgeries = Vec::new();
        let mut r = external.clone();
        r.source.clear();
        forgeries.push(r);
        let mut r = external.clone();
        r.target.clear();
        forgeries.push(r);
        let mut r = external.clone();
        r.target_type = "V.S".into();
        forgeries.push(r);
        let mut r = external.clone();
        r.images[0] = failed.source[0].clone();
        forgeries.push(r);
        let mut r = external.clone();
        r.bijection.as_mut().unwrap().forward.clear();
        forgeries.push(r);
        let mut r = external.clone();
        r.bijection.as_mut().unwrap().inverse.clear();
        forgeries.push(r);
        let mut r = external.clone();
        r.bijection = None;
        forgeries.push(r);
        let mut r = failed.clone();
        r.failures.clear();
        forgeries.push(r);
        let mut r = failed.clone();
        r.bijection = external.bijection.clone();
        forgeries.push(r);
        let mut r = failed.clone();
        r.source.pop();
        forgeries.push(r);
        for r in forgeries {
            assert!(matches!(
                r.recheck(&i, &mut Control::unlimited()),
                Err(ConstructionFailure::Inconsistent(_))
            ));
        }
        external.recheck(&i, &mut Control::unlimited()).unwrap();
        failed.recheck(&i, &mut Control::unlimited()).unwrap();
    }
}
