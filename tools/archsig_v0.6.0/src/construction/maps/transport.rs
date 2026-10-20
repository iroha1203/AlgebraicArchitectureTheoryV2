//! 同じ対応総写像による対象族の保存と、内部生成操作の全U自然性。
use super::*;

/// 全行で同じbase対応作用を使い、対象identityと各部分Configurationを保持する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectTransport {
    source: ObjectIdentity,
    target: ObjectIdentity,
    source_configuration: Configuration,
    target_configuration: Configuration,
    counterexamples: Vec<Counterexample>,
}
impl ObjectTransport {
    pub fn source(&self) -> &ObjectIdentity {
        &self.source
    }
    pub fn target(&self) -> &ObjectIdentity {
        &self.target
    }
    pub fn source_configuration(&self) -> &Configuration {
        &self.source_configuration
    }
    pub fn target_configuration(&self) -> &Configuration {
        &self.target_configuration
    }
    pub fn counterexamples(&self) -> &[Counterexample] {
        &self.counterexamples
    }
    pub fn is_preserved(&self) -> bool {
        self.counterexamples.is_empty()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Naturality {
    Preserved,
    /// left=μ∘e、right=μ(e)∘μ の最初の不一致。
    Refuted {
        fact: FactPointer,
        left: FactPointer,
        right: FactPointer,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorTransport {
    source: FactPointer,
    target: FactPointer,
    endpoints_preserved: Option<bool>,
    naturality: Option<Naturality>,
}
impl GeneratorTransport {
    pub fn source(&self) -> &FactPointer {
        &self.source
    }
    pub fn target(&self) -> &FactPointer {
        &self.target
    }
    pub fn endpoints_preserved(&self) -> Option<bool> {
        self.endpoints_preserved
    }
    pub fn naturality(&self) -> Option<&Naturality> {
        self.naturality.as_ref()
    }
}
/// Configurationの対象・内部生成操作に関する保存。Law等の追加読取りは別途検査する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationTransport {
    operation: ConfigurationOperation,
    source: InternalArrows,
    target: InternalArrows,
    objects: Vec<ObjectTransport>,
    generators: Vec<GeneratorTransport>,
}
impl ConfigurationTransport {
    /// 追加構造が反証・未決でも、確認済みconfiguration操作を保持する。
    pub fn operation(&self) -> &ConfigurationOperation {
        &self.operation
    }
    pub fn source(&self) -> &InternalArrows {
        &self.source
    }
    pub fn target(&self) -> &InternalArrows {
        &self.target
    }
    pub fn objects(&self) -> &[ObjectTransport] {
        &self.objects
    }
    pub fn generators(&self) -> &[GeneratorTransport] {
        &self.generators
    }
    /// 全対象成分が共有する原始correspondenceの総作用。
    pub fn action(&self) -> &MapCandidate {
        self.operation.map().candidate()
    }
    pub fn all_preserved(&self) -> bool {
        self.source.all_preserved()
            && self.target.all_preserved()
            && self.objects.iter().all(ObjectTransport::is_preserved)
            && self.generators.iter().all(|g| {
                g.endpoints_preserved == Some(true) && g.naturality == Some(Naturality::Preserved)
            })
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self != &configuration_transport(inputs, self.operation.map(), control)? {
            return Err(ConstructionFailure::Inconsistent(
                "対象対応・内部操作の自然性が現在入力と違う".into(),
            ));
        }
        tick(control)
    }
}
fn tick(control: &mut Control) -> Result<(), ConstructionFailure> {
    control
        .checkpoint(Checkpoint::ConfigurationTransport)
        .map_err(Into::into)
}
fn image<'a>(
    action: &'a BTreeMap<FactPointer, FactPointer>,
    fact: &FactPointer,
) -> Result<&'a FactPointer, ConstructionFailure> {
    action
        .get(fact)
        .ok_or_else(|| ConstructionFailure::Inconsistent("対応総写像に元位置がない".into()))
}
fn objects<'a>(
    construction: &'a ConfigurationConstruction,
    control: &mut Control,
) -> Result<Vec<(&'a FactPointer, &'a Configuration)>, ConstructionFailure> {
    tick(control)?;
    let base = construction
        .base()
        .configuration()
        .ok_or_else(|| ConstructionFailure::Inconsistent("保存済み対応のbaseが未確定".into()))?;
    let mut objects = vec![(construction.root(), base)];
    for c in construction.components() {
        tick(control)?;
        objects.push((
            c.subject(),
            c.candidate().configuration().ok_or_else(|| {
                ConstructionFailure::Inconsistent("保存済み対応の部分対象が未確定".into())
            })?,
        ));
    }
    Ok(objects)
}
fn naturality(
    map: &MapCandidate,
    source: &MapCandidate,
    target: &MapCandidate,
    control: &mut Control,
) -> Result<Naturality, ConstructionFailure> {
    if map.universe() != source.universe() || map.universe() != target.universe() {
        return Err(ConstructionFailure::Inconsistent(
            "自然性を比較する共通Uが違う".into(),
        ));
    }
    let mut mu = BTreeMap::new();
    let mut e = BTreeMap::new();
    let mut mapped = BTreeMap::new();
    for ((fact, image), (a, b)) in map
        .universe()
        .iter()
        .zip(map.images())
        .zip(source.images().iter().zip(target.images()))
    {
        tick(control)?;
        mu.insert(fact, image);
        e.insert(fact, a);
        mapped.insert(fact, b);
    }
    for fact in map.universe() {
        tick(control)?;
        let source_image = e
            .get(fact)
            .ok_or_else(|| ConstructionFailure::Inconsistent("内部操作の元像がない".into()))?;
        let map_image = mu
            .get(fact)
            .ok_or_else(|| ConstructionFailure::Inconsistent("対応の元像がない".into()))?;
        let left = mu
            .get(source_image)
            .ok_or_else(|| ConstructionFailure::Inconsistent("対応の合成像がない".into()))?;
        let right = mapped
            .get(map_image)
            .ok_or_else(|| ConstructionFailure::Inconsistent("内部操作の合成像がない".into()))?;
        if left != right {
            return Ok(Naturality::Refuted {
                fact: fact.clone(),
                left: (**left).clone(),
                right: (**right).clone(),
            });
        }
    }
    tick(control)?;
    Ok(Naturality::Preserved)
}
/// 保存済み原始correspondenceから対象写像と全生成操作の自然性を構成する。
pub fn configuration_transport(
    inputs: &CheckedInputs,
    map: &ConfigurationMap,
    control: &mut Control,
) -> Result<ConfigurationTransport, ConstructionFailure> {
    tick(control)?;
    if !matches!(map.candidate.origin, MapOrigin::Correspondence(_)) {
        return Err(ConstructionFailure::InvalidSelection(
            "対象族の対応は原始correspondenceの保存済みmapを要求する".into(),
        ));
    }
    let operation = ConfigurationOperation::from_map(inputs, map, control)?;
    let c = map.candidate();
    let source = internal_arrows(
        inputs,
        c.reading(),
        &c.source_root().snapshot,
        &c.source_root().subject,
        control,
    )?;
    let target = internal_arrows(
        inputs,
        c.to_reading(),
        &c.target_root().snapshot,
        &c.target_root().subject,
        control,
    )?;
    let source_objects = objects(source.construction(), control)?;
    let target_objects = objects(target.construction(), control)?;
    let mut action = BTreeMap::new();
    for (a, b) in c.universe().iter().zip(c.images()) {
        tick(control)?;
        action.insert(a.clone(), b.clone());
    }
    let mut object_rows = Vec::new();
    for (source_subject, source_config) in source_objects {
        tick(control)?;
        let target_subject = image(&action, source_subject)?;
        let mut selected = None;
        for (subject, config) in &target_objects {
            tick(control)?;
            if *subject == target_subject {
                selected = Some(*config);
                break;
            }
        }
        let target_config = selected.ok_or_else(|| {
            ConstructionFailure::Inconsistent("保存済み対応の像が終域対象族にない".into())
        })?;
        object_rows.push(ObjectTransport {
            source: ObjectIdentity::selected(c.reading(), c.source_root(), source_subject),
            target: ObjectIdentity::selected(c.to_reading(), c.target_root(), target_subject),
            source_configuration: source_config.clone(),
            target_configuration: target_config.clone(),
            counterexamples: preservation_counterexamples(
                source_config,
                target_config,
                true,
                &action,
                control,
            )?,
        });
    }
    let mut generators = Vec::new();
    for e in source.arrows() {
        tick(control)?;
        let target_arrow = image(&action, e.arrow())?.clone();
        let mut selected = None;
        for f in target.arrows() {
            tick(control)?;
            if f.arrow() == &target_arrow {
                selected = Some(f);
                break;
            }
        }
        let f = selected.ok_or_else(|| {
            ConstructionFailure::Inconsistent("保存済み対応の像が終域内部arrowにない".into())
        })?;
        let (endpoints_preserved, naturality) = if let (Some(e), Some(f)) = (e.map(), f.map()) {
            let e = e.candidate();
            let f = f.candidate();
            let endpoints = image(&action, e.source_root())? == f.source_root()
                && image(&action, e.target_root())? == f.target_root();
            (Some(endpoints), Some(naturality(c, e, f, control)?))
        } else {
            (None, None)
        };
        generators.push(GeneratorTransport {
            source: e.arrow().clone(),
            target: target_arrow,
            endpoints_preserved,
            naturality,
        });
    }
    tick(control)?;
    Ok(ConfigurationTransport {
        operation,
        source,
        target,
        objects: object_rows,
        generators,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn inputs(map: &str) -> CheckedInputs {
        crate::observed::input::check_inputs(
            crate::observed::input::InputSources::from_bytes(
                vec![include_bytes!("../../../tests/fixtures/reservations.atoms.json").to_vec()],
                include_bytes!("../../../tests/fixtures/configuration-operation.law").to_vec(),
                map.as_bytes().to_vec(),
            ),
            &mut Control::unlimited(),
        )
        .unwrap()
    }
    #[test]
    fn current_input_rejects_forged_object_generator_and_naturality_rows() {
        let a = include_str!("../../../tests/fixtures/object-configuration-map.archmap.json");
        let i = inputs(a);
        let m = correspondence(
            &i,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        let original =
            configuration_transport(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
        for kind in 0..11 {
            let mut forged = original.clone();
            match kind {
                0 => {
                    forged.objects.pop();
                }
                1 => {
                    forged.objects[1].source = forged.objects[2].source.clone();
                }
                2 => {
                    forged.objects[1].target = forged.objects[2].target.clone();
                }
                3 => {
                    forged.objects[1].source_configuration.family.pop();
                }
                4 => {
                    let source = forged.objects[1].source.subject().clone();
                    let image = forged.objects[1].target.subject().clone();
                    forged.objects[1]
                        .counterexamples
                        .push(Counterexample::Family { source, image });
                }
                5 => {
                    forged.generators.pop();
                }
                6 => {
                    forged.generators[0].target = forged.generators[0].source.clone();
                }
                7 => {
                    forged.generators[0].endpoints_preserved = Some(false);
                }
                8 => {
                    forged.generators[0].naturality = None;
                }
                9 => {
                    forged.generators[0].naturality = Some(Naturality::Refuted {
                        fact: forged.action().universe()[0].clone(),
                        left: forged.action().universe()[0].clone(),
                        right: forged.action().universe()[1].clone(),
                    });
                }
                _ => {
                    forged.target = forged.source.clone();
                }
            }
            assert!(
                forged.recheck(&i, &mut Control::unlimited()).is_err(),
                "{kind}"
            );
        }
        let bad = inputs(&a.replace(r#"[["v","u"],["v","w"]]"#, r#"[["v","u"],["v","r"]]"#));
        let m = correspondence(
            &bad,
            "v",
            "m",
            "Reservations",
            None,
            &mut Control::unlimited(),
        )
        .unwrap();
        let mut forged =
            configuration_transport(&bad, m.map().unwrap(), &mut Control::unlimited()).unwrap();
        assert!(matches!(
            forged.generators[0].naturality,
            Some(Naturality::Refuted { .. })
        ));
        forged.generators[0].naturality = Some(Naturality::Preserved);
        assert!(forged.recheck(&bad, &mut Control::unlimited()).is_err());
    }
}
