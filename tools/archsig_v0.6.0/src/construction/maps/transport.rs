//! 同じ対応総写像による対象族の保存と、内部生成操作の全U自然性。
use super::*;

/// Configuration保存後に、実像がObjectAlgebraの該当する族へ属さない構成条件の不成立。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransportConditionFailure {
    TargetObject {
        source: FactPointer,
        image: FactPointer,
    },
    TargetGenerator {
        source: FactPointer,
        image: FactPointer,
    },
}
/// 全行で同じbase対応作用を使い、対象identityと各部分Configurationを保持する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectTransport {
    source: ObjectIdentity,
    target: Option<ObjectIdentity>,
    source_configuration: Configuration,
    target_configuration: Option<Configuration>,
    counterexamples: Vec<Counterexample>,
    condition_failure: Option<TransportConditionFailure>,
}
impl ObjectTransport {
    pub fn source(&self) -> &ObjectIdentity {
        &self.source
    }
    pub fn target(&self) -> Option<&ObjectIdentity> {
        self.target.as_ref()
    }
    pub fn source_configuration(&self) -> &Configuration {
        &self.source_configuration
    }
    pub fn target_configuration(&self) -> Option<&Configuration> {
        self.target_configuration.as_ref()
    }
    pub fn counterexamples(&self) -> &[Counterexample] {
        &self.counterexamples
    }
    pub fn is_preserved(&self) -> bool {
        self.target.is_some()
            && self.target_configuration.is_some()
            && self.condition_failure.is_none()
            && self.counterexamples.is_empty()
    }
    pub fn condition_failure(&self) -> Option<&TransportConditionFailure> {
        self.condition_failure.as_ref()
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
    condition_failure: Option<TransportConditionFailure>,
}
impl GeneratorTransport {
    pub fn source(&self) -> &FactPointer {
        &self.source
    }
    /// 原始対応の像。生成元の族への所属はcondition_failure()で確認する。
    pub fn target(&self) -> &FactPointer {
        &self.target
    }
    pub fn endpoints_preserved(&self) -> Option<bool> {
        self.endpoints_preserved
    }
    pub fn naturality(&self) -> Option<&Naturality> {
        self.naturality.as_ref()
    }
    pub fn condition_failure(&self) -> Option<&TransportConditionFailure> {
        self.condition_failure.as_ref()
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
/// 完成済みの行と元Operation。全体の成立はoutcome()がSomeのときだけ読める。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationTransportPartial {
    operation: ConfigurationOperation,
    source: Option<InternalArrows>,
    target: Option<InternalArrows>,
    objects: Vec<ObjectTransport>,
    generators: Vec<GeneratorTransport>,
    outcome: Option<bool>,
}
impl ConfigurationTransportPartial {
    pub fn operation(&self) -> &ConfigurationOperation {
        &self.operation
    }
    pub fn source(&self) -> Option<&InternalArrows> {
        self.source.as_ref()
    }
    pub fn target(&self) -> Option<&InternalArrows> {
        self.target.as_ref()
    }
    pub fn objects(&self) -> &[ObjectTransport] {
        &self.objects
    }
    pub fn generators(&self) -> &[GeneratorTransport] {
        &self.generators
    }
    pub fn outcome(&self) -> Option<bool> {
        self.outcome
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationTransportFailure {
    cause: ConstructionFailure,
    partial: Option<Box<ConfigurationTransportPartial>>,
}
impl ConfigurationTransportFailure {
    pub fn cause(&self) -> &ConstructionFailure {
        &self.cause
    }
    pub fn partial(&self) -> Option<&ConfigurationTransportPartial> {
        self.partial.as_deref()
    }
    pub(crate) fn into_parts(
        self,
    ) -> (
        ConstructionFailure,
        Option<Box<ConfigurationTransportPartial>>,
    ) {
        (self.cause, self.partial)
    }
}
impl From<ConstructionFailure> for ConfigurationTransportFailure {
    fn from(cause: ConstructionFailure) -> Self {
        Self {
            cause,
            partial: None,
        }
    }
}
impl ConfigurationTransport {
    pub(crate) fn into_partial(self) -> ConfigurationTransportPartial {
        let outcome = Some(self.all_preserved());
        ConfigurationTransportPartial {
            operation: self.operation,
            source: Some(self.source),
            target: Some(self.target),
            objects: self.objects,
            generators: self.generators,
            outcome,
        }
    }
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
                g.condition_failure.is_none()
                    && g.endpoints_preserved == Some(true)
                    && g.naturality == Some(Naturality::Preserved)
            })
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        control: &mut Control,
    ) -> Result<(), ConstructionFailure> {
        if self
            != &configuration_transport(inputs, self.operation.map(), control)
                .map_err(|failure| failure.cause)?
        {
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
) -> Result<ConfigurationTransport, ConfigurationTransportFailure> {
    tick(control)?;
    if !matches!(map.candidate.origin, MapOrigin::Correspondence(_)) {
        return Err(ConstructionFailure::InvalidSelection(
            "対象族の対応は原始correspondenceの保存済みmapを要求する".into(),
        )
        .into());
    }
    let operation = ConfigurationOperation::from_map(inputs, map, control)?;
    let mut result = ConfigurationTransportPartial {
        operation,
        source: None,
        target: None,
        objects: vec![],
        generators: vec![],
        outcome: None,
    };
    let computed =
        (|| -> Result<(), ConstructionFailure> {
            let c = map.candidate();
            result.source = Some(
                match internal_arrows(
                    inputs,
                    c.reading(),
                    &c.source_root().snapshot,
                    &c.source_root().subject,
                    control,
                ) {
                    Ok(source) => source,
                    Err(failure) => {
                        let (cause, partial) = failure.into_parts();
                        result.source = partial.map(|r| *r);
                        return Err(cause);
                    }
                },
            );
            result.target = Some(
                match internal_arrows(
                    inputs,
                    c.to_reading(),
                    &c.target_root().snapshot,
                    &c.target_root().subject,
                    control,
                ) {
                    Ok(target) => target,
                    Err(failure) => {
                        let (cause, partial) = failure.into_parts();
                        result.target = partial.map(|r| *r);
                        return Err(cause);
                    }
                },
            );
            let source = result.source.as_ref().ok_or_else(|| {
                ConstructionFailure::Inconsistent("対象写像のsource表がない".into())
            })?;
            let target = result.target.as_ref().ok_or_else(|| {
                ConstructionFailure::Inconsistent("対象写像のtarget表がない".into())
            })?;
            let source_objects = objects(source.construction(), control)?;
            let target_objects = objects(target.construction(), control)?;
            let mut action = BTreeMap::new();
            for (a, b) in c.universe().iter().zip(c.images()) {
                tick(control)?;
                action.insert(a.clone(), b.clone());
            }
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
                let (target_object, target_configuration, counterexamples, condition_failure) =
                    if let Some(target_config) = selected {
                        (
                            Some(ObjectIdentity::selected(
                                c.to_reading(),
                                c.target_root(),
                                target_subject,
                            )),
                            Some(target_config.clone()),
                            preservation_counterexamples(
                                source_config,
                                target_config,
                                true,
                                &action,
                                control,
                            )?,
                            None,
                        )
                    } else {
                        (
                            None,
                            None,
                            vec![],
                            Some(TransportConditionFailure::TargetObject {
                                source: source_subject.clone(),
                                image: target_subject.clone(),
                            }),
                        )
                    };
                result.objects.push(ObjectTransport {
                    source: ObjectIdentity::selected(c.reading(), c.source_root(), source_subject),
                    target: target_object,
                    source_configuration: source_config.clone(),
                    target_configuration,
                    counterexamples,
                    condition_failure,
                });
                control.checkpoint(Checkpoint::ConfigurationTransportObject)?;
            }
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
                let condition_failure = if selected.is_none() {
                    Some(TransportConditionFailure::TargetGenerator {
                        source: e.arrow().clone(),
                        image: target_arrow.clone(),
                    })
                } else {
                    None
                };
                let (endpoints_preserved, naturality) = if let (Some(e), Some(f)) =
                    (e.map(), selected.and_then(InternalArrowResult::map))
                {
                    let e = e.candidate();
                    let f = f.candidate();
                    let endpoints = image(&action, e.source_root())? == f.source_root()
                        && image(&action, e.target_root())? == f.target_root();
                    (Some(endpoints), Some(naturality(c, e, f, control)?))
                } else {
                    (None, None)
                };
                result.generators.push(GeneratorTransport {
                    source: e.arrow().clone(),
                    target: target_arrow,
                    endpoints_preserved,
                    naturality,
                    condition_failure,
                });
                control.checkpoint(Checkpoint::ConfigurationTransportGenerator)?;
            }
            result.outcome = Some(
                source.all_preserved()
                    && target.all_preserved()
                    && result.objects.iter().all(ObjectTransport::is_preserved)
                    && result.generators.iter().all(|g| {
                        g.condition_failure.is_none()
                            && g.endpoints_preserved == Some(true)
                            && g.naturality == Some(Naturality::Preserved)
                    }),
            );
            tick(control)?;
            Ok(())
        })();
    match computed {
        Ok(()) => match result {
            ConfigurationTransportPartial {
                operation,
                source: Some(source),
                target: Some(target),
                objects,
                generators,
                outcome: Some(_),
            } => Ok(ConfigurationTransport {
                operation,
                source,
                target,
                objects,
                generators,
            }),
            partial => Err(ConfigurationTransportFailure {
                cause: ConstructionFailure::Inconsistent("対象写像の完成結果が揃っていない".into()),
                partial: Some(Box::new(partial)),
            }),
        },
        Err(cause) => Err(ConfigurationTransportFailure {
            cause,
            partial: Some(Box::new(result)),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn cross_kind_inputs() -> CheckedInputs {
        let d = include_bytes!("../../../tests/fixtures/cross-kind-transport.atoms.json");
        let definitions = crate::definition::check_definitions(&[("definition0", d)]).unwrap();
        let digest = &definitions.vocabularies["V"].digest;
        crate::observed::input::check_inputs(
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
        .unwrap()
    }
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
                    let image = forged.objects[1].target.as_ref().unwrap().subject().clone();
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
    #[test]
    fn recheck_rejects_erased_condition_failures_and_fabricated_targets() {
        let i = cross_kind_inputs();
        let m = correspondence(&i, "v", "m", "Read", None, &mut Control::unlimited()).unwrap();
        let original =
            configuration_transport(&i, m.map().unwrap(), &mut Control::unlimited()).unwrap();
        assert!(original.objects[2].condition_failure.is_some());
        assert!(original.generators[0].condition_failure.is_some());
        for kind in 0..5 {
            let mut forged = original.clone();
            match kind {
                0 => {
                    forged.objects[2].condition_failure = None;
                }
                1 => {
                    forged.objects[2].target = forged.objects[1].target.clone();
                    forged.objects[2].target_configuration =
                        forged.objects[1].target_configuration.clone();
                    forged.objects[2].condition_failure = None;
                }
                2 => {
                    forged.generators[0].condition_failure = None;
                    forged.generators[0].naturality = Some(Naturality::Preserved);
                    forged.generators[0].endpoints_preserved = Some(true);
                }
                3 => {
                    forged.generators.clear();
                }
                _ => {
                    forged.objects[2].condition_failure =
                        Some(TransportConditionFailure::TargetObject {
                            source: forged.objects[1].source.subject().clone(),
                            image: forged.objects[1].source.subject().clone(),
                        });
                }
            }
            assert!(
                forged.recheck(&i, &mut Control::unlimited()).is_err(),
                "{kind}"
            );
        }
    }
}
