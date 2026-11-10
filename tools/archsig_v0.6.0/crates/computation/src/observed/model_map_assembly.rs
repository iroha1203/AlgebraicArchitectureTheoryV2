//! 同じ入力で検査した局所写像を共有類の上で貼り合わせる。
//! raw correspondenceの選択とLawの評価は呼出し側が担い、この層は写像の四角形を検査する。
use super::model_assembly::Model;
use crate::construction::{
    ConstructionFailure,
    maps::{self, ActionDifference, ConfigurationMap, ConfigurationOperation},
};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::{archmap::Fact, input::CheckedInputs};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Debug)]
pub(super) struct Local {
    pub correspondence: Fact,
    pub source: usize,
    pub target: usize,
    pub map: ConfigurationMap,
}
#[derive(Debug)]
pub(super) struct Glued {
    pub map: ConfigurationMap,
    pub locals: Vec<Local>,
    pub restrictions: Vec<ConfigurationMap>,
}
#[derive(Clone, Copy, Debug)]
pub(super) enum SquareKind {
    Inclusion,
    Restriction,
}
impl SquareKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::Inclusion => "inclusion",
            Self::Restriction => "restriction",
        }
    }
}
#[derive(Debug)]
pub(super) struct FailedEndpoint {
    pub from: bool,
    pub subject: Fact,
}

#[derive(Debug)]
pub(super) enum Failure {
    Missing(Vec<Fact>),
    Unsupported {
        correspondence: Fact,
        location: archsig_common::issue::Location,
    },
    Coverage {
        facts: Vec<Fact>,
        endpoint: Option<FailedEndpoint>,
    },
    SharedImage {
        left_correspondence: Fact,
        right_correspondence: Fact,
        source: Fact,
        left: Fact,
        right: Fact,
    },
    Preservation {
        facts: Vec<Fact>,
    },
    Square {
        kind: SquareKind,
        correspondence: Fact,
        difference: ActionDifference,
    },
}
/// 元correspondenceの端点を既存の担当構成へ解決し、同じ入力で局所写像を検査する。
pub(super) fn select(
    inputs: &CheckedInputs,
    source: &Model,
    target: &Model,
    correspondences: &[Fact],
    c: &Control,
) -> Result<Result<Vec<Local>, Failure>, ConstructionFailure> {
    use super::model_assembly::{counterexample_facts, field_fact, subject};
    use archsig_input::{
        archmap::{Slot, Value},
        definition::model::PrimitiveSignature,
    };
    let lookup_error = |e: super::result::ValidationFailure| match e {
        super::result::ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
        _ => ConstructionFailure::InvalidSelection("原始correspondenceの参照先がない".into()),
    };
    let source_index: BTreeMap<_, _> = source
        .fragments
        .iter()
        .enumerate()
        .map(|(i, f)| (f.root(), i))
        .collect();
    let target_index: BTreeMap<_, _> = target
        .fragments
        .iter()
        .enumerate()
        .map(|(i, f)| (f.root(), i))
        .collect();
    let mut locals = Vec::new();
    for raw in correspondences {
        tick(c)?;
        let holder = subject(inputs, raw).map_err(&lookup_error)?;
        let declaration = inputs
            .definitions()
            .declarations()
            .get(holder.ty.as_str())
            .ok_or_else(|| {
                ConstructionFailure::InvalidSelection("correspondenceの定義がない".into())
            })?;
        let PrimitiveSignature::Correspondence {
            from,
            to,
            maps,
            alignments,
            implicit,
            ..
        } = &declaration.signature
        else {
            return Ok(Err(Failure::Coverage {
                endpoint: None,
                facts: vec![raw.clone()],
            }));
        };
        // 非恒等な型・field位置の整列は、原始C自体の一般検査ではなく組立て族の未対応。
        if from != to || maps.iter().any(|(_, a, b)| a != b) || implicit.iter().any(|(a, b)| a != b)
        {
            return Ok(Err(Failure::Unsupported {
                correspondence: raw.clone(),
                location: declaration.location.clone(),
            }));
        }
        if let Some(a) = alignments.iter().find(|a| a.source != a.target) {
            return Ok(Err(Failure::Unsupported {
                correspondence: raw.clone(),
                location: a.location.clone(),
            }));
        }
        let mut endpoints = Vec::new();
        let mut missing = Vec::new();
        for name in ["from", "to"] {
            let field = holder
                .fields
                .iter()
                .find(|f| f.name.short() == name)
                .ok_or_else(|| {
                    ConstructionFailure::InvalidSelection("correspondence端点のfieldがない".into())
                })?;
            match &field.slot {
                Slot::Missing => missing.push(field_fact(holder, field)),
                Slot::Known {
                    value: Value::Ref { snapshot, subject },
                    ..
                } => {
                    endpoints.push(Fact::from(archsig_input::archmap::FactData {
                        snapshot: snapshot.clone(),
                        subject: subject.clone(),
                        field: None,
                        atom: None,
                    }));
                }
                _ => {
                    return Err(ConstructionFailure::InvalidSelection(
                        "correspondence端点がRefでない".into(),
                    ));
                }
            }
        }
        if !missing.is_empty() {
            return Ok(Err(Failure::Missing(missing)));
        }
        let (Some(&s), Some(&t)) = (
            source_index.get(&endpoints[0]),
            target_index.get(&endpoints[1]),
        ) else {
            let from = !source_index.contains_key(&endpoints[0]);
            return Ok(Err(Failure::Coverage {
                endpoint: Some(FailedEndpoint {
                    from,
                    subject: endpoints[usize::from(!from)].clone(),
                }),
                facts: vec![raw.clone(), endpoints[0].clone(), endpoints[1].clone()],
            }));
        };
        let result = maps::correspondence_constructed(
            inputs,
            &raw.snapshot,
            &raw.subject,
            Arc::clone(&source.fragments[s]),
            Arc::clone(&target.fragments[t]),
            c,
        )
        .map_err(|f| f.cause().clone())?;
        if !result.missing().is_empty() {
            return Ok(Err(Failure::Missing(result.missing().to_vec())));
        }
        let Some(map) = result.map() else {
            let mut facts = vec![raw.clone()];
            facts.extend(counterexample_facts(result.counterexamples()));
            return Ok(Err(Failure::Preservation { facts }));
        };
        locals.push(Local {
            correspondence: raw.clone(),
            source: s,
            target: t,
            map: map.clone(),
        });
    }
    Ok(Ok(locals))
}
#[derive(Debug)]
pub(super) struct Verified {
    pub glued: Glued,
    pub transport: Arc<maps::ConfigurationTransport>,
    pub laws: Vec<super::object_law_transport::ObjectLawTransport>,
    pub unsupported_instances: Vec<usize>,
}
impl Verified {
    pub fn has_refutation(&self) -> bool {
        self.transport.objects().iter().any(|object| {
            object.condition_failure().is_some() || !object.counterexamples().is_empty()
        }) || self.transport.generators().iter().any(|generator| {
            generator.condition_failure().is_some()
                || generator.endpoints_preserved() == Some(false)
                || matches!(
                    generator.naturality(),
                    Some(maps::Naturality::Refuted { .. })
                )
        }) || self.laws.iter().any(|law| {
            matches!(
                law.outcome(),
                super::object_law_transport::LawTransportOutcome::Refuted(_)
            )
        })
    }
    pub fn all_preserved(&self) -> bool {
        self.transport.all_preserved()
            && self.unsupported_instances.is_empty()
            && self.laws.iter().all(|law| {
                matches!(
                    law.outcome(),
                    super::object_law_transport::LawTransportOutcome::Preserved
                )
            })
    }
}
/// 元ArchitectureBodyが所有する同じLaw評価を使い、対象とLawの全行を移送する。
pub(super) fn verify(
    inputs: Arc<CheckedInputs>,
    source: &Model,
    target: &Model,
    glued: Glued,
    evaluations: [Arc<super::object_evaluate::LawEvaluationCache>; 2],
    c: &Control,
) -> Result<Verified, super::object_law_transport::ObjectLawTransportFailure> {
    use super::object_law_transport::{ObjectLawTransportFailure, object_law_transport_on_state};
    tick(c)?;
    // 組立てには少なくとも一つの担当がある。global操作族は包含が既に共有している。
    let source_arrows = source
        .inclusions
        .first()
        .ok_or_else(|| ConstructionFailure::InvalidSelection("移送元の担当がない".into()))?
        .shared_target();
    let target_arrows = target
        .inclusions
        .first()
        .ok_or_else(|| ConstructionFailure::InvalidSelection("移送先の担当がない".into()))?
        .shared_target();
    let transport = Arc::new(
        maps::configuration_transport_constructed(
            &inputs,
            &glued.map,
            source_arrows,
            target_arrows,
            c,
        )
        .map_err(|f| ObjectLawTransportFailure::Transport(Box::new(f)))?,
    );
    let declarations = Arc::new(maps::declaration_correspondence_constructed(
        &inputs, &glued.map, c,
    )?);
    let states = if source.repaired_values.is_empty() && target.repaired_values.is_empty() {
        None
    } else {
        let prepare =
            |model: &Model, readings: &crate::construction::readings::ObjectReadingInstances| {
                let classify = |failure: super::result::ValidationFailure| match failure {
                    super::result::ValidationFailure::Stop(signal) => {
                        ConstructionFailure::Stopped(signal)
                    }
                    other => ConstructionFailure::Inconsistent(
                        other.internal_context("修復済み写像の始終状態".into()),
                    ),
                };
                let state = super::environment::Environment::with_primitive_valuation(
                    &inputs,
                    &model.repaired_values,
                    c,
                )
                .map_err(classify)?;
                let domains = (0..readings.objects().len())
                    .map(|object| {
                        tick(c)?;
                        super::object_evaluate::ObjectDomain::from_readings(
                            &inputs, readings, object, c,
                        )
                        .map(Arc::new)
                        .map_err(classify)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok::<_, ConstructionFailure>((state, domains))
            };
        Some([
            prepare(source, evaluations[0].readings())?,
            prepare(target, evaluations[1].readings())?,
        ])
    };
    let mut laws = Vec::new();
    let readings = evaluations[0].readings();
    let mut unsupported_instances = Vec::new();
    for (index, row) in readings.instances().iter().enumerate() {
        if row.declaration().kind != "law" {
            continue;
        }
        if !row.parameters().is_empty()
            && (!source.repaired_values.is_empty() || !target.repaired_values.is_empty())
        {
            unsupported_instances.push(index);
            continue;
        }
        for parameter in row.parameters() {
            let supported =
                super::finite::supported(&parameter.ty, inputs.law(), c).map_err(|e| match e {
                    super::result::ValidationFailure::Stop(s) => ConstructionFailure::Stopped(s),
                    e => ConstructionFailure::Inconsistent(
                        e.internal_context("組立てLaw族の有限性検査".into()),
                    ),
                })?;
            if !supported {
                unsupported_instances.push(index);
                break;
            }
        }
    }
    for object in 0..readings.objects().len() {
        for (instance, row) in readings.instances().iter().enumerate() {
            tick(c)?;
            if row.declaration().kind != "law"
                || unsupported_instances.binary_search(&instance).is_ok()
            {
                continue;
            }
            laws.push(object_law_transport_on_state(
                Arc::clone(&inputs),
                Arc::clone(&declarations),
                Arc::clone(&transport),
                evaluations.clone(),
                object,
                instance,
                states
                    .as_ref()
                    .map(|[(source, source_domains), (target, target_domains)]| {
                        [
                            (source, source_domains.as_slice()),
                            (target, target_domains.as_slice()),
                        ]
                    }),
                c,
            )?);
        }
    }
    Ok(Verified {
        glued,
        transport,
        laws,
        unsupported_instances,
    })
}
fn tick(c: &Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ConfigurationMap)?;
    Ok(())
}
fn operation(
    map: &ConfigurationMap,
    c: &Control,
) -> Result<ConfigurationOperation, ConstructionFailure> {
    ConfigurationOperation::from_checked_map(map, c)
}
/// `locals`のmapは同じ入力のraw correspondence検査から得たものに限る。
/// 公開入力の証明書や完成作用表を取り込む入口ではない。
pub(super) fn glue(
    inputs: &CheckedInputs,
    source: &Arc<Model>,
    target: &Arc<Model>,
    locals: Vec<Local>,
    c: &Control,
) -> Result<Result<Glued, Failure>, ConstructionFailure> {
    tick(c)?;
    let mut covered = BTreeSet::new();
    for local in &locals {
        tick(c)?;
        let (Some(s), Some(t)) = (
            source.fragments.get(local.source),
            target.fragments.get(local.target),
        ) else {
            return Ok(Err(Failure::Coverage {
                endpoint: None,
                facts: vec![local.correspondence.clone()],
            }));
        };
        if !covered.insert(local.source)
            || local.map.candidate().source_root() != s.root()
            || local.map.candidate().target_root() != t.root()
            || local.map.candidate().reading() != s.reading()
            || local.map.candidate().to_reading() != t.reading()
        {
            return Ok(Err(Failure::Coverage {
                endpoint: None,
                facts: vec![
                    local.correspondence.clone(),
                    s.root().clone(),
                    t.root().clone(),
                ],
            }));
        }
    }
    if covered.len() != source.fragments.len() {
        return Ok(Err(Failure::Coverage {
            endpoint: None,
            facts: source
                .fragments
                .iter()
                .enumerate()
                .filter(|(i, _)| !covered.contains(i))
                .map(|(_, s)| s.root().clone())
                .collect(),
        }));
    }
    let mut subjects: BTreeMap<Fact, (Fact, usize)> = BTreeMap::new();
    for (index, local) in locals.iter().enumerate() {
        for fact in source.fragments[local.source]
            .base()
            .known()
            .family()
            .iter()
            .filter(|f| f.field.is_none())
        {
            tick(c)?;
            let Some(image) = local.map.candidate().image(fact) else {
                return Ok(Err(Failure::Preservation {
                    facts: vec![local.correspondence.clone(), fact.clone()],
                }));
            };
            let from = source.construction.transported_subject(fact).clone();
            let to = target.construction.transported_subject(image).clone();
            if let Some((previous, origin)) = subjects.get(&from) {
                if previous != &to {
                    return Ok(Err(Failure::SharedImage {
                        left_correspondence: locals[*origin].correspondence.clone(),
                        right_correspondence: local.correspondence.clone(),
                        source: from,
                        left: previous.clone(),
                        right: to,
                    }));
                }
            } else {
                subjects.insert(from, (to, index));
            }
        }
    }
    let Some(map) = maps::assembled_map(
        inputs,
        Arc::clone(&source.construction),
        Arc::clone(&target.construction),
        subjects
            .into_iter()
            .map(|(from, (to, _))| (from, to))
            .collect(),
        c,
    )?
    else {
        return Ok(Err(Failure::Preservation {
            facts: locals.iter().map(|l| l.correspondence.clone()).collect(),
        }));
    };
    let global = operation(&map, c)?;
    let mut restrictions = Vec::new();
    for local in &locals {
        tick(c)?;
        let mu = operation(&local.map, c)?;
        let left = mu.compose_checked(target.inclusions[local.target].operation(), c)?;
        let right = source.inclusions[local.source]
            .operation()
            .compose_checked(&global, c)?;
        if let Some(difference) = left.action_difference_checked(&right, c)? {
            return Ok(Err(Failure::Square {
                kind: SquareKind::Inclusion,
                correspondence: local.correspondence.clone(),
                difference,
            }));
        }
        let rho_source = &source.restrictions[local.source];
        let rho_target = &target.restrictions[local.target];
        let source_image = rho_source
            .candidate()
            .source_construction()
            .ok_or_else(|| ConstructionFailure::InvalidSelection("局所像の構成がない".into()))?;
        let target_image = rho_target
            .candidate()
            .source_construction()
            .ok_or_else(|| {
                ConstructionFailure::InvalidSelection("移送先の局所像の構成がない".into())
            })?;
        let mut restricted_subjects = BTreeMap::new();
        for fact in source_image
            .base()
            .known()
            .family()
            .iter()
            .filter(|f| f.field.is_none())
        {
            tick(c)?;
            if let Some(image) = map.candidate().image(fact) {
                restricted_subjects.insert(fact.clone(), image.clone());
            }
        }
        let Some(restriction) =
            maps::assembled_map(inputs, source_image, target_image, restricted_subjects, c)?
        else {
            return Ok(Err(Failure::Preservation {
                facts: vec![local.correspondence.clone()],
            }));
        };
        let left = operation(&restriction, c)?.compose_checked(&operation(rho_target, c)?, c)?;
        let right = operation(rho_source, c)?.compose_checked(&mu, c)?;
        if let Some(difference) = left.action_difference_checked(&right, c)? {
            return Ok(Err(Failure::Square {
                kind: SquareKind::Restriction,
                correspondence: local.correspondence.clone(),
                difference,
            }));
        }
        restrictions.push(restriction);
    }
    Ok(Ok(Glued {
        map,
        locals,
        restrictions,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::model_assembly::{Preparation, compile};
    use archsig_common::canonical::Json;
    use archsig_input::input::check_inputs;
    #[allow(dead_code)]
    mod fixture {
        include!("../../../../tests/common/model_map_assembly_data.rs");
    }
    fn fact(id: &str) -> Fact {
        Fact::from(archsig_input::archmap::FactData {
            snapshot: "v".into(),
            subject: id.into(),
            field: None,
            atom: None,
        })
    }
    fn setup() -> (Arc<CheckedInputs>, Arc<Model>) {
        let c = Control::unlimited();
        let inputs = Arc::new(check_inputs(fixture::input(fixture::without_arrows), &c).unwrap());
        let Preparation::Ready(model) = compile(
            &inputs,
            "Assembly",
            &fact("G"),
            &[fact("A"), fact("B")],
            &[(fact("ma"), fact("mb"))],
            &BTreeMap::new(),
            &c,
        )
        .unwrap() else {
            panic!("model")
        };
        (inputs, Arc::new(model))
    }
    fn locals(inputs: &CheckedInputs, model: &Model, swap: bool) -> Vec<Local> {
        model
            .fragments
            .iter()
            .enumerate()
            .map(|(i, cfg)| {
                let subjects = cfg
                    .base()
                    .known()
                    .family()
                    .iter()
                    .filter(|f| f.field.is_none())
                    .map(|f| {
                        let image = if swap && i == 0 && f.subject == "a" {
                            fact("ma")
                        } else if swap && i == 0 && f.subject == "ma" {
                            fact("a")
                        } else {
                            f.clone()
                        };
                        (f.clone(), image)
                    })
                    .collect();
                Local {
                    correspondence: cfg.root().clone(),
                    source: i,
                    target: i,
                    map: maps::assembled_map(
                        inputs,
                        cfg.clone(),
                        cfg.clone(),
                        subjects,
                        &Control::unlimited(),
                    )
                    .unwrap()
                    .expect("局所写像"),
                }
            })
            .collect()
    }

    fn mapped(edit: impl FnOnce(String) -> String) -> (Arc<CheckedInputs>, Arc<Model>) {
        mapped_with_law(edit, None)
    }
    fn mapped_with_law(
        edit: impl FnOnce(String) -> String,
        body: Option<&str>,
    ) -> (Arc<CheckedInputs>, Arc<Model>) {
        let c = Control::unlimited();
        let original = fixture::mapped(edit);
        let original = if let Some(body) = body {
            archsig_input::input::InputSources::from_bytes(
                original
                    .definitions()
                    .iter()
                    .map(|d| d.bytes().to_vec())
                    .collect(),
                String::from_utf8(original.law().bytes().to_vec())
                    .unwrap()
                    .replace("law required zero(p:Part):p.quantity=0;", body)
                    .into_bytes(),
                original.archmap().bytes().to_vec(),
            )
        } else {
            original
        };
        let inputs = Arc::new(check_inputs(original, &c).unwrap());
        let Preparation::Ready(model) = compile(
            &inputs,
            "Assembly",
            &fact("G"),
            &[fact("A"), fact("B")],
            &[(fact("ma"), fact("mb"))],
            &BTreeMap::new(),
            &c,
        )
        .unwrap() else {
            panic!("model")
        };
        (inputs, Arc::new(model))
    }

    #[test]
    fn request_binds_two_model_assembly_handles_and_all_view_parameters() {
        let inputs = check_inputs(fixture::query(|s| s), &Control::unlimited()).unwrap();
        let first = fixture::ASSEMBLE;
        let good =
            "m=assemble_map(Assembly.moves,from=$a.assembly,to=$a.assembly,x=@v/moveA,y=@v/moveB)";
        let check = |query: &str| {
            super::super::request::resolve_observed_requests_controlled(
                inputs.law(),
                inputs.archmap(),
                &[first, query],
                &Control::unlimited(),
            )
        };
        assert!(check(good).is_ok(), "{:?}", check(good).err());
        assert!(check(&good.replace(",y=@v/moveB", "")).is_err());
        assert!(check(&good.replace("from=$a.assembly", "from=$a.object")).is_err());
        assert!(check(&good.replace("x=@v/moveA", "x=@v/A")).is_err());
        assert!(check(&good.replace("to=$a.assembly", "to=@v/G")).is_err());
        let output = crate::observed::evaluate_observed_bytes(
            inputs.sources().clone(),
            &[
                first,
                good,
                "c=compose($m.configuration_map,then=$m.configuration_map)",
                "same=compare($m.configuration_map,to=$c.map,kind=action)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        assert!(
            output
                .answers
                .iter()
                .all(|a| a.status == super::super::result::Decision::Established),
            "issues={:?}; statuses={:?}",
            output.issues,
            output
                .answers
                .iter()
                .map(|a| (&a.id, a.status))
                .collect::<Vec<_>>()
        );
        assert!(output.answers[1].outputs.contains_key("map"));
        assert!(output.answers[1].outputs.contains_key("configuration_map"));
        assert!(!output.answers[2].outputs.contains_key("operation"));
        assert!(output.answers[2].outputs.contains_key("candidate"));
        let word = "bad=compare($m.configuration_map,to=$m.configuration_map,kind=word)";
        assert!(
            super::super::request::resolve_observed_requests_controlled(
                inputs.law(),
                inputs.archmap(),
                &[first, good, word],
                &Control::unlimited()
            )
            .is_err()
        );
    }

    #[test]
    fn nonidentity_direct_map_agrees_with_three_steps_and_differs_from_two() {
        use super::super::result::Decision;
        let result = crate::observed::evaluate_observed_bytes(
            fixture::query(fixture::swapping),
            &[
                fixture::ASSEMBLE,
                fixture::MAP,
                "two=compose($m.configuration_map,then=$m.configuration_map)",
                "three=compose($two.map,then=$m.configuration_map)",
                "same=compare($m.configuration_map,to=$three.map,kind=action)",
                "different=compare($m.configuration_map,to=$two.map,kind=action)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        assert!(result.issues.is_empty(), "{:?}", result.issues);
        assert!(
            result.answers[..5]
                .iter()
                .all(|a| a.status == Decision::Established)
        );
        assert_eq!(result.answers[5].status, Decision::Refuted);
        assert!(!result.answers[5].evidence.is_empty());
        for atom in ["moveA-parts", "moveB-parts", "moveA-from", "moveB-to"] {
            assert!(
                result.nodes[result.answers[1].claim.unwrap().0]
                    .support
                    .iter()
                    .any(|f| f.atom.as_deref() == Some(atom)),
                "{atom}"
            );
        }
        for answer in &result.answers[2..4] {
            assert!(!answer.outputs.contains_key("operation"));
        }
    }
    #[test]
    fn repeated_native_map_squaring_compares_actions_without_an_operation_word() {
        use super::super::result::Decision;
        let mut asks = vec![fixture::ASSEMBLE.to_owned(), fixture::MAP.to_owned()];
        asks.push("c0=compose($m.configuration_map,then=$m.configuration_map)".into());
        for n in 1..4 {
            asks.push(format!(
                "c{n}=compose($c{}.map,then=$c{}.map)",
                n - 1,
                n - 1
            ));
        }
        asks.extend([
            "same=compare($c0.map,to=$c3.map,kind=action)".into(),
            "different=compare($m.configuration_map,to=$c3.map,kind=action)".into(),
        ]);
        let texts = asks.iter().map(String::as_str).collect::<Vec<_>>();
        let result = crate::observed::evaluate_observed_bytes(
            fixture::query(fixture::swapping),
            &texts,
            &Control::unlimited(),
        )
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
        assert!(
            result.answers[..7]
                .iter()
                .all(|a| a.status == Decision::Established),
            "{:?}",
            result.issues
        );
        assert_eq!(result.answers[7].status, Decision::Refuted);
        for answer in &result.answers[2..6] {
            assert!(answer.outputs.contains_key("map"));
            assert!(!answer.outputs.contains_key("operation"));
        }
    }
    #[test]
    fn missing_correspondence_endpoint_keeps_an_unknown_proposition_without_a_map() {
        use super::super::result::{Decision, ReasonKind};
        let result = crate::observed::evaluate_observed_bytes(
            fixture::query(|s| fixture::atom(s, "moveA-from", None)),
            &[fixture::ASSEMBLE, fixture::MAP],
            &Control::unlimited(),
        )
        .unwrap();
        let answer = &result.answers[1];
        assert_eq!(answer.status, Decision::Undetermined);
        assert!(answer.claim.is_some());
        assert!(!answer.outputs.contains_key("configuration_map"));
        assert!(!answer.outputs.contains_key("map"));
        assert!(answer.reasons.iter().any(|r| {
            matches!(r.kind, ReasonKind::Missing)
                && r.missing.iter().any(|f| {
                    f.subject == "moveA" && f.field.as_deref() == Some("Assemble.Move.from")
                })
        }));
        assert!(
            !result
                .issues
                .iter()
                .any(|r| matches!(r.kind, ReasonKind::Internal(_)))
        );
    }

    #[test]
    fn native_law_failure_keeps_configuration_map_and_actual_boolean_counterexample() {
        use super::super::{
            construction_result::ConstructionData as D,
            result::{Decision, Payload, Scalar},
        };
        for residual in ["", "law required parameter(r:Root,n:Z):n=n;"] {
            let input = fixture::query(|s| fixture::folding(s, true));
            let input = fixture::replace_law(
                input,
                "law required zero(p:Part):p.quantity=0;",
                "view only(a:Root):Set<Root> = set<Root>{a};view emptyInterfaces(a:Root):Unit=unit;law required zero(p:Part):p.quantity=0;",
            );
            let input = fixture::replace_law(
                input,
                "law required zero(p:Part):p.quantity=0;",
                &format!("law required zero(p:Part):p.quantity=0;{residual}"),
            );
            let result=crate::observed::evaluate_observed_bytes(input,&[fixture::ASSEMBLE,
            "b=assemble(Assembly.only,on=@v/G,along=Assembly.emptyInterfaces,a=@v/A)",
            "m=assemble_map(Assembly.moves,from=$a.assembly,to=$b.assembly,x=@v/moveA,y=@v/moveB)"],&Control::unlimited()).unwrap();
            assert!(
                result.answers[..2]
                    .iter()
                    .all(|a| a.status == Decision::Established),
                "{:?}",
                result.issues
            );
            let answer = &result.answers[2];
            assert_eq!(answer.status, Decision::Refuted, "{:?}", result.issues);
            let failure = answer
                .reasons
                .iter()
                .find_map(|r| match r.kind {
                    super::super::result::ReasonKind::ConditionFailed { condition, .. } => {
                        Some(condition)
                    }
                    _ => None,
                })
                .expect("元の反証条件を理由へ保持する");
            assert_eq!(
                result.nodes[failure.0].judgment.as_ref().unwrap().status,
                Decision::Refuted
            );
            assert_eq!(
                result.nodes[answer.claim.unwrap().0].reasons,
                answer.reasons
            );
            assert!(answer.outputs.contains_key("configuration_map"));
            assert!(!answer.outputs.contains_key("map"));
            let scalar = |r: usize| match result.nodes[r].payload.as_ref().unwrap() {
                Payload::Scalar(v) => v,
                Payload::Construction(v) => v.scalar().unwrap(),
                _ => panic!("native値"),
            };
            let Some(Payload::Construction(value)) = &result.nodes[answer.evidence[0].0].payload
            else {
                panic!("native反例")
            };
            let D::ModelMap(data) = &value.data else {
                panic!("組立ての反例")
            };
            let Json::Obj(ref record) = data.wire() else {
                panic!("反例record")
            };
            let Json::Obj(record) = &record["data"] else {
                panic!("反例data")
            };
            let left = record["left"].exact_node_reference().unwrap();
            let right = record["right"].exact_node_reference().unwrap();
            assert_eq!(scalar(left), &Scalar::Bool(true));
            assert_eq!(scalar(right), &Scalar::Bool(false));
            if !residual.is_empty() {
                assert!(
                    answer.reasons.iter().any(|reason| matches!(
                        reason.kind,
                        super::super::result::ReasonKind::UnsupportedAlgorithm { .. }
                    )),
                    "{:?}",
                    answer.reasons
                );
            }
        }
    }

    #[test]
    fn three_model_generations_preserve_named_generators_and_feed_the_existing_workflow() {
        use super::super::result::{Decision, Payload};
        let mut asks=(0..3).map(|n|format!("s{n}=assemble(Assembly.fragments,on=@v/G{n},along=Assembly.interfaces,a=@v/A{n},b=@v/B{n},ma=@v/ma{n},mb=@v/mb{n})")).collect::<Vec<_>>();
        asks.extend([
            "direct=assemble_map(Assembly.moves,from=$s0.assembly,to=$s2.assembly,x=@v/m02A,y=@v/m02B)",
            "first=assemble_map(Assembly.moves,from=$s0.assembly,to=$s1.assembly,x=@v/m01A,y=@v/m01B)",
            "second=assemble_map(Assembly.moves,from=$s1.assembly,to=$s2.assembly,x=@v/m12A,y=@v/m12B)",
            "composed=compose($first.configuration_map,then=$second.configuration_map)",
            "same=compare($direct.configuration_map,to=$composed.map,kind=action)",
            "name=compare($direct.map.generators[0].source,to=$first.map.generators[0].source,kind=word)",
            "c=check(Assembly.zero,on=$direct.map.target)",
            "l=localize($direct.map.target,law=Assembly.zero)",
            "u=evaluate(Assembly.singleton,p=@v/b2)",
            "p=prepare(Assembly.zero,using=Assembly.choose,on=$direct.map.target)",
            "s=solve($p.problem,within=$u.value)",
            "k=candidate($s.solutions,index=0)",
            "v=apply($k.assignment,in=$s.solutions)",
            "t=check(Assembly.zero,on=$v.object)",
            "o=evaluate(Assembly.ownerOf,on=$v.object,p=@v/b2)",
        ].into_iter().map(String::from));
        let texts = asks.iter().map(String::as_str).collect::<Vec<_>>();
        let result = crate::observed::evaluate_observed_bytes(
            fixture::generations(),
            &texts,
            &Control::unlimited(),
        )
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
        assert!(
            result
                .answers
                .iter()
                .all(|a| a.status == Decision::Established),
            "issues={:?}; statuses={:?}",
            result.issues,
            result
                .answers
                .iter()
                .map(|a| (&a.id, a.status))
                .collect::<Vec<_>>()
        );
        let Some(Payload::Construction(value)) =
            &result.nodes[result.answers[3].outputs["configuration_map"].0].payload
        else {
            panic!("native map")
        };
        let super::super::construction_result::ConstructionData::ModelMap(data) = &value.data
        else {
            panic!("native map")
        };
        let map = data.core_map().unwrap().candidate();
        assert_eq!(map.image(&fact("a0")), Some(&fact("a2")));
        assert_eq!(map.image(&fact("ma0")), Some(&fact("ma2")));
        assert_eq!(map.image(&fact("left0")), Some(&fact("left2")));
        // 派生所有者は元correspondence観測を書き換えない。別の参照候補には
        // 元のOwned/Map制約が引き続き適用される。
        let Some(Payload::Construction(target)) =
            &result.nodes[result.answers[2].outputs["object"].0].payload
        else {
            panic!("target architecture")
        };
        let super::super::construction_result::Witness::Architecture(witness) = &target.witness
        else {
            panic!("target witness")
        };
        let position = Fact::from(archsig_input::archmap::FactData {
            snapshot: "v".into(),
            subject: "a2".into(),
            atom: None,
            field: Some("Assemble.Part.owner".into()),
        });
        let owner_ref = |subject: &str| super::super::result::Scalar::Subject {
            snapshot: "v".into(),
            subject: subject.into(),
            entity: "Assemble.Root".into(),
        };
        let inputs = result.prepared.inputs();
        let control = Control::unlimited();
        assert!(
            super::super::environment::Environment::try_primitive_valuation(
                inputs,
                &[(position.clone(), owner_ref("G2"))],
                &control
            )
            .unwrap()
            .is_none()
        );
        assert!(
            super::super::environment::Environment::try_object_primitive_valuation(
                inputs,
                &[(position.clone(), owner_ref("G2"))],
                witness,
                &control
            )
            .unwrap()
            .is_some()
        );
        assert!(
            super::super::environment::Environment::try_object_primitive_valuation(
                inputs,
                &[(position, owner_ref("B0"))],
                witness,
                &control
            )
            .unwrap()
            .is_none()
        );
        let owner = &result.nodes[result.answers.last().unwrap().outputs["value"].0];
        let scalar = match owner.payload.as_ref().unwrap() {
            Payload::Scalar(v) => v,
            Payload::Construction(v) => v.scalar().unwrap(),
            _ => panic!("owner"),
        };
        assert!(
            matches!(scalar,super::super::result::Scalar::Subject{subject,..} if subject=="G2")
        );
    }
    #[test]
    fn global_generator_square_is_checked_after_locally_preserved_maps_and_configuration() {
        use super::super::{
            construction_result::ConstructionData as D,
            result::{Decision, Payload},
        };
        let input = fixture::replace_law(
            fixture::query(fixture::folding_with_arrows),
            "law required zero(p:Part):p.quantity=0;",
            "view only(a:Root):Set<Root> = set<Root>{a};view emptyInterfaces(a:Root):Unit=unit;law required zero(p:Part):p.quantity=0;",
        );
        let result=crate::observed::evaluate_observed_bytes(input,&[fixture::ASSEMBLE,
            "b=assemble(Assembly.only,on=@v/G,along=Assembly.emptyInterfaces,a=@v/A)",
            "m=assemble_map(Assembly.moves,from=$a.assembly,to=$b.assembly,x=@v/moveA,y=@v/moveB)",
            "wrong=compose($m.configuration_map,then=$m.configuration_map)"],&Control::unlimited()).unwrap_or_else(|e|panic!("{:?}",e.wire()));
        assert!(
            result.answers[..2]
                .iter()
                .all(|a| a.status == Decision::Established),
            "{:?}",
            result.issues
        );
        let answer = &result.answers[2];
        assert_eq!(answer.status, Decision::Refuted, "{:?}", result.issues);
        let failure = answer
            .reasons
            .iter()
            .find_map(|r| match r.kind {
                super::super::result::ReasonKind::ConditionFailed { condition, .. } => {
                    Some(condition)
                }
                _ => None,
            })
            .expect("元の反証条件を理由へ保持する");
        assert_eq!(
            result.nodes[failure.0].judgment.as_ref().unwrap().status,
            Decision::Refuted
        );
        assert_eq!(
            result.nodes[answer.claim.unwrap().0].reasons,
            answer.reasons
        );
        assert!(answer.outputs.contains_key("configuration_map"));
        assert!(!answer.outputs.contains_key("map"));
        let Some(Payload::Construction(value)) = &result.nodes[answer.evidence[0].0].payload else {
            panic!("native counterexample")
        };
        let D::ModelMap(data) = &value.data else {
            panic!("map")
        };
        let wire = data.wire();
        let Json::Obj(record) = &wire else {
            panic!("evidence")
        };
        let Json::Obj(record) = &record["data"] else {
            panic!("evidence data")
        };
        let Json::Obj(difference) = &record["action_difference"] else {
            panic!("typed action difference")
        };
        assert_eq!(difference["kind"], Json::str("generator"));
        assert_ne!(difference["left"], difference["right"]);
        assert_eq!(
            result.answers[3].status,
            Decision::Refuted,
            "同じroot名でも異なる構成環境の自己合成は成立しない: {:?}",
            result.issues
        );
        assert!(result.answers[3].claim.is_some());
        assert!(!result.answers[3].outputs.contains_key("map"));
    }
    #[test]
    fn raw_correspondences_glue_and_preserve_global_generators_and_laws() {
        let (inputs, model) = mapped(|s| s);
        let c = Control::unlimited();
        let locals = select(&inputs, &model, &model, &[fact("moveA"), fact("moveB")], &c)
            .unwrap()
            .unwrap();
        let glued = glue(&inputs, &model, &model, locals, &c).unwrap().unwrap();
        let readings = Arc::new(
            crate::construction::readings::object_reading_instances_checked(
                &inputs,
                model.construction.clone(),
                &c,
            )
            .unwrap(),
        );
        let evaluations = Arc::new(super::super::object_evaluate::LawEvaluationCache::new(
            inputs.clone(),
            readings,
        ));
        let verified = verify(
            inputs.clone(),
            &model,
            &model,
            glued,
            [evaluations.clone(), evaluations.clone()],
            &c,
        )
        .unwrap();
        assert!(
            verified.all_preserved(),
            "transport={}, laws={:?}",
            verified.transport.all_preserved(),
            verified
                .laws
                .iter()
                .map(|law| (law.instance().declaration().name.clone(), law.outcome()))
                .collect::<Vec<_>>()
        );
        assert!(!verified.transport.generators().is_empty());
        assert!(!verified.laws.is_empty());
        let index = evaluations
            .readings()
            .instances()
            .iter()
            .position(|r| r.declaration().kind == "law")
            .unwrap();
        let first = evaluations.evaluate(0, index, &c).unwrap();
        let second = evaluations.evaluate(0, index, &c).unwrap();
        assert!(Arc::ptr_eq(&first, &second));
        assert!(std::ptr::eq(
            verified.laws[0].source().unwrap(),
            first.as_ref()
        ));

        verified.glued.map.recheck(&inputs, &c).unwrap();
    }

    fn folding(quantity: bool) -> (Arc<CheckedInputs>, Arc<Model>, Arc<Model>) {
        use archsig_common::canonical::Json;
        let (inputs, source) = mapped_with_law(
            |s| {
                let s = fixture::atom(s, "moveA-steps", Some(Json::Arr(vec![])));
                let s = fixture::atom(s, "moveB-steps", Some(Json::Arr(vec![])));
                let s = fixture::without_arrows(s);
                let s = fixture::atom(
                    s,
                    "moveB-to",
                    Some(Json::Arr(vec![Json::str("v"), Json::str("A")])),
                );
                let pairs = [("mb", "ma"), ("b", "a")]
                    .into_iter()
                    .map(|(a, b)| {
                        Json::Arr(vec![
                            Json::Arr(vec![Json::str("v"), Json::str(a)]),
                            Json::Arr(vec![Json::str("v"), Json::str(b)]),
                        ])
                    })
                    .collect();
                let s = fixture::atom(s, "moveB-parts", Some(Json::Arr(pairs)));
                if quantity {
                    fixture::atom(s, "a-quantity", Some(Json::str("1")))
                } else {
                    s
                }
            },
            if quantity {
                None
            } else {
                Some("law required fixed(r:Root):true;")
            },
        );
        let Preparation::Ready(target) = compile(
            &inputs,
            "Assembly",
            &fact("G"),
            &[fact("A")],
            &[],
            &BTreeMap::new(),
            &Control::unlimited(),
        )
        .unwrap() else {
            panic!("target")
        };
        (inputs, source, Arc::new(target))
    }
    fn evaluate(inputs: Arc<CheckedInputs>, source: &Arc<Model>, target: &Arc<Model>) -> Verified {
        let c = Control::unlimited();
        let locals = select(&inputs, source, target, &[fact("moveA"), fact("moveB")], &c)
            .unwrap()
            .unwrap();
        let glued = glue(&inputs, source, target, locals, &c).unwrap().unwrap();
        let caches = [source, target].map(|model| {
            let readings = Arc::new(
                crate::construction::readings::object_reading_instances_checked(
                    &inputs,
                    model.construction.clone(),
                    &c,
                )
                .unwrap(),
            );
            Arc::new(super::super::object_evaluate::LawEvaluationCache::new(
                inputs.clone(),
                readings,
            ))
        });
        verify(inputs, source, target, glued, caches, &c).unwrap()
    }
    #[test]
    fn two_source_fragments_may_map_to_one_target_fragment() {
        let (inputs, source, target) = folding(false);
        let verified = evaluate(inputs, &source, &target);
        assert!(
            verified.all_preserved(),
            "transport={}, laws={:?}",
            verified.transport.all_preserved(),
            verified
                .laws
                .iter()
                .map(|law| (law.instance().declaration().name.clone(), law.outcome()))
                .collect::<Vec<_>>()
        );
        assert_eq!(verified.glued.locals.len(), 2);
        assert_eq!(
            verified.glued.map.candidate().image(&fact("b")),
            Some(&fact("a"))
        );
    }
    #[test]
    fn configuration_preservation_does_not_assert_law_preservation() {
        let (inputs, source, target) = folding(true);
        let verified = evaluate(inputs, &source, &target);
        assert!(verified.transport.all_preserved());
        assert!(!verified.all_preserved());
        assert!(verified.laws.iter().any(|law| matches!(
            law.outcome(),
            super::super::object_law_transport::LawTransportOutcome::Refuted(_)
        )));
    }

    #[test]
    fn infinite_parameter_is_not_replaced_by_observed_values_or_a_sample() {
        let (inputs, model) =
            mapped_with_law(|s| s, Some("law required parameter(r:Root,n:Z):n=n;"));
        let verified = evaluate(inputs, &model, &model);
        assert!(verified.transport.all_preserved());
        assert!(!verified.all_preserved());
        assert!(verified.laws.is_empty());
        assert_eq!(verified.unsupported_instances.len(), 1);
    }
    #[test]
    fn missing_raw_endpoint_is_not_a_refuted_or_guessed_map() {
        let (inputs, model) = mapped(|s| fixture::atom(s, "moveA-from", None));
        let failure = select(
            &inputs,
            &model,
            &model,
            &[fact("moveA"), fact("moveB")],
            &Control::unlimited(),
        )
        .unwrap()
        .unwrap_err();
        let Failure::Missing(facts) = failure else {
            panic!("{failure:?}")
        };
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].subject, "moveA");
        assert_eq!(facts[0].field.as_deref(), Some("Assemble.Move.from"));
    }
    #[test]
    fn identity_glues_and_checks_inclusion_and_restriction_squares() {
        let (inputs, model) = setup();
        let result = glue(
            &inputs,
            &model,
            &model,
            locals(&inputs, &model, false),
            &Control::unlimited(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(result.locals.len(), 2);
        assert_eq!(result.restrictions.len(), 2);
        let action = result.map.candidate();
        for fact in model.construction.base().known().family() {
            assert_eq!(action.image(fact), Some(fact));
        }
        // 外側の恒等射も同じ構成を使い、raw root名だけで比較しない。
        result.map.recheck(&inputs, &Control::unlimited()).unwrap();
    }
    #[test]
    fn locally_valid_maps_cannot_choose_different_images_of_shared_class() {
        let (inputs, model) = setup();
        let failure = glue(
            &inputs,
            &model,
            &model,
            locals(&inputs, &model, true),
            &Control::unlimited(),
        )
        .unwrap()
        .unwrap_err();
        let Failure::SharedImage {
            source,
            left,
            right,
            left_correspondence,
            right_correspondence,
        } = failure
        else {
            panic!("{failure:?}")
        };
        assert_eq!(source, fact("ma"));
        assert_eq!(left, fact("a"));
        assert_eq!(right, fact("ma"));
        assert_eq!(left_correspondence, fact("A"));
        assert_eq!(right_correspondence, fact("B"));
    }
    #[test]
    fn each_source_fragment_must_be_covered_exactly_once() {
        let (inputs, model) = setup();
        let mut maps = locals(&inputs, &model, false);
        maps.pop();
        assert!(matches!(
            glue(&inputs, &model, &model, maps, &Control::unlimited()).unwrap(),
            Err(Failure::Coverage { .. })
        ));
        let mut maps = locals(&inputs, &model, false);
        maps[1].source = 0;
        assert!(matches!(
            glue(&inputs, &model, &model, maps, &Control::unlimited()).unwrap(),
            Err(Failure::Coverage { .. })
        ));
    }
}
