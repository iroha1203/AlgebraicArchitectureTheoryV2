//! 元Architecture内のchange全instanceとLaw全束縛を同じ候補状態で読む。
use super::*;
use crate::law::model::Signature;
use crate::observed::{construction_result::ArchitectureWitness, object_evaluate::ObjectDomain};
use change_evaluation::{Candidates, SolutionRow};
use std::sync::Arc;

pub(in crate::observed) struct Search {
    pub linear: Option<change_affine::Linear>,
    pub rational: Option<field_change::Linear>,
    pub pending_integer: Option<change_affine::Pending>,
    pub candidates: Option<Candidates>,
    pub solutions: Vec<SolutionRow>,
    pub requirements: Vec<(String, Vec<(String, Scalar)>)>,
    pub bindings: Vec<(String, Scalar)>,
    pub missing: Vec<Fact>,
    pub complete: bool,
    pub valuation: Vec<(Fact, Scalar)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::observed::request::resolve_native_for_test;
    #[allow(dead_code)]
    mod fixture {
        include!("../../../tests/common/primitive_valuation_data.rs");
    }
    fn run(map: &str) -> Search {
        let inputs = fixture::with_body(
            map,
            "change choose(c:Part,b:Bool)=c with {flag=b};law required valid(c:Part):c.flag;",
        );
        let mut control = Control::unlimited();
        let requests = resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["s=solve(Selected.valid,on=@v/root,using=Selected.choose)"],
            &mut control,
        )
        .unwrap();
        let request = &requests.requests()[0];
        let witness = ArchitectureWitness::compute(
            inputs.clone(),
            request,
            "Selected",
            &Fact {
                snapshot: "v".into(),
                subject: "root".into(),
                field: None,
                atom: None,
            },
            &mut control,
        )
        .unwrap();
        let environment = Environment::new(&inputs, &mut control).unwrap();
        let graph = Graph::new(&control);
        match search(&environment, &graph, &witness, request, &mut control) {
            Ok(s) => s,
            Err(e) => panic!("{:?}", e.cause),
        }
    }
    #[test]
    fn all_local_instances_are_updated_before_all_law_bindings_are_checked() {
        let result = run(fixture::MAP);
        assert!(result.complete);
        let candidates = result.candidates.as_ref().unwrap();
        assert_eq!(candidates.subjects.len(), 2);
        assert_eq!(candidates.rows.len(), 4);
        assert_eq!(result.requirements.len(), 2);
        assert_eq!(
            result
                .solutions
                .iter()
                .map(|r| r.member)
                .collect::<Vec<_>>(),
            vec![Some(false), Some(false), Some(false), Some(true)]
        );
    }
    #[test]
    fn other_root_subjects_do_not_become_change_instances_or_requirements() {
        let map = fixture::MAP.replace(
            r#""id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"]"#,
            r#""id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","r2"]"#,
        );
        assert_ne!(map, fixture::MAP);
        let result = run(&map);
        assert!(result.complete);
        assert_eq!(result.candidates.as_ref().unwrap().subjects.len(), 1);
        assert_eq!(result.requirements.len(), 1);
        assert_eq!(
            result
                .solutions
                .iter()
                .map(|r| r.member)
                .collect::<Vec<_>>(),
            vec![Some(false), Some(true)]
        );
    }
    #[test]
    fn missing_membership_does_not_complete_a_smaller_candidate_space() {
        let map=fixture::MAP.replace(r#"{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#,"");
        assert_ne!(map, fixture::MAP);
        let result = run(&map);
        assert!(!result.complete);
        assert!(result.candidates.is_none());
        assert!(
            result
                .missing
                .iter()
                .any(|f| f.subject == "q" && f.field.as_deref() == Some("Pattern.Part.owner"))
        );
    }

    #[test]
    fn stored_completion_and_baseline_overrides_survive_solution_resubstitution() {
        let map = fixture::MAP.replace(r#"{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#, "");
        assert_ne!(map, fixture::MAP);
        let inputs = fixture::with_body(
            &map,
            "change choose(c:Part,b:Bool) when not c.flag=c with {flag=b};law required valid(c:Part):c.flag;",
        );
        let mut c = quiet_for_valuation();
        let env = Environment::new(&inputs, &mut c).unwrap();
        let requests = resolve_native_for_test(
            inputs.law(),
            inputs.archmap(),
            &["s=solve(Selected.valid,on=@v/root,using=Selected.choose)"],
            &mut c,
        )
        .unwrap();
        let witness = ArchitectureWitness::compute(
            inputs.clone(),
            &requests.requests()[0],
            "Selected",
            &Fact {
                snapshot: "v".into(),
                subject: "root".into(),
                field: None,
                atom: None,
            },
            &mut c,
        )
        .unwrap();
        let p = Scalar::Subject {
            snapshot: "v".into(),
            subject: "p".into(),
            entity: "Pattern.Part".into(),
        };
        // Baseline changes an observed true flag to false; the owner case pins q to r2.
        let valuation = vec![
            (
                Fact {
                    snapshot: "v".into(),
                    subject: "p".into(),
                    field: Some("Pattern.Part.flag".into()),
                    atom: None,
                },
                Scalar::Bool(false),
            ),
            (
                Fact {
                    snapshot: "v".into(),
                    subject: "q".into(),
                    field: Some("Pattern.Part.owner".into()),
                    atom: None,
                },
                Scalar::Subject {
                    snapshot: "v".into(),
                    subject: "r2".into(),
                    entity: "Pattern.Root".into(),
                },
            ),
        ];
        let mut case = Environment::with_primitive_valuation(&inputs, &valuation, &mut c).unwrap();
        case.object = Some(Arc::new(
            ObjectDomain::from_readings(&inputs, witness.readings(), 0, &mut c).unwrap(),
        ));
        let change = &inputs.law().declarations["Selected.choose"];
        let candidate = change_evaluation::candidate(
            &case,
            change,
            std::slice::from_ref(&p),
            &[Scalar::Bool(true)],
        )
        .unwrap();
        assert_eq!(candidate.update.state, change_evaluation::State::Ready);
        let requirements = vec![("Selected.valid".into(), vec![("c".into(), p.clone())])];
        let member = change_evaluation::solution_row(&case, &candidate, 0, &requirements).unwrap();
        assert_eq!(member.member, Some(true));
        let search = Search {
            linear: None,
            rational: None,
            pending_integer: None,
            candidates: Some(Candidates {
                subjects: vec![p],
                parameter_types: vec![Type::Bool],
                rows: vec![candidate],
                complete: true,
            }),
            solutions: vec![member],
            requirements,
            bindings: vec![],
            missing: vec![],
            complete: true,
            valuation,
        };
        verify_point(&env, &witness, &search, 0, &mut c).unwrap();
        let mut lost = search;
        lost.valuation.clear();
        assert!(verify_point(&env, &witness, &lost, 0, &mut c).is_err());
    }
    fn quiet_for_valuation() -> Control {
        Control::unlimited()
    }
}
pub(in crate::observed) struct SearchFailure {
    pub cause: ValidationFailure,
    pub partial: Box<Search>,
}
pub(in crate::observed) fn domain(
    environment: &Environment<'_>,
    ty: &Type,
    span: (usize, usize),
    missing: &mut Vec<Fact>,
) -> Result<Option<Vec<Scalar>>, ValidationFailure> {
    if !super::super::finite::supported(
        &ty.erase(),
        environment.inputs.law(),
        &environment.control,
    )? {
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law { span },
            feature: "変更候補のLaw parameter全域評価の有限域以外は未実装".into(),
        });
    }
    let enumeration = environment.finite_values(&ty.erase(), &mut |_, _| {})?;
    let mut values = Some(enumeration.values);
    // 依存型は各Law行のowner束縛で適合を検査する。onへの事前交差は
    // 明示された外部ownerの族を消す。ownerを持たないroot型も全登録族を使う。
    let directly_owned = match ty {
        Type::Ref(entity) => environment
            .inputs
            .definitions()
            .declarations
            .get(entity)
            .is_some_and(|d| {
                matches!(
                    d.signature,
                    crate::definition::model::PrimitiveSignature::Entity { owner: Some(_), .. }
                        | crate::definition::model::PrimitiveSignature::Arrow { .. }
                )
            }),
        _ => false,
    };
    if directly_owned && let Some(object) = environment.object_domain() {
        object.restrict(
            ty,
            &mut values,
            missing,
            &mut vec![],
            &mut Scope::default(),
            &environment.control,
            &[],
            environment.primitive_valuation.as_ref(),
        )?;
    }
    Ok(values)
}
pub(in crate::observed) fn selector(
    environment: &Environment<'_>,
    graph: &Graph,
    value: &Selector,
) -> Result<Scalar, ValidationFailure> {
    Ok(match value {
        Selector::Subject { snapshot, subject } => {
            let original = environment.subject(snapshot, subject)?;
            Scalar::Subject {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
                entity: original.ty.clone(),
            }
        }
        Selector::Answer { .. } => match environment.answer_binding(graph, value, (0, 0))? {
            AnswerBinding::Reference(r) => graph.scalar(r)?.clone(),
            AnswerBinding::Projection(node) => match node.payload {
                Some(Payload::Scalar(value)) => value,
                _ => return Err("変更候補の束縛射影が通常値でない".into()),
            },
            AnswerBinding::Inapplicable(_) => return Err("変更候補の束縛射影が不適合".into()),
        },
        _ => return Err("変更候補の束縛がHandleでない".into()),
    })
}

pub(in crate::observed) fn search(
    original: &Environment<'_>,
    graph: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    control: &mut Control,
) -> Result<Search, SearchFailure> {
    search_with_completions(original, graph, witness, request, &[], control)
}

pub(in crate::observed) fn search_with_completions(
    original: &Environment<'_>,
    graph: &Graph,
    witness: &ArchitectureWitness,
    request: &Request,
    completions: &[(Fact, Scalar)],
    control: &mut Control,
) -> Result<Search, SearchFailure> {
    let mut result = Search {
        linear: None,
        rational: None,
        pending_integer: None,
        candidates: None,
        solutions: vec![],
        requirements: vec![],
        bindings: vec![],
        missing: vec![],
        complete: false,
        valuation: original
            .architecture_values()
            .into_iter()
            .chain(witness.construction().resolved_owners().iter().map(|(field, owner)| {
                let subject = original.subject(&owner.snapshot, &owner.subject).expect("検査済みowner参照");
                (field.clone(), Scalar::Subject { snapshot: owner.snapshot.clone(), subject: owner.subject.clone(), entity: subject.ty.clone() })
            }))
            .chain(completions.iter().cloned())
            .collect(),
    };
    let computed = (|| -> Result<(), ValidationFailure> {
        let inputs = original.inputs;
        let mut environment =
            Environment::try_primitive_valuation(inputs, &result.valuation, control)?
                .ok_or("元修復Architectureの代入が不適合")?;
        environment.object = Some(Arc::new(ObjectDomain::from_readings(
            inputs,
            witness.readings(),
            0,
            control,
        )?));
        let law_name = request.declaration().ok_or("solveの元Lawがない")?;
        let law = inputs
            .law()
            .declarations
            .get(law_name)
            .ok_or("solveの元Law宣言がない")?;
        let Signature::Law { params, .. } = &law.signature else {
            return Err("solveのheadがLawでない".into());
        };
        let using = request
            .arguments
            .iter()
            .find(|a| a.name == "using")
            .ok_or("solveのusingがない")?;
        let Selector::Declaration { name } = &using.value else {
            return Err("solveのusingが宣言名でない".into());
        };
        let change = inputs
            .law()
            .declarations
            .get(name)
            .ok_or("solveのchange宣言がない")?;
        let Signature::Change {
            params: change_params,
            ..
        } = &change.signature
        else {
            return Err("solveのusingがchangeでない".into());
        };
        if law.reading != change.reading || witness.construction().reading() != law.reading {
            return Err("変更候補のLaw・change・対象readingが違う".into());
        }
        let first = change_params.first().ok_or("changeの第一parameterがない")?;
        let Some(mut subjects) = domain(&environment, &first.ty, first.span, &mut result.missing)?
        else {
            return Ok(());
        };
        let construction = witness.construction();
        subjects.retain(|value| {
            let Scalar::Subject {
                snapshot, subject, ..
            } = value
            else {
                return false;
            };
            std::iter::once(construction.root())
                .chain(construction.local_domain().known())
                .any(|fact| fact.snapshot == *snapshot && fact.subject == *subject)
                || construction.local_domain().conditional().iter().any(|member| {
                    member.subject().snapshot == *snapshot && member.subject().subject == *subject
                        && completions.iter().any(|(fact, value)| fact == member.owner_slot()
                            && matches!(value, Scalar::Subject { snapshot, subject, .. }
                                if *snapshot == member.owner().snapshot && *subject == member.owner().subject))
                })
        });
        let mut rows = vec![vec![]];
        for parameter in params {
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
            let argument = request
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", parameter.name));
            let values = if let Some(argument) = argument {
                let selected = selector(original, graph, &argument.value)?;
                result
                    .bindings
                    .push((parameter.name.clone(), selected.clone()));
                vec![selected]
            } else {
                if matches!(parameter.ty, Type::Z | Type::Q) {
                    continue;
                }
                let Some(values) = domain(
                    &environment,
                    &parameter.ty,
                    parameter.span,
                    &mut result.missing,
                )?
                else {
                    return Ok(());
                };
                values
            };
            let mut next = vec![];
            for row in rows {
                for value in &values {
                    control.checkpoint(Checkpoint::PrimitiveValuation)?;
                    let mut row = row.clone();
                    row.push((parameter.name.clone(), value.clone()));
                    next.push(row);
                }
            }
            rows = next;
        }
        result.requirements = rows.into_iter().map(|b| (law_name.to_owned(), b)).collect();
        if change_params.iter().skip(1).any(|p| p.ty==Type::Z) {
            let mut pending = change_affine::Pending::default();
            let computed = change_affine::compute(&environment,change,&subjects,&result.requirements,&mut pending);
            if !pending.facts.is_empty() || pending.unsupported.is_some() {
                result.missing.extend(pending.facts.iter().cloned());
                result.pending_integer = Some(pending);
            }
            let linear = computed?;
            let mut points=vec![];
            if let Some(particular)=&linear.particular {
                points.push(particular.clone());
                if linear.fiber.rank < linear.fiber.right.len() {
                    points.push(particular.iter().zip(&linear.kernel).map(|(p,k)|p+&k[0]).collect());
                }
            }
            let mut candidates=Candidates { parameter_types: vec![Type::Z;subjects.len()*(change_params.len()-1)],subjects,rows:vec![],complete:true };
            for (i,point) in points.into_iter().enumerate() {
                control.checkpoint(Checkpoint::PrimitiveValuation)?;
                let parameters=point.into_iter().map(Scalar::Z).collect::<Vec<_>>();
                let candidate=change_evaluation::candidate(&environment,change,&candidates.subjects,&parameters)?;
                // この段階は線形系の全解表示を準備する。具体点の通常Law再検査と
                // その確定直後の公開はchange_resultが順に行う。
                candidates.rows.push(candidate);result.solutions.push(SolutionRow{candidate:i,member:Some(true),missing:vec![]});
            }
            result.candidates=Some(candidates);result.linear=Some(linear);result.complete=true;
            return Ok(());
        }
        if change_params.iter().skip(1).any(|p|p.ty==Type::Q) {
            let mut pending=change_affine::Pending::default();
            let computed=field_change::compute(&environment,change,&subjects,&result.requirements,&mut pending);
            if !pending.facts.is_empty() || pending.unsupported.is_some() {
                result.missing.extend(pending.facts.iter().cloned());
                result.pending_integer=Some(pending);
            }
            let linear=computed?;
            let mut points=vec![];
            if let Some(particular)=&linear.particular {
                points.push(particular.clone());
                if linear.fiber.pivots.len()<linear.parameter_count {
                    points.push(particular.iter().zip(&linear.kernel).map(|(p,k)|
                        crate::observed::numeric::binary(BinOp::Add,p,&k[0],control)
                    ).collect::<Result<Vec<_>,_>>()?);
                }
            }
            let mut candidates=Candidates{parameter_types:vec![Type::Q;subjects.len()*(change_params.len()-1)],subjects,rows:vec![],complete:true};
            for (i,parameters) in points.into_iter().enumerate() {
                control.checkpoint(Checkpoint::PrimitiveValuation)?;
                candidates.rows.push(change_evaluation::candidate(&environment,change,&candidates.subjects,&parameters)?);
                result.solutions.push(SolutionRow{candidate:i,member:Some(true),missing:vec![]});
            }
            result.candidates=Some(candidates);result.rational=Some(linear);result.complete=true;
            return Ok(());
        }
        let table = match change_evaluation::candidates(&environment, change, &subjects) {
            Ok(table) => table,
            Err(failure) => {
                result.candidates = Some(failure.partial);
                return Err(failure.cause);
            }
        };
        result.candidates = Some(table);
        for (point, candidate) in result
            .candidates
            .as_ref()
            .ok_or("候補表がない")?
            .rows
            .iter()
            .enumerate()
        {
            control.checkpoint(Checkpoint::PrimitiveValuation)?;
            let row = change_evaluation::solution_row(
                &environment, candidate, point, &result.requirements,
            )?;
            result.missing.extend(row.missing.iter().cloned());
            result.solutions.push(row);
        }
        result.complete = true;
        Ok(())
    })();
    result.missing.sort();
    result.missing.dedup();
    match computed {
        Ok(()) => Ok(result),
        Err(cause) => Err(SearchFailure {
            cause,
            partial: Box::new(result),
        }),
    }
}

pub(in crate::observed) fn verify_point(
    original: &Environment<'_>,
    witness: &Arc<ArchitectureWitness>,
    search: &Search,
    point: usize,
    control: &mut Control,
) -> Result<(), ValidationFailure> {
    control.checkpoint(Checkpoint::ChangeWitness)?;
    let mut environment =
        Environment::try_primitive_valuation(original.inputs, &search.valuation, control)?
            .ok_or("元修復Architectureの代入が不適合")?;
    environment.object = Some(Arc::new(ObjectDomain::from_readings(
        original.inputs,
        witness.readings(),
        0,
        control,
    )?));
    let candidates = search.candidates.as_ref().ok_or("再代入の候補表がない")?;
    let candidate = candidates.rows.get(point).ok_or("再代入の候補点がない")?;
    let origin = crate::observed::construction_result::Witness::Architecture(Arc::clone(witness));
    let change = origin
        .request()
        .arguments
        .iter()
        .find_map(|a| match (&*a.name, &a.value) {
            ("using", Selector::Declaration { name }) => Some(name),
            _ => None,
        })
        .ok_or("再代入の元changeがない")?;
    let rebuilt = change_evaluation::candidate(
        &environment,
        &original.inputs.law().declarations[change],
        &candidates.subjects,
        &candidate.parameters,
    )?;
    if rebuilt != *candidate {
        return Err("再代入のguard・同時更新が元候補と違う".into());
    }
    let row =
        change_evaluation::solution_row(&environment, candidate, point, &search.requirements)?;
    if row.member != Some(true) {
        return Err("整数全解の点が元change/Lawへの再代入を満たさない".into());
    }
    Ok(())
}
