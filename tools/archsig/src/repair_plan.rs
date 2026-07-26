use std::collections::{BTreeMap, BTreeSet};

use serde_json::Value;

use crate::schema::RepairPlanComplexV1;
use crate::validation::{generic_validation_example, validation_check};
use crate::{
    ARCHSIG_REPAIR_PLAN_V1_SCHEMA, ArchMapDocumentV2, RepairPlanDocumentV1, ValidationCheck,
};


pub fn validate_repair_plan_v1_checks(
    plan: &RepairPlanDocumentV1,
    archmap: &ArchMapDocumentV2,
) -> Vec<ValidationCheck> {
    vec![
        check_schema(plan),
        check_conclusion_tokens(plan),
        check_references(plan),
        check_archmap_bindings(plan, archmap),
        check_enumeration_assumption(plan),
    ]
}

pub fn build_repair_plan_validation_report_v1(
    plan: &RepairPlanDocumentV1,
    archmap: &ArchMapDocumentV2,
    input_path: &str,
) -> Value {
    let checks = validate_repair_plan_v1_checks(plan, archmap);
    let failed_check_count = checks.iter().filter(|check| check.result == "fail").count();
    let warning_check_count = checks.iter().filter(|check| check.result == "warn").count();
    serde_json::json!({
        "schema": "archsig-repair-plan-validation-report/v0.5.4",
        "input": {
            "schema": plan.schema,
            "path": input_path,
            "id": plan.id,
            "archmapRef": archmap.id
        },
        "checks": checks,
        "assumptionLedger": [{
            "theoremRef": "part10/3.1",
            "assumption": "external semantic completeness beyond the declared ArchMap cover/incidence",
            "status": "assumed",
            "assumedBy": "repair-plan author",
            "source": "complex.enumerationComplete"
        }],
        "summary": {
            "result": if failed_check_count > 0 { "fail" } else if warning_check_count > 0 { "warn" } else { "pass" },
            "failedCheckCount": failed_check_count,
            "warningCheckCount": warning_check_count
        }
    })
}

pub(crate) fn complex_has_valid_finite_incidence(complex: &RepairPlanComplexV1) -> bool {
    let charts = complex.charts.iter().cloned().collect::<BTreeSet<_>>();
    let overlap_ids = complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.clone())
        .collect::<BTreeSet<_>>();
    let triple_ids = complex
        .triple_overlaps
        .iter()
        .map(|triple| triple.id.clone())
        .collect::<BTreeSet<_>>();
    charts.len() == complex.charts.len()
        && overlap_ids.len() == complex.overlaps.len()
        && triple_ids.len() == complex.triple_overlaps.len()
        && complex
            .overlaps
            .iter()
            .all(|overlap| charts.contains(&overlap.left) && charts.contains(&overlap.right))
        && complex.triple_overlaps.iter().all(|triple| {
            if triple.overlap_refs.len() != 3
                || triple.overlap_refs.iter().collect::<BTreeSet<_>>().len() != 3
                || triple
                    .overlap_refs
                    .iter()
                    .any(|overlap_ref| !overlap_ids.contains(overlap_ref))
            {
                return false;
            }
            let triple_overlaps = triple
                .overlap_refs
                .iter()
                .filter_map(|overlap_ref| {
                    complex
                        .overlaps
                        .iter()
                        .find(|overlap| &overlap.id == overlap_ref)
                })
                .collect::<Vec<_>>();
            let vertices = triple_overlaps
                .iter()
                .flat_map(|overlap| [&overlap.left, &overlap.right])
                .cloned()
                .collect::<BTreeSet<_>>();
            if vertices.len() != 3 {
                return false;
            }
            let edge_pairs = triple_overlaps
                .iter()
                .filter_map(|overlap| {
                    if overlap.left == overlap.right {
                        None
                    } else if overlap.left < overlap.right {
                        Some((overlap.left.clone(), overlap.right.clone()))
                    } else {
                        Some((overlap.right.clone(), overlap.left.clone()))
                    }
                })
                .collect::<BTreeSet<_>>();
            let vertices = vertices.into_iter().collect::<Vec<_>>();
            let expected_pairs = [(0, 1), (0, 2), (1, 2)]
                .into_iter()
                .map(|(left, right)| (vertices[left].clone(), vertices[right].clone()))
                .collect::<BTreeSet<_>>();
            edge_pairs == expected_pairs
        })
}

#[cfg(test)]
mod tests {
    use super::*;


    use crate::schema::{RepairPlanOverlapV1, RepairPlanTripleOverlapV1};

    fn complex_with_edges(edges: [(&str, &str, &str); 3]) -> RepairPlanComplexV1 {
        RepairPlanComplexV1 {
            charts: vec!["A".to_string(), "B".to_string(), "C".to_string()],
            overlaps: edges
                .into_iter()
                .map(|(id, left, right)| RepairPlanOverlapV1 {
                    id: id.to_string(),
                    left: left.to_string(),
                    right: right.to_string(),
                    archmap_context_ref: None,
                })
                .collect(),
            triple_overlaps: vec![RepairPlanTripleOverlapV1 {
                id: "t".to_string(),
                overlap_refs: vec!["e1".to_string(), "e2".to_string(), "e3".to_string()],
                archmap_context_ref: None,
            }],
            archmap_cover_ref: None,
            enumeration_complete: true,
        }
    }

    #[test]
    fn finite_incidence_requires_all_three_triangle_edges() {
        let triangle = complex_with_edges([("e1", "A", "B"), ("e2", "B", "C"), ("e3", "A", "C")]);
        assert!(complex_has_valid_finite_incidence(&triangle));

        let repeated_edge =
            complex_with_edges([("e1", "A", "B"), ("e2", "B", "C"), ("e3", "A", "B")]);
        assert!(!complex_has_valid_finite_incidence(&repeated_edge));
    }

    #[test]
    fn references_require_unique_triple_ids_across_components() {
        let mut plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_component_aware_one_cent.json"
        ))
        .expect("component-aware fixture parses");
        plan.complex.triple_overlaps.push(RepairPlanTripleOverlapV1 {
            id: "triple:consign-parcel-shipping".to_string(),
            overlap_refs: vec![
                "overlap:cancel-inside-payment".to_string(),
                "overlap:inside-payment-order".to_string(),
                "overlap:cancel-order".to_string(),
            ],
            archmap_context_ref: None,
        });

        assert_eq!(check_references(&plan).result, "fail");
    }

}

fn check_schema(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let mut check = validation_check(
        "repair-plan-schema052-schema",
        "RepairPlan uses the v0.5.4 schema discriminator",
        if plan.schema == ARCHSIG_REPAIR_PLAN_V1_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "expected {ARCHSIG_REPAIR_PLAN_V1_SCHEMA}, found {}",
            plan.schema
        ));
    }
    check
}

fn check_conclusion_tokens(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let value = serde_json::to_value(plan).unwrap_or(Value::Null);
    let mut hits = Vec::new();
    collect_conclusion_tokens(&value, "$", &mut hits);
    examples_check(
        "repair-plan-schema052-no-conclusion-tokens",
        "RepairPlan input does not supply theorem conclusion tokens",
        hits.into_iter()
            .map(|path| {
                generic_validation_example(
                    &path,
                    "generated-conclusion-token",
                    "h1Zero/globalCoherent/glues/verdict are generated by evaluators, not supplied",
                )
            })
            .collect(),
    )
}

fn check_references(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let charts = plan.complex.charts.iter().collect::<BTreeSet<_>>();
    let overlaps = plan
        .complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    let mut triple_ids = BTreeSet::new();
    let mut chart_ids = BTreeSet::new();
    for chart in &plan.complex.charts {
        if !chart_ids.insert(chart.as_str()) {
            examples.push(generic_validation_example(
                &format!("complex.charts[{chart}]"),
                chart,
                "chart IDs must be unique across the RepairPlan complex",
            ));
        }
    }
    let mut overlap_ids = BTreeSet::new();
    let mut overlap_pairs = BTreeSet::new();
    for overlap in &plan.complex.overlaps {
        if !overlap_ids.insert(overlap.id.as_str()) {
            examples.push(generic_validation_example(
                &format!("complex.overlaps[{}].id", overlap.id),
                &overlap.id,
                "overlap IDs must be unique across the RepairPlan complex",
            ));
        }
        let mut pair = [overlap.left.as_str(), overlap.right.as_str()];
        pair.sort_unstable();
        if !overlap_pairs.insert((pair[0].to_string(), pair[1].to_string())) {
            examples.push(generic_validation_example(
                &format!("complex.overlaps[{}]", overlap.id),
                &format!("{} / {}", pair[0], pair[1]),
                "each unordered chart pair must appear at most once in complex.overlaps",
            ));
        }
        for (field, chart) in [("left", &overlap.left), ("right", &overlap.right)] {
            if !charts.contains(chart) {
                examples.push(generic_validation_example(
                    &format!("complex.overlaps[{}].{field}", overlap.id),
                    chart,
                    "overlap endpoints must reference complex.charts",
                ));
            }
        }
    }
    for triple in &plan.complex.triple_overlaps {
        if !triple_ids.insert(triple.id.as_str()) {
            examples.push(generic_validation_example(
                &format!("complex.tripleOverlaps[{}].id", triple.id),
                &triple.id,
                "triple overlap IDs must be unique across the RepairPlan complex",
            ));
        }
        for overlap_ref in &triple.overlap_refs {
            if !overlaps.contains(overlap_ref.as_str()) {
                examples.push(generic_validation_example(
                    &format!("complex.tripleOverlaps[{}].overlapRefs", triple.id),
                    overlap_ref,
                    "triple overlap refs must resolve to complex.overlaps",
                ));
            }
        }
    }
    examples_check(
        "repair-plan-schema052-reference-resolution",
        "RepairPlan chart, overlap, and triple references resolve",
        examples,
    )
}

fn check_archmap_bindings(
    plan: &RepairPlanDocumentV1,
    archmap: &ArchMapDocumentV2,
) -> ValidationCheck {
    let context_ids = archmap
        .contexts
        .iter()
        .map(|context| context.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();
    for chart in &plan.complex.charts {
        if !context_ids.contains(chart.as_str()) {
            examples.push(generic_validation_example(
                "complex.charts",
                chart,
                "RepairPlan chart refs must resolve to ArchMap contexts",
            ));
        }
    }
    let has_archmap_complex_mapping = plan.complex.archmap_cover_ref.is_some()
        || plan
            .complex
            .overlaps
            .iter()
            .any(|overlap| overlap.archmap_context_ref.is_some())
        || plan
            .complex
            .triple_overlaps
            .iter()
            .any(|triple| triple.archmap_context_ref.is_some());
    if has_archmap_complex_mapping {
        let contexts = archmap
            .contexts
            .iter()
            .map(|context| (context.id.as_str(), context))
            .collect::<BTreeMap<_, _>>();
        let direct_predecessors = archmap
            .contexts
            .iter()
            .flat_map(|context| {
                context
                    .restricts_to
                    .iter()
                    .map(move |target| (target.as_str(), context.id.as_str()))
            })
            .fold(BTreeMap::new(), |mut predecessors, (target, source)| {
                predecessors
                    .entry(target)
                    .or_insert_with(BTreeSet::new)
                    .insert(source);
                predecessors
            });
        let chart_ids = plan
            .complex
            .charts
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let mut mapped_contexts = BTreeSet::new();
        let mut overlap_contexts = BTreeMap::new();

        for overlap in &plan.complex.overlaps {
            let path = format!("complex.overlaps[{}].archmapContextRef", overlap.id);
            let Some(context_ref) = overlap.archmap_context_ref.as_deref() else {
                // 導出時代の overlap は観測された chart↔chart restriction 辺そのものであり、
                // intersection context を持たない。その辺の実在は下の
                // expected_direct_restrictions(cover 完全一致検査)が観測側で検査する。
                continue;
            };
            overlap_contexts.insert(overlap.id.as_str(), context_ref);
            if chart_ids.contains(context_ref) {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "an overlap archmapContextRef must be distinct from every chart context",
                ));
            }
            if !mapped_contexts.insert(context_ref) {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "each overlap or triple requires its own ArchMap intersection context",
                ));
            }
            let Some(intersection) = contexts.get(context_ref) else {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "overlap archmapContextRef must resolve to an ArchMap context",
                ));
                continue;
            };
            let expected_predecessors = [&overlap.left, &overlap.right]
                .into_iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>();
            let actual_predecessors = direct_predecessors
                .get(context_ref)
                .cloned()
                .unwrap_or_default();
            if actual_predecessors != expected_predecessors {
                examples.push(generic_validation_example(
                    &path,
                    &format!("actual={actual_predecessors:?}, expected={expected_predecessors:?}"),
                    "a mapped overlap must have exactly its two chart contexts as direct restriction predecessors",
                ));
            }
            if !intersection
                .refs
                .iter()
                .any(|reference| !reference.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "mapped overlap contexts must retain a source-grounded ArchMap reference",
                ));
            }
        }

        for triple in &plan.complex.triple_overlaps {
            let path = format!("complex.tripleOverlaps[{}].archmapContextRef", triple.id);
            let Some(context_ref) = triple.archmap_context_ref.as_deref() else {
                // 導出時代の triple 宣言は cocycle 検査の対象指定であり、intersection
                // context を持たなくてよい。mapping を宣言した triple だけ強い検査を受ける。
                continue;
            };
            if chart_ids.contains(context_ref) {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "a triple archmapContextRef must be distinct from every chart context",
                ));
            }
            if !mapped_contexts.insert(context_ref) {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "each overlap or triple requires its own ArchMap intersection context",
                ));
            }
            let Some(intersection) = contexts.get(context_ref) else {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "triple archmapContextRef must resolve to an ArchMap context",
                ));
                continue;
            };
            let mut expected_predecessors = BTreeSet::new();
            for overlap_ref in &triple.overlap_refs {
                let Some(source_ref) = overlap_contexts.get(overlap_ref.as_str()) else {
                    examples.push(generic_validation_example(
                        &path,
                        overlap_ref,
                        "triple overlap mapping requires every referenced overlap mapping",
                    ));
                    continue;
                };
                expected_predecessors.insert(*source_ref);
            }
            let actual_predecessors = direct_predecessors
                .get(context_ref)
                .cloned()
                .unwrap_or_default();
            if actual_predecessors != expected_predecessors {
                examples.push(generic_validation_example(
                    &path,
                    &format!("actual={actual_predecessors:?}, expected={expected_predecessors:?}"),
                    "a mapped triple overlap must have exactly its mapped overlap contexts as direct restriction predecessors",
                ));
            }
            if !intersection
                .refs
                .iter()
                .any(|reference| !reference.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    &path,
                    context_ref,
                    "mapped triple contexts must retain a source-grounded ArchMap reference",
                ));
            }
        }

        match plan.complex.archmap_cover_ref.as_deref() {
            Some(cover_ref) => match archmap.covers.iter().find(|cover| cover.id == cover_ref) {
                Some(cover) => {
                    let expected_contexts = chart_ids
                        .into_iter()
                        .chain(mapped_contexts.iter().copied())
                        .collect::<BTreeSet<_>>();
                    let actual_contexts = cover
                        .contexts
                        .iter()
                        .map(String::as_str)
                        .collect::<BTreeSet<_>>();
                    let expected_direct_restrictions = plan
                        .complex
                        .overlaps
                        .iter()
                        .filter_map(|overlap| {
                            overlap.archmap_context_ref.as_deref().map(|context_ref| {
                                [&overlap.left, &overlap.right]
                                    .into_iter()
                                    .map(move |chart| (chart.as_str(), context_ref))
                            })
                        })
                        .flatten()
                        .chain(plan.complex.triple_overlaps.iter().flat_map(|triple| {
                            let Some(context_ref) = triple.archmap_context_ref.as_deref() else {
                                return Vec::new().into_iter();
                            };
                            triple
                                .overlap_refs
                                .iter()
                                .filter_map(|overlap_ref| {
                                    overlap_contexts
                                        .get(overlap_ref.as_str())
                                        .map(|source_ref| (*source_ref, context_ref))
                                })
                                .collect::<Vec<_>>()
                                .into_iter()
                        }))
                        .collect::<BTreeSet<_>>();
                    // chart どうしの restriction(観測 1-skeleton、residual 導出の入力面)も
                    // expected 側に含める: plan.complex.overlaps の各対を観測の向きへ正規化する。
                    let expected_direct_restrictions = expected_direct_restrictions
                        .into_iter()
                        .chain(plan.complex.overlaps.iter().map(|overlap| {
                            let forward = archmap.contexts.iter().any(|context| {
                                context.id == overlap.left
                                    && context.restricts_to.contains(&overlap.right)
                            });
                            if forward {
                                (overlap.left.as_str(), overlap.right.as_str())
                            } else {
                                (overlap.right.as_str(), overlap.left.as_str())
                            }
                        }))
                        .collect::<BTreeSet<_>>();
                    let actual_direct_restrictions = archmap
                        .contexts
                        .iter()
                        .filter(|context| actual_contexts.contains(context.id.as_str()))
                        .flat_map(|context| {
                            context
                                .restricts_to
                                .iter()
                                .filter(|target| actual_contexts.contains(target.as_str()))
                                .map(move |target| (context.id.as_str(), target.as_str()))
                        })
                        .collect::<BTreeSet<_>>();
                    let membership_valid = if plan.complex.enumeration_complete {
                        actual_contexts == expected_contexts
                            && actual_direct_restrictions == expected_direct_restrictions
                    } else {
                        expected_contexts.is_subset(&actual_contexts)
                    };
                    if !membership_valid {
                        examples.push(generic_validation_example(
                            "complex.archmapCoverRef",
                            &format!(
                                "cover={actual_contexts:?}, complex={expected_contexts:?}, restrictions={actual_direct_restrictions:?}, expectedRestrictions={expected_direct_restrictions:?}"
                            ),
                            "the mapped ArchMap cover must contain exactly the enumerated contexts and direct restrictions when enumerationComplete is true",
                        ));
                    }
                }
                None => examples.push(generic_validation_example(
                    "complex.archmapCoverRef",
                    cover_ref,
                    "archmapCoverRef must resolve to an ArchMap cover",
                )),
            },
            None => examples.push(generic_validation_example(
                "complex.archmapCoverRef",
                "missing",
                "overlap or triple ArchMap mappings require complex.archmapCoverRef",
            )),
        }
    }
    examples_check(
        "repair-plan-schema052-archmap-bindings",
        "RepairPlan charts and declared finite-complex mappings resolve against the supplied ArchMap",
        examples,
    )
}

fn check_enumeration_assumption(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let mut check = validation_check(
        "repair-plan-schema052-enumeration-assumption",
        "External semantic completeness remains an author assumption; declared ArchMap cover/incidence is checked separately",
        "warn",
    );
    check.reason = Some(format!(
        "complex.enumerationComplete={} records the author assumption about external semantic completeness; when complex.archmapCoverRef is mapped, cover membership and direct restrictions (chart-chart observation edges included) are checked by repair-plan-schema052-archmap-bindings",
        plan.complex.enumeration_complete
    ));
    check
}

fn collect_conclusion_tokens(value: &Value, path: &str, hits: &mut Vec<String>) {
    const TOKENS: &[&str] = &["h1Zero", "globalCoherent", "glues", "verdict"];
    match value {
        Value::Object(object) => {
            for (key, child) in object {
                let child_path = format!("{path}.{key}");
                if TOKENS.contains(&key.as_str()) {
                    hits.push(child_path.clone());
                }
                collect_conclusion_tokens(child, &child_path, hits);
            }
        }
        Value::Array(items) => {
            for (index, child) in items.iter().enumerate() {
                collect_conclusion_tokens(child, &format!("{path}[{index}]"), hits);
            }
        }
        Value::String(text) if TOKENS.contains(&text.as_str()) => hits.push(path.to_string()),
        _ => {}
    }
}



fn examples_check(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    check.count = Some(examples.len());
    check.examples = examples;
    check
}
