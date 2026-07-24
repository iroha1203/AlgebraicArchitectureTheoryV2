use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::schema::{
    H1ComparisonDataV052, H1PresentationCellV052, H1PresentationDataV052,
    H1PresentationRestrictionV052, RepairPlanComplexV1,
};
use crate::validation::{generic_validation_example, validation_check};
use crate::{
    ARCHSIG_REPAIR_PLAN_V1_SCHEMA, ArchMapDocumentV2, RepairPlanDocumentV1, ValidationCheck,
};

const COMPARISON_SOURCE_COMPLEX_REF: &str = "complex:repair";
const COMPARISON_TARGET_COMPLEX_REF: &str = "complex:cech";
const COMPARISON_COCHAIN_MAP_REF: &str = "comparison:cochain-map";

#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct ExplicitH1ComparisonChecks {
    pub degree_one_left_inverse: bool,
    pub degree_one_right_inverse: bool,
    pub difference_preserving: bool,
    pub degree_two_zero_preserving: bool,
    pub differential_commutative: bool,
    map_complete: bool,
}

impl ExplicitH1ComparisonChecks {
    pub(crate) fn all_pass(self) -> bool {
        self.map_complete
            && self.degree_one_left_inverse
            && self.degree_one_right_inverse
            && self.difference_preserving
            && self.degree_two_zero_preserving
            && self.differential_commutative
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct PresentationGeneratedH1Checks {
    pub presentation_exactness: bool,
    pub generator_completeness: bool,
    pub restriction_naturality: bool,
    pub degree_zero_commutative: bool,
    pub degree_one_commutative: bool,
    pub source_cocycle: bool,
    pub source_class_nonzero: Option<bool>,
    pub target_cocycle: bool,
    pub equation_lift_atlas_present: bool,
    pub residual_witness_computed: bool,
    pub target_class_nonzero: Option<bool>,
    residual_witness: Option<PresentationResidualWitness>,
    map_complete: bool,
}

impl PresentationGeneratedH1Checks {
    pub(crate) fn all_pass(&self) -> bool {
        self.map_complete
            && self.presentation_exactness
            && self.generator_completeness
            && self.restriction_naturality
            && self.degree_zero_commutative
            && self.degree_one_commutative
            && self.source_cocycle
            && self.target_cocycle
            && self.equation_lift_atlas_present
            && self.residual_witness_computed
    }
}

#[derive(Debug, Clone)]
struct PresentationResidualWitness {
    source_image: BTreeMap<String, Vec<u8>>,
    equation_residual: BTreeMap<String, Vec<u8>>,
    h: BTreeMap<String, Vec<u8>>,
}

#[derive(Debug, Clone)]
struct PresentationResidualAnalysis {
    source_cocycle: bool,
    source_class_nonzero: Option<bool>,
    target_cocycle: bool,
    target_class_nonzero: Option<bool>,
    witness: Option<PresentationResidualWitness>,
}

#[derive(Debug, Clone)]
struct ComparisonBasisMap {
    target_ref: String,
    variables: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
struct ExplicitCochainMap {
    degree_zero: BTreeMap<String, ComparisonBasisMap>,
    degree_one: BTreeMap<String, ComparisonBasisMap>,
    degree_two: BTreeMap<String, String>,
    degree_two_zero_image: BTreeSet<String>,
}

pub fn validate_repair_plan_v1_checks(
    plan: &RepairPlanDocumentV1,
    archmap: &ArchMapDocumentV2,
    residual_packet: Option<&Value>,
) -> Vec<ValidationCheck> {
    vec![
        check_schema(plan),
        check_supplied_slots(plan, archmap),
        check_conclusion_tokens(plan),
        check_references(plan),
        check_archmap_bindings(plan, archmap),
        check_measured_residual(plan, residual_packet),
        check_stage1_mode_and_coefficient(plan),
        check_overlap_primitive_bijection(plan),
        check_restriction_difference_rule(plan),
        check_delta_cocycle(plan),
        check_complete_support(plan),
        check_enumeration_assumption(plan),
    ]
}

pub fn build_repair_plan_validation_report_v1(
    plan: &RepairPlanDocumentV1,
    archmap: &ArchMapDocumentV2,
    input_path: &str,
    residual_packet: Option<&Value>,
) -> Value {
    let checks = validate_repair_plan_v1_checks(plan, archmap, residual_packet);
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
            "assumption": "repair-plan complex enumeration completeness",
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

pub(crate) fn comparison_complex_fingerprint(plan: &RepairPlanDocumentV1) -> String {
    complex_fingerprint(&plan.complex)
}

pub(crate) fn complex_fingerprint(complex: &RepairPlanComplexV1) -> String {
    let bytes = serde_json::to_vec(complex).unwrap_or_default();
    format!("{:x}", Sha256::digest(bytes))
}

pub(crate) fn comparison_target_complex(
    plan: &RepairPlanDocumentV1,
    comparison: &Value,
) -> Option<RepairPlanComplexV1> {
    let bridge = comparison.get("incidenceBridge")?.as_object()?;
    comparison_target_complex_from_bridge(plan, bridge)
}

fn comparison_target_complex_from_bridge(
    plan: &RepairPlanDocumentV1,
    bridge: &serde_json::Map<String, Value>,
) -> Option<RepairPlanComplexV1> {
    let target = match bridge.get("kind").and_then(Value::as_str) {
        Some("chart-indexed") => plan.complex.clone(),
        Some("explicit") => {
            let value = bridge.get("targetComplex")?.clone();
            match serde_json::from_value(value) {
                Ok(complex) => complex,
                Err(_) => return None,
            }
        }
        _ => return None,
    };
    let source_overlap_ids = plan
        .complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.as_str())
        .collect::<BTreeSet<_>>();
    let target_overlap_ids = target
        .overlaps
        .iter()
        .map(|overlap| overlap.id.as_str())
        .collect::<BTreeSet<_>>();
    let valid = plan.complex.enumeration_complete
        && target.enumeration_complete
        && complex_has_valid_finite_incidence(&plan.complex)
        && complex_has_valid_finite_incidence(&target)
        && source_overlap_ids == target_overlap_ids;
    valid.then_some(target)
}

fn complex_has_valid_finite_incidence(complex: &RepairPlanComplexV1) -> bool {
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
    fn comparison_bridge_rejects_non_triangle_target_before_map_checks() {
        let plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_comparison.json"
        ))
        .expect("comparison fixture parses");
        let comparison = plan.comparison.as_ref().expect("comparison is supplied");
        let mut bridge = comparison["incidenceBridge"]
            .as_object()
            .expect("incidence bridge is an object")
            .clone();
        bridge["targetComplex"]["overlaps"][2]["right"] = Value::String("ctx:inventory".into());
        assert!(comparison_target_complex_from_bridge(&plan, &bridge).is_none());
    }

    #[test]
    fn presentation_generated_circle_derives_exact_local_maps_and_independent_atlas_witness() {
        let plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_presentation_generated_circle.json"
        ))
        .expect("presentation-generated circle fixture parses");
        let comparison = plan.comparison.as_ref().expect("comparison is supplied");
        let h1 = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object");
        assert_eq!(
            h1["sourceComplexFingerprint"],
            comparison_complex_fingerprint(&plan)
        );
        let checks = presentation_generated_h1_checks(&plan, &plan.complex, h1);
        assert!(checks.all_pass());
        assert_eq!(checks.source_class_nonzero, Some(true));
        assert_eq!(checks.target_class_nonzero, Some(true));
        let output = presentation_generated_h1_output(&plan, &plan.complex, h1, &checks);
        assert_eq!(output["kind"], "presentation-generated");
        assert_eq!(output["presentationExactness"], true);
        assert_eq!(
            output["residualWitness"]["equation"],
            "kappa1(r_sem) = r_E + delta0(h)"
        );
        assert_eq!(
            output["residualWitness"]["h"].as_array().map(Vec::len),
            Some(4)
        );
        assert!(
            output["residualWitness"]["h"]
                .as_array()
                .expect("computed chart witness")
                .iter()
                .flat_map(|row| row["coefficients"].as_array().into_iter().flatten())
                .all(|entry| entry.as_u64() == Some(0))
        );
        assert_eq!(
            output["residualWitness"]["sourceImage"],
            output["residualWitness"]["equationResidual"],
            "Example 10.2 has r_E = kappa^1(r_sem) with zero local coordinate witness"
        );
    }

    #[test]
    fn presentation_generated_circle_archmap_mapping_is_exact_and_rejects_missing_overlap_edge() {
        let plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_presentation_generated_circle.json"
        ))
        .expect("presentation-generated circle fixture parses");
        let archmap: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2_presentation_generated_circle.json"
        ))
        .expect("presentation-generated circle ArchMap parses");
        let binding = validate_repair_plan_v1_checks(&plan, &archmap, None)
            .into_iter()
            .find(|check| check.id == "repair-plan-schema052-archmap-bindings")
            .expect("ArchMap binding validation exists");
        assert_eq!(binding.result, "pass");

        assert_eq!(plan.complex.charts.len(), 4);
        assert_eq!(plan.complex.overlaps.len(), 4);
        assert!(plan.complex.triple_overlaps.is_empty());
        assert_eq!(
            plan.complex.archmap_cover_ref.as_deref(),
            Some("cover:order-inventory")
        );

        let mut missing_overlap_edge = archmap.clone();
        missing_overlap_edge
            .contexts
            .iter_mut()
            .find(|context| context.id == "ctx:order")
            .expect("ctx:order exists")
            .restricts_to
            .retain(|target| target != "ctx:overlap-30");
        let binding = validate_repair_plan_v1_checks(&plan, &missing_overlap_edge, None)
            .into_iter()
            .find(|check| check.id == "repair-plan-schema052-archmap-bindings")
            .expect("ArchMap binding validation exists");
        assert_eq!(binding.result, "fail");
        assert!(binding.examples.iter().any(|example| {
            example.source.as_deref() == Some("complex.overlaps[overlap:30].archmapContextRef")
                && example.target.as_deref() == Some("ctx:order->ctx:overlap-30")
        }));
    }

    #[test]
    fn presentation_generated_circle_derives_nonzero_cohomologous_atlas_witness() {
        let mut plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_presentation_generated_circle.json"
        ))
        .expect("presentation-generated circle fixture parses");
        let transitions = plan.comparison.as_mut().expect("comparison is supplied")
            ["h1ComparisonData"]["presentation"]["equationLiftAtlas"]["transitionDifferences"]
            .as_array_mut()
            .expect("equation lift atlas transitions are an array");
        transitions
            .iter_mut()
            .find(|transition| transition["overlapRef"] == "overlap:01")
            .expect("overlap:01 transition")["coefficients"] = json!([0]);
        transitions
            .iter_mut()
            .find(|transition| transition["overlapRef"] == "overlap:30")
            .expect("overlap:30 transition")["coefficients"] = json!([1]);
        let comparison = plan.comparison.as_ref().expect("comparison is supplied");
        let h1 = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object");
        let checks = presentation_generated_h1_checks(&plan, &plan.complex, h1);
        assert!(checks.all_pass());
        let output = presentation_generated_h1_output(&plan, &plan.complex, h1, &checks);
        assert!(
            output["residualWitness"]["h"]
                .as_array()
                .expect("computed chart witness")
                .iter()
                .flat_map(|row| row["coefficients"].as_array().into_iter().flatten())
                .any(|entry| entry.as_u64() == Some(1)),
            "a distinct cohomologous atlas input must retain the nonzero local-coordinate witness path"
        );
    }

    #[test]
    fn presentation_generated_circle_rejects_kernel_mismatch_and_missing_generation() {
        let plan: RepairPlanDocumentV1 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/repair_plan_presentation_generated_circle.json"
        ))
        .expect("presentation-generated circle fixture parses");
        let comparison = plan.comparison.as_ref().expect("comparison is supplied");
        let mut kernel_mismatch = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object")
            .clone();
        kernel_mismatch["presentation"]["cells"]
            .as_array_mut()
            .expect("presentation cells are an array")[0]["repairRelationMatrix"] =
            serde_json::json!([[1]]);
        let kernel_checks =
            presentation_generated_h1_checks(&plan, &plan.complex, &kernel_mismatch);
        assert!(!kernel_checks.presentation_exactness);
        assert!(!kernel_checks.all_pass());

        let mut generation_missing = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object")
            .clone();
        let cell = &mut generation_missing["presentation"]["cells"]
            .as_array_mut()
            .expect("presentation cells are an array")[0];
        cell["equationGenerators"] = serde_json::json!(["q", "q2"]);
        cell["generatorMap"] = serde_json::json!([[1], [0]]);
        let generation_checks =
            presentation_generated_h1_checks(&plan, &plan.complex, &generation_missing);
        assert!(!generation_checks.generator_completeness);
        assert!(!generation_checks.all_pass());

        let mut residual_mismatch = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object")
            .clone();
        residual_mismatch["presentation"]["equationLiftAtlas"]["transitionDifferences"][0]["coefficients"] =
            serde_json::json!([0]);
        let residual_checks =
            presentation_generated_h1_checks(&plan, &plan.complex, &residual_mismatch);
        assert!(!residual_checks.residual_witness_computed);
        assert!(!residual_checks.all_pass());

        let mut relation_not_stable = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object")
            .clone();
        relation_not_stable["presentation"]["cells"]
            .as_array_mut()
            .expect("presentation cells are an array")[0]["repairRelationMatrix"] =
            serde_json::json!([[1]]);
        relation_not_stable["presentation"]["cells"]
            .as_array_mut()
            .expect("presentation cells are an array")[0]["equationRelationMatrix"] =
            serde_json::json!([[1]]);
        let relation_checks =
            presentation_generated_h1_checks(&plan, &plan.complex, &relation_not_stable);
        assert!(relation_checks.presentation_exactness);
        assert!(!relation_checks.restriction_naturality);
        assert!(!relation_checks.all_pass());

        let mut invalid_plan = plan.clone();
        invalid_plan
            .comparison
            .as_mut()
            .expect("comparison is supplied")["h1ComparisonData"] = Value::Object(kernel_mismatch);
        let archmap: ArchMapDocumentV2 = serde_json::from_str(include_str!(
            "../tests/fixtures/ag_measurement/archmap_v2.json"
        ))
        .expect("ArchMap fixture parses");
        let validation = validate_repair_plan_v1_checks(&invalid_plan, &archmap, None);
        let supplied_slots = validation
            .iter()
            .find(|check| check.id == "repair-plan-schema052-supplied-slots")
            .expect("supplied slot validation exists");
        assert_eq!(supplied_slots.result, "fail");
        assert!(supplied_slots.examples.iter().any(|example| {
            example
                .evidence
                .as_deref()
                .is_some_and(|target| target.contains("presentationExactness=false"))
        }));

        let mut missing_atlas = comparison["h1ComparisonData"]
            .as_object()
            .expect("H1 comparison data is an object")
            .clone();
        missing_atlas["presentation"]
            .as_object_mut()
            .expect("presentation is an object")
            .remove("equationLiftAtlas");
        let missing_checks = presentation_generated_h1_checks(&plan, &plan.complex, &missing_atlas);
        assert!(!missing_checks.equation_lift_atlas_present);
        assert!(!missing_checks.all_pass());

        let mut missing_atlas_plan = plan.clone();
        missing_atlas_plan
            .comparison
            .as_mut()
            .expect("comparison is supplied")["h1ComparisonData"] = Value::Object(missing_atlas);
        let missing_validation =
            validate_repair_plan_v1_checks(&missing_atlas_plan, &archmap, None);
        let missing_slots = missing_validation
            .iter()
            .find(|check| check.id == "repair-plan-schema052-supplied-slots")
            .expect("supplied slot validation exists");
        assert!(missing_slots.examples.iter().any(|example| {
            example
                .evidence
                .as_deref()
                .is_some_and(|target| target.contains("equationLiftAtlasPresent=false"))
        }));
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

fn check_supplied_slots(
    plan: &RepairPlanDocumentV1,
    archmap: &ArchMapDocumentV2,
) -> ValidationCheck {
    let mut examples = Vec::new();
    if plan.faithfulness.mode == "supplied" {
        match &plan.faithfulness.supplied {
            Some(supplied)
                if !supplied.zero_primitive_ref.is_empty()
                    && supplied.residual_support_predicate.kind == "finite-support"
                    && supplied.residual_support_predicate.zero_on_zero_primitive
                    && supplied.residual_support_predicate
                        .support_variables
                        .iter()
                        .all(|variable| !variable.is_empty())
                    && !supplied.faithfulness_law.is_empty() => {}
            Some(_) => examples.push(generic_validation_example(
                "faithfulness.supplied",
                "incomplete",
                "supplied faithfulness requires zeroPrimitiveRef, residualSupportPredicate, and faithfulnessLaw",
            )),
            None => examples.push(generic_validation_example(
                "faithfulness.supplied",
                "missing",
                "faithfulness.mode=supplied requires the three definition 4.6 data points",
            )),
        }
        if let Some(supplied) = &plan.faithfulness.supplied {
            let primitive = plan
                .primitives
                .iter()
                .find(|primitive| primitive.id == supplied.zero_primitive_ref);
            if primitive.is_none()
                || primitive.is_some_and(|primitive| !primitive.support.variables.is_empty())
            {
                examples.push(generic_validation_example(
                    "faithfulness.supplied.zeroPrimitiveRef",
                    &supplied.zero_primitive_ref,
                    "zeroPrimitiveRef must resolve to a primitive with empty support",
                ));
            }
            let actual_support = plan
                .primitives
                .iter()
                .flat_map(|primitive| primitive.support.variables.iter().cloned())
                .collect::<BTreeSet<_>>();
            let declared_support = supplied
                .residual_support_predicate
                .support_variables
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            if declared_support != actual_support {
                examples.push(generic_validation_example(
                    "faithfulness.supplied.residualSupportPredicate.supportVariables",
                    &format!("declared={declared_support:?}, actual={actual_support:?}"),
                    "Q(r) must match the finite residual support generated by the supplied primitives",
                ));
            }
        }
    } else if plan.faithfulness.supplied.is_some() {
        examples.push(generic_validation_example(
            "faithfulness.supplied",
            "present-without-supplied-mode",
            "supplied faithfulness data is only active when faithfulness.mode is supplied",
        ));
    }
    for (path, value) in [
        ("trueSheafCertificate", plan.true_sheaf_certificate.as_ref()),
        ("gluingData", plan.gluing_data.as_ref()),
        ("comparison", plan.comparison.as_ref()),
        ("grounding", plan.grounding.as_ref()),
    ] {
        if value.is_some_and(Value::is_null) {
            examples.push(generic_validation_example(
                path,
                "null",
                "optional supplied artifact must be an object when present",
            ));
        } else if let Some(value) = value {
            let Some(object) = value.as_object() else {
                examples.push(generic_validation_example(
                    path,
                    "not-object",
                    "optional supplied artifact must be an object when present",
                ));
                continue;
            };
            let kind = object
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or_default();
            match path {
                "trueSheafCertificate" if kind == "true-sheaf-certificate" => {
                    for key in object.keys() {
                        if !matches!(
                            key.as_str(),
                            "kind" | "coverRef" | "memberCharts" | "globalCondition"
                        ) {
                            examples.push(generic_validation_example(
                                &format!("{path}.{key}"),
                                "unknown-field",
                                "true-sheaf certificate has no unregistered supplied fields",
                            ));
                        }
                    }
                    let cover_ref = object
                        .get("coverRef")
                        .and_then(Value::as_str)
                        .unwrap_or_default();
                    let members = object.get("memberCharts").and_then(Value::as_array);
                    let global_condition = object
                        .get("globalCondition")
                        .and_then(Value::as_str)
                        .unwrap_or_default();
                    let expected_members = archmap
                        .covers
                        .iter()
                        .find(|cover| cover.id == cover_ref)
                        .map(|cover| {
                            cover
                                .contexts
                                .iter()
                                .map(String::as_str)
                                .collect::<BTreeSet<_>>()
                        })
                        .unwrap_or_default();
                    let members_valid = members.is_some_and(|items| {
                        let parsed = items.iter().map(Value::as_str).collect::<Option<Vec<_>>>();
                        parsed.as_ref().is_some_and(|members| {
                            !members.is_empty()
                                && members.len() == expected_members.len()
                                && members.iter().copied().collect::<BTreeSet<_>>()
                                    == expected_members
                        })
                    });
                    if !archmap.covers.iter().any(|cover| cover.id == cover_ref)
                        || !members_valid
                        || !matches!(global_condition, "assumed")
                    {
                        examples.push(generic_validation_example(
                            path,
                            "cover-membership-invalid",
                            "true-sheaf certificate coverRef/memberCharts must resolve to the selected finite site and globalCondition must be an explicit assumption status",
                        ));
                    }
                }
                "gluingData" if kind == "gluing-data" => {
                    for key in object.keys() {
                        if !matches!(key.as_str(), "kind" | "overlapRefs" | "sectionRefs") {
                            examples.push(generic_validation_example(
                                &format!("{path}.{key}"),
                                "unknown-field",
                                "gluing data has no unregistered supplied fields",
                            ));
                        }
                    }
                    let overlap_refs = object
                        .get("overlapRefs")
                        .and_then(Value::as_array)
                        .map(|items| {
                            items
                                .iter()
                                .filter_map(Value::as_str)
                                .collect::<BTreeSet<_>>()
                        })
                        .unwrap_or_default();
                    let overlap_count = object
                        .get("overlapRefs")
                        .and_then(Value::as_array)
                        .map_or(0, Vec::len);
                    let expected = plan
                        .complex
                        .overlaps
                        .iter()
                        .map(|overlap| overlap.id.as_str())
                        .collect::<BTreeSet<_>>();
                    let section_refs = object
                        .get("sectionRefs")
                        .and_then(Value::as_array)
                        .map(|items| {
                            items
                                .iter()
                                .filter_map(Value::as_object)
                                .filter_map(|item| {
                                    let overlap = item.get("overlapRef")?.as_str()?;
                                    let section = item.get("sectionRef")?.as_str()?;
                                    (!section.is_empty()).then_some(overlap)
                                })
                                .collect::<BTreeSet<_>>()
                        })
                        .unwrap_or_default();
                    let section_ids = object
                        .get("sectionRefs")
                        .and_then(Value::as_array)
                        .map(|items| {
                            items
                                .iter()
                                .filter_map(Value::as_object)
                                .filter_map(|item| item.get("sectionRef")?.as_str())
                                .collect::<BTreeSet<_>>()
                        })
                        .unwrap_or_default();
                    let section_count = object
                        .get("sectionRefs")
                        .and_then(Value::as_array)
                        .map_or(0, Vec::len);
                    if overlap_refs != expected
                        || overlap_count != expected.len()
                        || section_refs != expected
                        || section_count != expected.len()
                        || section_ids.len() != expected.len()
                    {
                        examples.push(generic_validation_example(
                            path,
                            "overlap-section-membership-invalid",
                            "gluing data must name every selected overlap exactly once and provide a non-empty sectionRef for each overlap",
                        ));
                    }
                }
                "comparison" if kind == "saga-comparison" => {
                    for key in object.keys() {
                        if !matches!(
                            key.as_str(),
                            "kind" | "incidenceBridge" | "h1ComparisonData"
                        ) {
                            examples.push(generic_validation_example(
                                &format!("{path}.{key}"),
                                "unknown-field",
                                "comparison has no unregistered supplied fields",
                            ));
                        }
                    }
                    let bridge = object.get("incidenceBridge").and_then(Value::as_object);
                    let h1 = object.get("h1ComparisonData").and_then(Value::as_object);
                    let target_complex = bridge
                        .and_then(|bridge| comparison_target_complex_from_bridge(plan, bridge));
                    let mut nested_unknown = false;
                    if let Some(bridge) = bridge {
                        for key in bridge.keys() {
                            let allowed = match bridge.get("kind").and_then(Value::as_str) {
                                Some("chart-indexed") => {
                                    ["kind", "repairChartRefs", "cechChartRefs"].as_slice()
                                }
                                Some("explicit") => [
                                    "kind",
                                    "sourceComplexRef",
                                    "targetComplexRef",
                                    "targetComplex",
                                ]
                                .as_slice(),
                                _ => ["kind"].as_slice(),
                            };
                            if !allowed.contains(&key.as_str()) {
                                nested_unknown = true;
                                examples.push(generic_validation_example(
                                    &format!("{path}.incidenceBridge.{key}"),
                                    "unknown-field",
                                    "incidence bridge has no unregistered supplied fields",
                                ));
                            }
                        }
                    }
                    if let Some(h1) = h1 {
                        for key in h1.keys() {
                            let allowed = match h1.get("kind").and_then(Value::as_str) {
                                Some("identity") => [
                                    "schema",
                                    "kind",
                                    "sourceComplexFingerprint",
                                    "targetComplexFingerprint",
                                    "targetCochainSupport",
                                ]
                                .as_slice(),
                                Some("explicit") => [
                                    "schema",
                                    "kind",
                                    "cochainMapRef",
                                    "sourceComplexFingerprint",
                                    "targetComplexFingerprint",
                                    "targetCochainSupport",
                                    "cochainMap",
                                ]
                                .as_slice(),
                                Some("presentation-generated") => [
                                    "schema",
                                    "kind",
                                    "sourceComplexFingerprint",
                                    "targetComplexFingerprint",
                                    "presentation",
                                ]
                                .as_slice(),
                                _ => ["kind"].as_slice(),
                            };
                            if !allowed.contains(&key.as_str()) {
                                nested_unknown = true;
                                examples.push(generic_validation_example(
                                    &format!("{path}.h1ComparisonData.{key}"),
                                    "unknown-field",
                                    "H1 comparison data has no unregistered supplied fields",
                                ));
                            }
                        }
                    }
                    let bridge_ok = !nested_unknown
                        && bridge.is_some_and(|bridge| {
                            let bridge_kind = bridge.get("kind").and_then(Value::as_str);
                            match bridge_kind {
                                Some("chart-indexed") => {
                                    let expected = plan
                                        .complex
                                        .charts
                                        .iter()
                                        .map(String::as_str)
                                        .collect::<BTreeSet<_>>();
                                    let parse_refs = |key: &str| {
                                        bridge.get(key).and_then(Value::as_array).and_then(
                                            |items| {
                                                items
                                                    .iter()
                                                    .map(Value::as_str)
                                                    .collect::<Option<Vec<_>>>()
                                            },
                                        )
                                    };
                                    let repair = parse_refs("repairChartRefs");
                                    let cech = parse_refs("cechChartRefs");
                                    repair.as_ref().is_some_and(|refs| {
                                        cech.as_ref().is_some_and(|cech_refs| {
                                            refs.len() == expected.len()
                                                && cech_refs.len() == expected.len()
                                                && refs.iter().copied().collect::<BTreeSet<_>>()
                                                    == expected
                                                && cech_refs
                                                    .iter()
                                                    .copied()
                                                    .collect::<BTreeSet<_>>()
                                                    == expected
                                        })
                                    })
                                }
                                Some("explicit") => {
                                    bridge.get("sourceComplexRef").and_then(Value::as_str)
                                        == Some(COMPARISON_SOURCE_COMPLEX_REF)
                                        && bridge.get("targetComplexRef").and_then(Value::as_str)
                                            == Some(COMPARISON_TARGET_COMPLEX_REF)
                                        && target_complex.is_some()
                                }
                                _ => false,
                            }
                        });
                    let mut explicit_checks = None;
                    let mut presentation_checks = None;
                    let h1_ok = !nested_unknown
                        && h1.is_some_and(|h1| {
                            let source_complex_fingerprint = comparison_complex_fingerprint(plan);
                            let target_fingerprint = target_complex
                                .as_ref()
                                .map(crate::repair_plan::complex_fingerprint);
                            let fingerprints_ok =
                                h1.get("sourceComplexFingerprint").and_then(Value::as_str)
                                    == Some(source_complex_fingerprint.as_str())
                                    && h1.get("targetComplexFingerprint").and_then(Value::as_str)
                                        == target_fingerprint.as_deref();
                            let kind = h1.get("kind").and_then(Value::as_str);
                            match kind {
                                Some("identity") => {
                                    h1.get("schema").and_then(Value::as_str)
                                        == Some("h1-comparison-data/v0.5.4")
                                        && fingerprints_ok
                                        && target_fingerprint.as_deref()
                                            == Some(source_complex_fingerprint.as_str())
                                        && target_complex.as_ref().is_some_and(|complex| {
                                            comparison_target_cochain_support_matches(complex, h1)
                                        })
                                }
                                Some("explicit") => {
                                    h1.get("schema").and_then(Value::as_str)
                                        == Some("h1-comparison-data/v0.5.4")
                                        && fingerprints_ok
                                        && h1.get("cochainMapRef").and_then(Value::as_str)
                                            == Some(COMPARISON_COCHAIN_MAP_REF)
                                        && target_complex.as_ref().is_some_and(|complex| {
                                            let checks =
                                                explicit_h1_comparison_checks(plan, complex, h1);
                                            explicit_checks = Some(checks);
                                            comparison_target_cochain_support_matches(complex, h1)
                                                && checks.all_pass()
                                        })
                                }
                                Some("presentation-generated") => {
                                    h1.get("schema").and_then(Value::as_str)
                                        == Some("h1-comparison-data/v0.5.4")
                                        && fingerprints_ok
                                        && target_fingerprint.as_deref()
                                            == Some(source_complex_fingerprint.as_str())
                                        && target_complex.as_ref().is_some_and(|complex| {
                                            let checks =
                                                presentation_generated_h1_checks(plan, complex, h1);
                                            presentation_checks = Some(checks.clone());
                                            checks.all_pass()
                                        })
                                }
                                _ => false,
                            }
                        });
                    if !bridge_ok || !h1_ok {
                        let reason = explicit_checks
                            .map(|checks| {
                                format!(
                                    "COMPARISON_DATA_CONTRACT_VIOLATION: checkedProperties degreeOneLeftInverse={} degreeOneRightInverse={} differencePreserving={} degreeTwoZeroPreserving={} differentialCommutative={}",
                                    checks.degree_one_left_inverse,
                                    checks.degree_one_right_inverse,
                                    checks.difference_preserving,
                                    checks.degree_two_zero_preserving,
                                    checks.differential_commutative,
                                )
                            })
                            .or_else(|| {
                                presentation_checks.map(|checks| {
                                    format!(
                                        "COMPARISON_DATA_CONTRACT_VIOLATION: presentationExactness={} generatorCompleteness={} restrictionNaturality={} degreeZeroCommutative={} degreeOneCommutative={} targetCocycle={} equationLiftAtlasPresent={} residualWitnessComputed={}",
                                        checks.presentation_exactness,
                                        checks.generator_completeness,
                                        checks.restriction_naturality,
                                        checks.degree_zero_commutative,
                                        checks.degree_one_commutative,
                                        checks.target_cocycle,
                                        checks.equation_lift_atlas_present,
                                        checks.residual_witness_computed,
                                    )
                                })
                            })
                            .unwrap_or_else(|| "COMPARISON_DATA_CONTRACT_VIOLATION: comparison requires a chart-indexed or explicit incidence bridge and a validated identity or explicit finite H1 comparison contract".to_string());
                        examples.push(generic_validation_example(
                            path,
                            "comparison-contract-invalid",
                            &reason,
                        ));
                    }
                }
                "grounding" if kind == "saga-grounding" => {
                    for key in object.keys() {
                        if !matches!(key.as_str(), "kind" | "surfaceRef" | "profileRef") {
                            examples.push(generic_validation_example(
                                &format!("{path}.{key}"),
                                "unknown-field",
                                "saga grounding has no unregistered supplied fields",
                            ));
                        }
                    }
                    if object
                        .get("surfaceRef")
                        .and_then(Value::as_str)
                        .is_none_or(str::is_empty)
                        || object
                            .get("profileRef")
                            .and_then(Value::as_str)
                            .is_none_or(str::is_empty)
                    {
                        examples.push(generic_validation_example(
                            path,
                            "grounding-reference-missing",
                            "saga grounding requires non-empty surfaceRef and profileRef",
                        ));
                    }
                }
                _ => examples.push(generic_validation_example(
                    path,
                    kind,
                    "supplied artifact kind or finite compatibility data is invalid",
                )),
            }
        }
    }
    examples_check(
        "repair-plan-schema052-supplied-slots",
        "Stage 2 supplied slots are explicit and checked before evaluator use",
        examples,
    )
}

fn comparison_target_cochain_support_matches(
    complex: &RepairPlanComplexV1,
    h1: &serde_json::Map<String, Value>,
) -> bool {
    comparison_target_cochain_support(complex, h1).is_some()
}

fn comparison_target_cochain_support(
    complex: &RepairPlanComplexV1,
    h1: &serde_json::Map<String, Value>,
) -> Option<BTreeMap<String, BTreeSet<String>>> {
    let expected = complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.clone())
        .collect::<BTreeSet<_>>();
    let items = h1.get("targetCochainSupport")?.as_array()?;
    let mut actual = BTreeMap::new();
    for item in items {
        let object = item.as_object()?;
        if object
            .keys()
            .any(|key| !matches!(key.as_str(), "overlapRef" | "support"))
        {
            return None;
        }
        let overlap_ref = object.get("overlapRef")?.as_str()?.to_string();
        let support = object.get("support")?.as_array()?;
        let support = support
            .iter()
            .map(Value::as_str)
            .collect::<Option<Vec<_>>>()?;
        let support_set = support
            .iter()
            .map(|variable| (*variable).to_string())
            .collect::<BTreeSet<_>>();
        if support.len() != support_set.len() || actual.insert(overlap_ref, support_set).is_some() {
            return None;
        }
    }
    (actual.keys().cloned().collect::<BTreeSet<_>>() == expected).then_some(actual)
}

pub(crate) fn explicit_h1_comparison_checks(
    plan: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    h1: &serde_json::Map<String, Value>,
) -> ExplicitH1ComparisonChecks {
    let Some(target_support) = comparison_target_cochain_support(target_complex, h1) else {
        return ExplicitH1ComparisonChecks::default();
    };
    let source_variables = plan
        .primitives
        .iter()
        .flat_map(|primitive| primitive.support.variables.iter().cloned())
        .collect::<BTreeSet<_>>();
    let target_variables = target_support
        .values()
        .flat_map(|support| support.iter().cloned())
        .collect::<BTreeSet<_>>();
    let source_charts = plan.complex.charts.iter().cloned().collect::<BTreeSet<_>>();
    let target_charts = target_complex
        .charts
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let source_overlaps = plan
        .complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.clone())
        .collect::<BTreeSet<_>>();
    let target_overlaps = target_complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.clone())
        .collect::<BTreeSet<_>>();
    let source_triples = plan
        .complex
        .triple_overlaps
        .iter()
        .map(|triple| triple.id.clone())
        .collect::<BTreeSet<_>>();
    let target_triples = target_complex
        .triple_overlaps
        .iter()
        .map(|triple| triple.id.clone())
        .collect::<BTreeSet<_>>();
    let Some(cochain_map) = parse_explicit_cochain_map(
        h1,
        &source_charts,
        &target_charts,
        &source_overlaps,
        &target_overlaps,
        &source_triples,
        &target_triples,
        &source_variables,
        &target_variables,
    ) else {
        return ExplicitH1ComparisonChecks::default();
    };

    let degree_one_pairs = degree_one_basis_pairs(&cochain_map.degree_one);
    let source_degree_one_basis = source_overlaps
        .iter()
        .flat_map(|overlap| {
            source_variables
                .iter()
                .map(move |variable| (overlap.clone(), variable.clone()))
        })
        .collect::<BTreeSet<_>>();
    let target_degree_one_basis = target_overlaps
        .iter()
        .flat_map(|overlap| {
            target_variables
                .iter()
                .map(move |variable| (overlap.clone(), variable.clone()))
        })
        .collect::<BTreeSet<_>>();
    let mapped_sources = degree_one_pairs
        .iter()
        .map(|(source, _)| source.clone())
        .collect::<BTreeSet<_>>();
    let mapped_targets = degree_one_pairs
        .iter()
        .map(|(_, target)| target.clone())
        .collect::<BTreeSet<_>>();
    let degree_one_left_inverse = mapped_sources == source_degree_one_basis;
    let degree_one_right_inverse = mapped_targets == target_degree_one_basis;

    let degree_zero_complete =
        map_rows_cover_targets(&cochain_map.degree_zero, &source_charts, &target_charts);
    let degree_one_complete =
        map_rows_cover_targets(&cochain_map.degree_one, &source_overlaps, &target_overlaps);
    let degree_two_complete = cochain_map.degree_two.len() == source_triples.len()
        && cochain_map
            .degree_two
            .values()
            .cloned()
            .collect::<BTreeSet<_>>()
            == target_triples;
    let map_complete = degree_zero_complete
        && degree_one_complete
        && degree_two_complete
        && degree_one_pairs.len() == source_degree_one_basis.len()
        && degree_one_pairs.len() == target_degree_one_basis.len();

    let difference_preserving = map_complete
        && difference_is_preserved(
            plan,
            target_complex,
            &cochain_map,
            &target_support,
            &source_variables,
        );
    let degree_two_zero_preserving = map_complete
        && map_degree_two_support(&BTreeSet::new(), &cochain_map.degree_two)
            == Some(cochain_map.degree_two_zero_image.clone())
        && cochain_map.degree_two_zero_image.is_empty();
    let differential_commutative =
        map_complete && differential_is_commutative(plan, target_complex, &cochain_map);

    ExplicitH1ComparisonChecks {
        degree_one_left_inverse,
        degree_one_right_inverse,
        difference_preserving,
        degree_two_zero_preserving,
        differential_commutative,
        map_complete,
    }
}

pub(crate) fn presentation_generated_h1_checks(
    plan: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    h1: &serde_json::Map<String, Value>,
) -> PresentationGeneratedH1Checks {
    let equation_lift_atlas_present = h1
        .get("presentation")
        .and_then(Value::as_object)
        .is_some_and(|presentation| presentation.get("equationLiftAtlas").is_some());
    let Ok(typed) = serde_json::from_value::<H1ComparisonDataV052>(Value::Object(h1.clone()))
    else {
        return PresentationGeneratedH1Checks {
            equation_lift_atlas_present,
            ..PresentationGeneratedH1Checks::default()
        };
    };
    if typed.schema != crate::H1_COMPARISON_DATA_V052_SCHEMA
        || typed.kind != "presentation-generated"
    {
        return PresentationGeneratedH1Checks::default();
    }
    let Some(presentation) = typed.presentation.as_ref() else {
        return PresentationGeneratedH1Checks::default();
    };

    let expected_cells = presentation_cell_refs(plan);
    let mut cells = BTreeMap::new();
    for cell in &presentation.cells {
        if cells.insert(cell.cell_ref.as_str(), cell).is_some() {
            return PresentationGeneratedH1Checks::default();
        }
    }
    let map_complete = cells.keys().copied().collect::<BTreeSet<_>>()
        == expected_cells.iter().map(String::as_str).collect();
    if !map_complete {
        return PresentationGeneratedH1Checks::default();
    }

    let cell_checks = cells
        .values()
        .map(|cell| presentation_cell_checks(cell))
        .collect::<Option<Vec<_>>>();
    let Some(cell_checks) = cell_checks else {
        return PresentationGeneratedH1Checks::default();
    };

    let expected_restrictions = presentation_restriction_refs(plan);
    let mut restrictions = BTreeMap::new();
    for restriction in &presentation.restrictions {
        if restrictions
            .insert(
                (restriction.from_ref.as_str(), restriction.to_ref.as_str()),
                restriction,
            )
            .is_some()
        {
            return PresentationGeneratedH1Checks::default();
        }
    }
    let restriction_complete = restrictions.keys().copied().collect::<BTreeSet<_>>()
        == expected_restrictions
            .iter()
            .map(|(from, to)| (from.as_str(), to.as_str()))
            .collect();
    let restriction_naturality = restriction_complete
        && restrictions.iter().all(|((from, to), restriction)| {
            cells
                .get(from)
                .zip(cells.get(to))
                .is_some_and(|(source, target)| {
                    presentation_restriction_commutes(source, target, restriction)
                })
        });
    let degree_zero_commutative = restriction_naturality
        && plan.complex.overlaps.iter().all(|overlap| {
            restrictions.contains_key(&(overlap.left.as_str(), overlap.id.as_str()))
                && restrictions.contains_key(&(overlap.right.as_str(), overlap.id.as_str()))
        });
    let degree_one_commutative = restriction_naturality
        && plan.complex.triple_overlaps.iter().all(|triple| {
            triple.overlap_refs.iter().all(|overlap_ref| {
                restrictions.contains_key(&(overlap_ref.as_str(), triple.id.as_str()))
            })
        });
    let analysis = (restriction_naturality && degree_zero_commutative && degree_one_commutative)
        .then(|| {
            presentation_residual_analysis(
                plan,
                target_complex,
                presentation,
                &cells,
                &restrictions,
            )
        })
        .flatten();
    let source_cocycle = analysis
        .as_ref()
        .is_some_and(|analysis| analysis.source_cocycle);
    let source_class_nonzero = analysis
        .as_ref()
        .and_then(|analysis| analysis.source_class_nonzero);
    let target_cocycle = analysis
        .as_ref()
        .is_some_and(|analysis| analysis.target_cocycle);
    let target_class_nonzero = analysis
        .as_ref()
        .and_then(|analysis| analysis.target_class_nonzero);
    let residual_witness = analysis.and_then(|analysis| analysis.witness);
    let residual_witness_computed = residual_witness.is_some();

    PresentationGeneratedH1Checks {
        presentation_exactness: cell_checks.iter().all(|(exactness, _)| *exactness),
        generator_completeness: cell_checks.iter().all(|(_, generation)| *generation),
        restriction_naturality,
        degree_zero_commutative,
        degree_one_commutative,
        source_cocycle,
        source_class_nonzero,
        target_cocycle,
        equation_lift_atlas_present,
        residual_witness_computed,
        target_class_nonzero,
        residual_witness,
        map_complete,
    }
}

pub(crate) fn presentation_generated_h1_output(
    plan: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    h1: &serde_json::Map<String, Value>,
    checks: &PresentationGeneratedH1Checks,
) -> Value {
    let typed = serde_json::from_value::<H1ComparisonDataV052>(Value::Object(h1.clone())).ok();
    let cells = typed
        .as_ref()
        .and_then(|typed| typed.presentation.as_ref())
        .map(|presentation| {
            presentation
                .cells
                .iter()
                .map(|cell| (cell.cell_ref.as_str(), cell))
                .collect::<BTreeMap<_, _>>()
        })
        .unwrap_or_default();
    let refs = |kind: &str| {
        let expected = match kind {
            "degreeZero" => plan
                .complex
                .charts
                .iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>(),
            "degreeOne" => plan
                .complex
                .overlaps
                .iter()
                .map(|overlap| overlap.id.as_str())
                .collect::<BTreeSet<_>>(),
            "degreeTwo" => plan
                .complex
                .triple_overlaps
                .iter()
                .map(|triple| triple.id.as_str())
                .collect::<BTreeSet<_>>(),
            _ => BTreeSet::new(),
        };
        cells
            .iter()
            .filter(|(cell_ref, _)| expected.contains(*cell_ref))
            .map(|(_, cell)| {
                json!({
                    "cellRef": cell.cell_ref,
                    "localPhiDerivedFrom": "generatorMap modulo repair/equation relations"
                })
            })
            .collect::<Vec<_>>()
    };
    let residual_witness = checks.residual_witness.as_ref().and_then(|witness| {
        Some(json!({
            "kind": "computed-quotient-atlas-witness",
            "equation": "kappa1(r_sem) = r_E + delta0(h)",
            "sourceImage": equation_cochain_json(target_complex, &cells, &witness.source_image)?,
            "equationResidual": equation_cochain_json(target_complex, &cells, &witness.equation_residual)?,
            "h": equation_chart_assignment_json(target_complex, &cells, &witness.h)?,
            "differenceIsDeltaZero": true
        }))
    });
    json!({
        "kind": "presentation-generated",
        "comparisonInput": {
            "kind": "canonical-presentation-repair-plan",
            "repairPlan": plan
        },
        "presentationExactness": checks.presentation_exactness,
        "generatorCompleteness": checks.generator_completeness,
        "generatedCochainMap": {
            "kind": "derived-from-local-phi",
            "degreeZero": refs("degreeZero"),
            "degreeOne": refs("degreeOne"),
            "degreeTwo": refs("degreeTwo"),
            "degreeZeroCommutative": checks.degree_zero_commutative,
            "degreeOneCommutative": checks.degree_one_commutative
        },
        "equationResidual": {
            "kind": "derived-from-independent-equation-lift-atlas",
            "targetCocycle": checks.target_cocycle,
            "targetClassNonZero": checks.target_class_nonzero
        },
        "semanticResidual": {
            "kind": "derived-from-semantic-repair-presentation",
            "sourceCocycle": checks.source_cocycle,
            "sourceClassNonZero": checks.source_class_nonzero
        },
        "residualWitness": residual_witness,
        "restrictionNaturality": checks.restriction_naturality
    })
}

pub(crate) fn recompute_presentation_generated_h1_output(
    plan: &RepairPlanDocumentV1,
) -> Option<Value> {
    let comparison = plan.comparison.as_ref()?;
    let h1 = comparison.get("h1ComparisonData")?.as_object()?;
    if h1.get("kind").and_then(Value::as_str) != Some("presentation-generated") {
        return None;
    }
    let target_complex = comparison_target_complex(plan, comparison)?;
    let checks = presentation_generated_h1_checks(plan, &target_complex, h1);
    Some(presentation_generated_h1_output(
        plan,
        &target_complex,
        h1,
        &checks,
    ))
}

fn presentation_cell_refs(plan: &RepairPlanDocumentV1) -> BTreeSet<String> {
    plan.complex
        .charts
        .iter()
        .cloned()
        .chain(
            plan.complex
                .overlaps
                .iter()
                .map(|overlap| overlap.id.clone()),
        )
        .chain(
            plan.complex
                .triple_overlaps
                .iter()
                .map(|triple| triple.id.clone()),
        )
        .collect()
}

fn presentation_restriction_refs(plan: &RepairPlanDocumentV1) -> BTreeSet<(String, String)> {
    let mut refs = BTreeSet::new();
    for overlap in &plan.complex.overlaps {
        refs.insert((overlap.left.clone(), overlap.id.clone()));
        refs.insert((overlap.right.clone(), overlap.id.clone()));
    }
    for triple in &plan.complex.triple_overlaps {
        for overlap_ref in &triple.overlap_refs {
            refs.insert((overlap_ref.clone(), triple.id.clone()));
        }
    }
    refs
}

fn presentation_cell_checks(cell: &H1PresentationCellV052) -> Option<(bool, bool)> {
    let semantic_count = cell.semantic_generators.len();
    let equation_count = cell.equation_generators.len();
    if semantic_count == 0
        || equation_count == 0
        || cell
            .semantic_generators
            .iter()
            .collect::<BTreeSet<_>>()
            .len()
            != semantic_count
        || cell
            .equation_generators
            .iter()
            .collect::<BTreeSet<_>>()
            .len()
            != equation_count
        || !binary_matrix(&cell.repair_relation_matrix, semantic_count)
        || !binary_matrix(&cell.equation_relation_matrix, equation_count)
        || !binary_matrix_with_shape(&cell.generator_map, equation_count, semantic_count)
    {
        return None;
    }
    let relation_rank = f2_rank(&cell.repair_relation_matrix, semantic_count)?;
    let equation_rank = f2_rank(&cell.equation_relation_matrix, equation_count)?;
    let generator_columns = matrix_columns(&cell.generator_map, semantic_count);
    let mut quotient_generators = cell.equation_relation_matrix.clone();
    quotient_generators.extend(generator_columns);
    let quotient_generator_rank = f2_rank(&quotient_generators, equation_count)?;
    let soundness = cell.repair_relation_matrix.iter().all(|relation| {
        f2_vector_in_span(
            &cell.equation_relation_matrix,
            equation_count,
            &f2_matrix_vector(&cell.generator_map, relation),
        )
        .unwrap_or(false)
    });
    let kernel_dimension = semantic_count.checked_sub(quotient_generator_rank - equation_rank)?;
    Some((
        soundness && relation_rank == kernel_dimension,
        quotient_generator_rank == equation_count,
    ))
}

fn presentation_restriction_commutes(
    source: &H1PresentationCellV052,
    target: &H1PresentationCellV052,
    restriction: &H1PresentationRestrictionV052,
) -> bool {
    let source_semantic = source.semantic_generators.len();
    let source_equation = source.equation_generators.len();
    let target_semantic = target.semantic_generators.len();
    let target_equation = target.equation_generators.len();
    if !binary_matrix_with_shape(
        &restriction.semantic_matrix,
        target_semantic,
        source_semantic,
    ) || !binary_matrix_with_shape(
        &restriction.equation_matrix,
        target_equation,
        source_equation,
    ) {
        return false;
    }
    let semantic_relations_preserved = source.repair_relation_matrix.iter().all(|relation| {
        f2_vector_in_span(
            &target.repair_relation_matrix,
            target_semantic,
            &f2_matrix_vector(&restriction.semantic_matrix, relation),
        )
        .unwrap_or(false)
    });
    let equation_relations_preserved = source.equation_relation_matrix.iter().all(|relation| {
        f2_vector_in_span(
            &target.equation_relation_matrix,
            target_equation,
            &f2_matrix_vector(&restriction.equation_matrix, relation),
        )
        .unwrap_or(false)
    });
    semantic_relations_preserved
        && equation_relations_preserved
        && (0..source_semantic).all(|index| {
            let mut basis = vec![0; source_semantic];
            basis[index] = 1;
            let through_semantic = f2_matrix_vector(
                &target.generator_map,
                &f2_matrix_vector(&restriction.semantic_matrix, &basis),
            );
            let through_equation = f2_matrix_vector(
                &restriction.equation_matrix,
                &f2_matrix_vector(&source.generator_map, &basis),
            );
            let difference = through_semantic
                .iter()
                .zip(through_equation)
                .map(|(left, right)| left ^ right)
                .collect::<Vec<_>>();
            f2_vector_in_span(
                &target.equation_relation_matrix,
                target_equation,
                &difference,
            )
            .unwrap_or(false)
        })
}

fn presentation_residual_analysis(
    plan: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    presentation: &H1PresentationDataV052,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    restrictions: &BTreeMap<(&str, &str), &H1PresentationRestrictionV052>,
) -> Option<PresentationResidualAnalysis> {
    let semantic_residual = generated_semantic_residual(plan, target_complex, cells)?;
    let source_image = generated_source_image(target_complex, cells, &semantic_residual)?;
    let source_cocycle =
        semantic_cochain_is_cocycle(target_complex, cells, restrictions, &semantic_residual)?;
    let source_class_nonzero = source_cocycle.then(|| {
        semantic_delta_zero_solution(target_complex, cells, restrictions, &semantic_residual)
            .is_none()
    });
    let equation_residual =
        equation_residual_from_lift_atlas(target_complex, presentation, cells, restrictions)?;
    let target_cocycle =
        equation_cochain_is_cocycle(target_complex, cells, restrictions, &equation_residual)?;
    if !source_cocycle || !target_cocycle {
        return Some(PresentationResidualAnalysis {
            source_cocycle,
            source_class_nonzero,
            target_cocycle: false,
            target_class_nonzero: None,
            witness: None,
        });
    }
    let difference = cochain_sum(target_complex, cells, &source_image, &equation_residual)?;
    let target_class_nonzero = Some(
        equation_delta_zero_solution(target_complex, cells, restrictions, &equation_residual)
            .is_none(),
    );
    let witness = equation_delta_zero_solution(target_complex, cells, restrictions, &difference)
        .map(|h| PresentationResidualWitness {
            source_image,
            equation_residual,
            h,
        });
    Some(PresentationResidualAnalysis {
        source_cocycle,
        source_class_nonzero,
        target_cocycle: true,
        target_class_nonzero,
        witness,
    })
}

fn generated_semantic_residual(
    plan: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
) -> Option<BTreeMap<String, Vec<u8>>> {
    let primitives = plan
        .primitives
        .iter()
        .map(|primitive| (primitive.overlap_ref.as_str(), primitive))
        .collect::<BTreeMap<_, _>>();
    if primitives.keys().copied().collect::<BTreeSet<_>>()
        != target_complex
            .overlaps
            .iter()
            .map(|overlap| overlap.id.as_str())
            .collect()
    {
        return None;
    }
    let mut semantic_cochain = BTreeMap::new();
    for overlap in &target_complex.overlaps {
        let cell = cells.get(overlap.id.as_str())?;
        let primitive = primitives.get(overlap.id.as_str())?;
        if primitive
            .support
            .variables
            .iter()
            .collect::<BTreeSet<_>>()
            .len()
            != primitive.support.variables.len()
        {
            return None;
        }
        let semantic_index = cell
            .semantic_generators
            .iter()
            .enumerate()
            .map(|(index, generator)| (generator.as_str(), index))
            .collect::<BTreeMap<_, _>>();
        let mut coefficients = vec![0; cell.semantic_generators.len()];
        for variable in &primitive.support.variables {
            coefficients[*semantic_index.get(variable.as_str())?] ^= 1;
        }
        semantic_cochain.insert(overlap.id.clone(), coefficients);
    }
    Some(semantic_cochain)
}

fn generated_source_image(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    semantic_residual: &BTreeMap<String, Vec<u8>>,
) -> Option<BTreeMap<String, Vec<u8>>> {
    target_complex
        .overlaps
        .iter()
        .map(|overlap| {
            let cell = cells.get(overlap.id.as_str())?;
            let residual = semantic_residual.get(&overlap.id)?;
            (residual.len() == cell.semantic_generators.len()).then(|| {
                (
                    overlap.id.clone(),
                    f2_matrix_vector(&cell.generator_map, residual),
                )
            })
        })
        .collect()
}

fn equation_residual_from_lift_atlas(
    target_complex: &RepairPlanComplexV1,
    presentation: &H1PresentationDataV052,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    restrictions: &BTreeMap<(&str, &str), &H1PresentationRestrictionV052>,
) -> Option<BTreeMap<String, Vec<u8>>> {
    let mut lifts = BTreeMap::new();
    for lift in &presentation.equation_lift_atlas.local_lifts {
        let cell = cells.get(lift.chart_ref.as_str())?;
        if !binary_vector(&lift.coefficients, cell.equation_generators.len())
            || lifts
                .insert(lift.chart_ref.as_str(), lift.coefficients.as_slice())
                .is_some()
        {
            return None;
        }
    }
    if lifts.keys().copied().collect::<BTreeSet<_>>()
        != target_complex.charts.iter().map(String::as_str).collect()
    {
        return None;
    }
    let mut transitions = BTreeMap::new();
    for transition in &presentation.equation_lift_atlas.transition_differences {
        let cell = cells.get(transition.overlap_ref.as_str())?;
        if !binary_vector(&transition.coefficients, cell.equation_generators.len())
            || transitions
                .insert(
                    transition.overlap_ref.as_str(),
                    transition.coefficients.as_slice(),
                )
                .is_some()
        {
            return None;
        }
    }
    if transitions.keys().copied().collect::<BTreeSet<_>>()
        != target_complex
            .overlaps
            .iter()
            .map(|overlap| overlap.id.as_str())
            .collect()
    {
        return None;
    }
    let mut residual = BTreeMap::new();
    for overlap in &target_complex.overlaps {
        let cell = cells.get(overlap.id.as_str())?;
        let left = restrictions.get(&(overlap.left.as_str(), overlap.id.as_str()))?;
        let right = restrictions.get(&(overlap.right.as_str(), overlap.id.as_str()))?;
        let mut value = transitions.get(overlap.id.as_str())?.to_vec();
        for restricted_lift in [
            f2_matrix_vector(&left.equation_matrix, lifts.get(overlap.left.as_str())?),
            f2_matrix_vector(&right.equation_matrix, lifts.get(overlap.right.as_str())?),
        ] {
            if restricted_lift.len() != cell.equation_generators.len() {
                return None;
            }
            for (entry, lift) in value.iter_mut().zip(restricted_lift) {
                *entry ^= lift;
            }
        }
        residual.insert(overlap.id.clone(), value);
    }
    Some(residual)
}

fn equation_cochain_is_cocycle(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    restrictions: &BTreeMap<(&str, &str), &H1PresentationRestrictionV052>,
    cochain: &BTreeMap<String, Vec<u8>>,
) -> Option<bool> {
    for triple in &target_complex.triple_overlaps {
        let target = cells.get(triple.id.as_str())?;
        let mut differential = vec![0; target.equation_generators.len()];
        for overlap_ref in &triple.overlap_refs {
            let restriction = restrictions.get(&(overlap_ref.as_str(), triple.id.as_str()))?;
            let restricted =
                f2_matrix_vector(&restriction.equation_matrix, cochain.get(overlap_ref)?);
            if restricted.len() != differential.len() {
                return None;
            }
            for (entry, value) in differential.iter_mut().zip(restricted) {
                *entry ^= value;
            }
        }
        if !f2_vector_in_span(
            &target.equation_relation_matrix,
            target.equation_generators.len(),
            &differential,
        )? {
            return Some(false);
        }
    }
    Some(true)
}

fn semantic_cochain_is_cocycle(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    restrictions: &BTreeMap<(&str, &str), &H1PresentationRestrictionV052>,
    cochain: &BTreeMap<String, Vec<u8>>,
) -> Option<bool> {
    for triple in &target_complex.triple_overlaps {
        let target = cells.get(triple.id.as_str())?;
        let mut differential = vec![0; target.semantic_generators.len()];
        for overlap_ref in &triple.overlap_refs {
            let restriction = restrictions.get(&(overlap_ref.as_str(), triple.id.as_str()))?;
            let restricted =
                f2_matrix_vector(&restriction.semantic_matrix, cochain.get(overlap_ref)?);
            if restricted.len() != differential.len() {
                return None;
            }
            for (entry, value) in differential.iter_mut().zip(restricted) {
                *entry ^= value;
            }
        }
        if !f2_vector_in_span(
            &target.repair_relation_matrix,
            target.semantic_generators.len(),
            &differential,
        )? {
            return Some(false);
        }
    }
    Some(true)
}

fn cochain_sum(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    left: &BTreeMap<String, Vec<u8>>,
    right: &BTreeMap<String, Vec<u8>>,
) -> Option<BTreeMap<String, Vec<u8>>> {
    target_complex
        .overlaps
        .iter()
        .map(|overlap| {
            let width = cells.get(overlap.id.as_str())?.equation_generators.len();
            let left = left.get(&overlap.id)?;
            let right = right.get(&overlap.id)?;
            (left.len() == width && right.len() == width).then(|| {
                (
                    overlap.id.clone(),
                    left.iter()
                        .zip(right)
                        .map(|(left, right)| left ^ right)
                        .collect(),
                )
            })
        })
        .collect()
}

fn equation_delta_zero_solution(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    restrictions: &BTreeMap<(&str, &str), &H1PresentationRestrictionV052>,
    cochain: &BTreeMap<String, Vec<u8>>,
) -> Option<BTreeMap<String, Vec<u8>>> {
    let mut chart_offsets = BTreeMap::new();
    let mut unknown_count = 0;
    for chart in &target_complex.charts {
        chart_offsets.insert(chart.as_str(), unknown_count);
        unknown_count += cells.get(chart.as_str())?.equation_generators.len();
    }
    let mut relation_offsets = BTreeMap::new();
    for overlap in &target_complex.overlaps {
        relation_offsets.insert(overlap.id.as_str(), unknown_count);
        unknown_count += cells
            .get(overlap.id.as_str())?
            .equation_relation_matrix
            .len();
    }
    let mut rows = Vec::new();
    for overlap in &target_complex.overlaps {
        let target = cells.get(overlap.id.as_str())?;
        let left = restrictions.get(&(overlap.left.as_str(), overlap.id.as_str()))?;
        let right = restrictions.get(&(overlap.right.as_str(), overlap.id.as_str()))?;
        let rhs = cochain.get(&overlap.id)?;
        if rhs.len() != target.equation_generators.len() {
            return None;
        }
        for coordinate in 0..target.equation_generators.len() {
            let mut row = vec![0; unknown_count + 1];
            for (chart, restriction) in [(&overlap.left, left), (&overlap.right, right)] {
                let offset = chart_offsets[chart.as_str()];
                for (index, coefficient) in
                    restriction.equation_matrix[coordinate].iter().enumerate()
                {
                    row[offset + index] ^= coefficient;
                }
            }
            let relation_offset = relation_offsets[overlap.id.as_str()];
            for (index, relation) in target.equation_relation_matrix.iter().enumerate() {
                row[relation_offset + index] ^= relation[coordinate];
            }
            row[unknown_count] = rhs[coordinate];
            rows.push(row);
        }
    }
    let solution = f2_solve(rows, unknown_count)?;
    target_complex
        .charts
        .iter()
        .map(|chart| {
            let offset = chart_offsets[chart.as_str()];
            let width = cells.get(chart.as_str())?.equation_generators.len();
            Some((chart.clone(), solution[offset..offset + width].to_vec()))
        })
        .collect()
}

fn semantic_delta_zero_solution(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    restrictions: &BTreeMap<(&str, &str), &H1PresentationRestrictionV052>,
    cochain: &BTreeMap<String, Vec<u8>>,
) -> Option<BTreeMap<String, Vec<u8>>> {
    let mut chart_offsets = BTreeMap::new();
    let mut unknown_count = 0;
    for chart in &target_complex.charts {
        chart_offsets.insert(chart.as_str(), unknown_count);
        unknown_count += cells.get(chart.as_str())?.semantic_generators.len();
    }
    let mut relation_offsets = BTreeMap::new();
    for overlap in &target_complex.overlaps {
        relation_offsets.insert(overlap.id.as_str(), unknown_count);
        unknown_count += cells.get(overlap.id.as_str())?.repair_relation_matrix.len();
    }
    let mut rows = Vec::new();
    for overlap in &target_complex.overlaps {
        let target = cells.get(overlap.id.as_str())?;
        let left = restrictions.get(&(overlap.left.as_str(), overlap.id.as_str()))?;
        let right = restrictions.get(&(overlap.right.as_str(), overlap.id.as_str()))?;
        let rhs = cochain.get(&overlap.id)?;
        if rhs.len() != target.semantic_generators.len() {
            return None;
        }
        for coordinate in 0..target.semantic_generators.len() {
            let mut row = vec![0; unknown_count + 1];
            for (chart, restriction) in [(&overlap.left, left), (&overlap.right, right)] {
                let offset = chart_offsets[chart.as_str()];
                for (index, coefficient) in
                    restriction.semantic_matrix[coordinate].iter().enumerate()
                {
                    row[offset + index] ^= coefficient;
                }
            }
            let relation_offset = relation_offsets[overlap.id.as_str()];
            for (index, relation) in target.repair_relation_matrix.iter().enumerate() {
                row[relation_offset + index] ^= relation[coordinate];
            }
            row[unknown_count] = rhs[coordinate];
            rows.push(row);
        }
    }
    let solution = f2_solve(rows, unknown_count)?;
    target_complex
        .charts
        .iter()
        .map(|chart| {
            let offset = chart_offsets[chart.as_str()];
            let width = cells.get(chart.as_str())?.semantic_generators.len();
            Some((chart.clone(), solution[offset..offset + width].to_vec()))
        })
        .collect()
}

fn equation_cochain_json(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    cochain: &BTreeMap<String, Vec<u8>>,
) -> Option<Vec<Value>> {
    target_complex
        .overlaps
        .iter()
        .map(|overlap| {
            let cell = cells.get(overlap.id.as_str())?;
            let coefficients = cochain.get(&overlap.id)?;
            (coefficients.len() == cell.equation_generators.len()).then(|| {
                json!({
                    "overlapRef": overlap.id,
                    "equationGenerators": cell.equation_generators,
                    "coefficients": coefficients
                })
            })
        })
        .collect()
}

fn equation_chart_assignment_json(
    target_complex: &RepairPlanComplexV1,
    cells: &BTreeMap<&str, &H1PresentationCellV052>,
    assignment: &BTreeMap<String, Vec<u8>>,
) -> Option<Vec<Value>> {
    target_complex
        .charts
        .iter()
        .map(|chart| {
            let cell = cells.get(chart.as_str())?;
            let coefficients = assignment.get(chart)?;
            (coefficients.len() == cell.equation_generators.len()).then(|| {
                json!({
                    "chartRef": chart,
                    "equationGenerators": cell.equation_generators,
                    "coefficients": coefficients
                })
            })
        })
        .collect()
}

fn binary_vector(vector: &[u8], width: usize) -> bool {
    vector.len() == width && vector.iter().all(|value| *value <= 1)
}

fn f2_solve(mut rows: Vec<Vec<u8>>, unknown_count: usize) -> Option<Vec<u8>> {
    if rows
        .iter()
        .any(|row| row.len() != unknown_count + 1 || row.iter().any(|value| *value > 1))
    {
        return None;
    }
    let mut pivot_row = 0;
    let mut pivots = Vec::new();
    for column in 0..unknown_count {
        let pivot = (pivot_row..rows.len()).find(|row| rows[*row][column] == 1);
        let Some(pivot) = pivot else {
            continue;
        };
        rows.swap(pivot_row, pivot);
        for row in 0..rows.len() {
            if row != pivot_row && rows[row][column] == 1 {
                for entry in column..=unknown_count {
                    rows[row][entry] ^= rows[pivot_row][entry];
                }
            }
        }
        pivots.push((pivot_row, column));
        pivot_row += 1;
    }
    if rows
        .iter()
        .any(|row| row[..unknown_count].iter().all(|value| *value == 0) && row[unknown_count] == 1)
    {
        return None;
    }
    let mut solution = vec![0; unknown_count];
    for (row, column) in pivots {
        solution[column] = rows[row][unknown_count];
    }
    Some(solution)
}

fn binary_matrix(rows: &[Vec<u8>], width: usize) -> bool {
    rows.iter()
        .all(|row| row.len() == width && row.iter().all(|value| *value <= 1))
}

fn binary_matrix_with_shape(rows: &[Vec<u8>], height: usize, width: usize) -> bool {
    rows.len() == height && binary_matrix(rows, width)
}

fn f2_rank(rows: &[Vec<u8>], width: usize) -> Option<usize> {
    if !binary_matrix(rows, width) {
        return None;
    }
    let mut rows = rows.to_vec();
    let mut rank = 0;
    for column in 0..width {
        let pivot = (rank..rows.len()).find(|row| rows[*row][column] == 1);
        let Some(pivot) = pivot else {
            continue;
        };
        rows.swap(rank, pivot);
        for row in 0..rows.len() {
            if row != rank && rows[row][column] == 1 {
                for entry in column..width {
                    rows[row][entry] ^= rows[rank][entry];
                }
            }
        }
        rank += 1;
    }
    Some(rank)
}

fn matrix_columns(matrix: &[Vec<u8>], width: usize) -> Vec<Vec<u8>> {
    (0..width)
        .map(|column| matrix.iter().map(|row| row[column]).collect())
        .collect()
}

fn f2_matrix_vector(matrix: &[Vec<u8>], vector: &[u8]) -> Vec<u8> {
    matrix
        .iter()
        .map(|row| {
            row.iter()
                .zip(vector)
                .fold(0, |sum, (coefficient, value)| sum ^ (*coefficient & *value))
        })
        .collect()
}

fn f2_vector_in_span(rows: &[Vec<u8>], width: usize, vector: &[u8]) -> Option<bool> {
    if vector.len() != width || vector.iter().any(|value| *value > 1) {
        return None;
    }
    let rank = f2_rank(rows, width)?;
    let mut augmented = rows.to_vec();
    augmented.push(vector.to_vec());
    Some(f2_rank(&augmented, width)? == rank)
}

fn parse_explicit_cochain_map(
    h1: &serde_json::Map<String, Value>,
    source_charts: &BTreeSet<String>,
    target_charts: &BTreeSet<String>,
    source_overlaps: &BTreeSet<String>,
    target_overlaps: &BTreeSet<String>,
    source_triples: &BTreeSet<String>,
    target_triples: &BTreeSet<String>,
    source_variables: &BTreeSet<String>,
    target_variables: &BTreeSet<String>,
) -> Option<ExplicitCochainMap> {
    let typed: H1ComparisonDataV052 = serde_json::from_value(Value::Object(h1.clone())).ok()?;
    if typed.schema != crate::H1_COMPARISON_DATA_V052_SCHEMA
        || typed.kind != "explicit"
        || typed.cochain_map.is_none()
    {
        return None;
    }
    let object = h1.get("cochainMap")?.as_object()?;
    if object
        .keys()
        .any(|key| !matches!(key.as_str(), "degreeZero" | "degreeOne" | "degreeTwo"))
    {
        return None;
    }
    let degree_zero = parse_basis_map_rows(
        object.get("degreeZero")?,
        "sourceChartRef",
        "targetChartRef",
        source_charts,
        target_charts,
        source_variables,
        target_variables,
    )?;
    let degree_one = parse_basis_map_rows(
        object.get("degreeOne")?,
        "sourceOverlapRef",
        "targetOverlapRef",
        source_overlaps,
        target_overlaps,
        source_variables,
        target_variables,
    )?;
    let degree_two_object = object.get("degreeTwo")?.as_object()?;
    if degree_two_object
        .keys()
        .any(|key| !matches!(key.as_str(), "basisMap" | "zeroImage"))
    {
        return None;
    }
    let degree_two_items = degree_two_object.get("basisMap")?.as_array()?;
    let mut degree_two = BTreeMap::new();
    for item in degree_two_items {
        let item = item.as_object()?;
        if item
            .keys()
            .any(|key| !matches!(key.as_str(), "sourceTripleRef" | "targetTripleRef"))
        {
            return None;
        }
        let source = item.get("sourceTripleRef")?.as_str()?.to_string();
        let target = item.get("targetTripleRef")?.as_str()?.to_string();
        if degree_two.insert(source, target).is_some() {
            return None;
        }
    }
    if degree_two.keys().cloned().collect::<BTreeSet<_>>() != *source_triples
        || degree_two.values().cloned().collect::<BTreeSet<_>>() != *target_triples
    {
        return None;
    }
    let zero_image = degree_two_object
        .get("zeroImage")?
        .as_array()?
        .iter()
        .map(|value| value.as_str().map(str::to_string))
        .collect::<Option<BTreeSet<_>>>()?;
    if zero_image
        .iter()
        .any(|triple| !target_triples.contains(triple))
    {
        return None;
    }
    Some(ExplicitCochainMap {
        degree_zero,
        degree_one,
        degree_two,
        degree_two_zero_image: zero_image,
    })
}

fn parse_basis_map_rows(
    value: &Value,
    source_ref_key: &str,
    target_ref_key: &str,
    source_refs: &BTreeSet<String>,
    target_refs: &BTreeSet<String>,
    source_variables: &BTreeSet<String>,
    target_variables: &BTreeSet<String>,
) -> Option<BTreeMap<String, ComparisonBasisMap>> {
    let items = value.as_array()?;
    let mut rows = BTreeMap::new();
    let mut mapped_targets = BTreeSet::new();
    for item in items {
        let item = item.as_object()?;
        if item
            .keys()
            .any(|key| key != source_ref_key && key != target_ref_key && key != "variableMap")
        {
            return None;
        }
        let source = item.get(source_ref_key)?.as_str()?.to_string();
        let target = item.get(target_ref_key)?.as_str()?.to_string();
        if !source_refs.contains(&source) || !target_refs.contains(&target) {
            return None;
        }
        let variable_items = item.get("variableMap")?.as_array()?;
        let mut variables = BTreeMap::new();
        let mut mapped_variables = BTreeSet::new();
        for variable_item in variable_items {
            let variable_item = variable_item.as_object()?;
            if variable_item
                .keys()
                .any(|key| !matches!(key.as_str(), "source" | "target"))
            {
                return None;
            }
            let source_variable = variable_item.get("source")?.as_str()?.to_string();
            let target_variable = variable_item.get("target")?.as_str()?.to_string();
            if !source_variables.contains(&source_variable)
                || !target_variables.contains(&target_variable)
                || variables
                    .insert(source_variable, target_variable.clone())
                    .is_some()
                || !mapped_variables.insert(target_variable)
            {
                return None;
            }
        }
        if variables.keys().cloned().collect::<BTreeSet<_>>() != *source_variables
            || mapped_variables != *target_variables
            || rows
                .insert(
                    source,
                    ComparisonBasisMap {
                        target_ref: target.clone(),
                        variables,
                    },
                )
                .is_some()
            || !mapped_targets.insert(target)
        {
            return None;
        }
    }
    if rows.keys().cloned().collect::<BTreeSet<_>>() != *source_refs
        || mapped_targets != *target_refs
    {
        return None;
    }
    Some(rows)
}

fn map_rows_cover_targets(
    rows: &BTreeMap<String, ComparisonBasisMap>,
    source_refs: &BTreeSet<String>,
    target_refs: &BTreeSet<String>,
) -> bool {
    rows.keys().cloned().collect::<BTreeSet<_>>() == *source_refs
        && rows
            .values()
            .map(|row| row.target_ref.clone())
            .collect::<BTreeSet<_>>()
            == *target_refs
}

fn degree_one_basis_pairs(
    rows: &BTreeMap<String, ComparisonBasisMap>,
) -> BTreeSet<((String, String), (String, String))> {
    rows.iter()
        .flat_map(|(source_overlap, row)| {
            row.variables.iter().map(move |(source, target)| {
                (
                    (source_overlap.clone(), source.clone()),
                    (row.target_ref.clone(), target.clone()),
                )
            })
        })
        .collect()
}

fn difference_is_preserved(
    plan: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    cochain_map: &ExplicitCochainMap,
    target_support: &BTreeMap<String, BTreeSet<String>>,
    source_variables: &BTreeSet<String>,
) -> bool {
    let target_overlap_by_id = target_complex
        .overlaps
        .iter()
        .map(|overlap| (overlap.id.as_str(), overlap))
        .collect::<BTreeMap<_, _>>();
    for source_overlap in &plan.complex.overlaps {
        let Some(degree_one) = cochain_map.degree_one.get(&source_overlap.id) else {
            return false;
        };
        let Some(target_overlap) = target_overlap_by_id.get(degree_one.target_ref.as_str()) else {
            return false;
        };
        let Some(left_map) = cochain_map.degree_zero.get(&source_overlap.left) else {
            return false;
        };
        let Some(right_map) = cochain_map.degree_zero.get(&source_overlap.right) else {
            return false;
        };
        let mapped_endpoints = [left_map.target_ref.as_str(), right_map.target_ref.as_str()]
            .into_iter()
            .collect::<BTreeSet<_>>();
        let target_endpoints = [target_overlap.left.as_str(), target_overlap.right.as_str()]
            .into_iter()
            .collect::<BTreeSet<_>>();
        if mapped_endpoints != target_endpoints {
            return false;
        }
        for variable in source_variables {
            let Some(left_variable) = left_map.variables.get(variable) else {
                return false;
            };
            let Some(right_variable) = right_map.variables.get(variable) else {
                return false;
            };
            let Some(degree_one_variable) = degree_one.variables.get(variable) else {
                return false;
            };
            if left_variable != right_variable || left_variable != degree_one_variable {
                return false;
            }
        }
        let Some(source_primitive) = plan
            .primitives
            .iter()
            .find(|primitive| primitive.overlap_ref == source_overlap.id)
        else {
            return false;
        };
        let mapped_support = source_primitive
            .support
            .variables
            .iter()
            .filter_map(|variable| degree_one.variables.get(variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        if mapped_support
            != *target_support
                .get(&degree_one.target_ref)
                .unwrap_or(&BTreeSet::new())
        {
            return false;
        }
    }
    true
}

fn map_degree_two_support(
    support: &BTreeSet<String>,
    map: &BTreeMap<String, String>,
) -> Option<BTreeSet<String>> {
    support
        .iter()
        .map(|source| map.get(source).cloned())
        .collect()
}

fn differential_is_commutative(
    source_complex: &RepairPlanDocumentV1,
    target_complex: &RepairPlanComplexV1,
    cochain_map: &ExplicitCochainMap,
) -> bool {
    let target_triples_by_overlap = target_complex
        .overlaps
        .iter()
        .map(|overlap| {
            (
                overlap.id.as_str(),
                target_complex
                    .triple_overlaps
                    .iter()
                    .filter(|triple| triple.overlap_refs.contains(&overlap.id))
                    .map(|triple| triple.id.clone())
                    .collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for source_overlap in &source_complex.complex.overlaps {
        let Some(degree_one) = cochain_map.degree_one.get(&source_overlap.id) else {
            return false;
        };
        let source_incidence = source_complex
            .complex
            .triple_overlaps
            .iter()
            .filter(|triple| triple.overlap_refs.contains(&source_overlap.id))
            .map(|triple| triple.id.clone())
            .collect::<BTreeSet<_>>();
        let Some(mapped_incidence) =
            map_degree_two_support(&source_incidence, &cochain_map.degree_two)
        else {
            return false;
        };
        let Some(target_incidence) = target_triples_by_overlap.get(degree_one.target_ref.as_str())
        else {
            return false;
        };
        if mapped_incidence != *target_incidence {
            return false;
        }
    }
    true
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
    for overlap in &plan.complex.overlaps {
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
    for primitive in &plan.primitives {
        if !overlaps.contains(primitive.overlap_ref.as_str()) {
            examples.push(generic_validation_example(
                &format!("primitives[{}].overlapRef", primitive.id),
                &primitive.overlap_ref,
                "primitive overlapRef must resolve to complex.overlaps",
            ));
        }
    }
    for triple in &plan.complex.triple_overlaps {
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
    if let Some(comparison) = plan.comparison.as_ref() {
        if comparison.get("kind").and_then(Value::as_str) == Some("saga-comparison") {
            if let Some(bridge) = comparison.get("incidenceBridge") {
                if bridge.get("kind").and_then(Value::as_str) == Some("explicit") {
                    for (field, expected) in [
                        ("sourceComplexRef", COMPARISON_SOURCE_COMPLEX_REF),
                        ("targetComplexRef", COMPARISON_TARGET_COMPLEX_REF),
                    ] {
                        let actual = bridge.get(field).and_then(Value::as_str);
                        if actual != Some(expected) {
                            examples.push(generic_validation_example(
                                &format!("comparison.incidenceBridge.{field}"),
                                actual.unwrap_or("<missing>"),
                                &format!(
                                    "explicit comparison reference must resolve to {expected}"
                                ),
                            ));
                        }
                    }
                }
            }
            if let Some(h1) = comparison.get("h1ComparisonData") {
                if h1.get("kind").and_then(Value::as_str) == Some("explicit")
                    && h1.get("cochainMapRef").and_then(Value::as_str)
                        != Some(COMPARISON_COCHAIN_MAP_REF)
                {
                    examples.push(generic_validation_example(
                        "comparison.h1ComparisonData.cochainMapRef",
                        h1.get("cochainMapRef")
                            .and_then(Value::as_str)
                            .unwrap_or("<missing>"),
                        "explicit comparison cochain map reference must resolve to comparison:cochain-map",
                    ));
                }
            }
        }
    }
    examples_check(
        "repair-plan-schema052-reference-resolution",
        "RepairPlan chart, overlap, primitive, triple, and comparison references resolve",
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
    let atom_subjects = archmap
        .atoms
        .iter()
        .map(|atom| (atom.id.as_str(), atom.subject.as_str()))
        .collect::<BTreeMap<_, _>>();
    let subjects = archmap
        .atoms
        .iter()
        .map(|atom| atom.subject.as_str())
        .collect::<BTreeSet<_>>();
    let lambda = plan
        .semantic_projection
        .lambda
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let k = plan
        .semantic_projection
        .k
        .iter()
        .map(String::as_str)
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
                examples.push(generic_validation_example(
                    &path,
                    "missing",
                    "an ArchMap complex mapping requires every overlap to declare archmapContextRef",
                ));
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
            for chart in [&overlap.left, &overlap.right] {
                let has_direct_restriction = contexts.get(chart.as_str()).is_some_and(|source| {
                    source
                        .restricts_to
                        .iter()
                        .any(|target| target == context_ref)
                });
                if !has_direct_restriction {
                    examples.push(generic_validation_example(
                        &path,
                        &format!("{chart}->{context_ref}"),
                        "each mapped overlap must receive direct restrictions from its two chart contexts",
                    ));
                }
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
                examples.push(generic_validation_example(
                    &path,
                    "missing",
                    "an ArchMap complex mapping requires every triple overlap to declare archmapContextRef",
                ));
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
            for overlap_ref in &triple.overlap_refs {
                let Some(source_ref) = overlap_contexts.get(overlap_ref.as_str()) else {
                    examples.push(generic_validation_example(
                        &path,
                        overlap_ref,
                        "triple overlap mapping requires every referenced overlap mapping",
                    ));
                    continue;
                };
                let has_direct_restriction = contexts.get(source_ref).is_some_and(|source| {
                    source
                        .restricts_to
                        .iter()
                        .any(|target| target == context_ref)
                });
                if !has_direct_restriction {
                    examples.push(generic_validation_example(
                        &path,
                        &format!("{source_ref}->{context_ref}"),
                        "each mapped triple overlap must receive direct restrictions from its three mapped overlap contexts",
                    ));
                }
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
                    let membership_valid = if plan.complex.enumeration_complete {
                        actual_contexts == expected_contexts
                    } else {
                        expected_contexts.is_subset(&actual_contexts)
                    };
                    if !membership_valid {
                        examples.push(generic_validation_example(
                            "complex.archmapCoverRef",
                            &format!("cover={actual_contexts:?}, complex={expected_contexts:?}"),
                            "the mapped ArchMap cover must contain exactly the enumerated chart and intersection contexts when enumerationComplete is true",
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
    for atom_ref in &plan.semantic_projection.lambda {
        if !atom_subjects.contains_key(atom_ref.as_str()) {
            examples.push(generic_validation_example(
                "semanticProjection.lambda",
                atom_ref,
                "RepairPlan lambda entries must resolve to ArchMap atoms",
            ));
        }
    }
    for subject in &plan.semantic_projection.k {
        if !subjects.contains(subject.as_str()) {
            examples.push(generic_validation_example(
                "semanticProjection.k",
                subject,
                "RepairPlan K entries must be ArchMap atom subjects",
            ));
        }
    }
    for row in &plan.semantic_projection.pi {
        match atom_subjects.get(row.atom_ref.as_str()) {
            Some(subject) if *subject == row.subject => {}
            Some(subject) => examples.push(generic_validation_example(
                &format!("semanticProjection.pi[{}].subject", row.atom_ref),
                &row.subject,
                &format!("pi subject must equal ArchMap atom subject {subject}"),
            )),
            None => examples.push(generic_validation_example(
                &format!("semanticProjection.pi[{}].atomRef", row.atom_ref),
                &row.atom_ref,
                "pi atomRef must resolve to an ArchMap atom",
            )),
        }
        if !lambda.contains(row.atom_ref.as_str()) {
            examples.push(generic_validation_example(
                &format!("semanticProjection.pi[{}].atomRef", row.atom_ref),
                &row.atom_ref,
                "pi atomRef must be listed in semanticProjection.lambda",
            ));
        }
        if !k.contains(row.subject.as_str()) {
            examples.push(generic_validation_example(
                &format!("semanticProjection.pi[{}].subject", row.atom_ref),
                &row.subject,
                "pi subject must be listed in semanticProjection.k",
            ));
        }
    }
    examples_check(
        "repair-plan-schema052-archmap-bindings",
        "RepairPlan charts, declared finite-complex mappings, and semantic projection resolve against the supplied ArchMap",
        examples,
    )
}

fn check_measured_residual(
    plan: &RepairPlanDocumentV1,
    residual_packet: Option<&Value>,
) -> ValidationCheck {
    let mut examples = Vec::new();
    if plan.residual.kind == "measured" {
        if plan.residual.packet_ref.is_none() || plan.residual.invariant_ref.is_none() {
            examples.push(generic_validation_example(
                "residual",
                "missing-packet-or-invariant-ref",
                "measured residuals must pin packetRef and invariantRef",
            ));
        }
        if residual_packet.is_none() {
            examples.push(generic_validation_example(
                "--residual-packet",
                "missing",
                "measured residual validation requires the referenced residual packet artifact",
            ));
        }
        if let (Some(packet), Some(packet_ref)) = (residual_packet, &plan.residual.packet_ref) {
            if packet["packetId"].as_str() != Some(packet_ref.as_str()) {
                examples.push(generic_validation_example(
                    "residual.packetRef",
                    packet_ref,
                    "measured residual packetRef must match the supplied residual packet packetId",
                ));
            }
        }
        if let (Some(packet), Some(invariant_ref)) = (residual_packet, &plan.residual.invariant_ref)
        {
            let invariant_found =
                packet["computedInvariants"]
                    .as_array()
                    .is_some_and(|invariants| {
                        invariants.iter().any(|invariant| {
                            invariant["invariantId"].as_str() == Some(invariant_ref)
                        })
                    });
            if !invariant_found {
                examples.push(generic_validation_example(
                    "residual.invariantRef",
                    invariant_ref,
                    "measured residual invariantRef must resolve inside the supplied residual packet computedInvariants",
                ));
            }
        }
    }
    examples_check(
        "repair-plan-schema052-measured-residual-binding",
        "Measured residuals are bound to supplied packet evidence",
        examples,
    )
}

fn check_stage1_mode_and_coefficient(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if !matches!(plan.residual.kind.as_str(), "measured" | "supplied") {
        examples.push(generic_validation_example(
            "residual.kind",
            &plan.residual.kind,
            "Stage 1 RepairPlan residual.kind must be measured or supplied",
        ));
    }
    if !matches!(
        plan.faithfulness.mode.as_str(),
        "complete-support" | "none" | "supplied"
    ) {
        examples.push(generic_validation_example(
            "faithfulness.mode",
            &plan.faithfulness.mode,
            "Stage 1 RepairPlan faithfulness.mode must be complete-support or none; supplied is reserved fail-closed",
        ));
    }
    if !plan.coefficient.is_f2_additive()
        && plan.coefficient.supplied().is_none_or(|coefficient| {
            coefficient.kind != "f2-additive"
                || coefficient.characteristic != 2
                || !coefficient.additive
                || !coefficient.delta_one_after_delta_zero
                || !coefficient.zero_maps_to_zero
        })
    {
        examples.push(generic_validation_example(
            "coefficient",
            &serde_json::to_string(&plan.coefficient).unwrap_or_default(),
            "RepairPlan coefficient must be f2-additive or a checked characteristic-two additive supplied coefficient",
        ));
    }
    examples_check(
        "repair-plan-schema052-stage1-regime",
        "RepairPlan uses the Stage 1 residual, faithfulness, and coefficient vocabulary",
        examples,
    )
}

fn check_restriction_difference_rule(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for primitive in &plan.primitives {
        let expected = symmetric_difference(&primitive.res_l, &primitive.res_r);
        let actual = sorted_set(&primitive.support.variables);
        if expected != actual {
            examples.push(generic_validation_example(
                &format!("primitives[{}].support.variables", primitive.id),
                &format!("{actual:?}"),
                "support.variables must equal the F2 restriction-difference of resL and resR",
            ));
        }
    }
    examples_check(
        "repair-plan-schema052-restriction-difference-rule",
        "Supplied primitives satisfy the restriction-difference rule before use",
        examples,
    )
}

fn check_overlap_primitive_bijection(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let overlap_ids = plan
        .complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut primitive_refs = BTreeMap::<&str, Vec<&str>>::new();
    for primitive in &plan.primitives {
        primitive_refs
            .entry(primitive.overlap_ref.as_str())
            .or_default()
            .push(primitive.id.as_str());
    }
    let mut examples = Vec::new();
    for overlap_id in &overlap_ids {
        match primitive_refs.get(overlap_id).map(Vec::as_slice) {
            Some([_]) => {}
            Some(ids) => examples.push(generic_validation_example(
                &format!("complex.overlaps[{overlap_id}]"),
                &format!("{ids:?}"),
                "each overlap must have exactly one primitive",
            )),
            None => examples.push(generic_validation_example(
                &format!("complex.overlaps[{overlap_id}]"),
                "missing",
                "each overlap must have exactly one primitive",
            )),
        }
    }
    for primitive in &plan.primitives {
        if !overlap_ids.contains(primitive.overlap_ref.as_str()) {
            examples.push(generic_validation_example(
                &format!("primitives[{}].overlapRef", primitive.id),
                &primitive.overlap_ref,
                "primitive overlapRef must resolve to complex.overlaps[].id",
            ));
        }
    }
    examples_check(
        "repair-plan-schema052-overlap-primitive-bijection",
        "Every complex overlap is represented by exactly one primitive before SAGA evaluation",
        examples,
    )
}

fn check_delta_cocycle(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let primitives = plan
        .primitives
        .iter()
        .map(|primitive| (primitive.overlap_ref.as_str(), primitive))
        .collect::<BTreeMap<_, _>>();
    let mut examples = Vec::new();
    for triple in &plan.complex.triple_overlaps {
        let overlap_refs = triple.overlap_refs.iter().collect::<BTreeSet<_>>();
        if triple.overlap_refs.len() != 3 || overlap_refs.len() != 3 {
            examples.push(generic_validation_example(
                &format!("complex.tripleOverlaps[{}].overlapRefs", triple.id),
                &format!("{:?}", triple.overlap_refs),
                "a supplied triple overlap must contain three distinct selected overlap refs",
            ));
            continue;
        }
        let mut parity = BTreeMap::<String, usize>::new();
        for overlap_ref in &triple.overlap_refs {
            if let Some(primitive) = primitives.get(overlap_ref.as_str()) {
                for variable in &primitive.support.variables {
                    *parity.entry(variable.clone()).or_default() += 1;
                }
            }
        }
        let odd = parity
            .into_iter()
            .filter_map(|(variable, count)| (count % 2 == 1).then_some(variable))
            .collect::<Vec<_>>();
        if !odd.is_empty() {
            examples.push(generic_validation_example(
                &format!("complex.tripleOverlaps[{}]", triple.id),
                &format!("{odd:?}"),
                "delta1 residual parity must vanish on supplied triple overlaps",
            ));
        }
    }
    examples_check(
        "repair-plan-schema052-delta-cocycle",
        "Supplied residual satisfies delta1(delta0)=0 and delta1(r)=0 checks",
        examples,
    )
}

fn check_complete_support(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if plan.faithfulness.mode == "complete-support" {
        for primitive in &plan.primitives {
            if primitive.support.kind != "complete" {
                examples.push(generic_validation_example(
                    &format!("primitives[{}].support.kind", primitive.id),
                    &primitive.support.kind,
                    "complete-support mode requires every primitive support.kind to be complete",
                ));
            }
        }
    }
    examples_check(
        "repair-plan-schema052-complete-support-cross-check",
        "Complete-support mode cross-checks every primitive support declaration",
        examples,
    )
}

fn check_enumeration_assumption(plan: &RepairPlanDocumentV1) -> ValidationCheck {
    let mut check = validation_check(
        "repair-plan-schema052-enumeration-assumption",
        "Enumeration completeness is recorded as an author assumption, not verified",
        "warn",
    );
    check.reason = Some(format!(
        "complex.enumerationComplete={} is recorded in the assumption ledger with assumed_by=repair-plan author",
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

fn symmetric_difference(left: &[String], right: &[String]) -> BTreeSet<String> {
    let left = sorted_set(left);
    let right = sorted_set(right);
    left.symmetric_difference(&right).cloned().collect()
}

fn sorted_set(values: &[String]) -> BTreeSet<String> {
    values.iter().cloned().collect()
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
