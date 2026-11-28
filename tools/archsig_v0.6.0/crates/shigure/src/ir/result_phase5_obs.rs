//! Phase 5 第17章・第18章（`OccurrenceOutcomeDetail`・`PartialOutcomeDetail`）の結果詳細型。

use crate::ir::result::ReevalCheck;
use archsig_common::canonical::{Json, JsonObject};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceCollisionDetail {
    pub kind: String,
    pub detail: String,
    pub derivation_steps: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeparatingContextDetail {
    pub sort: String,
    pub lhs: String,
    pub rhs: String,
    pub context_expr: String,
    pub lhs_value: Option<String>,
    pub rhs_value: Option<String>,
    pub verified: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttributeRealizationDetail {
    pub eval_separation_kappa: BTreeMap<String, usize>,
    pub sound_identification_exists: bool,
    pub minimal_sound_kappa_tuples: Vec<BTreeMap<String, usize>>,
    /// sort -> (occurrence -> auxiliary attribute value)
    pub selected_attribute_assignment: BTreeMap<String, BTreeMap<String, usize>>,
    pub failure_reason: Option<String>,
    pub reevaluation: Option<ReevalCheck>,
}

/// `shigure_occurrence`（第17章）の計算詳細結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceOutcomeDetail {
    pub minimal_functional_classes: BTreeMap<String, Vec<Vec<String>>>,
    pub collisions: Vec<OccurrenceCollisionDetail>,
    pub derivation_verified: bool,
    pub context_closed_17_5: bool,
    pub context_equivalence_classes: BTreeMap<String, Vec<Vec<String>>>,
    pub separating_contexts: Vec<SeparatingContextDetail>,
    pub sound_identifications_count: Option<usize>,
    pub coarsest_sound_exists: bool,
    pub coarsest_sound_classes: Option<BTreeMap<String, Vec<Vec<String>>>>,
    pub attribute_realization: Option<AttributeRealizationDetail>,
}

impl OccurrenceOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mfc = classes_to_json(&self.minimal_functional_classes);
        let cec = classes_to_json(&self.context_equivalence_classes);
        let collisions = self
            .collisions
            .iter()
            .map(|c| {
                Json::obj([
                    ("kind", Json::str(&c.kind)),
                    ("detail", Json::str(&c.detail)),
                    (
                        "derivation_steps",
                        Json::Arr(c.derivation_steps.iter().map(Json::str).collect()),
                    ),
                ])
            })
            .collect();
        let seps = self
            .separating_contexts
            .iter()
            .map(|s| {
                let mut o = JsonObject::from([
                    ("sort".into(), Json::str(&s.sort)),
                    ("lhs".into(), Json::str(&s.lhs)),
                    ("rhs".into(), Json::str(&s.rhs)),
                    ("context_expr".into(), Json::str(&s.context_expr)),
                    ("verified".into(), Json::Bool(s.verified)),
                ]);
                if let Some(v) = &s.lhs_value {
                    o.insert("lhs_value".into(), Json::str(v));
                }
                if let Some(v) = &s.rhs_value {
                    o.insert("rhs_value".into(), Json::str(v));
                }
                Json::Obj(o)
            })
            .collect();

        let mut obj = JsonObject::from([
            ("minimal_functional_classes".into(), mfc),
            ("collisions".into(), Json::Arr(collisions)),
            (
                "derivation_verified".into(),
                Json::Bool(self.derivation_verified),
            ),
            (
                "context_closed_17_5".into(),
                Json::Bool(self.context_closed_17_5),
            ),
            ("context_equivalence_classes".into(), cec),
            ("separating_contexts".into(), Json::Arr(seps)),
            (
                "coarsest_sound_exists".into(),
                Json::Bool(self.coarsest_sound_exists),
            ),
        ]);
        if let Some(cnt) = self.sound_identifications_count {
            obj.insert("sound_identifications_count".into(), Json::Nat(cnt as u64));
        }
        if let Some(coarsest) = &self.coarsest_sound_classes {
            obj.insert("coarsest_sound_classes".into(), classes_to_json(coarsest));
        }
        if let Some(attr) = &self.attribute_realization {
            let eval_k = attr
                .eval_separation_kappa
                .iter()
                .map(|(k, v)| (k.clone(), Json::Nat(*v as u64)))
                .collect();
            let min_tuples = attr
                .minimal_sound_kappa_tuples
                .iter()
                .map(|m| {
                    Json::Obj(
                        m.iter()
                            .map(|(k, v)| (k.clone(), Json::Nat(*v as u64)))
                            .collect(),
                    )
                })
                .collect();
            let assign = attr
                .selected_attribute_assignment
                .iter()
                .map(|(s, map)| {
                    (
                        s.clone(),
                        Json::Obj(
                            map.iter()
                                .map(|(e, v)| (e.clone(), Json::Nat(*v as u64)))
                                .collect(),
                        ),
                    )
                })
                .collect();
            let mut ao = JsonObject::from([
                ("eval_separation_kappa".into(), Json::Obj(eval_k)),
                (
                    "sound_identification_exists".into(),
                    Json::Bool(attr.sound_identification_exists),
                ),
                ("minimal_sound_kappa_tuples".into(), Json::Arr(min_tuples)),
                ("selected_attribute_assignment".into(), Json::Obj(assign)),
            ]);
            if let Some(reason) = &attr.failure_reason {
                ao.insert("failure_reason".into(), Json::str(reason));
            }
            if let Some(re) = &attr.reevaluation {
                ao.insert("reevaluation".into(), re.to_json());
            }
            obj.insert("attribute_realization".into(), Json::Obj(ao));
        }
        Json::Obj(obj)
    }
}

fn classes_to_json(classes: &BTreeMap<String, Vec<Vec<String>>>) -> Json {
    Json::Obj(
        classes
            .iter()
            .map(|(s, cls)| {
                let arr = cls
                    .iter()
                    .map(|c| Json::Arr(c.iter().map(Json::str).collect()))
                    .collect();
                (s.clone(), Json::Arr(arr))
            })
            .collect(),
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialLawEvalSummary {
    pub law_name: String,
    pub strong_kleene: String,
    pub supervaluation: String,
    pub antecedent_regime: Option<String>,
    pub conditional_conclusion_eval: Option<String>,
    pub affine_normalized_eval: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantifierHierarchyDetail {
    pub e_holds: bool,
    pub u_holds: bool,
    pub g_holds: bool,
    pub q_holds: bool,
    pub g_iff_u_and_q_verified: bool,
    pub required_slot_sets: Vec<Vec<String>>,
    pub insufficiency_witness: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenDomainResultDetail {
    pub is_full_substructure: bool,
    pub all_fibers_locally_exhaustive: bool,
    pub uncovered_fibers: Vec<String>,
    pub sub_law_eval: String,
    pub ambient_law_eval: String,
    pub positive_preserved: bool,
    pub law_evaluations_match: bool,
    pub affine_unique_repair_exists: Option<bool>,
    pub affine_image_dim: Option<usize>,
    pub affine_fiber_dim: Option<usize>,
    pub reevaluation: Option<ReevalCheck>,
}

/// `shigure_partial`（第18章）の計算詳細結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialOutcomeDetail {
    pub completion_consistent: bool,
    pub completion_count: Option<usize>,
    pub minimal_inconsistent_subsets: Vec<Vec<String>>,
    pub mus_verified: bool,
    pub law_evaluations: Vec<PartialLawEvalSummary>,
    pub kleene_soundness_verified: bool,
    pub quantifier_hierarchy: Option<QuantifierHierarchyDetail>,
    pub open_domain: Option<OpenDomainResultDetail>,
}

impl PartialOutcomeDetail {
    pub fn to_json(&self) -> Json {
        let mus = self
            .minimal_inconsistent_subsets
            .iter()
            .map(|m| Json::Arr(m.iter().map(Json::str).collect()))
            .collect();
        let laws = self
            .law_evaluations
            .iter()
            .map(|l| {
                let mut lo = JsonObject::from([
                    ("law_name".into(), Json::str(&l.law_name)),
                    ("strong_kleene".into(), Json::str(&l.strong_kleene)),
                    ("supervaluation".into(), Json::str(&l.supervaluation)),
                ]);
                if let Some(reg) = &l.antecedent_regime {
                    lo.insert("antecedent_regime".into(), Json::str(reg));
                }
                if let Some(cond) = &l.conditional_conclusion_eval {
                    lo.insert("conditional_conclusion_eval".into(), Json::str(cond));
                }
                if let Some(aff) = &l.affine_normalized_eval {
                    lo.insert("affine_normalized_eval".into(), Json::str(aff));
                }
                Json::Obj(lo)
            })
            .collect();

        let mut obj = JsonObject::from([
            (
                "completion_consistent".into(),
                Json::Bool(self.completion_consistent),
            ),
            ("minimal_inconsistent_subsets".into(), Json::Arr(mus)),
            ("mus_verified".into(), Json::Bool(self.mus_verified)),
            ("law_evaluations".into(), Json::Arr(laws)),
            (
                "kleene_soundness_verified".into(),
                Json::Bool(self.kleene_soundness_verified),
            ),
        ]);
        if let Some(cnt) = self.completion_count {
            obj.insert("completion_count".into(), Json::Nat(cnt as u64));
        }
        if let Some(q) = &self.quantifier_hierarchy {
            let mut qo = JsonObject::from([
                ("E".into(), Json::Bool(q.e_holds)),
                ("U".into(), Json::Bool(q.u_holds)),
                ("G".into(), Json::Bool(q.g_holds)),
                ("Q".into(), Json::Bool(q.q_holds)),
                (
                    "g_iff_u_and_q_verified".into(),
                    Json::Bool(q.g_iff_u_and_q_verified),
                ),
                (
                    "required_slot_sets".into(),
                    Json::Arr(
                        q.required_slot_sets
                            .iter()
                            .map(|s| Json::Arr(s.iter().map(Json::str).collect()))
                            .collect(),
                    ),
                ),
            ]);
            if let Some(w) = &q.insufficiency_witness {
                qo.insert("insufficiency_witness".into(), Json::str(w));
            }
            obj.insert("quantifier_hierarchy".into(), Json::Obj(qo));
        }
        if let Some(od) = &self.open_domain {
            let mut oo = JsonObject::from([
                (
                    "is_full_substructure".into(),
                    Json::Bool(od.is_full_substructure),
                ),
                (
                    "all_fibers_locally_exhaustive".into(),
                    Json::Bool(od.all_fibers_locally_exhaustive),
                ),
                (
                    "uncovered_fibers".into(),
                    Json::Arr(od.uncovered_fibers.iter().map(Json::str).collect()),
                ),
                ("sub_law_eval".into(), Json::str(&od.sub_law_eval)),
                ("ambient_law_eval".into(), Json::str(&od.ambient_law_eval)),
                (
                    "positive_preserved".into(),
                    Json::Bool(od.positive_preserved),
                ),
                (
                    "law_evaluations_match".into(),
                    Json::Bool(od.law_evaluations_match),
                ),
            ]);
            if let Some(u) = od.affine_unique_repair_exists {
                oo.insert("affine_unique_repair_exists".into(), Json::Bool(u));
            }
            if let Some(d) = od.affine_image_dim {
                oo.insert("affine_image_dim".into(), Json::Nat(d as u64));
            }
            if let Some(d) = od.affine_fiber_dim {
                oo.insert("affine_fiber_dim".into(), Json::Nat(d as u64));
            }
            if let Some(re) = &od.reevaluation {
                oo.insert("reevaluation".into(), re.to_json());
            }
            obj.insert("open_domain".into(), Json::Obj(oo));
        }
        Json::Obj(obj)
    }
}
