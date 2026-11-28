//! AAT 第19章後半（多源高次構造衝突の極小列挙・検証後に結論を支える最小由来支持）の検証済み IR
//! （`MultisourceTaskSpec` / `CheckedMultisourceTask`）。

use crate::algebra::hitting_set::{DEFAULT_MAX_HITTING_SET_RESULTS, DEFAULT_MAX_HITTING_SET_STEPS};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::revision::{RevisionConstraintSpec, RevisionCoordSpec, RevisionPredicate};
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_coeff_domain, validate_provenance,
    validate_scalar_lit, validate_source_ref,
};
use std::collections::{BTreeMap, BTreeSet};

/// 多源提示の 1 観測源（由来を混同せず上書きしない、定義 19.8）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourcePresentationSpec {
    pub source_id: String,
    pub origin: SourceRef,
    pub assignments: BTreeMap<String, ScalarLit>,
    /// 明示不在（禁止値）記録 `(coord, forbidden_value)`。
    pub forbidden_values: Vec<(String, ScalarLit)>,
    pub extra_constraints: Vec<RevisionConstraintSpec>,
}

/// 未確認候補記録 $h_i$（設定 19.10）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateRecordSpec {
    pub id: String,
    pub coord: String,
    pub value: ScalarLit,
    /// 任意の非負費用 $c_i$（有理数/整数リテラル）。
    pub cost: Option<ScalarLit>,
    pub origin: SourceRef,
    /// 検証後に候補と異なる結果が得られた場合の実測値（命題 19.12: 改訂スパン再評価用）。
    pub verified_actual_value: Option<ScalarLit>,
}

/// 目標結論 $(\varphi, v)$（例 19.13 等の等式・線形制約）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SupportGoalFormula {
    CoordEquality(String, String),
    CoordEqualsConst(String, ScalarLit),
}

/// 信頼済み提示 $T$・未確認候補 $(h_i)_{i \in I}$・目標結論 $(\varphi, v)$（設定 19.10）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupportGoalSpec {
    pub trusted_assignments: BTreeMap<String, ScalarLit>,
    pub candidates: Vec<CandidateRecordSpec>,
    pub goal: SupportGoalFormula,
    pub expected_truth: bool,
    pub check_post_adoption_stability: bool,
}

/// 多源統合タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultisourceTaskSpec {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub coords: Vec<RevisionCoordSpec>,
    pub background_constraints: Vec<RevisionConstraintSpec>,
    pub sources: Vec<SourcePresentationSpec>,
    pub support_goal: Option<SupportGoalSpec>,
    pub max_sources_subset_steps: usize,
    pub max_results: usize,
    pub provenance: Provenance,
    pub undeclared_unobserved_slots: Vec<String>,
}

/// 検証済みの多源統合タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedMultisourceTask {
    name: String,
    coeff_domain: CoeffDomain,
    coords: Vec<RevisionCoordSpec>,
    background_constraints: Vec<RevisionConstraintSpec>,
    sources: Vec<SourcePresentationSpec>,
    support_goal: Option<SupportGoalSpec>,
    max_sources_subset_steps: usize,
    max_results: usize,
    provenance: Provenance,
    undeclared_unobserved_slots: Vec<String>,
}

impl CheckedMultisourceTask {
    pub fn validate(spec: MultisourceTaskSpec) -> Result<Self, ValidationError> {
        validate_multisource_task(spec)
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn coeff_domain(&self) -> &CoeffDomain {
        &self.coeff_domain
    }

    pub fn coords(&self) -> &[RevisionCoordSpec] {
        &self.coords
    }

    pub fn background_constraints(&self) -> &[RevisionConstraintSpec] {
        &self.background_constraints
    }

    pub fn sources(&self) -> &[SourcePresentationSpec] {
        &self.sources
    }

    pub fn support_goal(&self) -> Option<&SupportGoalSpec> {
        self.support_goal.as_ref()
    }

    pub fn max_sources_subset_steps(&self) -> usize {
        self.max_sources_subset_steps
    }

    pub fn max_results(&self) -> usize {
        self.max_results
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn undeclared_unobserved_slots(&self) -> &[String] {
        &self.undeclared_unobserved_slots
    }
}

pub fn validate_multisource_task(
    mut spec: MultisourceTaskSpec,
) -> Result<CheckedMultisourceTask, ValidationError> {
    require_non_empty(&spec.name, "multisource.name")?;
    validate_provenance(&spec.provenance, &format!("multisource `{}`", spec.name))?;
    validate_coeff_domain(&spec.coeff_domain, &format!("multisource `{}`", spec.name))?;

    if spec.max_sources_subset_steps == 0 {
        spec.max_sources_subset_steps = DEFAULT_MAX_HITTING_SET_STEPS;
    }
    if spec.max_results == 0 {
        spec.max_results = DEFAULT_MAX_HITTING_SET_RESULTS;
    }

    let mut coord_names = BTreeSet::new();
    for c in &spec.coords {
        require_non_empty(&c.id, "multisource.coord.id")?;
        if !coord_names.insert(c.id.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "multisource_coord",
                name: c.id.clone(),
            });
        }
        if c.domain_values.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: format!("multisource coord `{}` has empty domain_values", c.id),
            });
        }
        for v in &c.domain_values {
            validate_scalar_lit(
                v,
                &spec.coeff_domain,
                &format!("multisource coord `{}`", c.id),
            )?;
        }
    }

    for con in &spec.background_constraints {
        validate_ms_constraint(con, &coord_names, &spec.coeff_domain)?;
    }

    let mut source_ids = BTreeSet::new();
    for src in &spec.sources {
        require_non_empty(&src.source_id, "multisource.source.id")?;
        if !source_ids.insert(src.source_id.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "multisource_source",
                name: src.source_id.clone(),
            });
        }
        validate_source_ref(
            &src.origin,
            &format!("multisource source `{}`", src.source_id),
        )?;
        for (c, v) in &src.assignments {
            if !coord_names.contains(c) {
                return Err(ValidationError::UnknownRef {
                    kind: "coord",
                    name: c.clone(),
                    context: format!("source `{}`", src.source_id),
                });
            }
            validate_scalar_lit(
                v,
                &spec.coeff_domain,
                &format!("source `{}`", src.source_id),
            )?;
        }
        for (c, v) in &src.forbidden_values {
            if !coord_names.contains(c) {
                return Err(ValidationError::UnknownRef {
                    kind: "coord",
                    name: c.clone(),
                    context: format!("source `{}` forbidden", src.source_id),
                });
            }
            validate_scalar_lit(
                v,
                &spec.coeff_domain,
                &format!("source `{}`", src.source_id),
            )?;
        }
        for con in &src.extra_constraints {
            validate_ms_constraint(con, &coord_names, &spec.coeff_domain)?;
        }
    }

    if let Some(sg) = &spec.support_goal {
        for (c, v) in &sg.trusted_assignments {
            if !coord_names.contains(c) {
                return Err(ValidationError::UnknownRef {
                    kind: "coord",
                    name: c.clone(),
                    context: "multisource.trusted".to_owned(),
                });
            }
            validate_scalar_lit(v, &spec.coeff_domain, "multisource.trusted")?;
        }
        let mut cand_ids = BTreeSet::new();
        let mut with_cost = 0usize;
        let mut without_cost = 0usize;
        for cand in &sg.candidates {
            require_non_empty(&cand.id, "multisource.candidate.id")?;
            if !cand_ids.insert(cand.id.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "multisource_candidate",
                    name: cand.id.clone(),
                });
            }
            validate_source_ref(
                &cand.origin,
                &format!("multisource candidate `{}`", cand.id),
            )?;
            if !coord_names.contains(&cand.coord) {
                return Err(ValidationError::UnknownRef {
                    kind: "coord",
                    name: cand.coord.clone(),
                    context: format!("candidate `{}`", cand.id),
                });
            }
            validate_scalar_lit(
                &cand.value,
                &spec.coeff_domain,
                &format!("candidate `{}`", cand.id),
            )?;
            if let Some(actual) = &cand.verified_actual_value {
                validate_scalar_lit(
                    actual,
                    &spec.coeff_domain,
                    &format!("candidate `{}` verified_actual_value", cand.id),
                )?;
            }
            if let Some(cost) = &cand.cost {
                with_cost += 1;
                if !is_nonnegative_scalar(cost) {
                    return Err(ValidationError::ConversionError {
                        detail: format!("candidate `{}` cost must be nonnegative", cand.id),
                    });
                }
            } else {
                without_cost += 1;
            }
        }
        if with_cost > 0 && without_cost > 0 {
            return Err(ValidationError::ConversionError {
                detail: "candidates must either all specify `cost` or none specify `cost`"
                    .to_owned(),
            });
        }
        match &sg.goal {
            SupportGoalFormula::CoordEquality(a, b) => {
                for x in [a, b] {
                    if !coord_names.contains(x) {
                        return Err(ValidationError::UnknownRef {
                            kind: "coord",
                            name: x.clone(),
                            context: "multisource.support_goal".to_owned(),
                        });
                    }
                }
            }
            SupportGoalFormula::CoordEqualsConst(c, v) => {
                if !coord_names.contains(c) {
                    return Err(ValidationError::UnknownRef {
                        kind: "coord",
                        name: c.clone(),
                        context: "multisource.support_goal".to_owned(),
                    });
                }
                validate_scalar_lit(v, &spec.coeff_domain, "multisource.support_goal")?;
            }
        }
    }

    Ok(CheckedMultisourceTask {
        name: spec.name,
        coeff_domain: spec.coeff_domain,
        coords: spec.coords,
        background_constraints: spec.background_constraints,
        sources: spec.sources,
        support_goal: spec.support_goal,
        max_sources_subset_steps: spec.max_sources_subset_steps,
        max_results: spec.max_results,
        provenance: spec.provenance,
        undeclared_unobserved_slots: spec.undeclared_unobserved_slots,
    })
}

fn is_nonnegative_scalar(lit: &ScalarLit) -> bool {
    use num_traits::{Signed, Zero};
    match lit {
        ScalarLit::Z(n) => !n.is_negative(),
        ScalarLit::Q { num, den } => !den.is_zero() && !(num.is_negative() ^ den.is_negative()),
        ScalarLit::Fp { .. } => true,
    }
}

fn validate_ms_constraint(
    con: &RevisionConstraintSpec,
    coord_names: &BTreeSet<String>,
    domain: &CoeffDomain,
) -> Result<(), ValidationError> {
    require_non_empty(&con.id, "multisource.constraint.id")?;
    for s in &con.support {
        if !coord_names.contains(s) {
            return Err(ValidationError::UnknownRef {
                kind: "coord",
                name: s.clone(),
                context: format!("constraint `{}` support", con.id),
            });
        }
    }
    match &con.predicate {
        RevisionPredicate::Equality(a, b) => {
            for x in [a, b] {
                if !coord_names.contains(x) {
                    return Err(ValidationError::UnknownRef {
                        kind: "coord",
                        name: x.clone(),
                        context: format!("constraint `{}`", con.id),
                    });
                }
            }
        }
        RevisionPredicate::LinearZero { terms } => {
            for (c, x) in terms {
                validate_scalar_lit(c, domain, &format!("constraint `{}`", con.id))?;
                if !coord_names.contains(x) {
                    return Err(ValidationError::UnknownRef {
                        kind: "coord",
                        name: x.clone(),
                        context: format!("constraint `{}`", con.id),
                    });
                }
            }
        }
        RevisionPredicate::AllowedTuples { coords, tuples } => {
            for x in coords {
                if !coord_names.contains(x) {
                    return Err(ValidationError::UnknownRef {
                        kind: "coord",
                        name: x.clone(),
                        context: format!("constraint `{}`", con.id),
                    });
                }
            }
            for tup in tuples {
                if tup.len() != coords.len() {
                    return Err(ValidationError::ArityMismatch {
                        context: format!("constraint `{}` tuple", con.id),
                        expected: coords.len(),
                        actual: tup.len(),
                    });
                }
                for v in tup {
                    validate_scalar_lit(v, domain, &format!("constraint `{}`", con.id))?;
                }
            }
        }
    }
    Ok(())
}
