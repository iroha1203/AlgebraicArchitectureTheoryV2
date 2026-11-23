//! 頑健判定（`RobustnessTaskSpec` / `CheckedRobustnessTask`）と
//! Chevalley 四分類（`ChevalleyTaskSpec` / `CheckedChevalleyTask`）の IR。

use crate::ir::change::PointDomain;
use crate::ir::family::{CandidateSpace, CheckedFamilySpec, FamilySpec};
use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_provenance, validate_scalar_lit,
};
use crate::ir::validate_change::validate_point_domain_compatibility;
use std::collections::{BTreeMap, BTreeSet};

/// 共有規則候補 $c \in C_b$ の明示指定方法。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CandidateSelector {
    ById(String),
    ByValues(BTreeMap<String, ScalarLit>),
}

/// 複数解釈族上の 3 量化・全係数移送 $\mathcal{R}(R)$・reading 比較タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RobustnessTaskSpec {
    pub name: String,
    pub family: FamilySpec,
    pub point_domain: PointDomain,
    pub base_value: Vec<ScalarLit>,
    pub designated_candidate: Option<CandidateSelector>,
    pub check_universal_ring: bool,
    pub fine_base_value: Option<Vec<ScalarLit>>,
    pub provenance: Provenance,
}

/// 検証済みの頑健判定タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedRobustnessTask {
    name: String,
    family: CheckedFamilySpec,
    point_domain: PointDomain,
    base_value: Vec<ScalarLit>,
    designated_candidate: Option<CandidateSelector>,
    check_universal_ring: bool,
    fine_base_value: Option<Vec<ScalarLit>>,
    provenance: Provenance,
}

impl CheckedRobustnessTask {
    pub fn validate(spec: RobustnessTaskSpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "robustness_task.name")?;
        validate_provenance(&spec.provenance, &format!("robustness `{}`", spec.name))?;
        let family = CheckedFamilySpec::validate(spec.family)?;
        let coeff_domain = family.coeff_domain();
        validate_point_domain_compatibility(coeff_domain, &spec.point_domain)?;

        validate_base_vec(
            &spec.base_value,
            family.b_vars().len(),
            coeff_domain,
            &format!("robustness `{}` base_value", spec.name),
        )?;
        if let Some(sel) = &spec.designated_candidate {
            validate_candidate_selector(sel, &family, &spec.name)?;
        }
        if let Some(fine_val) = &spec.fine_base_value {
            let Some(rc) = family.reading_comparison() else {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "robustness `{}` specifies `fine_base_value` without `reading_comparison` on family `{}`",
                        spec.name,
                        family.inner().name
                    ),
                });
            };
            validate_base_vec(
                fine_val,
                rc.fine_b_vars.len(),
                coeff_domain,
                &format!("robustness `{}` fine_base_value", spec.name),
            )?;
        }

        Ok(Self {
            name: spec.name,
            family,
            point_domain: spec.point_domain,
            base_value: spec.base_value,
            designated_candidate: spec.designated_candidate,
            check_universal_ring: spec.check_universal_ring,
            fine_base_value: spec.fine_base_value,
            provenance: spec.provenance,
        })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn family(&self) -> &CheckedFamilySpec {
        &self.family
    }

    pub fn point_domain(&self) -> &PointDomain {
        &self.point_domain
    }

    pub fn base_value(&self) -> &[ScalarLit] {
        &self.base_value
    }

    pub fn designated_candidate(&self) -> Option<&CandidateSelector> {
        self.designated_candidate.as_ref()
    }

    pub fn check_universal_ring(&self) -> bool {
        self.check_universal_ring
    }

    pub fn fine_base_value(&self) -> Option<&[ScalarLit]> {
        self.fine_base_value.as_deref()
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn unobserved_slots(&self) -> Vec<String> {
        self.family.unobserved_slots()
    }
}

/// 幾何点分類と対比する有理点 fiber の独立プローブ（例: W5 $t = 2$ 上の平方根有理点 fiber）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalFiberProbe {
    pub name: String,
    pub u_assignments: BTreeMap<String, ScalarLit>,
    pub c_assignments: BTreeMap<String, ScalarLit>,
}

/// 構成可能像（G-141 D6）および Chevalley 四分類（G-141 D7 / G-142 G7）タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChevalleyTaskSpec {
    pub name: String,
    pub family: FamilySpec,
    /// Chevalley 四分類は代数閉包上の幾何点分類であるため `PointDomain::AlgebraicClosure` のみを許す。
    pub point_domain: PointDomain,
    pub base_value: Option<Vec<ScalarLit>>,
    pub designated_candidate: Option<CandidateSelector>,
    pub rational_fiber_probes: Vec<RationalFiberProbe>,
    pub check_global_regular_section: bool,
    pub check_universal_ring: bool,
    pub provenance: Provenance,
}

/// 検証済みの Chevalley 四分類タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedChevalleyTask {
    name: String,
    family: CheckedFamilySpec,
    point_domain: PointDomain,
    base_value: Option<Vec<ScalarLit>>,
    designated_candidate: Option<CandidateSelector>,
    rational_fiber_probes: Vec<RationalFiberProbe>,
    check_global_regular_section: bool,
    check_universal_ring: bool,
    provenance: Provenance,
}

impl CheckedChevalleyTask {
    pub fn validate(spec: ChevalleyTaskSpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "chevalley_task.name")?;
        validate_provenance(&spec.provenance, &format!("chevalley `{}`", spec.name))?;
        let family = CheckedFamilySpec::validate(spec.family)?;
        let coeff_domain = family.coeff_domain();

        if spec.point_domain != PointDomain::AlgebraicClosure {
            return Err(ValidationError::PointDomainMismatch {
                coeff_domain: coeff_domain.clone(),
                point_domain: spec.point_domain,
            });
        }
        validate_point_domain_compatibility(coeff_domain, &spec.point_domain)?;

        if let Some(bv) = &spec.base_value {
            validate_base_vec(
                bv,
                family.b_vars().len(),
                coeff_domain,
                &format!("chevalley `{}` base_value", spec.name),
            )?;
        }
        if let Some(sel) = &spec.designated_candidate {
            validate_candidate_selector(sel, &family, &spec.name)?;
        }

        let u_set: BTreeSet<&str> = family.u_vars().iter().map(String::as_str).collect();
        let c_set: BTreeSet<&str> = family.c_vars().iter().map(String::as_str).collect();
        let mut probe_names = BTreeSet::new();
        for probe in &spec.rational_fiber_probes {
            require_non_empty(&probe.name, "chevalley.rational_fiber_probe.name")?;
            if !probe_names.insert(probe.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "rational_fiber_probe",
                    name: probe.name.clone(),
                });
            }
            for (k, lit) in &probe.u_assignments {
                if !u_set.contains(k.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "realization variable",
                        name: k.clone(),
                        context: format!("chevalley `{}` probe `{}`", spec.name, probe.name),
                    });
                }
                validate_scalar_lit(lit, coeff_domain, &format!("probe `{}`.{k}", probe.name))?;
            }
            for (k, lit) in &probe.c_assignments {
                if !c_set.contains(k.as_str()) {
                    return Err(ValidationError::UnknownRef {
                        kind: "candidate variable",
                        name: k.clone(),
                        context: format!("chevalley `{}` probe `{}`", spec.name, probe.name),
                    });
                }
                validate_scalar_lit(lit, coeff_domain, &format!("probe `{}`.{k}", probe.name))?;
            }
        }

        Ok(Self {
            name: spec.name,
            family,
            point_domain: spec.point_domain,
            base_value: spec.base_value,
            designated_candidate: spec.designated_candidate,
            rational_fiber_probes: spec.rational_fiber_probes,
            check_global_regular_section: spec.check_global_regular_section,
            check_universal_ring: spec.check_universal_ring,
            provenance: spec.provenance,
        })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn family(&self) -> &CheckedFamilySpec {
        &self.family
    }

    pub fn point_domain(&self) -> &PointDomain {
        &self.point_domain
    }

    pub fn base_value(&self) -> Option<&[ScalarLit]> {
        self.base_value.as_deref()
    }

    pub fn designated_candidate(&self) -> Option<&CandidateSelector> {
        self.designated_candidate.as_ref()
    }

    pub fn rational_fiber_probes(&self) -> &[RationalFiberProbe] {
        &self.rational_fiber_probes
    }

    pub fn check_global_regular_section(&self) -> bool {
        self.check_global_regular_section
    }

    pub fn check_universal_ring(&self) -> bool {
        self.check_universal_ring
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn unobserved_slots(&self) -> Vec<String> {
        self.family.unobserved_slots()
    }
}

pub(crate) fn validate_base_vec(
    values: &[ScalarLit],
    expected_len: usize,
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<(), ValidationError> {
    if values.len() != expected_len {
        return Err(ValidationError::ArityMismatch {
            context: context.to_owned(),
            expected: expected_len,
            actual: values.len(),
        });
    }
    for (i, lit) in values.iter().enumerate() {
        validate_scalar_lit(lit, coeff_domain, &format!("{context}[{i}]"))?;
    }
    Ok(())
}

pub(crate) fn validate_candidate_selector(
    selector: &CandidateSelector,
    family: &CheckedFamilySpec,
    context: &str,
) -> Result<(), ValidationError> {
    match selector {
        CandidateSelector::ById(id) => {
            require_non_empty(id, "candidate_selector.id")?;
            match &family.inner().candidates.space {
                CandidateSpace::FiniteMembers(members) if members.iter().any(|m| m.id == *id) => {
                    Ok(())
                }
                _ => Err(ValidationError::UnknownRef {
                    kind: "candidate member",
                    name: id.clone(),
                    context: format!("designated_candidate in `{context}`"),
                }),
            }
        }
        CandidateSelector::ByValues(map) => {
            let c_vars = family.c_vars();
            if map.len() != c_vars.len() || !c_vars.iter().all(|v| map.contains_key(v)) {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "designated_candidate values in `{context}` must assign all candidate variables {:?}",
                        c_vars
                    ),
                });
            }
            for (k, lit) in map {
                validate_scalar_lit(
                    lit,
                    family.coeff_domain(),
                    &format!("{context}.candidate.{k}"),
                )?;
            }
            Ok(())
        }
    }
}
