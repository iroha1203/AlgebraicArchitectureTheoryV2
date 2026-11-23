//! 追加観測の kernel 条件検査・全包含極小十分観測列挙タスクの IR
//! （`ObservationTaskSpec` / `CheckedObservationTask`、G-142 G5–G6 / W4・W6）。

use crate::ir::change::{NamedPoly, PointDomain};
use crate::ir::family::{CheckedFamilySpec, FamilySpec};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::robustness::validate_base_vec;
use crate::ir::term::ScalarLit;
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_provenance, validate_source_ref,
};
use crate::ir::validate_change::{validate_named_polys, validate_point_domain_compatibility};
use num_bigint::BigInt;
use std::collections::BTreeSet;

/// 追加観測候補 $e_i: U \to V_i$ の宣言（応用側の任意費用 `cost` は包含極小判定と分離保持）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateObservationDecl {
    pub id: String,
    pub components: Vec<NamedPoly>,
    pub cost: Option<BigInt>,
    pub origin: SourceRef,
}

/// 元の Law readout への adequacy と保存判定 $\chi_E$ への adequacy を区別比較するための readout 仕様（W6）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawReadoutSpec {
    pub name: String,
    pub components: Vec<NamedPoly>,
    pub provenance: Provenance,
}

/// 追加観測充足性・全包含極小列挙タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservationTaskSpec {
    pub name: String,
    pub family: FamilySpec,
    pub point_domain: PointDomain,
    pub base_value: Vec<ScalarLit>,
    pub observations: Vec<CandidateObservationDecl>,
    pub law_readout: Option<LawReadoutSpec>,
    pub provenance: Provenance,
}

/// 検証済みの追加観測タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedObservationTask {
    name: String,
    family: CheckedFamilySpec,
    point_domain: PointDomain,
    base_value: Vec<ScalarLit>,
    observations: Vec<CandidateObservationDecl>,
    law_readout: Option<LawReadoutSpec>,
    provenance: Provenance,
}

impl CheckedObservationTask {
    pub fn validate(spec: ObservationTaskSpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "observation_task.name")?;
        validate_provenance(&spec.provenance, &format!("observations `{}`", spec.name))?;
        let family = CheckedFamilySpec::validate(spec.family)?;
        let coeff_domain = family.coeff_domain();
        validate_point_domain_compatibility(coeff_domain, &spec.point_domain)?;

        validate_base_vec(
            &spec.base_value,
            family.b_vars().len(),
            coeff_domain,
            &format!("observations `{}` base_value", spec.name),
        )?;

        let u_set: BTreeSet<String> = family.u_vars().iter().cloned().collect();
        let mut seen_ids = BTreeSet::new();
        let mut with_cost = 0usize;
        let mut without_cost = 0usize;

        for obs in &spec.observations {
            require_non_empty(&obs.id, "observation.id")?;
            if !seen_ids.insert(obs.id.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "observation candidate",
                    name: obs.id.clone(),
                });
            }
            validate_source_ref(&obs.origin, &format!("observation `{}`", obs.id))?;
            if obs.components.is_empty() {
                return Err(ValidationError::EmptyObservation {
                    phase: spec.name.clone(),
                    observation: obs.id.clone(),
                });
            }
            validate_named_polys(
                &obs.components,
                "observation_component",
                coeff_domain,
                &u_set,
            )?;
            if let Some(cost) = &obs.cost {
                if cost.sign() == num_bigint::Sign::Minus {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "observation `{}` in `{}` cannot have negative cost ({cost})",
                            obs.id, spec.name
                        ),
                    });
                }
                with_cost += 1;
            } else {
                without_cost += 1;
            }
        }

        if with_cost > 0 && without_cost > 0 {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "observations task `{}` must either specify `cost` on every observation or on none",
                    spec.name
                ),
            });
        }

        if let Some(readout) = &spec.law_readout {
            require_non_empty(&readout.name, "law_readout.name")?;
            validate_provenance(
                &readout.provenance,
                &format!("law_readout `{}`", readout.name),
            )?;
            if readout.components.is_empty() {
                return Err(ValidationError::EmptyObservation {
                    phase: spec.name.clone(),
                    observation: readout.name.clone(),
                });
            }
            validate_named_polys(
                &readout.components,
                "law_readout_component",
                coeff_domain,
                &u_set,
            )?;
        }

        Ok(Self {
            name: spec.name,
            family,
            point_domain: spec.point_domain,
            base_value: spec.base_value,
            observations: spec.observations,
            law_readout: spec.law_readout,
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

    pub fn observations(&self) -> &[CandidateObservationDecl] {
        &self.observations
    }

    pub fn law_readout(&self) -> Option<&LawReadoutSpec> {
        self.law_readout.as_ref()
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn unobserved_slots(&self) -> Vec<String> {
        let mut slots: BTreeSet<String> = self.family.unobserved_slots().into_iter().collect();
        for obs in &self.observations {
            for comp in &obs.components {
                comp.expr.collect_unobserved(&mut slots);
            }
        }
        if let Some(lr) = &self.law_readout {
            for comp in &lr.components {
                comp.expr.collect_unobserved(&mut slots);
            }
        }
        slots.into_iter().collect()
    }
}
