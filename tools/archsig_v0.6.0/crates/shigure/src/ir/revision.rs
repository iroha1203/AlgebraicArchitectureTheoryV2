//! AAT 第19章前半（追記 vs 改訂スパン・無効化錐 $\operatorname{Cone}(\Delta)$・作用素/右辺分離 SNF 再利用）の検証済み IR
//! （`RevisionTaskSpec` / `CheckedRevisionTask`）。

use crate::ir::provenance::Provenance;
use crate::ir::term::{CoeffDomain, ScalarLit};
use crate::ir::validate::{
    ValidationError, require_non_empty, validate_coeff_domain, validate_provenance,
    validate_scalar_lit,
};
use std::collections::{BTreeMap, BTreeSet};

/// 追記（$P_1 \hookrightarrow P_2$）と改訂スパン（$P_1 \hookleftarrow P_0 \hookrightarrow P_2$）の区別（定義 19.1）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RevisionKind {
    Extension,
    Span,
}

/// 原始座標 $\lambda \in \Lambda$（設定 19.3）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionCoordSpec {
    pub id: String,
    pub domain_values: Vec<ScalarLit>,
}

/// 支持 $S_c \subseteq \Lambda$ を持つ構造制約述語。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RevisionPredicate {
    Equality(String, String),
    LinearZero {
        terms: Vec<(ScalarLit, String)>,
    },
    AllowedTuples {
        coords: Vec<String>,
        tuples: Vec<Vec<ScalarLit>>,
    },
}

/// 構造制約（一価性・全域性・共有スロット・参照候補等）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionConstraintSpec {
    pub id: String,
    pub support: Vec<String>,
    pub predicate: RevisionPredicate,
}

/// $P_1$ または $P_2$ 側の部分提示仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionSideSpec {
    pub assignments: BTreeMap<String, ScalarLit>,
    pub extra_constraints: Vec<RevisionConstraintSpec>,
}

/// 錐外または追記で保存を調べる局所評価プローブ（例: `eta == 0`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionEvalProbe {
    pub name: String,
    pub support: Vec<String>,
    pub target_coord: String,
    pub expected_value: ScalarLit,
    /// 条件付き Law の適用区分確認用（任意: `antecedent_coord == antecedent_value`）。
    pub antecedent_coord: Option<String>,
    pub antecedent_value: Option<ScalarLit>,
}

/// 作用素と右辺を分離した SNF 修復再利用仕様（補題 19.6・定理 19.7）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnfRevisionSpec {
    pub coeff_domain: CoeffDomain,
    pub m_before: Vec<Vec<ScalarLit>>,
    pub m_after: Vec<Vec<ScalarLit>>,
    pub num_cols: usize,
    pub rhs_before: Vec<ScalarLit>,
    pub rhs_after: Vec<ScalarLit>,
    /// 作用素を決める部分提示 $P_{\mathrm{op}}$ が共通部分 $P_0$ に残るか。
    pub op_in_common_p0: bool,
    /// 共通部分 $P_0$ から作用素が一意に定まるか。
    pub op_uniquely_determined: bool,
    /// 作用素改訂時に既存分解の再利用を強制指定したか（true かつ作用素変化なら再利用拒否で `undetermined`）。
    pub force_reuse_existing_snf: bool,
    /// 由来ラベルのみの改訂か。
    pub origin_label_only: bool,
}

/// 観測改訂・無効化錐・SNF 再利用タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionTaskSpec {
    pub name: String,
    pub kind: RevisionKind,
    pub coeff_domain: CoeffDomain,
    pub coords: Vec<RevisionCoordSpec>,
    pub shared_constraints: Vec<RevisionConstraintSpec>,
    pub before: RevisionSideSpec,
    pub after: RevisionSideSpec,
    /// 改訂対象として明示マークされた座標・制約支持の初期集合 $\Delta$。
    pub explicit_delta_coords: Vec<String>,
    pub probes: Vec<RevisionEvalProbe>,
    pub snf_spec: Option<SnfRevisionSpec>,
    pub max_completions: usize,
    pub provenance: Provenance,
    pub undeclared_unobserved_slots: Vec<String>,
}

/// 検証済みの観測改訂タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedRevisionTask {
    name: String,
    kind: RevisionKind,
    coeff_domain: CoeffDomain,
    coords: Vec<RevisionCoordSpec>,
    shared_constraints: Vec<RevisionConstraintSpec>,
    before: RevisionSideSpec,
    after: RevisionSideSpec,
    explicit_delta_coords: Vec<String>,
    probes: Vec<RevisionEvalProbe>,
    snf_spec: Option<SnfRevisionSpec>,
    max_completions: usize,
    provenance: Provenance,
    undeclared_unobserved_slots: Vec<String>,
}

impl CheckedRevisionTask {
    pub fn validate(spec: RevisionTaskSpec) -> Result<Self, ValidationError> {
        validate_revision_task(spec)
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kind(&self) -> RevisionKind {
        self.kind
    }

    pub fn coeff_domain(&self) -> &CoeffDomain {
        &self.coeff_domain
    }

    pub fn coords(&self) -> &[RevisionCoordSpec] {
        &self.coords
    }

    pub fn shared_constraints(&self) -> &[RevisionConstraintSpec] {
        &self.shared_constraints
    }

    pub fn before(&self) -> &RevisionSideSpec {
        &self.before
    }

    pub fn after(&self) -> &RevisionSideSpec {
        &self.after
    }

    pub fn explicit_delta_coords(&self) -> &[String] {
        &self.explicit_delta_coords
    }

    pub fn probes(&self) -> &[RevisionEvalProbe] {
        &self.probes
    }

    pub fn snf_spec(&self) -> Option<&SnfRevisionSpec> {
        self.snf_spec.as_ref()
    }

    pub fn max_completions(&self) -> usize {
        self.max_completions
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn undeclared_unobserved_slots(&self) -> &[String] {
        &self.undeclared_unobserved_slots
    }
}

pub const DEFAULT_MAX_REVISION_COMPLETIONS: usize = 4_096;

pub fn validate_revision_task(
    mut spec: RevisionTaskSpec,
) -> Result<CheckedRevisionTask, ValidationError> {
    require_non_empty(&spec.name, "revision.name")?;
    validate_provenance(&spec.provenance, &format!("revision `{}`", spec.name))?;
    validate_coeff_domain(&spec.coeff_domain, &format!("revision `{}`", spec.name))?;
    if spec.max_completions == 0 {
        spec.max_completions = DEFAULT_MAX_REVISION_COMPLETIONS;
    }

    let mut coord_names = BTreeSet::new();
    for c in &spec.coords {
        require_non_empty(&c.id, "revision.coord.id")?;
        if !coord_names.insert(c.id.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "revision_coord",
                name: c.id.clone(),
            });
        }
        if c.domain_values.is_empty() {
            return Err(ValidationError::ConversionError {
                detail: format!("revision coord `{}` has empty domain_values", c.id),
            });
        }
        for v in &c.domain_values {
            validate_scalar_lit(v, &spec.coeff_domain, &format!("revision coord `{}`", c.id))?;
        }
    }

    for con in spec
        .shared_constraints
        .iter()
        .chain(&spec.before.extra_constraints)
        .chain(&spec.after.extra_constraints)
    {
        validate_constraint(con, &coord_names, &spec.coeff_domain)?;
    }

    for (k, v) in spec
        .before
        .assignments
        .iter()
        .chain(&spec.after.assignments)
    {
        if !coord_names.contains(k) {
            return Err(ValidationError::UnknownRef {
                kind: "coord",
                name: k.clone(),
                context: "revision.assignment".to_owned(),
            });
        }
        validate_scalar_lit(v, &spec.coeff_domain, &format!("revision assignment `{k}`"))?;
    }

    for d in &spec.explicit_delta_coords {
        if !coord_names.contains(d) {
            return Err(ValidationError::UnknownRef {
                kind: "coord",
                name: d.clone(),
                context: "revision.explicit_delta_coords".to_owned(),
            });
        }
    }

    for p in &spec.probes {
        require_non_empty(&p.name, "revision.probe.name")?;
        if !coord_names.contains(&p.target_coord) {
            return Err(ValidationError::UnknownRef {
                kind: "coord",
                name: p.target_coord.clone(),
                context: format!("revision probe `{}`", p.name),
            });
        }
        let mut probe_sup = BTreeSet::new();
        for s in &p.support {
            if !coord_names.contains(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "coord",
                    name: s.clone(),
                    context: format!("revision probe `{}` support", p.name),
                });
            }
            probe_sup.insert(s.as_str());
        }
        if !probe_sup.contains(p.target_coord.as_str()) {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "revision probe `{}` support must contain target_coord `{}`",
                    p.name, p.target_coord
                ),
            });
        }
        validate_scalar_lit(
            &p.expected_value,
            &spec.coeff_domain,
            &format!("revision probe `{}`", p.name),
        )?;
        match (&p.antecedent_coord, &p.antecedent_value) {
            (Some(ac), Some(av)) => {
                if !coord_names.contains(ac) {
                    return Err(ValidationError::UnknownRef {
                        kind: "coord",
                        name: ac.clone(),
                        context: format!("revision probe `{}` antecedent", p.name),
                    });
                }
                if !probe_sup.contains(ac.as_str()) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "revision probe `{}` support must contain antecedent_coord `{ac}`",
                            p.name
                        ),
                    });
                }
                validate_scalar_lit(
                    av,
                    &spec.coeff_domain,
                    &format!("revision probe `{}` antecedent", p.name),
                )?;
            }
            (None, None) => {}
            _ => {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "revision probe `{}` antecedent_coord and antecedent_value must both be present or both absent",
                        p.name
                    ),
                });
            }
        }
    }

    if let Some(snf) = &spec.snf_spec {
        validate_snf_spec(snf)?;
    }

    Ok(CheckedRevisionTask {
        name: spec.name,
        kind: spec.kind,
        coeff_domain: spec.coeff_domain,
        coords: spec.coords,
        shared_constraints: spec.shared_constraints,
        before: spec.before,
        after: spec.after,
        explicit_delta_coords: spec.explicit_delta_coords,
        probes: spec.probes,
        snf_spec: spec.snf_spec,
        max_completions: spec.max_completions,
        provenance: spec.provenance,
        undeclared_unobserved_slots: spec.undeclared_unobserved_slots,
    })
}

fn validate_constraint(
    con: &RevisionConstraintSpec,
    coord_names: &BTreeSet<String>,
    domain: &CoeffDomain,
) -> Result<(), ValidationError> {
    require_non_empty(&con.id, "revision.constraint.id")?;
    let mut sup_set = BTreeSet::new();
    for s in &con.support {
        if !coord_names.contains(s) {
            return Err(ValidationError::UnknownRef {
                kind: "coord",
                name: s.clone(),
                context: format!("constraint `{}` support", con.id),
            });
        }
        sup_set.insert(s.as_str());
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
                if !sup_set.contains(x.as_str()) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "constraint `{}` support must include referenced coord `{x}`",
                            con.id
                        ),
                    });
                }
            }
        }
        RevisionPredicate::LinearZero { terms } => {
            for (coeff, x) in terms {
                validate_scalar_lit(coeff, domain, &format!("constraint `{}`", con.id))?;
                if !coord_names.contains(x) {
                    return Err(ValidationError::UnknownRef {
                        kind: "coord",
                        name: x.clone(),
                        context: format!("constraint `{}`", con.id),
                    });
                }
                if !sup_set.contains(x.as_str()) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "constraint `{}` support must include referenced coord `{x}`",
                            con.id
                        ),
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
                if !sup_set.contains(x.as_str()) {
                    return Err(ValidationError::ConversionError {
                        detail: format!(
                            "constraint `{}` support must include referenced coord `{x}`",
                            con.id
                        ),
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

fn validate_snf_spec(snf: &SnfRevisionSpec) -> Result<(), ValidationError> {
    validate_coeff_domain(&snf.coeff_domain, "revision.snf")?;
    if !matches!(snf.coeff_domain, CoeffDomain::Z | CoeffDomain::Q) {
        return Err(ValidationError::ConversionError {
            detail: "SNF revision spec requires Z or Q coefficient domain".to_owned(),
        });
    }
    if snf.m_before.len() != snf.rhs_before.len() {
        return Err(ValidationError::ArityMismatch {
            context: "snf.m_before/rhs_before".to_owned(),
            expected: snf.m_before.len(),
            actual: snf.rhs_before.len(),
        });
    }
    if snf.m_after.len() != snf.rhs_after.len() {
        return Err(ValidationError::ArityMismatch {
            context: "snf.m_after/rhs_after".to_owned(),
            expected: snf.m_after.len(),
            actual: snf.rhs_after.len(),
        });
    }
    for row in snf.m_before.iter().chain(&snf.m_after) {
        if row.len() != snf.num_cols {
            return Err(ValidationError::ArityMismatch {
                context: "snf matrix cols".to_owned(),
                expected: snf.num_cols,
                actual: row.len(),
            });
        }
        for v in row {
            validate_scalar_lit(v, &snf.coeff_domain, "snf matrix")?;
        }
    }
    for v in snf.rhs_before.iter().chain(&snf.rhs_after) {
        validate_scalar_lit(v, &snf.coeff_domain, "snf rhs")?;
    }
    if snf.origin_label_only && (snf.m_before != snf.m_after || snf.rhs_before != snf.rhs_after) {
        return Err(ValidationError::ConversionError {
            detail: "snf origin_label_only cannot differ in operator or rhs".to_owned(),
        });
    }
    if snf.op_in_common_p0 && snf.m_before != snf.m_after {
        return Err(ValidationError::ConversionError {
            detail: "snf op_in_common_p0 requires m_before == m_after".to_owned(),
        });
    }
    Ok(())
}
