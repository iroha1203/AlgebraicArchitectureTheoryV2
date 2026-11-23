//! 複数解釈族・共有規則候補・良否関係（直接型 $E_{\mathrm{dir}}$ / 存在型 $E_{\mathrm{exists}}$）・
//! reading 比較の IR と `CheckedFamilySpec`（G-140 E3–E5.1・P7 / G-142 G1–G4）。

use crate::ir::change::{ChangeSpec, NamedPoly};
use crate::ir::presentation::{ComparisonPair, CoordValue, Presentation};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate::{
    ValidationError, collect_morphism_unobserved, collect_presentation_unobserved,
    require_non_empty, validate_coeff_domain, validate_poly_expr,
    validate_presentation_ref_checked_params, validate_provenance, validate_scalar_lit,
    validate_source_ref,
};
use crate::ir::validate_change::{
    collect_and_check_param_names, validate_change_spec_checked_params,
    validate_comparison_pair_checked_params, validate_named_polys,
};
use std::collections::{BTreeMap, BTreeSet};

/// 有限列挙される実現族 $U$ の 1 候補（由来 `OriginKind`・raw 表示フラグ・座標値・任意原始表示を保持）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealizationMember {
    pub id: String,
    pub assignments: BTreeMap<String, CoordValue>,
    /// 保存検査前 raw 表示候補（W6 / P7）であるかどうかを明示する。
    pub is_raw_candidate: bool,
    pub presentation: Option<Presentation>,
    pub origin: SourceRef,
}

/// 実現族 $U \xrightarrow{q} B$ の定義空間（有限列挙族または有限多項式 scheme 族）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealizationSpace {
    FiniteMembers(Vec<RealizationMember>),
    PolynomialScheme {
        equations: Vec<NamedPoly>,
        invertibles: Vec<NamedPoly>,
        is_raw_candidate: bool,
        origin: SourceRef,
    },
}

/// 観測と整合する複数解釈の実現族 $U \xrightarrow{q} B$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealizationFamilySpec {
    pub name: String,
    pub u_vars: Vec<String>,
    pub b_vars: Vec<String>,
    /// reading $q: U \to B$ の成分式（`u_vars` 上の `ParamVar`、長さは `b_vars.len()`）。
    pub reading_q: Vec<PolyExpr>,
    pub space: RealizationSpace,
}

/// 有限列挙される共有候補族 $C$ の 1 候補。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateMember {
    pub id: String,
    pub assignments: BTreeMap<String, CoordValue>,
    pub origin: SourceRef,
}

/// 共有規則候補族 $C \xrightarrow{\pi} B$ の定義空間。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CandidateSpace {
    FiniteMembers(Vec<CandidateMember>),
    PolynomialScheme {
        equations: Vec<NamedPoly>,
        invertibles: Vec<NamedPoly>,
        origin: SourceRef,
    },
}

/// 共有規則候補族 $C \xrightarrow{\pi} B$。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateFamilySpec {
    pub name: String,
    pub c_vars: Vec<String>,
    /// 射影 $\pi: C \to B$ の成分式（`c_vars` 上の `ParamVar`、長さは `b_vars.len()`）。
    pub pi: Vec<PolyExpr>,
    pub space: CandidateSpace,
}

/// 原始表示上の有限操作列に対する生評価と中間状態 Law 検査仕様（P7）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSequenceCheck {
    pub start_phase: String,
    pub start_state: BTreeMap<String, ScalarLit>,
    /// 実行する操作名と引数定数の列（例: `begin; apply(1); finish`）。
    pub steps: Vec<(String, Vec<ScalarLit>)>,
    /// `read` 等の中間/最終観測比較に用いる観測名（例: `read`）。
    pub observation_name: String,
    /// `steps` 内の基準観測ステップ index（省略時は直前ステップの観測と比較）。
    pub baseline_step_index: Option<usize>,
    pub provenance: Provenance,
}

/// 既存の `ComparisonPair` / `ChangeSpec` の保存義務を $U \times_B C$ 上の良否式へ接続する仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreservationGoodnessSource {
    pub pair: ComparisonPair,
    pub change_spec: ChangeSpec,
    /// `change_spec` のパラメータ名から `(u_vars, c_vars, witness_vars)` 式への対応。
    pub param_bindings: BTreeMap<String, PolyExpr>,
}

/// 良否関係 $E_{\mathrm{dir}}$ と存在型 $E_{\mathrm{exists}}$ の型レベル区別（G-140 E3 / G-142 G1）。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GoodnessKind {
    /// 直接指定型 $E_{\mathrm{dir}} \hookrightarrow U \times_B C$。
    Direct,
    /// 存在型 $E_{\mathrm{exists}}(R) = \{(u,c) \mid \mathcal{F}_{u,c}(R) \neq \varnothing\}$。
    Existential,
}

impl GoodnessKind {
    pub fn wire(self) -> &'static str {
        match self {
            GoodnessKind::Direct => "direct",
            GoodnessKind::Existential => "existential",
        }
    }
}

/// 良否判定 $E_{\mathrm{ok}}$（`Direct` vs `Existential`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GoodnessSpec {
    Direct {
        equations: Vec<NamedPoly>,
        invertibles: Vec<NamedPoly>,
        preservation: Option<PreservationGoodnessSource>,
        raw_sequence: Option<RawSequenceCheck>,
    },
    Existential {
        witness_vars: Vec<String>,
        equations: Vec<NamedPoly>,
        invertibles: Vec<NamedPoly>,
        preservation: Option<PreservationGoodnessSource>,
    },
}

impl GoodnessSpec {
    pub fn kind(&self) -> GoodnessKind {
        match self {
            GoodnessSpec::Direct { .. } => GoodnessKind::Direct,
            GoodnessSpec::Existential { .. } => GoodnessKind::Existential,
        }
    }

    pub fn witness_vars(&self) -> &[String] {
        match self {
            GoodnessSpec::Direct { .. } => &[],
            GoodnessSpec::Existential { witness_vars, .. } => witness_vars,
        }
    }
}

/// 細 reading $q': U \to B'$ と粗化写像 $r: B' \to B$（$q = r \circ q'$）の比較仕様（G-140 E5.1 / G-142 G4）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadingComparisonSpec {
    pub name: String,
    pub fine_b_vars: Vec<String>,
    pub fine_q: Vec<PolyExpr>,
    /// 粗化写像 $r: B' \to B$（`fine_b_vars` 上の `ParamVar`、長さは `b_vars.len()`）。
    pub coarsen_r: Vec<PolyExpr>,
    pub provenance: Provenance,
}

/// 複数解釈族・共有規則・良否関係・reading 比較の完全仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilySpec {
    pub name: String,
    pub coeff_domain: CoeffDomain,
    pub realizations: RealizationFamilySpec,
    pub candidates: CandidateFamilySpec,
    pub goodness: GoodnessSpec,
    pub reading_comparison: Option<ReadingComparisonSpec>,
    pub provenance: Provenance,
}

/// 検証済みの複数解釈族仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedFamilySpec(FamilySpec);

impl CheckedFamilySpec {
    pub fn validate(spec: FamilySpec) -> Result<Self, ValidationError> {
        require_non_empty(&spec.name, "family.name")?;
        validate_coeff_domain(&spec.coeff_domain, &format!("family `{}`", spec.name))?;
        validate_provenance(&spec.provenance, &format!("family `{}`", spec.name))?;

        let u_set = collect_var_set(&spec.realizations.u_vars, "family.u_vars")?;
        let b_set = collect_var_set(&spec.realizations.b_vars, "family.b_vars")?;
        let c_set = collect_var_set(&spec.candidates.c_vars, "family.c_vars")?;
        let w_set = collect_var_set(spec.goodness.witness_vars(), "family.witness_vars")?;

        ensure_disjoint(&u_set, &c_set, "u_vars", "c_vars", &spec.name)?;
        ensure_disjoint(&u_set, &w_set, "u_vars", "witness_vars", &spec.name)?;
        ensure_disjoint(&c_set, &w_set, "c_vars", "witness_vars", &spec.name)?;

        validate_realizations(&spec.realizations, &spec.coeff_domain, &u_set, &b_set)?;
        validate_candidates(&spec.candidates, &spec.coeff_domain, &c_set, &b_set)?;

        let uc_set: BTreeSet<String> = u_set.union(&c_set).cloned().collect();
        validate_goodness(
            &spec.goodness,
            &spec.coeff_domain,
            &spec.realizations,
            &uc_set,
            &w_set,
        )?;

        if let Some(rc) = &spec.reading_comparison {
            validate_reading_comparison(
                rc,
                &spec.coeff_domain,
                &u_set,
                spec.realizations.b_vars.len(),
            )?;
        }

        Ok(Self(spec))
    }

    pub fn inner(&self) -> &FamilySpec {
        &self.0
    }

    pub fn coeff_domain(&self) -> &CoeffDomain {
        &self.0.coeff_domain
    }

    pub fn u_vars(&self) -> &[String] {
        &self.0.realizations.u_vars
    }

    pub fn c_vars(&self) -> &[String] {
        &self.0.candidates.c_vars
    }

    pub fn b_vars(&self) -> &[String] {
        &self.0.realizations.b_vars
    }

    pub fn witness_vars(&self) -> &[String] {
        self.0.goodness.witness_vars()
    }

    pub fn reading_comparison(&self) -> Option<&ReadingComparisonSpec> {
        self.0.reading_comparison.as_ref()
    }

    /// 族定義内に含まれる未観測 slot（`CoordValue::Missing` および `PolyExpr::Unobserved`）を収集する。
    pub fn unobserved_slots(&self) -> Vec<String> {
        let mut slots = BTreeSet::new();
        for expr in &self.0.realizations.reading_q {
            expr.collect_unobserved(&mut slots);
        }
        match &self.0.realizations.space {
            RealizationSpace::FiniteMembers(members) => {
                for m in members {
                    for (k, v) in &m.assignments {
                        if matches!(v, CoordValue::Missing) {
                            slots.insert(format!("{}.realization.{}.{k}", self.0.name, m.id));
                        }
                    }
                    if let Some(pres) = &m.presentation {
                        collect_presentation_unobserved(pres, &mut slots);
                    }
                }
            }
            RealizationSpace::PolynomialScheme {
                equations,
                invertibles,
                ..
            } => {
                for item in equations.iter().chain(invertibles) {
                    item.expr.collect_unobserved(&mut slots);
                }
            }
        }
        for expr in &self.0.candidates.pi {
            expr.collect_unobserved(&mut slots);
        }
        match &self.0.candidates.space {
            CandidateSpace::FiniteMembers(members) => {
                for m in members {
                    for (k, v) in &m.assignments {
                        if matches!(v, CoordValue::Missing) {
                            slots.insert(format!("{}.candidate.{}.{k}", self.0.name, m.id));
                        }
                    }
                }
            }
            CandidateSpace::PolynomialScheme {
                equations,
                invertibles,
                ..
            } => {
                for item in equations.iter().chain(invertibles) {
                    item.expr.collect_unobserved(&mut slots);
                }
            }
        }
        match &self.0.goodness {
            GoodnessSpec::Direct {
                equations,
                invertibles,
                preservation,
                ..
            }
            | GoodnessSpec::Existential {
                equations,
                invertibles,
                preservation,
                ..
            } => {
                for item in equations.iter().chain(invertibles) {
                    item.expr.collect_unobserved(&mut slots);
                }
                if let Some(p) = preservation {
                    collect_presentation_unobserved(&p.pair.before, &mut slots);
                    collect_presentation_unobserved(&p.pair.after, &mut slots);
                    collect_morphism_unobserved(
                        &p.pair.state_comparisons,
                        &p.pair.word_translation,
                        &mut slots,
                    );
                    for expr in p.param_bindings.values() {
                        expr.collect_unobserved(&mut slots);
                    }
                }
            }
        }
        if let Some(rc) = &self.0.reading_comparison {
            for expr in rc.fine_q.iter().chain(&rc.coarsen_r) {
                expr.collect_unobserved(&mut slots);
            }
        }
        slots.into_iter().collect()
    }
}

pub(crate) fn collect_var_set(
    vars: &[String],
    context: &str,
) -> Result<BTreeSet<String>, ValidationError> {
    let mut set = BTreeSet::new();
    for v in vars {
        require_non_empty(v, context)?;
        if !set.insert(v.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "variable",
                name: format!("{context}:{v}"),
            });
        }
    }
    Ok(set)
}

fn ensure_disjoint(
    lhs: &BTreeSet<String>,
    rhs: &BTreeSet<String>,
    lhs_label: &str,
    rhs_label: &str,
    family_name: &str,
) -> Result<(), ValidationError> {
    for v in lhs {
        if rhs.contains(v) {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "variable `{v}` in family `{family_name}` overlaps between {lhs_label} and {rhs_label}"
                ),
            });
        }
    }
    Ok(())
}

fn validate_member_assignments(
    assignments: &BTreeMap<String, CoordValue>,
    expected_vars: &BTreeSet<String>,
    coeff_domain: &CoeffDomain,
    context: &str,
) -> Result<(), ValidationError> {
    if assignments.len() != expected_vars.len()
        || !expected_vars.iter().all(|v| assignments.contains_key(v))
    {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "{context} assignments must match expected coordinate variables {:?}",
                expected_vars
            ),
        });
    }
    for (k, val) in assignments {
        match val {
            CoordValue::Observed(lit) => {
                validate_scalar_lit(lit, coeff_domain, &format!("{context}.{k}"))?;
            }
            CoordValue::Missing => {}
            CoordValue::Symbolic => {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "{context}.{k} cannot be `Symbolic` in finite member assignments; use PolynomialScheme for symbolic families"
                    ),
                });
            }
        }
    }
    Ok(())
}

fn validate_realizations(
    real: &RealizationFamilySpec,
    coeff_domain: &CoeffDomain,
    u_set: &BTreeSet<String>,
    b_set: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    require_non_empty(&real.name, "realization_family.name")?;
    if real.reading_q.len() != b_set.len() {
        return Err(ValidationError::ArityMismatch {
            context: format!("realization family `{}` reading_q", real.name),
            expected: b_set.len(),
            actual: real.reading_q.len(),
        });
    }
    let empty = BTreeSet::new();
    for (i, expr) in real.reading_q.iter().enumerate() {
        validate_poly_expr(
            expr,
            coeff_domain,
            &empty,
            &empty,
            u_set,
            &format!("realization `{}`.reading_q[{i}]", real.name),
        )?;
    }
    match &real.space {
        RealizationSpace::FiniteMembers(members) => {
            let mut seen_ids = BTreeSet::new();
            for m in members {
                require_non_empty(&m.id, "realization_member.id")?;
                if !seen_ids.insert(m.id.clone()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "realization member",
                        name: m.id.clone(),
                    });
                }
                validate_source_ref(&m.origin, &format!("realization member `{}`", m.id))?;
                validate_member_assignments(
                    &m.assignments,
                    u_set,
                    coeff_domain,
                    &format!("realization member `{}`", m.id),
                )?;
                if let Some(pres) = &m.presentation {
                    if &pres.coeff_domain != coeff_domain {
                        return Err(ValidationError::DomainMismatch {
                            expected: coeff_domain.clone(),
                            actual: pres.coeff_domain.clone(),
                            context: format!("realization member `{}` presentation", m.id),
                        });
                    }
                    validate_presentation_ref_checked_params(pres, &empty)?;
                }
            }
        }
        RealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
            ..
        } => {
            validate_source_ref(origin, &format!("realization scheme `{}`", real.name))?;
            validate_named_polys(equations, "realization_equation", coeff_domain, u_set)?;
            validate_named_polys(invertibles, "realization_invertible", coeff_domain, u_set)?;
        }
    }
    Ok(())
}

fn validate_candidates(
    cand: &CandidateFamilySpec,
    coeff_domain: &CoeffDomain,
    c_set: &BTreeSet<String>,
    b_set: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    require_non_empty(&cand.name, "candidate_family.name")?;
    if cand.pi.len() != b_set.len() {
        return Err(ValidationError::ArityMismatch {
            context: format!("candidate family `{}` pi", cand.name),
            expected: b_set.len(),
            actual: cand.pi.len(),
        });
    }
    let empty = BTreeSet::new();
    for (i, expr) in cand.pi.iter().enumerate() {
        validate_poly_expr(
            expr,
            coeff_domain,
            &empty,
            &empty,
            c_set,
            &format!("candidate `{}`.pi[{i}]", cand.name),
        )?;
    }
    match &cand.space {
        CandidateSpace::FiniteMembers(members) => {
            let mut seen_ids = BTreeSet::new();
            for m in members {
                require_non_empty(&m.id, "candidate_member.id")?;
                if !seen_ids.insert(m.id.clone()) {
                    return Err(ValidationError::DuplicateDecl {
                        kind: "candidate member",
                        name: m.id.clone(),
                    });
                }
                validate_source_ref(&m.origin, &format!("candidate member `{}`", m.id))?;
                validate_member_assignments(
                    &m.assignments,
                    c_set,
                    coeff_domain,
                    &format!("candidate member `{}`", m.id),
                )?;
            }
        }
        CandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
        } => {
            validate_source_ref(origin, &format!("candidate scheme `{}`", cand.name))?;
            validate_named_polys(equations, "candidate_equation", coeff_domain, c_set)?;
            validate_named_polys(invertibles, "candidate_invertible", coeff_domain, c_set)?;
        }
    }
    Ok(())
}

fn validate_goodness(
    goodness: &GoodnessSpec,
    coeff_domain: &CoeffDomain,
    realizations: &RealizationFamilySpec,
    uc_set: &BTreeSet<String>,
    w_set: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    match goodness {
        GoodnessSpec::Direct {
            equations,
            invertibles,
            preservation,
            raw_sequence,
        } => {
            validate_named_polys(equations, "goodness_equation", coeff_domain, uc_set)?;
            validate_named_polys(invertibles, "goodness_invertible", coeff_domain, uc_set)?;
            if let Some(pres_src) = preservation {
                validate_preservation_source(pres_src, coeff_domain, uc_set)?;
            }
            if let Some(raw_seq) = raw_sequence {
                validate_raw_sequence(raw_seq, coeff_domain, realizations)?;
            }
        }
        GoodnessSpec::Existential {
            witness_vars,
            equations,
            invertibles,
            preservation,
        } => {
            if witness_vars.is_empty() {
                return Err(ValidationError::ConversionError {
                    detail: "existential goodness requires at least one witness variable"
                        .to_owned(),
                });
            }
            let ucw_set: BTreeSet<String> = uc_set.union(w_set).cloned().collect();
            validate_named_polys(equations, "goodness_equation", coeff_domain, &ucw_set)?;
            validate_named_polys(invertibles, "goodness_invertible", coeff_domain, &ucw_set)?;
            if let Some(pres_src) = preservation {
                validate_preservation_source(pres_src, coeff_domain, &ucw_set)?;
            }
        }
    }
    Ok(())
}

fn validate_preservation_source(
    src: &PreservationGoodnessSource,
    coeff_domain: &CoeffDomain,
    allowed_family_vars: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    if &src.change_spec.coeff_domain != coeff_domain {
        return Err(ValidationError::DomainMismatch {
            expected: coeff_domain.clone(),
            actual: src.change_spec.coeff_domain.clone(),
            context: "family goodness preservation change_spec".to_owned(),
        });
    }
    let cs_params = collect_and_check_param_names(&src.change_spec)?;
    let checked_pair = validate_comparison_pair_checked_params(src.pair.clone(), &cs_params)?;
    let _checked_cs = validate_change_spec_checked_params(src.change_spec.clone(), &checked_pair)?;
    let empty = BTreeSet::new();
    for (param_name, expr) in &src.param_bindings {
        if !cs_params.contains(param_name) {
            return Err(ValidationError::UnknownRef {
                kind: "parameter",
                name: param_name.clone(),
                context: "goodness preservation param_bindings".to_owned(),
            });
        }
        validate_poly_expr(
            expr,
            coeff_domain,
            &empty,
            &empty,
            allowed_family_vars,
            &format!("goodness param_binding `{param_name}`"),
        )?;
    }
    for p in &cs_params {
        if !src.param_bindings.contains_key(p) && !allowed_family_vars.contains(p) {
            return Err(ValidationError::UnknownRef {
                kind: "family variable",
                name: p.clone(),
                context: "goodness preservation parameter without binding".to_owned(),
            });
        }
    }
    Ok(())
}

fn validate_raw_sequence(
    seq: &RawSequenceCheck,
    coeff_domain: &CoeffDomain,
    realizations: &RealizationFamilySpec,
) -> Result<(), ValidationError> {
    require_non_empty(&seq.start_phase, "raw_sequence.start_phase")?;
    require_non_empty(&seq.observation_name, "raw_sequence.observation_name")?;
    validate_provenance(&seq.provenance, "raw_sequence")?;
    for (k, lit) in &seq.start_state {
        require_non_empty(k, "raw_sequence.start_state")?;
        validate_scalar_lit(lit, coeff_domain, &format!("raw_sequence.start_state.{k}"))?;
    }
    if seq.steps.is_empty() {
        return Err(ValidationError::ConversionError {
            detail: "raw_sequence.steps must contain at least one operation step".to_owned(),
        });
    }
    for (op_name, args) in &seq.steps {
        require_non_empty(op_name, "raw_sequence.step")?;
        for (i, lit) in args.iter().enumerate() {
            validate_scalar_lit(lit, coeff_domain, &format!("raw_sequence.{op_name}[{i}]"))?;
        }
    }
    if let Some(idx) = seq.baseline_step_index
        && idx >= seq.steps.len()
    {
        return Err(ValidationError::ConversionError {
            detail: format!(
                "raw_sequence baseline_step_index {idx} out of bounds (steps = {})",
                seq.steps.len()
            ),
        });
    }
    let members = match &realizations.space {
        RealizationSpace::FiniteMembers(members) => members,
        RealizationSpace::PolynomialScheme { .. } => {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "raw_sequence goodness requires FiniteMembers realization space with per-member Presentation, got PolynomialScheme on `{}`",
                    realizations.name
                ),
            });
        }
    };
    for m in members {
        let Some(pres) = &m.presentation else {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "raw_sequence goodness requires realization member `{}` to carry a Presentation",
                    m.id
                ),
            });
        };
        validate_raw_sequence_against_presentation(seq, pres, &m.id)?;
    }
    Ok(())
}

fn validate_raw_sequence_against_presentation(
    seq: &RawSequenceCheck,
    pres: &Presentation,
    member_id: &str,
) -> Result<(), ValidationError> {
    let ctx = format!(
        "raw_sequence on member `{member_id}` (presentation `{}`)",
        pres.name
    );
    let start_phase = pres
        .phase(&seq.start_phase)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "phase",
            name: seq.start_phase.clone(),
            context: ctx.clone(),
        })?;
    let phase_coord_names: BTreeSet<&str> =
        start_phase.coords.iter().map(|c| c.name.as_str()).collect();
    for k in seq.start_state.keys() {
        if !phase_coord_names.contains(k.as_str()) {
            return Err(ValidationError::UnknownRef {
                kind: "state coordinate",
                name: k.clone(),
                context: format!("{ctx} phase `{}`", start_phase.name),
            });
        }
    }
    for coord in &start_phase.coords {
        match (&coord.value, seq.start_state.get(&coord.name)) {
            (CoordValue::Symbolic, None) => {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "{ctx}: start_state is missing initial value for coordinate `{}` of phase `{}`",
                        coord.name, start_phase.name
                    ),
                });
            }
            (CoordValue::Observed(obs_lit), Some(start_lit)) if start_lit != obs_lit => {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "{ctx}: start_state cannot overwrite Observed coordinate `{}` ({obs_lit}) of phase `{}` with `{start_lit}`",
                        coord.name, start_phase.name
                    ),
                });
            }
            _ => {}
        }
    }

    let mut cur_phase = seq.start_phase.as_str();
    let mut baseline_phase: Option<&str> = match seq.baseline_step_index {
        None if seq.steps.len() == 1 => Some(seq.start_phase.as_str()),
        _ => None,
    };
    let effective_baseline_idx = seq
        .baseline_step_index
        .unwrap_or_else(|| seq.steps.len().saturating_sub(2));
    for (idx, (op_name, args)) in seq.steps.iter().enumerate() {
        let op = pres
            .operation(op_name)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "operation",
                name: op_name.clone(),
                context: format!("{ctx} step {idx}"),
            })?;
        if op.source_phase != cur_phase {
            return Err(ValidationError::PhasePathMismatch {
                after_operation: op_name.clone(),
                detail: format!(
                    "{ctx} step {idx}: operation `{}` expects source phase `{}`, got `{cur_phase}`",
                    op.name, op.source_phase
                ),
            });
        }
        if args.len() != op.args.len() {
            return Err(ValidationError::ArityMismatch {
                context: format!("{ctx} step {idx} (`{op_name}`)"),
                expected: op.args.len(),
                actual: args.len(),
            });
        }
        cur_phase = op.target_phase.as_str();
        if baseline_phase.is_none() && idx == effective_baseline_idx {
            baseline_phase = Some(cur_phase);
        }
    }

    let final_obs = pres
        .observations
        .iter()
        .find(|o| o.name == seq.observation_name && o.phase == cur_phase)
        .ok_or_else(|| ValidationError::UnknownRef {
            kind: "observation",
            name: seq.observation_name.clone(),
            context: format!("{ctx} final phase `{cur_phase}`"),
        })?;
    if let Some(b_phase) = baseline_phase {
        let base_obs = pres
            .observations
            .iter()
            .find(|o| o.name == seq.observation_name && o.phase == b_phase)
            .ok_or_else(|| ValidationError::UnknownRef {
                kind: "observation",
                name: seq.observation_name.clone(),
                context: format!("{ctx} baseline phase `{b_phase}`"),
            })?;
        if final_obs.components.len() != base_obs.components.len() {
            return Err(ValidationError::ArityMismatch {
                context: format!(
                    "{ctx} observation `{}` component count across baseline `{b_phase}` and final `{cur_phase}`",
                    seq.observation_name
                ),
                expected: base_obs.components.len(),
                actual: final_obs.components.len(),
            });
        }
    }
    Ok(())
}

fn validate_reading_comparison(
    rc: &ReadingComparisonSpec,
    coeff_domain: &CoeffDomain,
    u_set: &BTreeSet<String>,
    coarse_b_len: usize,
) -> Result<(), ValidationError> {
    require_non_empty(&rc.name, "reading_comparison.name")?;
    validate_provenance(&rc.provenance, &format!("reading_comparison `{}`", rc.name))?;
    let fine_b_set = collect_var_set(&rc.fine_b_vars, "reading_comparison.fine_b_vars")?;
    if rc.fine_q.len() != rc.fine_b_vars.len() {
        return Err(ValidationError::ArityMismatch {
            context: format!("reading_comparison `{}`.fine_q", rc.name),
            expected: rc.fine_b_vars.len(),
            actual: rc.fine_q.len(),
        });
    }
    if rc.coarsen_r.len() != coarse_b_len {
        return Err(ValidationError::ArityMismatch {
            context: format!("reading_comparison `{}`.coarsen_r", rc.name),
            expected: coarse_b_len,
            actual: rc.coarsen_r.len(),
        });
    }
    let empty = BTreeSet::new();
    for (i, expr) in rc.fine_q.iter().enumerate() {
        validate_poly_expr(
            expr,
            coeff_domain,
            &empty,
            &empty,
            u_set,
            &format!("reading_comparison `{}`.fine_q[{i}]", rc.name),
        )?;
    }
    for (i, expr) in rc.coarsen_r.iter().enumerate() {
        validate_poly_expr(
            expr,
            coeff_domain,
            &empty,
            &empty,
            &fine_b_set,
            &format!("reading_comparison `{}`.coarsen_r[{i}]", rc.name),
        )?;
    }
    Ok(())
}
