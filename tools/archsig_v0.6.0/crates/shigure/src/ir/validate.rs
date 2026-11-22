//! SHIGURE IR の検証と検証済み構築経路（Checked* ラッパー）。
//!
//! 下流の計算核は `validate_*` を通過した `Checked*` 型のみを受け取ることで、
//! 不正な参照・型不一致・意味 Law の編集許可・固定/編集衝突・未観測値の暗黙零補完を防ぐ。

use crate::ir::change::{ChangeSpec, EvalCondition, PointDomain};
use crate::ir::presentation::{
    ComparisonPair, CoordValue, Presentation, StateComparison, WordTranslation,
};
use crate::ir::provenance::{Provenance, SourceRef};
use crate::ir::term::{CoeffDomain, PolyExpr, ScalarLit};
use crate::ir::validate_change::{
    collect_and_check_param_names, validate_change_spec_checked_params,
    validate_comparison_pair_checked_params, validate_eval_condition_checked_params,
};
use archsig_common::prime::is_prime;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub use crate::ir::validate_change::{
    validate_change_spec, validate_comparison_pair, validate_eval_condition,
};

/// IR 検証エラー。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValidationError {
    EmptyName {
        context: String,
    },
    InvalidPrimeModulus {
        modulus: BigUint,
        context: String,
    },
    InvalidRational {
        context: String,
    },
    InvalidFpLiteral {
        context: String,
    },
    DuplicateDecl {
        kind: &'static str,
        name: String,
    },
    UnknownRef {
        kind: &'static str,
        name: String,
        context: String,
    },
    DomainMismatch {
        expected: CoeffDomain,
        actual: CoeffDomain,
        context: String,
    },
    ZeroRankSort {
        sort: String,
    },
    InvalidSourceSpan {
        origin_id: String,
        start: u64,
        end: u64,
    },
    MissingObservation {
        after_phase: String,
        before_phase: String,
        observation: String,
    },
    MissingCoordUpdate {
        operation: String,
        coord: String,
    },
    UnknownCoordUpdate {
        operation: String,
        coord: String,
    },
    EmptyObservation {
        phase: String,
        observation: String,
    },
    MissingStateComparison {
        after_phase: String,
    },
    MissingWordTranslation {
        after_operation: String,
    },
    ArityMismatch {
        context: String,
        expected: usize,
        actual: usize,
    },
    PhasePathMismatch {
        after_operation: String,
        detail: String,
    },
    FixedEditableConflict {
        target: String,
    },
    SemanticLawEditable {
        presentation: String,
        phase: String,
        law: String,
    },
    PointDomainMismatch {
        coeff_domain: CoeffDomain,
        point_domain: PointDomain,
    },
    ConclusionInjectionRejected {
        field: String,
    },
    ConversionError {
        detail: String,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::EmptyName { context } => write!(f, "empty name in {context}"),
            ValidationError::InvalidPrimeModulus { modulus, context } => {
                write!(f, "modulus `{modulus}` is not prime in {context}")
            }
            ValidationError::InvalidRational { context } => {
                write!(f, "invalid rational literal in {context}")
            }
            ValidationError::InvalidFpLiteral { context } => {
                write!(f, "invalid Fp literal in {context}")
            }
            ValidationError::DuplicateDecl { kind, name } => {
                write!(f, "duplicate {kind} declaration `{name}`")
            }
            ValidationError::UnknownRef {
                kind,
                name,
                context,
            } => {
                write!(f, "unknown {kind} `{name}` referenced in {context}")
            }
            ValidationError::DomainMismatch {
                expected,
                actual,
                context,
            } => {
                write!(
                    f,
                    "coefficient domain mismatch in {context}: expected {expected}, got {actual}"
                )
            }
            ValidationError::ZeroRankSort { sort } => {
                write!(f, "sort `{sort}` must have positive rank")
            }
            ValidationError::InvalidSourceSpan {
                origin_id,
                start,
                end,
            } => {
                write!(
                    f,
                    "invalid source span [{start}, {end}) on origin `{origin_id}`: expected start <= end"
                )
            }
            ValidationError::MissingObservation {
                after_phase,
                before_phase,
                observation,
            } => {
                write!(
                    f,
                    "after phase `{after_phase}` is missing observation `{observation}` required by before phase `{before_phase}`"
                )
            }
            ValidationError::MissingCoordUpdate { operation, coord } => {
                write!(
                    f,
                    "operation `{operation}` is missing update for coordinate `{coord}`"
                )
            }
            ValidationError::UnknownCoordUpdate { operation, coord } => {
                write!(
                    f,
                    "operation `{operation}` updates unknown coordinate `{coord}`"
                )
            }
            ValidationError::EmptyObservation { phase, observation } => {
                write!(
                    f,
                    "observation `{phase}.{observation}` must have at least one component"
                )
            }
            ValidationError::MissingStateComparison { after_phase } => {
                write!(
                    f,
                    "missing state comparison h for after phase `{after_phase}`"
                )
            }
            ValidationError::MissingWordTranslation { after_operation } => {
                write!(
                    f,
                    "missing word translation tau for after operation `{after_operation}`"
                )
            }
            ValidationError::ArityMismatch {
                context,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "arity mismatch in {context}: expected {expected}, got {actual}"
                )
            }
            ValidationError::PhasePathMismatch {
                after_operation,
                detail,
            } => {
                write!(
                    f,
                    "word translation phase mismatch for `{after_operation}`: {detail}"
                )
            }
            ValidationError::FixedEditableConflict { target } => {
                write!(
                    f,
                    "target `{target}` cannot be both fixed and editable in ChangeSpec"
                )
            }
            ValidationError::SemanticLawEditable {
                presentation,
                phase,
                law,
            } => {
                write!(
                    f,
                    "semantic law `{presentation}.{phase}.{law}` cannot be marked editable"
                )
            }
            ValidationError::PointDomainMismatch {
                coeff_domain,
                point_domain,
            } => {
                write!(
                    f,
                    "point domain `{point_domain}` is incompatible with coefficient domain `{coeff_domain}`"
                )
            }
            ValidationError::ConclusionInjectionRejected { field } => {
                write!(f, "conclusion injection field `{field}` is forbidden")
            }
            ValidationError::ConversionError { detail } => {
                write!(f, "input conversion error: {detail}")
            }
        }
    }
}

impl std::error::Error for ValidationError {}

/// 検証済みの `Presentation`。外部から直接構築できない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedPresentation(Presentation);

impl CheckedPresentation {
    pub fn inner(&self) -> &Presentation {
        &self.0
    }

    pub(crate) fn into_inner(self) -> Presentation {
        self.0
    }
}

/// 検証済みの `ComparisonPair`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedComparisonPair(ComparisonPair);

impl CheckedComparisonPair {
    pub(crate) fn from_validated(pair: ComparisonPair) -> Self {
        Self(pair)
    }

    pub fn inner(&self) -> &ComparisonPair {
        &self.0
    }
}

/// 検証済みの `ChangeSpec`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedChangeSpec(ChangeSpec);

impl CheckedChangeSpec {
    pub(crate) fn from_validated(spec: ChangeSpec) -> Self {
        Self(spec)
    }

    pub fn inner(&self) -> &ChangeSpec {
        &self.0
    }
}

/// 検証済みの `EvalCondition`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedEvalCondition(EvalCondition);

impl CheckedEvalCondition {
    pub(crate) fn from_validated(cond: EvalCondition) -> Self {
        Self(cond)
    }

    pub fn inner(&self) -> &EvalCondition {
        &self.0
    }
}

/// 検証済みの SHIGURE 計算タスク全体（`ComparisonPair` + `ChangeSpec` + 任意の `EvalCondition`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedShigureTask {
    pair: CheckedComparisonPair,
    change_spec: CheckedChangeSpec,
    eval_condition: Option<CheckedEvalCondition>,
}

impl CheckedShigureTask {
    pub fn validate(
        pair: ComparisonPair,
        change_spec: ChangeSpec,
        eval_condition: Option<EvalCondition>,
    ) -> Result<Self, ValidationError> {
        let param_names = collect_and_check_param_names(&change_spec)?;
        let checked_pair = validate_comparison_pair_checked_params(pair, &param_names)?;
        let checked_spec = validate_change_spec_checked_params(change_spec, &checked_pair)?;
        let checked_eval = match eval_condition {
            Some(cond) => Some(validate_eval_condition_checked_params(
                cond,
                &checked_spec.inner().coeff_domain,
                &param_names,
            )?),
            None => None,
        };
        Ok(Self {
            pair: checked_pair,
            change_spec: checked_spec,
            eval_condition: checked_eval,
        })
    }

    pub fn pair(&self) -> &ComparisonPair {
        self.pair.inner()
    }

    pub fn change_spec(&self) -> &ChangeSpec {
        self.change_spec.inner()
    }

    pub fn eval_condition(&self) -> Option<&EvalCondition> {
        self.eval_condition
            .as_ref()
            .map(CheckedEvalCondition::inner)
    }

    /// タスク全体に含まれる未観測 slot（座標欠測および `PolyExpr::Unobserved`）を収集する。
    pub fn unobserved_slots(&self) -> Vec<String> {
        let mut slots = BTreeSet::new();
        collect_presentation_unobserved(&self.pair.0.before, &mut slots);
        collect_presentation_unobserved(&self.pair.0.after, &mut slots);
        collect_morphism_unobserved(
            &self.pair.0.state_comparisons,
            &self.pair.0.word_translation,
            &mut slots,
        );
        if let Some(cond) = &self.eval_condition {
            collect_eval_unobserved(&cond.0, &mut slots);
        }
        slots.into_iter().collect()
    }
}

pub(crate) fn collect_morphism_unobserved(
    scs: &[StateComparison],
    wt: &WordTranslation,
    out: &mut BTreeSet<String>,
) {
    for sc in scs {
        for expr in sc.map.values() {
            expr.collect_unobserved(out);
        }
    }
    for tw in &wt.entries {
        for step in &tw.steps {
            for expr in &step.arg_exprs {
                expr.collect_unobserved(out);
            }
        }
    }
}

pub(crate) fn collect_eval_unobserved(cond: &EvalCondition, out: &mut BTreeSet<String>) {
    for item in cond
        .evaluations
        .iter()
        .chain(&cond.equations)
        .chain(&cond.invertibles)
    {
        item.expr.collect_unobserved(out);
    }
}

pub(crate) fn collect_presentation_unobserved(pres: &Presentation, out: &mut BTreeSet<String>) {
    for phase in &pres.phases {
        for coord in &phase.coords {
            if coord.is_missing() {
                out.insert(format!("{}.{}.{}", pres.name, phase.name, coord.name));
            }
        }
        for law in &phase.state_laws {
            law.polynomial.collect_unobserved(out);
        }
    }
    for op in &pres.operations {
        for law in &op.domain_laws {
            law.polynomial.collect_unobserved(out);
        }
        for expr in op.updates.values() {
            expr.collect_unobserved(out);
        }
    }
    for obs in &pres.observations {
        for expr in &obs.components {
            expr.collect_unobserved(out);
        }
    }
}

pub(crate) fn require_non_empty(name: &str, context: &str) -> Result<(), ValidationError> {
    if name.trim().is_empty() {
        Err(ValidationError::EmptyName {
            context: context.to_owned(),
        })
    } else {
        Ok(())
    }
}

pub(crate) fn validate_allowed_params(
    allowed_params: &BTreeSet<String>,
    context: &str,
) -> Result<(), ValidationError> {
    for name in allowed_params {
        require_non_empty(name, context)?;
    }
    Ok(())
}

pub(crate) fn validate_source_ref(
    source_ref: &SourceRef,
    context: &str,
) -> Result<(), ValidationError> {
    require_non_empty(&source_ref.origin_id, &format!("{context}.origin_id"))?;
    if let Some(src) = &source_ref.source_id {
        require_non_empty(src, &format!("{context}.source_id"))?;
    }
    if let Some(path) = &source_ref.path {
        require_non_empty(path, &format!("{context}.path"))?;
    }
    if let Some(atom_ref) = &source_ref.atom_ref {
        require_non_empty(atom_ref, &format!("{context}.atom_ref"))?;
    }
    if let Some(decl) = &source_ref.law_declaration {
        require_non_empty(decl, &format!("{context}.law_declaration"))?;
    }
    if let Some((start, end)) = source_ref.span
        && start > end
    {
        return Err(ValidationError::InvalidSourceSpan {
            origin_id: source_ref.origin_id.clone(),
            start,
            end,
        });
    }
    Ok(())
}

pub(crate) fn validate_opt_source_ref(
    source_ref: Option<&SourceRef>,
    context: &str,
) -> Result<(), ValidationError> {
    if let Some(sr) = source_ref {
        validate_source_ref(sr, context)?;
    }
    Ok(())
}

pub(crate) fn validate_provenance(
    provenance: &Provenance,
    context: &str,
) -> Result<(), ValidationError> {
    for sr in &provenance.origins {
        validate_source_ref(sr, context)?;
    }
    Ok(())
}

pub fn validate_coeff_domain(domain: &CoeffDomain, context: &str) -> Result<(), ValidationError> {
    if let CoeffDomain::Fp(p) = domain
        && !is_prime(p)
    {
        return Err(ValidationError::InvalidPrimeModulus {
            modulus: p.clone(),
            context: context.to_owned(),
        });
    }
    Ok(())
}

pub(crate) fn validate_scalar_lit(
    lit: &ScalarLit,
    expected: &CoeffDomain,
    context: &str,
) -> Result<(), ValidationError> {
    if !lit.matches_domain(expected) {
        return Err(ValidationError::DomainMismatch {
            expected: expected.clone(),
            actual: lit.domain(),
            context: context.to_owned(),
        });
    }
    match lit {
        ScalarLit::Z(_) => Ok(()),
        ScalarLit::Q { num, den } => {
            if !den.is_positive() {
                return Err(ValidationError::InvalidRational {
                    context: context.to_owned(),
                });
            }
            if num.is_zero() {
                if !den.is_one() {
                    return Err(ValidationError::InvalidRational {
                        context: context.to_owned(),
                    });
                }
            } else if !num.gcd(den).is_one() {
                return Err(ValidationError::InvalidRational {
                    context: context.to_owned(),
                });
            }
            Ok(())
        }
        ScalarLit::Fp { value, modulus } => {
            // `expected` は事前に `validate_coeff_domain` で素数性検証済みであり、
            // 上の `matches_domain` により `modulus == p` が成立しているため再検定を省く。
            debug_assert!(is_prime(modulus));
            if value >= modulus {
                return Err(ValidationError::InvalidFpLiteral {
                    context: context.to_owned(),
                });
            }
            Ok(())
        }
    }
}

pub(crate) fn validate_poly_expr(
    expr: &PolyExpr,
    expected: &CoeffDomain,
    allowed_states: &BTreeSet<String>,
    allowed_args: &BTreeSet<String>,
    allowed_params: &BTreeSet<String>,
    context: &str,
) -> Result<(), ValidationError> {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node {
            PolyExpr::Const(lit) => validate_scalar_lit(lit, expected, context)?,
            PolyExpr::StateVar(v) => {
                if !allowed_states.contains(v) {
                    return Err(ValidationError::UnknownRef {
                        kind: "state coordinate",
                        name: v.clone(),
                        context: context.to_owned(),
                    });
                }
            }
            PolyExpr::ArgVar(v) => {
                if !allowed_args.contains(v) {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation argument",
                        name: v.clone(),
                        context: context.to_owned(),
                    });
                }
            }
            PolyExpr::ParamVar(v) => {
                require_non_empty(v, context)?;
                if !allowed_params.contains(v) {
                    return Err(ValidationError::UnknownRef {
                        kind: "parameter",
                        name: v.clone(),
                        context: context.to_owned(),
                    });
                }
            }
            PolyExpr::Unobserved { slot, origin } => {
                require_non_empty(slot, context)?;
                validate_opt_source_ref(origin.as_ref(), context)?;
            }
            PolyExpr::Neg(e) | PolyExpr::Pow(e, _) => stack.push(e),
            PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
                stack.push(b);
                stack.push(a);
            }
        }
    }
    Ok(())
}

/// 単一の `Presentation` を検証する。
pub fn validate_presentation(
    pres: Presentation,
    allowed_params: &BTreeSet<String>,
) -> Result<CheckedPresentation, ValidationError> {
    validate_allowed_params(allowed_params, "presentation.allowed_params")?;
    validate_presentation_checked_params(pres, allowed_params)
}

pub(crate) fn validate_presentation_checked_params(
    pres: Presentation,
    allowed_params: &BTreeSet<String>,
) -> Result<CheckedPresentation, ValidationError> {
    validate_presentation_ref_checked_params(&pres, allowed_params)?;
    Ok(CheckedPresentation(pres))
}

pub(crate) fn validate_presentation_ref_checked_params(
    pres: &Presentation,
    allowed_params: &BTreeSet<String>,
) -> Result<(), ValidationError> {
    require_non_empty(&pres.name, "presentation.name")?;
    validate_coeff_domain(&pres.coeff_domain, &format!("presentation `{}`", pres.name))?;
    validate_provenance(&pres.provenance, &format!("presentation `{}`", pres.name))?;

    let mut sort_names = BTreeSet::new();
    for sort in &pres.sorts {
        require_non_empty(&sort.name, "sort.name")?;
        validate_opt_source_ref(sort.provenance.as_ref(), &format!("sort `{}`", sort.name))?;
        if !sort_names.insert(sort.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "sort",
                name: sort.name.clone(),
            });
        }
        if sort.rank == 0 {
            return Err(ValidationError::ZeroRankSort {
                sort: sort.name.clone(),
            });
        }
        validate_coeff_domain(&sort.coeff_domain, &format!("sort `{}`", sort.name))?;
        if sort.coeff_domain != pres.coeff_domain {
            return Err(ValidationError::DomainMismatch {
                expected: pres.coeff_domain.clone(),
                actual: sort.coeff_domain.clone(),
                context: format!("sort `{}`", sort.name),
            });
        }
    }

    let empty_args = BTreeSet::new();
    let mut phase_coords: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for phase in &pres.phases {
        require_non_empty(&phase.name, "phase.name")?;
        validate_opt_source_ref(
            phase.provenance.as_ref(),
            &format!("phase `{}`", phase.name),
        )?;
        if phase_coords.contains_key(&phase.name) {
            return Err(ValidationError::DuplicateDecl {
                kind: "phase",
                name: phase.name.clone(),
            });
        }
        let mut coords = BTreeSet::new();
        for coord in &phase.coords {
            require_non_empty(&coord.name, &format!("phase `{}` coord", phase.name))?;
            validate_opt_source_ref(
                coord.provenance.as_ref(),
                &format!("coordinate `{}.{}`", phase.name, coord.name),
            )?;
            if !coords.insert(coord.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "coordinate",
                    name: format!("{}.{}", phase.name, coord.name),
                });
            }
            if !sort_names.contains(&coord.sort) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: coord.sort.clone(),
                    context: format!("coordinate `{}.{}`", phase.name, coord.name),
                });
            }
            if let CoordValue::Observed(lit) = &coord.value {
                validate_scalar_lit(
                    lit,
                    &pres.coeff_domain,
                    &format!("coordinate `{}.{}`", phase.name, coord.name),
                )?;
            }
        }
        let mut law_names = BTreeSet::new();
        for law in &phase.state_laws {
            require_non_empty(&law.name, &format!("phase `{}` state_law", phase.name))?;
            validate_opt_source_ref(
                law.provenance.as_ref(),
                &format!("state_law `{}.{}`", phase.name, law.name),
            )?;
            if !law_names.insert(law.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "state_law",
                    name: format!("{}.{}", phase.name, law.name),
                });
            }
            validate_poly_expr(
                &law.polynomial,
                &pres.coeff_domain,
                &coords,
                &empty_args,
                allowed_params,
                &format!("state_law `{}.{}`", phase.name, law.name),
            )?;
        }
        phase_coords.insert(phase.name.clone(), coords);
    }

    let mut op_names = BTreeSet::new();
    for op in &pres.operations {
        require_non_empty(&op.name, "operation.name")?;
        validate_opt_source_ref(op.provenance.as_ref(), &format!("operation `{}`", op.name))?;
        if !op_names.insert(op.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "operation",
                name: op.name.clone(),
            });
        }
        let Some(src_coords) = phase_coords.get(&op.source_phase) else {
            return Err(ValidationError::UnknownRef {
                kind: "phase",
                name: op.source_phase.clone(),
                context: format!("operation `{}` source_phase", op.name),
            });
        };
        let Some(dst_coords) = phase_coords.get(&op.target_phase) else {
            return Err(ValidationError::UnknownRef {
                kind: "phase",
                name: op.target_phase.clone(),
                context: format!("operation `{}` target_phase", op.name),
            });
        };
        let mut arg_names = BTreeSet::new();
        for (arg_name, sort_name) in &op.args {
            require_non_empty(arg_name, &format!("operation `{}` arg", op.name))?;
            if !arg_names.insert(arg_name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "operation argument",
                    name: format!("{}.{}", op.name, arg_name),
                });
            }
            if !sort_names.contains(sort_name) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: sort_name.clone(),
                    context: format!("operation `{}` argument `{arg_name}`", op.name),
                });
            }
        }
        let mut domain_law_names = BTreeSet::new();
        for dlaw in &op.domain_laws {
            require_non_empty(&dlaw.name, &format!("operation `{}` domain_law", op.name))?;
            validate_opt_source_ref(
                dlaw.provenance.as_ref(),
                &format!("domain_law `{}.{}`", op.name, dlaw.name),
            )?;
            if !domain_law_names.insert(dlaw.name.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "domain_law",
                    name: format!("{}.{}", op.name, dlaw.name),
                });
            }
            validate_poly_expr(
                &dlaw.polynomial,
                &pres.coeff_domain,
                src_coords,
                &arg_names,
                allowed_params,
                &format!("operation `{}` domain_law `{}`", op.name, dlaw.name),
            )?;
        }
        for dst in dst_coords {
            if !op.updates.contains_key(dst) {
                return Err(ValidationError::MissingCoordUpdate {
                    operation: op.name.clone(),
                    coord: dst.clone(),
                });
            }
        }
        for (coord, expr) in &op.updates {
            if !dst_coords.contains(coord) {
                return Err(ValidationError::UnknownCoordUpdate {
                    operation: op.name.clone(),
                    coord: coord.clone(),
                });
            }
            validate_poly_expr(
                expr,
                &pres.coeff_domain,
                src_coords,
                &arg_names,
                allowed_params,
                &format!("operation `{}` update `{coord}`", op.name),
            )?;
        }
    }

    let mut obs_keys = BTreeSet::new();
    for obs in &pres.observations {
        require_non_empty(&obs.name, "observation.name")?;
        validate_opt_source_ref(
            obs.provenance.as_ref(),
            &format!("observation `{}.{}`", obs.phase, obs.name),
        )?;
        let Some(coords) = phase_coords.get(&obs.phase) else {
            return Err(ValidationError::UnknownRef {
                kind: "phase",
                name: obs.phase.clone(),
                context: format!("observation `{}`", obs.name),
            });
        };
        if !obs_keys.insert((obs.phase.clone(), obs.name.clone())) {
            return Err(ValidationError::DuplicateDecl {
                kind: "observation",
                name: format!("{}.{}", obs.phase, obs.name),
            });
        }
        if obs.components.is_empty() {
            return Err(ValidationError::EmptyObservation {
                phase: obs.phase.clone(),
                observation: obs.name.clone(),
            });
        }
        for (i, expr) in obs.components.iter().enumerate() {
            validate_poly_expr(
                expr,
                &pres.coeff_domain,
                coords,
                &empty_args,
                allowed_params,
                &format!("observation `{}.{}[{i}]`", obs.phase, obs.name),
            )?;
        }
    }

    Ok(())
}
