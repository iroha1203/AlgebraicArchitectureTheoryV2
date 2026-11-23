//! `archsig.law/2` 内の SHIGURE 宣言群の静的検査（名前・型・参照・素数・意味 Law 保護）。

use super::check_diagram::check_diagram;
use super::check_path::check_path;
use super::check_relations::{
    check_change_spec, check_comparison, check_eval_condition, check_task,
};
use super::check_transfer::check_transfer;
use super::*;
use crate::definition::CheckedDefinitions;
use crate::law::ast::{QName, Span};
use crate::law::check::{Checker, check_decl_name, duplicate, full, reference, syntax};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Details, Issue, Location};
use archsig_common::json::InputError;
use archsig_common::prime::is_prime_controlled;
use archsig_common::types::Type;
use num_bigint::BigUint;
use std::collections::{BTreeSet, HashMap, HashSet};

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

pub(super) type CResult<T, E> = Result<T, E>;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum DeclCategory {
    Presentation,
    Comparison,
    ChangeSpec,
    EvalCondition,
    Task,
    Diagram,
    Path,
    Transfer,
    Family,
    Robustness,
    Chevalley,
    Observations,
}

/// 既存の `Checker` 状態（reading・alias・vocabulary import・通常宣言名）を使って
/// 全 reading 内の SHIGURE 宣言を検査し、`CheckedShigureDecls` を構成する。
pub(crate) fn check_shigure_decls<E: InputError>(
    checker: &mut Checker<'_, E>,
    control: &Control,
) -> CResult<CheckedShigureDecls, E> {
    let readings = checker.ast.clone();
    let mut index: HashMap<String, (DeclCategory, Span, usize)> = HashMap::new();
    let mut shigure_edges: Vec<(usize, usize, Span)> = Vec::new();

    // Pass 1: 名前の一意性確認（組込み演算名・alias・原始定義 FQN・通常宣言・SHIGURE 宣言相互の衝突を拒否）
    for (r_idx, r) in readings.iter().enumerate() {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        for d in &r.shigure_decls {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            check_decl_name::<E>(d.name())?;
            if checker.aliases[r_idx].contains_key(&d.name().name) {
                return duplicate(
                    d.name().span,
                    format!(
                        "SHIGURE declaration `{}` conflicts with `use` alias in reading `{}`",
                        d.name().name,
                        r.name.name
                    ),
                );
            }
            let name = full(&r.name.name, &[&d.name().name]);
            if checker.primitive_identifier_exists(&name)? {
                return duplicate(
                    d.name().span,
                    format!("fully qualified name `{name}` conflicts with a primitive definition"),
                );
            }
            if checker.decl_index.contains_key(&name) || index.contains_key(&name) {
                return duplicate(d.name().span, format!("duplicate declaration `{name}`"));
            }
            let cat = match d {
                ShigureDeclAst::Presentation(_) => DeclCategory::Presentation,
                ShigureDeclAst::Comparison(_) => DeclCategory::Comparison,
                ShigureDeclAst::ChangeSpec(_) => DeclCategory::ChangeSpec,
                ShigureDeclAst::EvalCondition(_) => DeclCategory::EvalCondition,
                ShigureDeclAst::Task(_) => DeclCategory::Task,
                ShigureDeclAst::Diagram(_) => DeclCategory::Diagram,
                ShigureDeclAst::Path(_) => DeclCategory::Path,
                ShigureDeclAst::Transfer(_) => DeclCategory::Transfer,
                ShigureDeclAst::Family(_) => DeclCategory::Family,
                ShigureDeclAst::Robustness(_) => DeclCategory::Robustness,
                ShigureDeclAst::Chevalley(_) => DeclCategory::Chevalley,
                ShigureDeclAst::Observations(_) => DeclCategory::Observations,
            };
            index.insert(name, (cat, d.span(), r_idx));
        }
    }

    if index.is_empty() {
        return Ok(CheckedShigureDecls::default());
    }

    let mut out = CheckedShigureDecls::default();

    // Pass 2: presentations
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            if let ShigureDeclAst::Presentation(raw) = d {
                E::checkpoint(control, Checkpoint::LawSemantics)?;
                let checked = check_presentation(raw, r_idx, &r.name.name, checker, control)?;
                out.presentations.insert(checked.name.clone(), checked);
            }
        }
    }

    // Pass 3: comparisons, change_specs, eval_conditions
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            match d {
                ShigureDeclAst::Comparison(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_comparison(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        &index,
                        &out.presentations,
                        &mut shigure_edges,
                        control,
                    )?;
                    out.comparisons.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::ChangeSpec(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_change_spec(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        &index,
                        &out.presentations,
                        &mut shigure_edges,
                        control,
                    )?;
                    out.change_specs.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::EvalCondition(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_eval_condition(raw, &r.name.name, control)?;
                    out.eval_conditions.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Presentation(_)
                | ShigureDeclAst::Task(_)
                | ShigureDeclAst::Diagram(_)
                | ShigureDeclAst::Path(_)
                | ShigureDeclAst::Transfer(_)
                | ShigureDeclAst::Family(_)
                | ShigureDeclAst::Robustness(_)
                | ShigureDeclAst::Chevalley(_)
                | ShigureDeclAst::Observations(_) => {}
            }
        }
    }

    // Pass 3.5: Phase 3 families (depends on presentations, comparisons, change_specs)
    super::check_phase3_tasks::check_all_families(
        checker,
        &index,
        &mut out,
        &mut shigure_edges,
        control,
    )?;

    // Pass 4: tasks, diagrams, paths, transfers, and Phase 3 tasks
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            match d {
                ShigureDeclAst::Task(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_task(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        &index,
                        &out,
                        &mut shigure_edges,
                        control,
                    )?;
                    out.tasks.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Diagram(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_diagram(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        &index,
                        &out,
                        &mut shigure_edges,
                        control,
                    )?;
                    out.diagrams.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Path(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_path(
                        raw.as_ref(),
                        r_idx,
                        &r.name.name,
                        checker,
                        &index,
                        &out,
                        &mut shigure_edges,
                        control,
                    )?;
                    out.paths.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Transfer(raw) => {
                    E::checkpoint(control, Checkpoint::LawSemantics)?;
                    let checked = check_transfer(
                        raw,
                        r_idx,
                        &r.name.name,
                        checker,
                        &index,
                        &out,
                        &mut shigure_edges,
                        control,
                    )?;
                    out.transfers.insert(checked.name.clone(), checked);
                }
                ShigureDeclAst::Presentation(_)
                | ShigureDeclAst::Comparison(_)
                | ShigureDeclAst::ChangeSpec(_)
                | ShigureDeclAst::EvalCondition(_)
                | ShigureDeclAst::Family(_)
                | ShigureDeclAst::Robustness(_)
                | ShigureDeclAst::Chevalley(_)
                | ShigureDeclAst::Observations(_) => {}
            }
        }
    }
    super::check_phase3_tasks::check_all_phase3_tasks(
        checker,
        &index,
        &mut out,
        &mut shigure_edges,
        control,
    )?;

    // reading 間の依存グラフ非循環性（通常宣言と SHIGURE 宣言の混合循環も含む）を検査する。
    if !shigure_edges.is_empty() {
        checker.reading_edges.extend(shigure_edges);
        checker.check_reading_cycles()?;
    }

    Ok(out)
}

pub(super) fn check_coeff_domain<E: InputError>(
    raw: &RawCoeffDomain,
    control: &Control,
) -> CResult<ShigureCoeffDomain, E> {
    match raw {
        RawCoeffDomain::Z(_) => Ok(ShigureCoeffDomain::Z),
        RawCoeffDomain::Q(_) => Ok(ShigureCoeffDomain::Q),
        RawCoeffDomain::Fp { modulus, span } => {
            let p = parse_prime(modulus, *span, control)?;
            Ok(ShigureCoeffDomain::Fp(p))
        }
    }
}

pub(super) fn check_point_domain<E: InputError>(
    raw: &RawPointDomain,
    control: &Control,
) -> CResult<ShigurePointDomain, E> {
    match raw {
        RawPointDomain::AlgebraicClosure(_) => Ok(ShigurePointDomain::AlgebraicClosure),
        RawPointDomain::RationalPoints(_) => Ok(ShigurePointDomain::RationalPoints),
        RawPointDomain::IntegerPoints(_) => Ok(ShigurePointDomain::IntegerPoints),
        RawPointDomain::UniversalRing(_) => Ok(ShigurePointDomain::UniversalRing),
        RawPointDomain::FiniteFieldPoints { modulus, span } => {
            let p = parse_prime(modulus, *span, control)?;
            Ok(ShigurePointDomain::FiniteFieldPoints(p))
        }
    }
}

fn parse_prime<E: InputError>(modulus: &str, span: Span, control: &Control) -> CResult<BigUint, E> {
    let p = modulus
        .parse::<BigUint>()
        .map_err(|_| Box::new(Issue::law(Code::Syntax, span, "invalid prime modulus")))?;
    let prime = is_prime_controlled::<E>(&p, control, Checkpoint::LawSemantics)?;
    if !prime {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!("Fp modulus `{modulus}` must be prime"),
        ))
        .into());
    }
    Ok(p)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum LiteralDomainRule<'a> {
    Exact(&'a ShigureCoeffDomain),
    /// `algebraic_closure` / `rational_points`: `Z`/`Q` のみ許可、`fp(...)` は拒否。
    NonFp,
    /// `universal_ring` 単独（`task` 側で `spec.coeff_domain` に照合する）。
    Any,
}

pub(super) fn check_poly_literals<E: InputError>(
    expr: &ShigurePolyExpr,
    rule: LiteralDomainRule<'_>,
    span: Span,
    control: &Control,
) -> CResult<(), E> {
    stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match expr {
            ShigurePolyExpr::Var(_) => Ok(()),
            ShigurePolyExpr::Int(n) => {
                if let LiteralDomainRule::Exact(ShigureCoeffDomain::Fp(p)) = rule {
                    let valid = n.to_biguint().is_some_and(|u| &u < p);
                    if !valid {
                        return Err(Box::new(Issue::law(
                            Code::Type,
                            span,
                            format!(
                                "integer literal `{n}` in Fp({p}) must satisfy 0 <= value < {p}"
                            ),
                        ))
                        .into());
                    }
                }
                Ok(())
            }
            ShigurePolyExpr::Rat { .. } => {
                if let LiteralDomainRule::Exact(d) = rule
                    && !matches!(d, ShigureCoeffDomain::Q)
                {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        span,
                        "rational literal `rat(n,d)` is only valid in coefficient domain Q",
                    ))
                    .into());
                }
                Ok(())
            }
            ShigurePolyExpr::Fp { value, modulus } => {
                let prime = is_prime_controlled::<E>(modulus, control, Checkpoint::LawSemantics)?;
                if !prime {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        span,
                        format!("Fp literal modulus `{modulus}` must be prime"),
                    ))
                    .into());
                }
                if value >= modulus {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        span,
                        format!("Fp literal `{value}` must satisfy 0 <= value < {modulus}"),
                    ))
                    .into());
                }
                match rule {
                    LiteralDomainRule::NonFp => {
                        return Err(Box::new(Issue::law(
                            Code::Type,
                            span,
                            "Fp literal is incompatible with characteristic-0 point domain",
                        ))
                        .into());
                    }
                    LiteralDomainRule::Exact(ShigureCoeffDomain::Fp(expected))
                        if expected == modulus => {}
                    LiteralDomainRule::Exact(_) => {
                        return Err(Box::new(Issue::law(
                            Code::Type,
                            span,
                            "Fp literal modulus does not match declaration coefficient domain",
                        ))
                        .into());
                    }
                    LiteralDomainRule::Any => {}
                }
                Ok(())
            }
            ShigurePolyExpr::Neg(a) | ShigurePolyExpr::Pow(a, _) => {
                check_poly_literals(a, rule, span, control)
            }
            ShigurePolyExpr::Add(a, b)
            | ShigurePolyExpr::Sub(a, b)
            | ShigurePolyExpr::Mul(a, b) => {
                check_poly_literals(a, rule.clone(), span, control)?;
                check_poly_literals(b, rule, span, control)
            }
        }
    })
}

fn check_presentation<E: InputError>(
    raw: &RawPresentation,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigurePresentation, E> {
    let full_name = full(reading_name, &[&raw.name.name]);
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;

    let mut sort_names = HashSet::new();
    let mut sorts = Vec::with_capacity(raw.sorts.len());
    for s in &raw.sorts {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if s.rank == 0 {
            return Err(Box::new(Issue::law(
                Code::Type,
                s.span,
                format!("sort `{}` must have rank >= 1", s.name.name),
            ))
            .into());
        }
        if !sort_names.insert(s.name.name.clone()) {
            return duplicate(s.name.span, format!("duplicate sort `{}`", s.name.name));
        }
        sorts.push(ShigureSortDecl {
            name: s.name.name.clone(),
            rank: s.rank,
            span: s.span,
        });
    }

    let mut phase_coords: HashMap<String, HashSet<String>> = HashMap::new();
    let mut phases = Vec::with_capacity(raw.phases.len());
    for ph in &raw.phases {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if phase_coords.contains_key(&ph.name.name) {
            return duplicate(ph.name.span, format!("duplicate phase `{}`", ph.name.name));
        }
        let mut coords = Vec::with_capacity(ph.coords.len());
        let mut coord_names = HashSet::new();
        for c in &ph.coords {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !coord_names.insert(c.name.name.clone()) {
                return duplicate(
                    c.name.span,
                    format!(
                        "duplicate coordinate `{}` in phase `{}`",
                        c.name.name, ph.name.name
                    ),
                );
            }
            if !sort_names.contains(&c.sort.name) {
                return reference(
                    c.sort.span,
                    format!(
                        "unknown sort `{}` in coordinate `{}`",
                        c.sort.name, c.name.name
                    ),
                );
            }
            let binding = match &c.binding {
                RawCoordBinding::Symbolic => ShigureCoordBinding::Symbolic,
                RawCoordBinding::ObservedField { field, span } => resolve_observed_field(
                    field,
                    *span,
                    &coeff_domain,
                    &checker.imports[r_idx],
                    checker.definitions,
                )?,
            };
            coords.push(ShigureCoordDecl {
                name: c.name.name.clone(),
                sort: c.sort.name.clone(),
                binding,
                span: c.span,
            });
        }
        let mut law_names = HashSet::new();
        let mut state_laws = Vec::with_capacity(ph.state_laws.len());
        for l in &ph.state_laws {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !law_names.insert(l.name.name.clone()) {
                return duplicate(
                    l.name.span,
                    format!(
                        "duplicate state law `{}` in phase `{}`",
                        l.name.name, ph.name.name
                    ),
                );
            }
            check_poly_literals(
                &l.expr,
                LiteralDomainRule::Exact(&coeff_domain),
                l.span,
                control,
            )?;
            state_laws.push(ShigureStateLawDecl {
                name: l.name.name.clone(),
                kind: l.kind,
                expr: l.expr.clone(),
                span: l.span,
            });
        }
        phase_coords.insert(ph.name.name.clone(), coord_names);
        phases.push(ShigurePhaseDecl {
            name: ph.name.name.clone(),
            coords,
            state_laws,
            span: ph.span,
        });
    }

    let mut op_names = HashSet::new();
    let mut operations = Vec::with_capacity(raw.operations.len());
    for op in &raw.operations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !op_names.insert(op.name.name.clone()) {
            return duplicate(
                op.name.span,
                format!("duplicate operation `{}`", op.name.name),
            );
        }
        let Some(source_coords) = phase_coords.get(&op.source_phase.name) else {
            return reference(
                op.source_phase.span,
                format!("unknown source phase `{}`", op.source_phase.name),
            );
        };
        let Some(target_coords) = phase_coords.get(&op.target_phase.name) else {
            return reference(
                op.target_phase.span,
                format!("unknown target phase `{}`", op.target_phase.name),
            );
        };
        let mut arg_names = HashSet::new();
        let mut args = Vec::with_capacity(op.args.len());
        for (a_name, a_sort) in &op.args {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !arg_names.insert(a_name.name.clone()) {
                return duplicate(a_name.span, format!("duplicate argument `{}`", a_name.name));
            }
            if source_coords.contains(&a_name.name) {
                return duplicate(
                    a_name.span,
                    format!(
                        "argument `{}` of operation `{}` collides with coordinate of source phase `{}`",
                        a_name.name, op.name.name, op.source_phase.name
                    ),
                );
            }
            if !sort_names.contains(&a_sort.name) {
                return reference(
                    a_sort.span,
                    format!(
                        "unknown sort `{}` in argument `{}`",
                        a_sort.name, a_name.name
                    ),
                );
            }
            args.push((a_name.name.clone(), a_sort.name.clone()));
        }
        let mut seen_updates = HashSet::new();
        let mut updates = Vec::with_capacity(op.updates.len());
        for (u_name, u_expr) in &op.updates {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if !target_coords.contains(&u_name.name) {
                return reference(
                    u_name.span,
                    format!(
                        "update targets unknown coordinate `{}` of phase `{}`",
                        u_name.name, op.target_phase.name
                    ),
                );
            }
            if !seen_updates.insert(u_name.name.clone()) {
                return duplicate(
                    u_name.span,
                    format!("duplicate update for coordinate `{}`", u_name.name),
                );
            }
            check_poly_literals(
                u_expr,
                LiteralDomainRule::Exact(&coeff_domain),
                op.span,
                control,
            )?;
            updates.push((u_name.name.clone(), u_expr.clone()));
        }
        if seen_updates.len() != target_coords.len() {
            return Err(Box::new(Issue::law(
                Code::Type,
                op.span,
                format!(
                    "operation `{}` must assign every coordinate of target phase `{}`",
                    op.name.name, op.target_phase.name
                ),
            ))
            .into());
        }
        let domain_laws = super::check_ext_common::check_state_law_list(
            &op.domain_laws,
            &coeff_domain,
            &format!("operation `{}`", op.name.name),
            control,
        )?;
        operations.push(ShigureOperationDecl {
            name: op.name.name.clone(),
            source_phase: op.source_phase.name.clone(),
            target_phase: op.target_phase.name.clone(),
            args,
            domain_laws,
            updates,
            span: op.span,
        });
    }

    let mut obs_keys = HashSet::new();
    let mut observations = Vec::with_capacity(raw.observations.len());
    for obs in &raw.observations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !phase_coords.contains_key(&obs.phase.name) {
            return reference(
                obs.phase.span,
                format!(
                    "unknown phase `{}` in observation `{}`",
                    obs.phase.name, obs.name.name
                ),
            );
        }
        if !obs_keys.insert((obs.phase.name.clone(), obs.name.name.clone())) {
            return duplicate(
                obs.name.span,
                format!(
                    "duplicate observation `{}` on phase `{}`",
                    obs.name.name, obs.phase.name
                ),
            );
        }
        if obs.components.is_empty() {
            return syntax(
                obs.span,
                format!(
                    "observation `{}` must have at least one component",
                    obs.name.name
                ),
            );
        }
        for comp in &obs.components {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            check_poly_literals(
                comp,
                LiteralDomainRule::Exact(&coeff_domain),
                obs.span,
                control,
            )?;
        }
        observations.push(ShigureObservationDecl {
            name: obs.name.name.clone(),
            phase: obs.phase.name.clone(),
            components: obs.components.clone(),
            span: obs.span,
        });
    }

    Ok(ShigurePresentation {
        name: full_name,
        reading: reading_name.to_owned(),
        coeff_domain,
        sorts,
        phases,
        operations,
        observations,
        span: raw.span,
    })
}

pub(super) fn resolve_observed_field<E: InputError>(
    qname: &QName,
    span: Span,
    domain: &ShigureCoeffDomain,
    imported_vocabs: &BTreeSet<String>,
    definitions: &CheckedDefinitions,
) -> CResult<ShigureCoordBinding, E> {
    let parts: Vec<&str> = qname.parts.iter().map(|p| p.name.as_str()).collect();
    let (entity_full, field_short) = match parts.as_slice() {
        [entity, field] => {
            let mut matches = Vec::new();
            for ns in imported_vocabs {
                let candidate = format!("{ns}.{entity}");
                if definitions.declarations.contains_key(&candidate) {
                    matches.push(candidate);
                }
            }
            if matches.is_empty() {
                return reference(
                    span,
                    format!("unknown primitive entity `{entity}` in imported vocabularies"),
                );
            }
            if matches.len() > 1 {
                return reference(
                    span,
                    format!(
                        "ambiguous entity `{entity}` across imported vocabularies; use qualified name"
                    ),
                );
            }
            (matches.remove(0), *field)
        }
        [ns, entity, field] => {
            if !imported_vocabs.contains(*ns) {
                return reference(
                    span,
                    format!("vocabulary `{ns}` is not imported in this reading"),
                );
            }
            let candidate = format!("{ns}.{entity}");
            if !definitions.declarations.contains_key(&candidate) {
                return reference(span, format!("unknown primitive declaration `{candidate}`"));
            }
            (candidate, *field)
        }
        _ => {
            return syntax(
                span,
                "observed field binding must be `Entity.field` or `Namespace.Entity.field`",
            );
        }
    };

    let decl = &definitions.declarations[&entity_full];
    let Some((params, fields)) = decl.signature.record_fields() else {
        return Err(Box::new(Issue::law(
            Code::Type,
            span,
            format!("`{entity_full}` is not an entity/arrow/correspondence with fields"),
        ))
        .into());
    };
    let Some(field_def) = params.iter().chain(fields).find(|f| f.name == field_short) else {
        return reference(
            span,
            format!("unknown field `{field_short}` on `{entity_full}`"),
        );
    };
    let expected_ty = match domain {
        ShigureCoeffDomain::Z => Type::Z,
        ShigureCoeffDomain::Q => Type::Q,
        ShigureCoeffDomain::Fp(p) => Type::Fp(p.to_string()),
    };
    if field_def.ty != expected_ty {
        return Err(Box::new(Issue {
            code: Code::Type,
            message: format!(
                "observed field `{entity_full}.{field_short}` type does not match presentation coefficient domain"
            ),
            location: Location::Law { span },
            details: Details::Type {
                expected: expected_ty,
                actual: field_def.ty.clone(),
            },
        })
        .into());
    }
    Ok(ShigureCoordBinding::ObservedField {
        entity: entity_full.clone(),
        field: format!("{entity_full}.{field_short}"),
        span,
    })
}

pub(super) fn resolve_shigure_ref<E: InputError>(
    qname: &QName,
    expected: DeclCategory,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    index: &HashMap<String, (DeclCategory, Span, usize)>,
    edges: &mut Vec<(usize, usize, Span)>,
) -> CResult<String, E> {
    let parts: Vec<&str> = qname.parts.iter().map(|p| p.name.as_str()).collect();
    let resolved = match parts.as_slice() {
        [short] => full(reading_name, &[short]),
        [prefix, short] => {
            if let Some(target_reading) = checker.aliases[r_idx].get(*prefix) {
                full(target_reading, &[short])
            } else {
                full(prefix, &[short])
            }
        }
        _ => {
            return reference(
                qname.span(),
                format!("invalid SHIGURE declaration reference `{}`", qname.text()),
            );
        }
    };
    let Some((cat, _, target_r_idx)) = index.get(&resolved) else {
        return reference(
            qname.span(),
            format!("unknown SHIGURE declaration `{}`", qname.text()),
        );
    };
    if *cat != expected {
        return Err(Box::new(Issue::law(
            Code::Type,
            qname.span(),
            format!("SHIGURE declaration `{resolved}` has unexpected kind"),
        ))
        .into());
    }
    if *target_r_idx != r_idx {
        edges.push((r_idx, *target_r_idx, qname.span()));
    }
    Ok(resolved)
}

/// 反復走査で `ShigurePolyExpr::Var` がすべて許可変数集合に含まれることを検査する。
pub(super) fn check_poly_vars<E: InputError>(
    expr: &ShigurePolyExpr,
    allowed: &HashSet<&str>,
    span: Span,
    context: &str,
    control: &Control,
) -> CResult<(), E> {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        match node {
            ShigurePolyExpr::Var(v) => {
                if !allowed.contains(v.as_str()) {
                    return reference(span, format!("unknown variable `{v}` in {context}"));
                }
            }
            ShigurePolyExpr::Int(_) | ShigurePolyExpr::Rat { .. } | ShigurePolyExpr::Fp { .. } => {}
            ShigurePolyExpr::Neg(a) | ShigurePolyExpr::Pow(a, _) => stack.push(a),
            ShigurePolyExpr::Add(a, b)
            | ShigurePolyExpr::Sub(a, b)
            | ShigurePolyExpr::Mul(a, b) => {
                stack.push(b);
                stack.push(a);
            }
        }
    }
    Ok(())
}

/// 表示内の全式（`state_laws`・`operations`・`observations`）に対し、
/// 変数参照と名前空間衝突（座標・引数・パラメータ）を検査する。
/// `params == None` のとき `before` 表示としてパラメータを一切許可しない。
pub(super) fn check_presentation_vars<E: InputError>(
    pres: &ShigurePresentation,
    params: Option<&HashSet<&str>>,
    control: &Control,
) -> CResult<(), E> {
    let mut phase_coords: HashMap<&str, HashSet<&str>> = HashMap::new();
    for ph in &pres.phases {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let mut coords: HashSet<&str> = HashSet::new();
        for c in &ph.coords {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if let Some(ps) = params
                && ps.contains(c.name.as_str())
            {
                return duplicate(
                    c.span,
                    format!(
                        "coordinate `{}` in `{}.{}` collides with change_spec parameter",
                        c.name, pres.name, ph.name
                    ),
                );
            }
            coords.insert(c.name.as_str());
        }
        let mut allowed = coords.clone();
        if let Some(ps) = params {
            allowed.extend(ps.iter().copied());
        }
        for l in &ph.state_laws {
            let ctx = format!("{}.{}.{}", pres.name, ph.name, l.name);
            check_poly_vars(&l.expr, &allowed, l.span, &ctx, control)?;
        }
        phase_coords.insert(ph.name.as_str(), coords);
    }

    for op in &pres.operations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let mut allowed = phase_coords[op.source_phase.as_str()].clone();
        for (a_name, _) in &op.args {
            E::checkpoint(control, Checkpoint::LawSemantics)?;
            if let Some(ps) = params
                && ps.contains(a_name.as_str())
            {
                return duplicate(
                    op.span,
                    format!(
                        "argument `{a_name}` in `{}.{}` collides with change_spec parameter",
                        pres.name, op.name
                    ),
                );
            }
            allowed.insert(a_name.as_str());
        }
        if let Some(ps) = params {
            allowed.extend(ps.iter().copied());
        }
        for l in &op.domain_laws {
            let ctx = format!("{}.{}.domain_law.{}", pres.name, op.name, l.name);
            check_poly_vars(&l.expr, &allowed, l.span, &ctx, control)?;
        }
        for (u_name, u_expr) in &op.updates {
            let ctx = format!("{}.{}.{u_name}", pres.name, op.name);
            check_poly_vars(u_expr, &allowed, op.span, &ctx, control)?;
        }
    }

    for obs in &pres.observations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let mut allowed = phase_coords[obs.phase.as_str()].clone();
        if let Some(ps) = params {
            allowed.extend(ps.iter().copied());
        }
        let ctx = format!("{}.{}.{}", pres.name, obs.phase, obs.name);
        for comp in &obs.components {
            check_poly_vars(comp, &allowed, obs.span, &ctx, control)?;
        }
    }
    Ok(())
}
