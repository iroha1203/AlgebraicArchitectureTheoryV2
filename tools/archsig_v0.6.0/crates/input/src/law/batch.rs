//! Law ファイルの複数エラー一括収集。

use super::ast::*;
use super::check::*;
use super::model::*;
use super::{
    CheckedLaw, FORMAT, SEMANTICS, ir, lexer, model_digest_inner, parser, resolve_names, shigure,
};
use crate::definition::{Binding, CheckedDefinitions};
use archsig_common::canonical::sha256_digest;
use archsig_common::control::{CheckFailure, Checkpoint, Control};
use archsig_common::issue::{Code, Details, Issue, Location};
use archsig_common::json::InputError;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

type E = CheckFailure<Box<Issue>>;

/// 複数エラー収集時の Law 失敗。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawBatchFailure {
    pub issues: Vec<Issue>,
    pub bytes_digest: String,
    pub model_digest: Option<String>,
}

/// Law を検査し、独立した構文・重複・参照・型エラーを最大 `max_errors` 件まで収集する。
#[allow(clippy::result_large_err)]
pub fn check_law_batch_controlled(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &Control,
    max_errors: usize,
) -> Result<CheckedLaw, CheckFailure<LawBatchFailure>> {
    let max_errors = max_errors.max(1);
    control
        .checkpoint(Checkpoint::BeforeLaw)
        .map_err(CheckFailure::Stopped)?;
    let result = check_law_batch_processing(bytes, definitions, control, max_errors);
    match (result, control.checkpoint(Checkpoint::LawIteration)) {
        (res, Ok(())) => res,
        (_, Err(stop)) => Err(CheckFailure::Stopped(stop)),
    }
}

fn fail_single(
    err: E,
    bytes_digest: &str,
    model_digest: Option<String>,
) -> CheckFailure<LawBatchFailure> {
    match err {
        CheckFailure::Stopped(reason) => CheckFailure::Stopped(reason),
        CheckFailure::Input(issue) => CheckFailure::Input(LawBatchFailure {
            issues: vec![*issue],
            bytes_digest: bytes_digest.to_owned(),
            model_digest,
        }),
    }
}

fn check_law_batch_processing(
    bytes: &[u8],
    definitions: &CheckedDefinitions,
    control: &Control,
    max_errors: usize,
) -> Result<CheckedLaw, CheckFailure<LawBatchFailure>> {
    #[cfg(test)]
    super::entry_control_tests::BYTES_DIGEST_STARTS.with(|count| count.set(count.get() + 1));
    let bytes_digest = sha256_digest(bytes);

    let head = lexer::lex_inner::<E>(bytes, 5, control, Checkpoint::LawIteration)
        .map_err(|e| fail_single(e, &bytes_digest, None))?;
    let header = parser::Parser::<E>::with_error(head, bytes.len(), control.clone())
        .header()
        .map_err(|e| fail_single(e, &bytes_digest, None))?;
    if header.format != FORMAT || header.semantics != SEMANTICS {
        let issue = Issue {
            code: Code::UnsupportedVersion,
            message: "unsupported format or semantics".into(),
            location: Location::Law { span: header.span },
            details: Details::Version {
                found_format: header.format,
                found_semantics: Some(header.semantics),
            },
        };
        return Err(CheckFailure::Input(LawBatchFailure {
            issues: vec![issue],
            bytes_digest,
            model_digest: None,
        }));
    }

    let tokens = lexer::lex_inner::<E>(bytes, usize::MAX, control, Checkpoint::LawIteration)
        .map_err(|e| fail_single(e, &bytes_digest, None))?;
    let digest = model_digest_inner::<E>(&tokens, control)
        .map_err(|e| fail_single(e, &bytes_digest, None))?;
    let mut p = parser::Parser::<E>::with_error(tokens, bytes.len(), control.clone());
    p.header()
        .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;
    let readings = p
        .readings()
        .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;

    let mut checker =
        Checker::with_definitions(p, readings, definitions, control, Checkpoint::LawSemantics)
            .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;

    let semantic_result: Result<(), Result<Vec<Issue>, CheckFailure<Box<Issue>>>> = (|| {
        let mut issues = collect_names_batch(&mut checker, control, max_errors).map_err(Err)?;
        if issues.is_empty() {
            issues = check_bodies_batch(&mut checker, control, max_errors).map_err(Err)?;
        }
        if issues.is_empty() {
            Ok(())
        } else {
            Err(Ok(issues))
        }
    })();

    match control.checkpoint(Checkpoint::LawSemantics) {
        Err(stop) => return Err(CheckFailure::Stopped(stop)),
        Ok(()) => match semantic_result {
            Ok(()) => {}
            Err(Err(err)) => return Err(fail_single(err, &bytes_digest, Some(digest))),
            Err(Ok(issues)) => {
                return Err(CheckFailure::Input(LawBatchFailure {
                    issues,
                    bytes_digest,
                    model_digest: Some(digest),
                }));
            }
        },
    }

    let shigure_result = shigure::check::check_shigure_decls(&mut checker, control);
    let shigure = E::finish(shigure_result, control, Checkpoint::LawSemantics)
        .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;
    let infos = checker
        .declaration_infos()
        .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;

    let mut declarations = BTreeMap::new();
    for r in checker.ast.iter() {
        control
            .checkpoint(Checkpoint::LawIteration)
            .map_err(CheckFailure::Stopped)?;
        for d in &r.decls {
            control
                .checkpoint(Checkpoint::LawIteration)
                .map_err(CheckFailure::Stopped)?;
            let name = full(&r.name.name, &[&d.name.name]);
            let signature = checker.sigs[&name].clone();
            declarations.insert(
                name.clone(),
                Declaration {
                    name,
                    reading: r.name.name.clone(),
                    signature,
                    span: d.span,
                },
            );
        }
    }
    let mut expr_types = std::mem::take(&mut checker.expr_types);
    expr_types.resize(checker.parser.exprs.len(), None);
    let resolved_names = resolve_names::<E>(definitions, &declarations, &infos, control)
        .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;
    let program = ir::Program::build::<E>(
        &checker.parser.exprs,
        &expr_types,
        &infos,
        &checker.lexical,
        &checker.callees,
        &checker.resolved_fields,
        control,
    )
    .map_err(|e| fail_single(e, &bytes_digest, Some(digest.clone())))?;
    Ok(CheckedLaw {
        program,
        resolved_names,
        bytes_digest,
        model_digest: digest,
        declarations,
        exprs: std::mem::take(&mut checker.parser.exprs),
        expr_types,
        quantifier_types: std::mem::take(&mut checker.quantifier_types),
        infos,
        definitions: definitions.clone(),
        shigure,
    })
}

fn push_err(issues: &mut Vec<Issue>, max_errors: usize, err: E) -> CResult<(), E> {
    match err {
        CheckFailure::Stopped(reason) => Err(CheckFailure::Stopped(reason)),
        CheckFailure::Input(issue) => {
            if issues.len() < max_errors {
                issues.push(*issue);
            }
            Ok(())
        }
    }
}

fn collect_names_batch(
    checker: &mut Checker<'_, E>,
    control: &Control,
    max_errors: usize,
) -> CResult<Vec<Issue>, E> {
    let mut issues: Vec<Issue> = Vec::new();
    let ast = checker.ast.clone();

    for (ri, r) in ast.iter().enumerate() {
        checker.cooperate()?;
        E::checkpoint(control, Checkpoint::LawIteration)?;
        if checker.reading_index.contains_key(&r.name.name) {
            push_err(
                &mut issues,
                max_errors,
                E::from(Box::new(Issue::law(
                    Code::DuplicateId,
                    r.name.span,
                    format!("duplicate reading `{}`", r.name.name),
                ))),
            )?;
        } else {
            checker.reading_index.insert(r.name.name.clone(), ri);
        }
    }

    let mut seen_bad_vocab_bindings = BTreeSet::new();

    for (ri, r) in ast.iter().enumerate() {
        checker.cooperate()?;
        E::checkpoint(control, Checkpoint::LawIteration)?;
        let mut scope: HashSet<String> = HashSet::new();
        let mut shorts = HashSet::new();
        let mut aliases = HashMap::new();

        for u in &r.uses {
            checker.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            if !scope.insert(u.alias.name.clone()) {
                push_err(
                    &mut issues,
                    max_errors,
                    E::from(Box::new(Issue::law(
                        Code::DuplicateId,
                        u.alias.span,
                        format!("duplicate name `{}`", u.alias.name),
                    ))),
                )?;
                continue;
            }
            let Some(&target) = checker.reading_index.get(&u.reading.name) else {
                push_err(
                    &mut issues,
                    max_errors,
                    E::from(Box::new(Issue::law(
                        Code::Reference,
                        u.reading.span,
                        format!("reading `{}` is not included", u.reading.name),
                    ))),
                )?;
                continue;
            };
            if target == ri {
                push_err(
                    &mut issues,
                    max_errors,
                    E::from(Box::new(Issue::law(
                        Code::Cycle,
                        u.reading.span,
                        "a reading cannot use itself",
                    ))),
                )?;
                continue;
            }
            checker.reading_edges.push((ri, target, u.reading.span));
            aliases.insert(u.alias.name.clone(), u.reading.name.clone());
        }

        let mut imports = BTreeSet::new();
        for v in &r.vocabularies {
            checker.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            if !imports.insert(v.namespace.name.clone()) {
                push_err(
                    &mut issues,
                    max_errors,
                    E::from(Box::new(Issue::law(
                        Code::DuplicateId,
                        v.namespace.span,
                        "duplicate import of the same namespace",
                    ))),
                )?;
                continue;
            }
            if let Err(err) = checker.definitions.check_binding(&Binding {
                namespace: v.namespace.name.clone(),
                version: v.version.clone(),
                digest: v.digest.clone(),
                location: Location::Law { span: v.span },
            }) && seen_bad_vocab_bindings.insert((
                v.namespace.name.clone(),
                v.version.clone(),
                v.digest.clone(),
            )) {
                push_err(&mut issues, max_errors, E::from(err))?;
            }
        }
        checker.imports.push(imports);

        for (di, d) in r.decls.iter().enumerate() {
            checker.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            if let Err(err) = check_decl_name::<E>(&d.name) {
                push_err(&mut issues, max_errors, err)?;
                continue;
            }
            if !scope.insert(d.name.name.clone()) {
                push_err(
                    &mut issues,
                    max_errors,
                    E::from(Box::new(Issue::law(
                        Code::DuplicateId,
                        d.name.span,
                        format!("duplicate name `{}`", d.name.name),
                    ))),
                )?;
                continue;
            }
            shorts.insert(d.name.name.clone());
            let name = full(&r.name.name, &[&d.name.name]);
            if checker.primitive_identifier_exists(&name)? {
                push_err(
                    &mut issues,
                    max_errors,
                    E::from(Box::new(Issue::law(
                        Code::DuplicateId,
                        d.name.span,
                        format!(
                            "fully qualified name `{name}` conflicts with a primitive definition"
                        ),
                    ))),
                )?;
                continue;
            }
            checker.decl_index.insert(name, (ri, di));
            match &d.kind {
                DeclKind::View { params, .. }
                | DeclKind::Law { params, .. }
                | DeclKind::Local { params, .. }
                | DeclKind::Change { params, .. }
                | DeclKind::Relation { params, .. } => {
                    let mut seen = HashSet::new();
                    for f in params {
                        checker.cooperate()?;
                        E::checkpoint(control, Checkpoint::LawIteration)?;
                        if let Err(err) = check_binding_name::<E>(&f.name) {
                            push_err(&mut issues, max_errors, err)?;
                            continue;
                        }
                        if !seen.insert(f.name.name.clone()) {
                            push_err(
                                &mut issues,
                                max_errors,
                                E::from(Box::new(Issue::law(
                                    Code::DuplicateId,
                                    f.name.span,
                                    format!("duplicate parameter `{}`", f.name.name),
                                ))),
                            )?;
                        }
                    }
                }
                DeclKind::Entity { .. }
                | DeclKind::Arrow { .. }
                | DeclKind::Correspondence { .. }
                | DeclKind::Data { .. } => {
                    unreachable!("Law /2 does not accept primitive declarations")
                }
            }
        }
        checker.aliases.push(aliases);
        checker.shorts.push(shorts);
    }

    Ok(issues)
}

fn check_bodies_batch(
    checker: &mut Checker<'_, E>,
    control: &Control,
    max_errors: usize,
) -> CResult<Vec<Issue>, E> {
    let mut issues: Vec<Issue> = Vec::new();
    let ast = checker.ast.clone();

    // 1. 全 View 署名の解決エラーを一括収集する。
    let mut failed_view_sigs = false;

    for (ri, r) in ast.iter().enumerate() {
        checker.cooperate()?;
        E::checkpoint(control, Checkpoint::LawIteration)?;
        checker.current_reading = ri;
        for d in &r.decls {
            checker.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            if let DeclKind::View {
                params,
                returns,
                body,
            } = &d.kind
            {
                let name = full(&r.name.name, &[&d.name.name]);
                checker.refs = Vec::new();
                let res: CResult<(), E> = (|| {
                    let params = checker.params(ri, params, false)?;
                    let tctx = TypeCtx {
                        reading: ri,
                        index: &params,
                        allow_path: true,
                        ref_free: false,
                        validate: true,
                    };
                    let returns = checker.resolve_type(returns, &tctx)?;
                    checker.sigs.insert(
                        name.clone(),
                        Signature::View {
                            params,
                            returns,
                            body: *body,
                        },
                    );
                    let refs = std::mem::take(&mut checker.refs);
                    checker.decl_refs.insert(name, refs);
                    Ok(())
                })();
                if let Err(err) = res {
                    failed_view_sigs = true;
                    push_err(&mut issues, max_errors, err)?;
                }
            }
        }
    }

    if failed_view_sigs {
        // View 署名が 1 つでも欠けている場合でも、他の non-View 宣言パラメータ誤りだけは安全に収集できる。
        for (ri, r) in ast.iter().enumerate() {
            checker.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            checker.current_reading = ri;
            for d in &r.decls {
                if issues.len() >= max_errors {
                    break;
                }
                let param_res = match &d.kind {
                    DeclKind::Law { params, .. }
                    | DeclKind::Local { params, .. }
                    | DeclKind::Relation { params, .. } => checker.params(ri, params, false),
                    DeclKind::Change { params, .. } if !params.is_empty() => {
                        checker.params(ri, params, true)
                    }
                    _ => continue,
                };
                if let Err(err) = param_res {
                    push_err(&mut issues, max_errors, err)?;
                }
            }
        }
        return Ok(issues);
    }

    // 2. 全 View 署名が揃った状態で各宣言本文を独立に検証し、複数エラーを収集する。
    for (ri, r) in ast.iter().enumerate() {
        checker.cooperate()?;
        E::checkpoint(control, Checkpoint::LawIteration)?;
        checker.current_reading = ri;
        for d in &r.decls {
            checker.cooperate()?;
            E::checkpoint(control, Checkpoint::LawIteration)?;
            if d.kind.is_primitive() {
                continue;
            }
            let name = full(&r.name.name, &[&d.name.name]);
            checker.refs = checker.decl_refs.remove(&name).unwrap_or_default();
            let mut exprs = Vec::new();
            match checker.check_decl_body(ri, &name, d, &mut exprs) {
                Ok(sig) => {
                    exprs.sort_by_key(|e: &ResolvedExpression| (e.span.0, e.kind));
                    checker.decl_exprs.insert(name.clone(), exprs);
                    let refs = std::mem::take(&mut checker.refs);
                    checker.decl_refs.insert(name.clone(), refs);
                    checker.sigs.insert(name, sig);
                }
                Err(err) => {
                    checker.refs.clear();
                    push_err(&mut issues, max_errors, err)?;
                }
            }
        }
    }

    if !issues.is_empty() {
        return Ok(issues);
    }

    if let Err(err) = checker.check_view_cycles() {
        push_err(&mut issues, max_errors, err)?;
        return Ok(issues);
    }
    if let Err(err) = checker.check_reading_cycles() {
        push_err(&mut issues, max_errors, err)?;
        return Ok(issues);
    }
    E::checkpoint(control, Checkpoint::LawIteration)?;
    Ok(issues)
}
