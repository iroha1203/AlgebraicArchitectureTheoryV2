//! view・law・local・change・relation の署名と式、宣言の解決結果、語彙 manifest。

use super::ast::*;
use super::check::*;
use super::expr::*;
use super::model::*;
use crate::canonical::{Json, sha256_digest};
use crate::types::Type;
use std::collections::{BTreeMap, BTreeSet};

impl Checker {
    pub fn check_bodies(&mut self) -> CResult<()> {
        let ast = self.ast.clone();
        // 先に全 view の署名を解決し、本体から呼べるようにする。
        for (ri, r) in ast.iter().enumerate() {
            self.current_reading = ri;
            for d in &r.decls {
                if let DeclKind::View {
                    params,
                    returns,
                    body,
                } = &d.kind
                {
                    let name = full(&r.name.name, &[&d.name.name]);
                    self.refs = Vec::new();
                    let params = self.params(ri, params, false)?;
                    let tctx = TypeCtx {
                        reading: ri,
                        index: &params,
                        allow_path: true,
                        ref_free: false,
                        validate: true,
                    };
                    let returns = self.resolve_type(returns, &tctx)?;
                    self.sigs.insert(
                        name.clone(),
                        Signature::View {
                            params,
                            returns,
                            body: *body,
                        },
                    );
                    let refs = std::mem::take(&mut self.refs);
                    self.decl_refs.insert(name, refs);
                }
            }
        }
        for (ri, r) in ast.iter().enumerate() {
            self.current_reading = ri;
            for d in &r.decls {
                if d.kind.is_primitive() {
                    continue;
                }
                let name = full(&r.name.name, &[&d.name.name]);
                self.refs = self.decl_refs.remove(&name).unwrap_or_default();
                let mut exprs = Vec::new();
                let sig = self.check_decl_body(ri, &name, d, &mut exprs)?;
                exprs.sort_by_key(|e: &ResolvedExpression| (e.span.0, e.kind));
                self.decl_exprs.insert(name.clone(), exprs);
                let refs = std::mem::take(&mut self.refs);
                self.decl_refs.insert(name.clone(), refs);
                self.sigs.insert(name, sig);
            }
        }
        self.check_view_cycles()?;
        self.check_reading_cycles()
    }

    fn params(&mut self, ri: usize, fields: &[Field], change: bool) -> CResult<Vec<Param>> {
        let mut ps: Vec<Param> = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            let value_only = change && i > 0;
            let tctx = TypeCtx {
                reading: ri,
                index: &ps,
                allow_path: !value_only,
                ref_free: value_only,
                validate: true,
            };
            let ty = self.resolve_type(&f.ty, &tctx)?;
            if change
                && i == 0
                && !matches!(
                    ty.ref_target().and_then(|n| self.decl_kind(n)),
                    Some("entity")
                )
            {
                return syntax(f.ty.span(), "change の第1引数は entity の参照");
            }
            ps.push(Param {
                name: f.name.name.clone(),
                ty,
                span: f.name.span,
            });
        }
        Ok(ps)
    }

    fn env_for(&mut self, params: &[Param]) -> CResult<Env> {
        let mut env = Env::default();
        for (i, p) in params.iter().enumerate() {
            let id = Ident {
                name: p.name.clone(),
                span: p.span,
                tok: 0,
            };
            self.bind(&mut env, &id, p.ty.clone(), Origin::Param(i))?;
        }
        Ok(env)
    }

    fn check_decl_body(
        &mut self,
        ri: usize,
        name: &str,
        d: &Decl,
        exprs: &mut Vec<ResolvedExpression>,
    ) -> CResult<Signature> {
        let mut ctx = Ctx {
            reading: ri,
            decl: name.to_owned(),
            is_view: false,
            rec: None,
            term: false,
        };
        let mut record = |me: &mut Self, kind, id: ExprId, ty: Type| {
            exprs.push(ResolvedExpression {
                kind,
                span: me.parser.exprs[id].span,
                ty,
            });
        };
        Ok(match &d.kind {
            DeclKind::View { body, .. } => {
                let Some(Signature::View {
                    params, returns, ..
                }) = self.sigs.get(name).cloned()
                else {
                    unreachable!()
                };
                ctx.is_view = true;
                ctx.rec = params.iter().enumerate().find_map(|(i, p)| match &p.ty {
                    Type::Data(dname) => Some((i, dname.clone())),
                    _ => None,
                });
                let mut env = self.env_for(&params)?;
                let t = self.check(*body, Some(&returns), &mut env, &ctx)?;
                record(self, ExpressionKind::Body, *body, t);
                Signature::View {
                    params,
                    returns,
                    body: *body,
                }
            }
            DeclKind::Law {
                role,
                params,
                guard,
                body,
            } => {
                let params = self.params(ri, params, false)?;
                let mut env = self.env_for(&params)?;
                if let Some(g) = guard {
                    let t = self.check(*g, Some(&Type::Bool), &mut env, &ctx)?;
                    record(self, ExpressionKind::Guard, *g, t);
                }
                let t = self.check(*body, Some(&Type::Bool), &mut env, &ctx)?;
                record(self, ExpressionKind::Body, *body, t);
                Signature::Law {
                    role: *role,
                    params,
                    guard: *guard,
                    body: *body,
                }
            }
            DeclKind::Local {
                params,
                guard,
                reads,
            } => {
                let params = self.params(ri, params, false)?;
                let mut env = self.env_for(&params)?;
                if let Some(g) = guard {
                    let t = self.check(*g, Some(&Type::Bool), &mut env, &ctx)?;
                    record(self, ExpressionKind::Guard, *g, t);
                }
                for r in reads {
                    let t = self.check(*r, None, &mut env, &ctx)?;
                    record(self, ExpressionKind::Read, *r, t);
                }
                Signature::Local {
                    params,
                    guard: *guard,
                    reads: reads.clone(),
                }
            }
            DeclKind::Change {
                params,
                guard,
                body,
            } => {
                if params.is_empty() {
                    return syntax(d.name.span, "change は第1引数に entity の参照を持つ");
                }
                let params = self.params(ri, params, true)?;
                let mut env = self.env_for(&params)?;
                if let Some(g) = guard {
                    let t = self.check(*g, Some(&Type::Bool), &mut env, &ctx)?;
                    record(self, ExpressionKind::Guard, *g, t);
                }
                let t = self.check_change_body(*body, &params, &mut env, &ctx)?;
                record(self, ExpressionKind::Body, *body, t);
                Signature::Change {
                    params,
                    guard: *guard,
                    body: *body,
                }
            }
            DeclKind::Relation {
                params,
                guard,
                body,
            } => {
                let params = self.params(ri, params, false)?;
                let mut env = self.env_for(&params)?;
                if let Some(g) = guard {
                    let t = self.check(*g, Some(&Type::Bool), &mut env, &ctx)?;
                    record(self, ExpressionKind::Guard, *g, t);
                }
                let (left, right) = match self.parser.exprs[*body].kind {
                    ExprKind::Binary {
                        op: BinOp::Eq,
                        lhs,
                        rhs,
                    } => (lhs, rhs),
                    _ => {
                        return syntax(
                            self.parser.exprs[*body].span,
                            "relation の body は最上位の `=` の二項式",
                        );
                    }
                };
                let lt = self.check(left, None, &mut env, &ctx)?;
                if !matches!(lt, Type::Path(..)) {
                    return syntax(self.parser.exprs[left].span, "relation の両辺は Path");
                }
                let rt = self.check(right, Some(&lt), &mut env, &ctx)?;
                record(self, ExpressionKind::RelationLeft, left, lt);
                record(self, ExpressionKind::RelationRight, right, rt);
                Signature::Relation {
                    params,
                    guard: *guard,
                    left,
                    right,
                }
            }
            _ => unreachable!("原始宣言は別に検査する"),
        })
    }

    /// change の body は第1引数の `with` 更新。owner・参照・Map は更新しない。
    fn check_change_body(
        &mut self,
        body: ExprId,
        params: &[Param],
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let t = stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
            self.check_change_result(body, params, env, ctx)
        })?;
        if self.expr_types.len() < self.parser.exprs.len() {
            self.expr_types.resize(self.parser.exprs.len(), None);
        }
        self.expr_types[body] = Some(t.clone());
        Ok(t)
    }

    /// change の body の結果の位置(括弧、if の両枝、let の本体)は、第1引数への `with` 更新。
    fn check_change_result(
        &mut self,
        body: ExprId,
        params: &[Param],
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let span = self.parser.exprs[body].span;
        let kind = self.parser.exprs[body].kind.clone();
        let result = match kind {
            ExprKind::Group(inner) => Some(self.check_change_body(inner, params, env, ctx)?),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.check(cond, Some(&Type::Bool), env, ctx)?;
                self.check_change_body(then_branch, params, env, ctx)?;
                Some(self.check_change_body(else_branch, params, env, ctx)?)
            }
            ExprKind::Let {
                name,
                value,
                body: inner,
            } => {
                let t = self.check(value, None, env, ctx)?;
                let mark = env.vars.len();
                self.bind(env, &name, t, Origin::Other)?;
                let r = self.check_change_body(inner, params, env, ctx)?;
                env.vars.truncate(mark);
                Some(r)
            }
            _ => None,
        };
        if let Some(t) = result {
            return Ok(t);
        }
        let ExprKind::With { base, updates } = self.parser.exprs[body].kind.clone() else {
            return syntax(span, "change の body の結果は第1引数の `with` 更新");
        };
        let first = &params[0];
        let mut target = base;
        while let ExprKind::Group(inner) = self.parser.exprs[target].kind {
            target = inner;
        }
        let is_first = matches!(&self.parser.exprs[target].kind, ExprKind::Dotted(p) if p.len() == 1 && p[0].name == first.name);
        if !is_first {
            return syntax(
                self.parser.exprs[base].span,
                "change の `with` は第1引数を更新する",
            );
        }
        let entity = first.ty.ref_target().expect("entity の参照").to_owned();
        self.check(base, None, env, ctx)?;
        let sig = self.sigs.get(&entity).cloned().expect("entity の署名");
        let mut seen = BTreeSet::new();
        for (field, value) in &updates {
            let Some(f) = sig.field(&field.name).cloned() else {
                return reference(
                    field.span,
                    format!("`{entity}` に field `{}` はない", field.name),
                );
            };
            if !seen.insert(field.name.clone()) {
                return duplicate(
                    field.span,
                    format!("field `{}` の更新が重複している", field.name),
                );
            }
            if field.name == "owner" || self.has_reference(&f.ty) {
                return syntax(
                    field.span,
                    "change は owner・参照・Map を含む field を更新しない",
                );
            }
            self.record(field.span, full(&entity, &[&field.name]));
            self.check(*value, Some(&f.ty), env, ctx)?;
        }
        let t = Type::Ref(entity);
        if self.expr_types.len() < self.parser.exprs.len() {
            self.expr_types.resize(self.parser.exprs.len(), None);
        }
        self.expr_types[body] = Some(t.clone());
        Ok(t)
    }

    /// view の相互呼出しは非循環。自己再帰は構造再帰として別に検査済み。
    fn check_view_cycles(&mut self) -> CResult<()> {
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (a, b, _) in &self.view_edges {
            edges.entry(a.clone()).or_default().insert(b.clone());
        }
        if let Some(n) = find_cycle(&edges) {
            let span = self
                .view_edges
                .iter()
                .find(|(a, _, _)| *a == n)
                .map(|e| e.2)
                .expect("閉路の辺");
            return cycle(span, format!("view `{n}` を含む相互呼出しが循環している"));
        }
        Ok(())
    }

    fn check_reading_cycles(&mut self) -> CResult<()> {
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (a, b, _) in &self.reading_edges {
            edges
                .entry(a.to_string())
                .or_default()
                .insert(b.to_string());
        }
        if let Some(n) = find_cycle(&edges) {
            let i: usize = n.parse().expect("reading の位置");
            let span = self
                .reading_edges
                .iter()
                .find(|(a, _, _)| *a == i)
                .map(|e| e.2)
                .expect("閉路の辺");
            return cycle(
                span,
                format!(
                    "reading `{}` を含む参照が循環している",
                    self.reading_name(i)
                ),
            );
        }
        Ok(())
    }

    // ---- 解決結果 ----

    pub fn declaration_infos(&mut self) -> Vec<DeclarationInfo> {
        let ast = self.ast.clone();
        let mut infos = Vec::new();
        for r in ast.iter() {
            let mut references: Vec<(Span, String)> = r
                .uses
                .iter()
                .map(|u| (u.reading.span, u.reading.name.clone()))
                .collect();
            references.sort();
            let has_local = r
                .decls
                .iter()
                .any(|d| matches!(d.kind, DeclKind::Local { .. }));
            infos.push(DeclarationInfo {
                name: r.name.name.clone(),
                kind: "reading",
                parameters: Vec::new(),
                fields: Vec::new(),
                returns: None,
                role: None,
                span: r.span,
                dependencies: dependencies(&references),
                references,
                expressions: Vec::new(),
                supplied: vec![if has_local {
                    SuppliedRule::LocalDeclared { span: r.span }
                } else {
                    SuppliedRule::LocalSupport { span: r.span }
                }],
            });
            for d in &r.decls {
                let name = full(&r.name.name, &[&d.name.name]);
                let sig = self.sigs[&name].clone();
                let mut references = self.decl_refs.get(&name).cloned().unwrap_or_default();
                references.sort();
                let expressions = self.decl_exprs.get(&name).cloned().unwrap_or_default();
                let pairs = |ps: &[Param]| {
                    ps.iter()
                        .map(|p| (p.name.clone(), p.ty.clone()))
                        .collect::<Vec<_>>()
                };
                let mut info = DeclarationInfo {
                    name: name.clone(),
                    kind: sig.kind(),
                    parameters: Vec::new(),
                    fields: Vec::new(),
                    returns: None,
                    role: None,
                    span: d.span,
                    dependencies: dependencies(&references),
                    references: references.clone(),
                    expressions,
                    supplied: Vec::new(),
                };
                let guard_omitted = |g: &Option<ExprId>| g.is_none();
                match &sig {
                    Signature::Entity {
                        params, members, ..
                    }
                    | Signature::Arrow {
                        params, members, ..
                    } => {
                        info.parameters = pairs(params);
                        info.fields = pairs(members);
                    }
                    Signature::Correspondence {
                        params,
                        members,
                        implicit,
                        ..
                    } => {
                        info.parameters = pairs(params);
                        info.fields = pairs(members);
                        if !implicit.is_empty() {
                            info.supplied.push(SuppliedRule::SameNameAlignment {
                                span: d.span,
                                pairs: implicit.clone(),
                            });
                        }
                    }
                    Signature::Data { constructors } => {
                        for c in constructors {
                            let cname = full(&name, &[&c.name]);
                            let crefs: Vec<(Span, String)> = references
                                .iter()
                                .filter(|(s, _)| s.0 >= c.span.0 && s.1 <= c.span.1)
                                .cloned()
                                .collect();
                            infos.push(DeclarationInfo {
                                name: cname,
                                kind: "data",
                                parameters: c
                                    .args
                                    .iter()
                                    .enumerate()
                                    .map(|(i, t)| (format!("arg{i}"), t.clone()))
                                    .collect(),
                                fields: Vec::new(),
                                returns: None,
                                role: None,
                                span: c.span,
                                dependencies: dependencies(&crefs),
                                references: crefs,
                                expressions: Vec::new(),
                                supplied: Vec::new(),
                            });
                        }
                    }
                    Signature::View {
                        params, returns, ..
                    } => {
                        info.parameters = pairs(params);
                        info.returns = Some(returns.clone());
                    }
                    Signature::Law {
                        role,
                        params,
                        guard,
                        ..
                    } => {
                        info.parameters = pairs(params);
                        info.role = Some(*role);
                        if guard_omitted(guard) {
                            info.supplied.push(SuppliedRule::GuardTrue { span: d.span });
                        }
                    }
                    Signature::Local { params, guard, .. }
                    | Signature::Change { params, guard, .. }
                    | Signature::Relation { params, guard, .. } => {
                        info.parameters = pairs(params);
                        if guard_omitted(guard) {
                            info.supplied.push(SuppliedRule::GuardTrue { span: d.span });
                        }
                    }
                }
                infos.push(info);
            }
        }
        infos.sort_by(|a, b| a.name.cmp(&b.name));
        infos
    }

    pub fn vocabularies(&self) -> Vec<Vocabulary> {
        let mut out = Vec::new();
        for r in self.ast.iter() {
            let mut decls: Vec<(String, Json)> = Vec::new();
            for d in &r.decls {
                let name = full(&r.name.name, &[&d.name.name]);
                let fields = |ps: &[Param]| {
                    Json::Arr(
                        ps.iter()
                            .map(|p| {
                                Json::obj([
                                    ("name", Json::str(p.name.clone())),
                                    ("type", p.ty.wire()),
                                ])
                            })
                            .collect(),
                    )
                };
                let entry = match &self.sigs[&name] {
                    Signature::Entity {
                        params, members, ..
                    }
                    | Signature::Arrow {
                        params, members, ..
                    } => Json::obj([
                        ("kind", Json::str(d.kind.name())),
                        ("name", Json::str(name.clone())),
                        ("parameters", fields(params)),
                        ("fields", fields(members)),
                        ("alignments", Json::Arr(vec![])),
                    ]),
                    Signature::Correspondence {
                        params,
                        members,
                        alignments,
                        ..
                    } => Json::obj([
                        ("kind", Json::str("correspondence")),
                        ("name", Json::str(name.clone())),
                        ("parameters", fields(params)),
                        ("fields", fields(members)),
                        (
                            "alignments",
                            Json::Arr(
                                alignments
                                    .iter()
                                    .map(|(s, t)| {
                                        Json::obj([
                                            ("source", Json::str(s.clone())),
                                            ("target", Json::str(t.clone())),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                    ]),
                    Signature::Data { constructors } => Json::obj([
                        ("kind", Json::str("data")),
                        ("name", Json::str(name.clone())),
                        (
                            "constructors",
                            Json::Arr(
                                constructors
                                    .iter()
                                    .map(|c| {
                                        Json::obj([
                                            ("name", Json::str(c.name.clone())),
                                            (
                                                "arguments",
                                                Json::Arr(c.args.iter().map(Type::wire).collect()),
                                            ),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                    ]),
                    _ => continue,
                };
                decls.push((name, entry));
            }
            decls.sort_by(|a, b| a.0.cmp(&b.0));
            let manifest = Json::obj([
                ("semantics", Json::str(super::SEMANTICS)),
                ("reading", Json::str(r.name.name.clone())),
                (
                    "declarations",
                    Json::Arr(decls.into_iter().map(|(_, j)| j).collect()),
                ),
            ]);
            let digest = sha256_digest(manifest.canonical().as_bytes());
            out.push(Vocabulary {
                reading: r.name.name.clone(),
                manifest,
                digest,
            });
        }
        out.sort_by(|a, b| a.reading.cmp(&b.reading));
        out
    }
}

/// resolution.references の解決先を重複なく辞書順に並べる。
fn dependencies(references: &[(Span, String)]) -> Vec<String> {
    references
        .iter()
        .map(|(_, n)| n.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}
