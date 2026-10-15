//! view・law・local・change・relation の署名・式・変更結果と参照循環の検査。

use super::ast::*;
use super::check::*;
use super::expr::*;
use super::model::*;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
use crate::types::Type;
use std::collections::{BTreeMap, BTreeSet};

impl Checker {
    pub(super) fn check_bodies_controlled<E: InputError>(
        &mut self,
        control: &mut Control,
    ) -> Result<(), E> {
        let ast = self.ast.clone();
        // 先に全 view の署名を解決し、本体から呼べるようにする。
        for (ri, r) in ast.iter().enumerate() {
            E::checkpoint(control, Checkpoint::LawIteration)?;
            self.current_reading = ri;
            for d in &r.decls {
                E::checkpoint(control, Checkpoint::LawIteration)?;
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
            E::checkpoint(control, Checkpoint::LawIteration)?;
            self.current_reading = ri;
            for d in &r.decls {
                E::checkpoint(control, Checkpoint::LawIteration)?;
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
        self.check_reading_cycles()?;
        E::checkpoint(control, Checkpoint::LawIteration)?;
        Ok(())
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
}
