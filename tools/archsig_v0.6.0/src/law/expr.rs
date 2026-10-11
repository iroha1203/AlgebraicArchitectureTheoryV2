//! 式の型検査、束縛、純粋性、構造再帰(Law 仕様 §4)。

use super::ast::*;
use super::check::*;
use super::model::*;
use crate::types::Type;
use num_bigint::BigUint;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    Param(usize),
    /// 再帰 parameter の match で得た直接の subterm。
    RecChild,
    Other,
}

#[derive(Clone, Debug)]
pub struct Binding {
    pub name: String,
    pub ty: Type,
    pub origin: Origin,
    pub span: Span,
}

/// 束縛の環境。`boundary` より前の束縛は Term の本体から見えない(捕獲の禁止)。
#[derive(Clone, Debug, Default)]
pub struct Env {
    pub vars: Vec<Binding>,
    pub boundary: usize,
}

pub enum Lookup<'a> {
    Found(&'a Binding),
    Captured,
    Missing,
}

impl Env {
    pub fn lookup(&self, name: &str) -> Lookup<'_> {
        match self.vars.iter().rposition(|b| b.name == name) {
            Some(i) if i >= self.boundary => Lookup::Found(&self.vars[i]),
            Some(_) => Lookup::Captured,
            None => Lookup::Missing,
        }
    }

    fn params(&self) -> Vec<Param> {
        self.vars[self.boundary..]
            .iter()
            .map(|b| Param {
                name: b.name.clone(),
                ty: b.ty.clone(),
                span: b.span,
            })
            .collect()
    }
}

/// 式を検査する宣言の文脈。
#[derive(Clone, Debug)]
pub struct Ctx {
    pub reading: usize,
    pub decl: String,
    pub is_view: bool,
    /// 構造再帰に使う左端の data parameter の位置とその data 型。
    pub rec: Option<(usize, String)>,
    /// Term の本体の中。
    pub term: bool,
}

/// constructor pattern の位置と、分岐がその constructor の値を残さず受けるか。
struct PatternCover {
    index: usize,
    covers: bool,
    plain: bool,
}

enum Callee {
    View(String),
    Ctor(String, usize),
    Builtin(&'static str),
    Value(Type),
}

struct Checkpoint {
    refs: usize,
    view_edges: usize,
    reading_edges: usize,
    vars: usize,
}

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

fn collection_elem(t: &Type) -> Option<Type> {
    match t {
        Type::List(e) | Type::Set(e) => Some((**e).clone()),
        _ => None,
    }
}

impl Checker {
    fn checkpoint(&self, env: &Env) -> Checkpoint {
        Checkpoint {
            refs: self.refs.len(),
            view_edges: self.view_edges.len(),
            reading_edges: self.reading_edges.len(),
            vars: env.vars.len(),
        }
    }

    fn rollback(&mut self, cp: Checkpoint, env: &mut Env) {
        self.refs.truncate(cp.refs);
        self.view_edges.truncate(cp.view_edges);
        self.reading_edges.truncate(cp.reading_edges);
        env.vars.truncate(cp.vars);
    }

    fn span(&self, id: ExprId) -> Span {
        self.parser.exprs[id].span
    }

    pub fn bind(&mut self, env: &mut Env, id: &Ident, ty: Type, origin: Origin) -> CResult<()> {
        check_binding_name(id)?;
        if env.vars.iter().any(|b| b.name == id.name) {
            return duplicate(
                id.span,
                format!("束縛名 `{}` が外側の束縛と重なる", id.name),
            );
        }
        env.vars.push(Binding {
            name: id.name.clone(),
            ty: ty.erase(),
            origin,
            span: id.span,
        });
        Ok(())
    }

    fn expr_type_ctx<'a>(&self, ctx: &Ctx, index: &'a [Param]) -> TypeCtx<'a> {
        TypeCtx {
            reading: ctx.reading,
            index,
            allow_path: !ctx.term,
            ref_free: ctx.term,
            validate: true,
        }
    }

    fn resolve_type_in(&mut self, ast: &TypeAst, env: &Env, ctx: &Ctx) -> CResult<Type> {
        let index = env.params();
        let tctx = self.expr_type_ctx(ctx, &index);
        Ok(self.resolve_type(ast, &tctx)?.erase())
    }

    /// 式を検査して型を返す。`expected` があればその型との一致を確かめる。
    pub fn check(
        &mut self,
        id: ExprId,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let t = stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            self.check_inner(id, expected, env, ctx)
        })?;
        let t = t.erase();
        if let Some(e) = expected
            && e.erase() != t
        {
            return type_error(self.span(id), e, &t, "式の型が合わない");
        }
        if self.expr_types.len() < self.parser.exprs.len() {
            self.expr_types.resize(self.parser.exprs.len(), None);
        }
        self.expr_types[id] = Some(t.clone());
        Ok(t)
    }

    fn check_bool(&mut self, id: ExprId, env: &mut Env, ctx: &Ctx) -> CResult<()> {
        self.check(id, Some(&Type::Bool), env, ctx).map(|_| ())
    }

    /// 文脈の型がないと読めない式(整数 literal、短い constructor 名)。
    fn needs_context(&mut self, id: ExprId, env: &Env) -> bool {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || self.needs_context_inner(id, env))
    }

    fn needs_context_inner(&mut self, id: ExprId, env: &Env) -> bool {
        match self.parser.exprs[id].kind.clone() {
            ExprKind::Int(_) => true,
            ExprKind::Unary {
                op: UnOp::Neg,
                operand,
            }
            | ExprKind::Group(operand)
            | ExprKind::Some(operand) => self.needs_context(operand, env),
            ExprKind::Let { body, .. } | ExprKind::Fn { body, .. } => self.needs_context(body, env),
            ExprKind::Match { arms, .. } => arms.iter().all(|a| self.needs_context(a.body, env)),
            ExprKind::Binary {
                op: BinOp::Add | BinOp::Sub | BinOp::Mul,
                lhs,
                rhs,
            } => self.needs_context(lhs, env) && self.needs_context(rhs, env),
            ExprKind::Tuple(items) => items.iter().any(|&i| self.needs_context(i, env)),
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self.needs_context(then_branch, env) && self.needs_context(else_branch, env),
            ExprKind::Dotted(parts) => parts.len() == 1 && self.is_unknown_short(&parts[0], env),
            ExprKind::Call { callee, .. } => match &self.parser.exprs[callee].kind {
                ExprKind::Dotted(parts) if parts.len() == 1 => {
                    let p = parts[0].clone();
                    !BUILTIN_OPS.contains(&p.name.as_str()) && self.is_unknown_short(&p, env)
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn is_unknown_short(&mut self, p: &Ident, env: &Env) -> bool {
        matches!(env.lookup(&p.name), Lookup::Missing)
            && self.resolve_prefix_silent_ref(p).is_none()
    }

    fn resolve_prefix_silent_ref(&mut self, p: &Ident) -> Option<(Target, usize)> {
        let reading = self.current_reading;
        self.resolve_prefix_silent(reading, std::slice::from_ref(p))
    }

    /// 二つの被演算子の共通の型。文脈の要る側を後に読む。
    fn pair_type(&mut self, l: ExprId, r: ExprId, env: &mut Env, ctx: &Ctx) -> CResult<Type> {
        if self.needs_context(l, env) && !self.needs_context(r, env) {
            let t = self.check(r, None, env, ctx)?;
            self.check(l, Some(&t), env, ctx)?;
            Ok(t)
        } else {
            let t = self.check(l, None, env, ctx)?;
            self.check(r, Some(&t), env, ctx)?;
            Ok(t)
        }
    }

    fn check_inner(
        &mut self,
        id: ExprId,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let span = self.span(id);
        let kind = self.parser.exprs[id].kind.clone();
        match kind {
            ExprKind::Int(text) => match expected.map(Type::erase).as_ref() {
                None | Some(Type::Z) => Ok(Type::Z),
                Some(Type::Q) => Ok(Type::Q),
                Some(Type::Fp(p)) => {
                    let v: BigUint = text.parse().expect("10進整数");
                    let p_val: BigUint = p.parse().expect("10進整数");
                    if v >= p_val {
                        return syntax(span, format!("整数 {text} は Fp({p}) の範囲 0..{p} の外"));
                    }
                    Ok(Type::Fp(p.clone()))
                }
                Some(other) => type_error(span, other, &Type::Z, "整数 literal の型が合わない"),
            },
            ExprKind::Str(_) => Ok(Type::Text),
            ExprKind::Bool(_) => Ok(Type::Bool),
            ExprKind::Unit => Ok(Type::Unit),
            ExprKind::Group(inner) => self.check(inner, expected, env, ctx),
            ExprKind::Tuple(items) => {
                let parts = match expected.map(Type::erase).as_ref() {
                    Some(Type::Tuple(ts)) if ts.len() == items.len() => {
                        ts.iter().cloned().map(Some).collect()
                    }
                    _ => vec![None; items.len()],
                };
                let mut out = Vec::new();
                for (i, t) in items.iter().zip(parts) {
                    out.push(self.check(*i, t.as_ref(), env, ctx)?);
                }
                Ok(Type::Tuple(out))
            }
            ExprKind::Unary {
                op: UnOp::Not,
                operand,
            } => {
                self.check_bool(operand, env, ctx)?;
                Ok(Type::Bool)
            }
            ExprKind::Unary {
                op: UnOp::Neg,
                operand,
            } => {
                let t = self.check(operand, expected, env, ctx)?;
                if !t.is_numeric() {
                    return type_error(span, &Type::Z, &t, "単項 - は Z・Q・Fp とその組");
                }
                Ok(t)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.check_binary(op, lhs, rhs, span, expected, env, ctx)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.check_bool(cond, env, ctx)?;
                if let Some(e) = expected {
                    self.check(then_branch, Some(e), env, ctx)?;
                    self.check(else_branch, Some(e), env, ctx)
                } else {
                    self.pair_type(then_branch, else_branch, env, ctx)
                }
            }
            ExprKind::Let { name, value, body } => {
                let t = self.check(value, None, env, ctx)?;
                let mark = env.vars.len();
                self.bind(env, &name, t, Origin::Other)?;
                let out = self.check(body, expected, env, ctx)?;
                env.vars.truncate(mark);
                Ok(out)
            }
            ExprKind::Match { scrutinee, arms } => {
                self.check_match(scrutinee, &arms, span, expected, env, ctx)
            }
            ExprKind::Quant {
                kind: _,
                var,
                split,
            } => {
                self.check_quant(id, &var, &split, span, env, ctx)?;
                Ok(Type::Bool)
            }
            ExprKind::Dotted(parts) => self.check_dotted(&parts, expected, env, ctx),
            ExprKind::Field { base, name } => {
                let t = self.check(base, None, env, ctx)?;
                self.project_field(&t, &name, ctx)
            }
            ExprKind::Index {
                base,
                index,
                index_span,
                ..
            } => {
                let t = self.check(base, None, env, ctx)?;
                match &t {
                    Type::Tuple(items) if index < items.len() => Ok(items[index].clone()),
                    Type::Tuple(_) => syntax(index_span, "組の位置が範囲外"),
                    other => type_error(
                        self.span(base),
                        &Type::Tuple(vec![]),
                        other,
                        "数値射影は組だけに使える",
                    ),
                }
            }
            ExprKind::Call { callee, args } => {
                self.check_call(callee, &args, span, expected, env, ctx)
            }
            ExprKind::With { .. } => syntax(span, "`with` は change の body だけに置ける"),
            ExprKind::ThenOp => syntax(span, "`then` は適用して使う"),
            ExprKind::ListLit { ty, items } => {
                let t = self.resolve_type_in(&ty, env, ctx)?;
                for i in items {
                    self.check(i, Some(&t), env, ctx)?;
                }
                Ok(Type::List(Box::new(t)))
            }
            ExprKind::SetLit { ty, items } => {
                let t = self.resolve_type_in(&ty, env, ctx)?;
                if self.has_term_or_path(&t) {
                    return syntax(ty.span(), "Set の要素型は Term・Path を含まない");
                }
                for i in items {
                    self.check(i, Some(&t), env, ctx)?;
                }
                Ok(Type::Set(Box::new(t)))
            }
            ExprKind::SetComp {
                elem,
                var,
                domain,
                filter,
            } => {
                let d = self.check(domain, None, env, ctx)?;
                let Some(e) = collection_elem(&d) else {
                    return type_error(
                        self.span(domain),
                        &Type::List(Box::new(d.clone())),
                        &d,
                        "内包の域は List か Set",
                    );
                };
                let mark = env.vars.len();
                self.bind(env, &var, e, Origin::Other)?;
                if let Some(f) = filter {
                    self.check_bool(f, env, ctx)?;
                }
                let t = self.check(elem, None, env, ctx)?;
                env.vars.truncate(mark);
                if self.has_term_or_path(&t) {
                    return syntax(self.span(elem), "Set の要素型は Term・Path を含まない");
                }
                Ok(Type::Set(Box::new(t)))
            }
            ExprKind::None(ty) => Ok(Type::Option(Box::new(self.resolve_type_in(&ty, env, ctx)?))),
            ExprKind::Some(inner) => {
                let inner_expected = match expected.map(Type::erase).as_ref() {
                    Some(Type::Option(t)) => Some((**t).clone()),
                    _ => None,
                };
                Ok(Type::Option(Box::new(self.check(
                    inner,
                    inner_expected.as_ref(),
                    env,
                    ctx,
                )?)))
            }
            ExprKind::Fn { params, body } => self.check_fn(&params, body, expected, env, ctx),
            ExprKind::Family { name, owner } => {
                if ctx.term {
                    return reference(span, "Term の本体は観測族を読めない");
                }
                let target = match self.resolve_prefix(ctx.reading, &name.parts) {
                    Some((Target::Decl(n), k)) if k == name.parts.len() => n,
                    _ => {
                        return reference(name.span(), format!("`{}` を解決できない", name.text()));
                    }
                };
                if !matches!(self.decl_kind(&target), Some("entity" | "arrow")) {
                    return syntax(name.span(), "観測族は所属を持つ entity・arrow の名前");
                }
                let Some(root) = self.owner_root(&target) else {
                    return syntax(name.span(), format!("`{}` は所属先を持たない", name.text()));
                };
                self.record(name.span(), target.clone());
                self.check(owner, Some(&Type::Ref(root)), env, ctx)?;
                Ok(Type::Set(Box::new(Type::Ref(target))))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn check_binary(
        &mut self,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        span: Span,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        match op {
            BinOp::And | BinOp::Or | BinOp::Implies => {
                self.check_bool(lhs, env, ctx)?;
                self.check_bool(rhs, env, ctx)?;
                Ok(Type::Bool)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let t = if let Some(e) = expected {
                    self.check(lhs, Some(e), env, ctx)?;
                    self.check(rhs, Some(e), env, ctx)?
                } else {
                    self.pair_type(lhs, rhs, env, ctx)?
                };
                if !t.is_numeric() {
                    return type_error(span, &Type::Z, &t, "算術は Z・Q・Fp とその組");
                }
                Ok(t)
            }
            BinOp::Eq | BinOp::Ne => {
                self.pair_type(lhs, rhs, env, ctx)?;
                Ok(Type::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let t = self.pair_type(lhs, rhs, env, ctx)?;
                if t != Type::Z && t != Type::Q {
                    return type_error(span, &Type::Z, &t, "順序は Z と Q だけ");
                }
                Ok(Type::Bool)
            }
            BinOp::In => {
                let c = self.check(rhs, None, env, ctx)?;
                let Some(e) = collection_elem(&c) else {
                    return type_error(
                        self.span(rhs),
                        &Type::List(Box::new(c.clone())),
                        &c,
                        "`in` の右辺は List か Set",
                    );
                };
                self.check(lhs, Some(&e), env, ctx)?;
                Ok(Type::Bool)
            }
        }
    }

    fn project_field(&mut self, base: &Type, name: &Ident, ctx: &Ctx) -> CResult<Type> {
        if ctx.term {
            return reference(name.span, "Term の本体は field を読めない");
        }
        let Some(decl) = base.ref_target().map(str::to_owned) else {
            return syntax(
                name.span,
                format!("field `{}` は参照型の値から読む", name.name),
            );
        };
        let Some(field) = self
            .sigs
            .get(&decl)
            .and_then(|s| s.field(&name.name))
            .cloned()
        else {
            return reference(
                name.span,
                format!("`{decl}` に field `{}` はない", name.name),
            );
        };
        self.record(name.span, full(&decl, &[&name.name]));
        Ok(field.ty.erase())
    }

    fn check_dotted(
        &mut self,
        parts: &[Ident],
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let head = &parts[0];
        match env.lookup(&head.name) {
            Lookup::Found(b) => {
                let mut t = b.ty.clone();
                for p in &parts[1..] {
                    t = self.project_field(&t, p, ctx)?;
                }
                return Ok(t);
            }
            Lookup::Captured => {
                return reference(
                    head.span,
                    format!("Term は外側の束縛 `{}` を捕獲できない", head.name),
                );
            }
            Lookup::Missing => {}
        }
        let whole = (head.span.0, parts[parts.len() - 1].span.1);
        if parts.len() == 1 {
            if let Some((data, index)) = self.short_ctor(&head.name, expected) {
                return self.ctor_value(&data, index, head.span, &[], env, ctx);
            }
            if BUILTIN_OPS.contains(&head.name.as_str()) {
                return syntax(
                    head.span,
                    format!("組込み演算 `{}` は適用して使う", head.name),
                );
            }
        }
        match self.resolve_prefix(ctx.reading, parts) {
            Some((Target::Ctor { data, index }, k)) if k == parts.len() => {
                self.ctor_value(&data, index, whole, &[], env, ctx)
            }
            Some((Target::Decl(n), k))
                if k == parts.len() && self.decl_kind(&n) == Some("view") =>
            {
                syntax(whole, format!("view `{n}` は適用して使う"))
            }
            Some((target, k)) => {
                let shown = match target {
                    Target::Decl(n) => n,
                    Target::Ctor { data, index } => format!("{data}#{index}"),
                };
                if k < parts.len() {
                    reference(
                        parts[k].span,
                        format!("`{shown}` の後の `{}` を解決できない", parts[k].name),
                    )
                } else {
                    reference(whole, format!("宣言 `{shown}` は値として使えない"))
                }
            }
            None => reference(
                whole,
                format!(
                    "名前 `{}` を解決できない",
                    parts
                        .iter()
                        .map(|p| p.name.as_str())
                        .collect::<Vec<_>>()
                        .join(".")
                ),
            ),
        }
    }

    fn short_ctor(&self, name: &str, expected: Option<&Type>) -> Option<(String, usize)> {
        let expected = expected.map(Type::erase);
        let Some(Type::Data(d)) = expected.as_ref() else {
            return None;
        };
        let Some(Signature::Data { constructors }) = self.sigs.get(d) else {
            return None;
        };
        constructors
            .iter()
            .position(|c| c.name == name)
            .map(|i| (d.clone(), i))
    }

    fn ctor_value(
        &mut self,
        data: &str,
        index: usize,
        span: Span,
        args: &[ExprId],
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let Some(Signature::Data { constructors }) = self.sigs.get(data).cloned() else {
            unreachable!()
        };
        let c = &constructors[index];
        if c.args.len() != args.len() {
            return syntax(
                span,
                format!("constructor `{}` の引数は {} 個", c.name, c.args.len()),
            );
        }
        self.record(span, full(data, &[&c.name]));
        for (a, t) in args.iter().zip(&c.args) {
            self.check(*a, Some(t), env, ctx)?;
        }
        Ok(Type::Data(data.to_owned()))
    }

    fn strip_groups(&self, mut id: ExprId) -> ExprId {
        while let ExprKind::Group(inner) = self.parser.exprs[id].kind {
            id = inner;
        }
        id
    }

    fn resolve_callee(
        &mut self,
        callee: ExprId,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<(Callee, Span)> {
        let inner = self.strip_groups(callee);
        let span = self.span(inner);
        match self.parser.exprs[inner].kind.clone() {
            ExprKind::ThenOp => Ok((Callee::Builtin("then"), span)),
            ExprKind::Dotted(parts) => {
                let head = &parts[0];
                match env.lookup(&head.name) {
                    Lookup::Found(_) => {
                        return Ok((Callee::Value(self.check(callee, None, env, ctx)?), span));
                    }
                    Lookup::Captured => {
                        return reference(
                            head.span,
                            format!("Term は外側の束縛 `{}` を捕獲できない", head.name),
                        );
                    }
                    Lookup::Missing => {}
                }
                if parts.len() == 1 {
                    if let Some((data, index)) = self.short_ctor(&head.name, expected) {
                        return Ok((Callee::Ctor(data, index), span));
                    }
                    if let Some(b) = BUILTIN_OPS.iter().find(|b| **b == head.name) {
                        return Ok((Callee::Builtin(b), span));
                    }
                }
                match self.resolve_prefix(ctx.reading, &parts) {
                    Some((Target::Ctor { data, index }, k)) if k == parts.len() => {
                        Ok((Callee::Ctor(data, index), span))
                    }
                    Some((Target::Decl(n), k))
                        if k == parts.len() && self.decl_kind(&n) == Some("view") =>
                    {
                        self.record(span, n.clone());
                        Ok((Callee::View(n), span))
                    }
                    Some((_, k)) if k < parts.len() => {
                        reference(parts[k].span, format!("`{}` を解決できない", parts[k].name))
                    }
                    Some(_) => syntax(
                        span,
                        "適用できるのは view・Map・Term・constructor・固定演算",
                    ),
                    None => reference(
                        span,
                        format!(
                            "名前 `{}` を解決できない",
                            parts
                                .iter()
                                .map(|p| p.name.as_str())
                                .collect::<Vec<_>>()
                                .join(".")
                        ),
                    ),
                }
            }
            _ => Ok((Callee::Value(self.check(callee, None, env, ctx)?), span)),
        }
    }

    fn arity(&self, span: Span, args: &[ExprId], n: usize, what: &str) -> CResult<()> {
        if args.len() != n {
            return syntax(span, format!("{what} の引数は {n} 個"));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn check_call(
        &mut self,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let (target, name_span) = self.resolve_callee(callee, expected, env, ctx)?;
        match target {
            Callee::Ctor(data, index) => self.ctor_value(&data, index, name_span, args, env, ctx),
            Callee::View(view) => {
                if ctx.term {
                    return reference(name_span, "Term の本体は view を呼べない");
                }
                let Some(Signature::View {
                    params, returns, ..
                }) = self.sigs.get(&view).cloned()
                else {
                    unreachable!("view の署名は本体より先に解決する")
                };
                self.arity(span, args, params.len(), &format!("view `{view}`"))?;
                if view == ctx.decl {
                    self.check_structural_call(args, name_span, env, ctx)?;
                } else if ctx.is_view {
                    self.view_edges
                        .push((ctx.decl.clone(), view.clone(), name_span));
                }
                for (a, p) in args.iter().zip(&params) {
                    self.check(*a, Some(&p.ty.erase()), env, ctx)?;
                }
                Ok(returns.erase())
            }
            Callee::Value(t) => match &t {
                Type::Map(a, b) => {
                    self.arity(span, args, 1, "Map の適用")?;
                    self.check(args[0], Some(a), env, ctx)?;
                    Ok((**b).clone())
                }
                Type::Term(ps, r) => {
                    if ctx.term {
                        return reference(name_span, "Term の本体は Term を呼べない");
                    }
                    self.arity(span, args, ps.len(), "Term の適用")?;
                    for (a, p) in args.iter().zip(ps.iter()) {
                        self.check(*a, Some(p), env, ctx)?;
                    }
                    Ok((**r).clone())
                }
                other => syntax(
                    name_span,
                    format!("型 {} の値は適用できない", other.wire().canonical()),
                ),
            },
            Callee::Builtin(b) => self.check_builtin(b, args, span, name_span, expected, env, ctx),
        }
    }

    fn check_structural_call(
        &mut self,
        args: &[ExprId],
        span: Span,
        env: &Env,
        ctx: &Ctx,
    ) -> CResult<()> {
        let rec = ctx.rec.clone();
        let Some((index, data)) = rec else {
            return cycle(span, "view の自己再帰には左端の data parameter が要る");
        };
        let arg = self.strip_groups(args[index]);
        if let ExprKind::Dotted(parts) = &self.parser.exprs[arg].kind
            && parts.len() == 1
            && let Lookup::Found(b) = env.lookup(&parts[0].name)
            && b.origin == Origin::RecChild
            && b.ty == Type::Data(data.clone())
        {
            return Ok(());
        }
        cycle(
            self.span(args[index]),
            "自己再帰の左端の data 引数は、その parameter の match で得た直接の subterm",
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn check_builtin(
        &mut self,
        b: &str,
        args: &[ExprId],
        span: Span,
        name_span: Span,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let path_op = matches!(b, "path" | "identity" | "then" | "source" | "target");
        if ctx.term && path_op {
            return reference(name_span, format!("Term の本体は `{b}` を呼べない"));
        }
        match b {
            "rat" => {
                self.arity(span, args, 2, "rat")?;
                // 引数は整数 literal そのもの。負の有理数は単項 `-` を rat の外に置く。
                let n_ok = matches!(&self.parser.exprs[args[0]].kind, ExprKind::Int(_));
                let d_ok = matches!(&self.parser.exprs[args[1]].kind, ExprKind::Int(t) if t != "0");
                if !n_ok || !d_ok {
                    return syntax(span, "rat の引数は整数 literal で、分母は正");
                }
                self.check(args[0], Some(&Type::Z), env, ctx)?;
                self.check(args[1], Some(&Type::Z), env, ctx)?;
                Ok(Type::Q)
            }
            "count" | "sum" => {
                self.arity(span, args, 1, b)?;
                let c = self.check(args[0], None, env, ctx)?;
                let Some(e) = collection_elem(&c) else {
                    return type_error(
                        self.span(args[0]),
                        &Type::List(Box::new(c.clone())),
                        &c,
                        format!("{b} の引数は List か Set"),
                    );
                };
                if b == "count" {
                    return Ok(Type::Z);
                }
                if !e.is_numeric() {
                    return type_error(
                        self.span(args[0]),
                        &Type::List(Box::new(Type::Z)),
                        &c,
                        "sum の要素は数値",
                    );
                }
                Ok(e)
            }
            "path" => {
                self.arity(span, args, 1, "path")?;
                let t = self.check(args[0], None, env, ctx)?;
                let target = t.ref_target().map(str::to_owned);
                match target.as_ref().and_then(|n| self.sigs.get(n)) {
                    Some(Signature::Arrow { endpoint, .. }) => {
                        Ok(Type::Path(endpoint.clone(), endpoint.clone()))
                    }
                    Some(Signature::Correspondence { from, to, .. }) => {
                        Ok(Type::Path(from.clone(), to.clone()))
                    }
                    _ => syntax(
                        self.span(args[0]),
                        "path の引数は arrow か correspondence の参照",
                    ),
                }
            }
            "identity" => {
                self.arity(span, args, 1, "identity")?;
                let t = self.check(args[0], None, env, ctx)?;
                match t.ref_target() {
                    Some(n) if self.decl_kind(n) == Some("entity") => {
                        Ok(Type::Path(n.to_owned(), n.to_owned()))
                    }
                    _ => syntax(self.span(args[0]), "identity の引数は entity の参照"),
                }
            }
            "then" => {
                self.arity(span, args, 2, "then")?;
                let p = self.check(args[0], None, env, ctx)?;
                let Type::Path(a, mid) = &p else {
                    return syntax(self.span(args[0]), "then の引数は Path");
                };
                let (a, mid) = (a.clone(), mid.clone());
                let q = self.check(args[1], None, env, ctx)?;
                match &q {
                    Type::Path(m, c) if *m == mid => Ok(Type::Path(a, c.clone())),
                    Type::Path(_, c) => type_error(
                        self.span(args[1]),
                        &Type::Path(mid, c.clone()),
                        &q,
                        "then の端点が合わない",
                    ),
                    _ => syntax(self.span(args[1]), "then の引数は Path"),
                }
            }
            "source" | "target" => {
                self.arity(span, args, 1, b)?;
                match &self.check(args[0], None, env, ctx)? {
                    Type::Path(a, c) => {
                        Ok(Type::Ref(if b == "source" { a.clone() } else { c.clone() }))
                    }
                    _ => syntax(self.span(args[0]), format!("{b} の引数は Path")),
                }
            }
            _ => {
                let _ = expected;
                unreachable!("組込み演算は固定")
            }
        }
    }

    fn check_fn(
        &mut self,
        params: &[Field],
        body: ExprId,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let term_ctx = Ctx {
            term: true,
            ..ctx.clone()
        };
        let saved_boundary = env.boundary;
        let mark = env.vars.len();
        env.boundary = mark;
        let mut types = Vec::new();
        let result = (|| {
            for p in params {
                let t = self.resolve_type_in(&p.ty, env, &term_ctx)?;
                self.bind(env, &p.name, t.clone(), Origin::Other)?;
                types.push(t);
            }
            let ret_expected = match expected.map(Type::erase).as_ref() {
                Some(Type::Term(_, r)) => Some((**r).clone()),
                _ => None,
            };
            self.check(body, ret_expected.as_ref(), env, &term_ctx)
        })();
        env.vars.truncate(mark);
        env.boundary = saved_boundary;
        let ret = result?;
        if self.has_reference(&ret) {
            return syntax(
                self.span(body),
                "Term の戻り型は参照・Map・Path を含まない値型",
            );
        }
        Ok(Type::Term(types, Box::new(ret)))
    }

    // ---- match ----

    fn check_match(
        &mut self,
        scrutinee: ExprId,
        arms: &[Arm],
        span: Span,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type> {
        let st = self.check(scrutinee, None, env, ctx)?;
        // data 型の値は constructor で場合分けする。その他の型の値は `_` と束縛だけで受ける。
        let constructors = match &st {
            Type::Data(data) => match self.sigs.get(data) {
                Some(Signature::Data { constructors }) => constructors.len(),
                _ => unreachable!("data 型の署名"),
            },
            _ => 0,
        };
        let is_data = matches!(st, Type::Data(_));
        let rec_scrutinee = match &self.parser.exprs[self.strip_groups(scrutinee)].kind {
            ExprKind::Dotted(parts) if parts.len() == 1 => {
                match (env.lookup(&parts[0].name), &ctx.rec) {
                    (Lookup::Found(b), Some((i, _))) => b.origin == Origin::Param(*i),
                    _ => false,
                }
            }
            _ => false,
        };
        let mut seen = std::collections::HashSet::new();
        let mut covered = std::collections::HashSet::new();
        let mut plainly_covered = std::collections::HashSet::new();
        let mut catch_all = false;
        let mut result: Option<Type> = expected.map(Type::erase);
        let mut pending = Vec::new();
        for arm in arms {
            if catch_all {
                return syntax(arm.pattern.span(), "到達できない分岐");
            }
            let mark = env.vars.len();
            match self.check_pattern(&arm.pattern, &st, env, ctx, rec_scrutinee, true)? {
                None => {
                    if is_data && plainly_covered.len() == constructors {
                        return syntax(arm.pattern.span(), "到達できない分岐");
                    }
                    catch_all = true;
                }
                Some(PatternCover {
                    index,
                    covers,
                    plain,
                }) => {
                    if !seen.insert(index) {
                        return syntax(arm.pattern.span(), "同じ constructor の分岐が重複している");
                    }
                    if covers {
                        covered.insert(index);
                    }
                    if plain {
                        plainly_covered.insert(index);
                    }
                }
            }
            match &result {
                Some(t) => {
                    let t = t.clone();
                    self.check(arm.body, Some(&t), env, ctx)?;
                }
                None if self.needs_context(arm.body, env) => {
                    pending.push((arm.body, env.vars[mark..].to_vec()))
                }
                None => result = Some(self.check(arm.body, None, env, ctx)?),
            }
            env.vars.truncate(mark);
        }
        if !catch_all && (!is_data || covered.len() != constructors) {
            return syntax(
                span,
                "match は全 constructor を一度ずつ覆うか、末尾に `_` を置く",
            );
        }
        for (body, vars) in pending {
            let mark = env.vars.len();
            env.vars.extend(vars);
            let t = self.check(body, result.as_ref(), env, ctx)?;
            env.vars.truncate(mark);
            result.get_or_insert(t);
        }
        Ok(result.expect("分岐は一つ以上"))
    }

    /// pattern を検査して束縛を加える。constructor pattern なら (位置, 引数がすべて既約でない) を返す。
    fn check_pattern(
        &mut self,
        p: &Pattern,
        ty: &Type,
        env: &mut Env,
        ctx: &Ctx,
        rec_scrutinee: bool,
        top: bool,
    ) -> CResult<Option<PatternCover>> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || match p {
            Pattern::Wild(_) => Ok(None),
            Pattern::Name(id) => {
                if let Some((data, index)) = self.short_ctor(&id.name, Some(ty)) {
                    self.pattern_ctor(&data, index, id.span, &[], env, ctx)?;
                    return Ok(Some(PatternCover {
                        index,
                        covers: true,
                        plain: true,
                    }));
                }
                let origin = if rec_scrutinee && !top {
                    Origin::RecChild
                } else {
                    Origin::Other
                };
                self.bind(env, id, ty.clone(), origin)?;
                Ok(None)
            }
            Pattern::Ctor { name, args, .. } => {
                let resolved = if name.parts.len() == 1 {
                    self.short_ctor(&name.parts[0].name, Some(ty))
                } else {
                    None
                };
                let (data, index) = match resolved {
                    Some(hit) => hit,
                    None => match self.resolve_prefix(ctx.reading, &name.parts) {
                        Some((Target::Ctor { data, index }, k)) if k == name.parts.len() => {
                            (data, index)
                        }
                        _ => {
                            return reference(
                                name.span(),
                                format!("constructor `{}` を解決できない", name.text()),
                            );
                        }
                    },
                };
                if Type::Data(data.clone()) != *ty {
                    return type_error(
                        name.span(),
                        ty,
                        &Type::Data(data),
                        "pattern の constructor の型が合わない",
                    );
                }
                let child_rec = rec_scrutinee && top;
                self.pattern_ctor(&data, index, name.span(), args, env, ctx)?;
                let Some(Signature::Data { constructors }) = self.sigs.get(&data).cloned() else {
                    unreachable!()
                };
                // 引数の pattern が全て、その型の値を残さず受けるなら、この分岐は constructor を覆う。
                // constructor が一つだけの data への pattern は、その引数が全て覆えば値を残さない。
                // plain は引数が全て `_` か束縛であること。到達不能な `_` は plain な分岐だけから判定する。
                let mut covers = true;
                let mut plain = true;
                for (a, t) in args.iter().zip(&constructors[index].args) {
                    let arg_covers = match self.check_pattern(a, t, env, ctx, child_rec, false)? {
                        None => true,
                        Some(inner) => {
                            plain = false;
                            inner.covers
                                && matches!(t, Type::Data(d) if matches!(
                                    self.sigs.get(d),
                                    Some(Signature::Data { constructors }) if constructors.len() == 1
                                ))
                        }
                    };
                    covers &= arg_covers;
                }
                Ok(Some(PatternCover {
                    index,
                    covers,
                    plain,
                }))
            }
        })
    }

    fn pattern_ctor(
        &mut self,
        data: &str,
        index: usize,
        span: Span,
        args: &[Pattern],
        _env: &mut Env,
        _ctx: &Ctx,
    ) -> CResult<()> {
        let Some(Signature::Data { constructors }) = self.sigs.get(data) else {
            unreachable!()
        };
        let c = &constructors[index];
        if c.args.len() != args.len() {
            return syntax(
                span,
                format!("constructor `{}` の引数は {} 個", c.name, c.args.len()),
            );
        }
        let name = full(data, &[&c.name]);
        self.record(span, name);
        Ok(())
    }

    // ---- 量化 ----

    #[allow(clippy::too_many_arguments)]
    /// 量化の域と本体の区切りを決めて検査し、決めた区切りを原式の量化ノードへ書き戻す。
    fn check_quant(
        &mut self,
        id: ExprId,
        var: &Ident,
        split: &QuantSplit,
        span: Span,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<()> {
        let (domain, body) = match split {
            QuantSplit::Fixed { domain, body } => (domain.clone(), *body),
            QuantSplit::Candidates(cands) => {
                let mut valid = Vec::new();
                for (domain, body) in cands {
                    let cp = self.checkpoint(env);
                    let ok = match domain {
                        QuantDomain::In(d) => {
                            matches!(self.check(*d, None, env, ctx), Ok(t) if collection_elem(&t).is_some())
                        }
                        QuantDomain::Type(t) => self.resolve_type_in(t, env, ctx).is_ok(),
                    };
                    self.rollback(cp, env);
                    if ok {
                        valid.push((domain.clone(), *body));
                    }
                }
                // 候補は `.` の位置の順。複数の域が読めるときは、名前の最長一致と同じく最も長い域を選ぶ。
                match valid.len() {
                    0 => {
                        // 最初の候補の域の誤りを返す。
                        match &cands[0].0 {
                            QuantDomain::In(d) => {
                                self.quant_domain(*d, env, ctx)?;
                            }
                            QuantDomain::Type(t) => {
                                self.resolve_type_in(t, env, ctx)?;
                            }
                        }
                        return syntax(span, "量化の域と本体の区切りが決まらない");
                    }
                    _ => valid.pop().expect("一つ以上の候補"),
                }
            }
        };
        let elem = match &domain {
            QuantDomain::In(d) => self.quant_domain(*d, env, ctx)?,
            QuantDomain::Type(t) => self.resolve_type_in(t, env, ctx)?,
        };
        let mark = env.vars.len();
        self.bind(env, var, elem, Origin::Other)?;
        self.check_bool(body, env, ctx)?;
        env.vars.truncate(mark);
        if let ExprKind::Quant { split, .. } = &mut self.parser.exprs[id].kind {
            *split = QuantSplit::Fixed { domain, body };
        }
        Ok(())
    }

    fn quant_domain(&mut self, d: ExprId, env: &mut Env, ctx: &Ctx) -> CResult<Type> {
        let t = self.check(d, None, env, ctx)?;
        match collection_elem(&t) {
            Some(e) => Ok(e),
            None => type_error(
                self.span(d),
                &Type::List(Box::new(t.clone())),
                &t,
                "量化の域は List か Set",
            ),
        }
    }
}
