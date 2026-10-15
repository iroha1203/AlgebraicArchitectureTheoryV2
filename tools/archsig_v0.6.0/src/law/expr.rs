//! 式の型検査、束縛、純粋性、構造再帰(Law 仕様 §4)。

use super::ast::*;
use super::check::*;
use super::model::*;
use crate::json::InputError;
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

impl<E: InputError> Checker<E> {
    fn lookup<'a>(&self, env: &'a Env, name: &str) -> CResult<Lookup<'a>, E> {
        for (index, binding) in env.vars.iter().enumerate().rev() {
            self.cooperate()?;
            if binding.name == name {
                return Ok(if index >= env.boundary {
                    Lookup::Found(binding)
                } else {
                    Lookup::Captured
                });
            }
        }
        self.cooperate()?;
        Ok(Lookup::Missing)
    }
    fn env_params(&self, env: &Env) -> CResult<Vec<Param>, E> {
        let mut params = Vec::new();
        for binding in &env.vars[env.boundary..] {
            self.cooperate()?;
            params.push(Param {
                name: binding.name.clone(),
                ty: binding.ty.clone(),
                span: binding.span,
            });
        }
        Ok(params)
    }
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

    pub fn bind(&mut self, env: &mut Env, id: &Ident, ty: Type, origin: Origin) -> CResult<(), E> {
        check_binding_name::<E>(id)?;
        if !matches!(self.lookup(env, &id.name)?, Lookup::Missing) {
            return duplicate(
                id.span,
                format!("束縛名 `{}` が外側の束縛と重なる", id.name),
            );
        }
        env.vars.push(Binding {
            name: id.name.clone(),
            ty: self.erase_type(&ty)?,
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

    fn resolve_type_in(&mut self, ast: &TypeAst, env: &Env, ctx: &Ctx) -> CResult<Type, E> {
        let index = self.env_params(env)?;
        let tctx = self.expr_type_ctx(ctx, &index);
        let ty = self.resolve_type(ast, &tctx)?;
        self.erase_type(&ty)
    }

    /// 式を検査して型を返す。`expected` があればその型との一致を確かめる。
    pub fn check(
        &mut self,
        id: ExprId,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type, E> {
        self.cooperate()?;
        let result = (|| {
            let t = stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
                self.check_inner(id, expected, env, ctx)
            })?;
            let t = self.erase_type(&t)?;
            if let Some(e) = expected
                && self.erase_type(e)? != t
            {
                return self.type_error(self.span(id), e, &t, "式の型が合わない");
            }
            if self.expr_types.len() < self.parser.exprs.len() {
                self.expr_types.resize(self.parser.exprs.len(), None);
            }
            self.expr_types[id] = Some(t.clone());
            Ok(t)
        })();
        E::finish(result, &mut self.control.clone(), self.semantic_point)
    }

    fn check_bool(&mut self, id: ExprId, env: &mut Env, ctx: &Ctx) -> CResult<(), E> {
        self.check(id, Some(&Type::Bool), env, ctx).map(|_| ())
    }

    /// 文脈の型がないと読めない式(整数 literal、短い constructor 名)。
    fn needs_context(&mut self, id: ExprId, env: &Env) -> CResult<bool, E> {
        self.cooperate()?;
        let result =
            stacker::maybe_grow(RED_ZONE, STACK_STEP, || self.needs_context_inner(id, env));
        E::finish(result, &mut self.control.clone(), self.semantic_point)
    }
    fn needs_context_inner(&mut self, id: ExprId, env: &Env) -> CResult<bool, E> {
        Ok(match self.parser.exprs[id].kind.clone() {
            ExprKind::Int(_) => true,
            ExprKind::Unary {
                op: UnOp::Neg,
                operand,
            }
            | ExprKind::Group(operand)
            | ExprKind::Some(operand) => self.needs_context(operand, env)?,
            ExprKind::Let { body, .. } | ExprKind::Fn { body, .. } => {
                self.needs_context(body, env)?
            }
            ExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.cooperate()?;
                    if !self.needs_context(arm.body, env)? {
                        return Ok(false);
                    }
                }
                true
            }
            ExprKind::Binary {
                op: BinOp::Add | BinOp::Sub | BinOp::Mul,
                lhs,
                rhs,
            } => self.needs_context(lhs, env)? && self.needs_context(rhs, env)?,
            ExprKind::Tuple(items) => {
                for item in items {
                    self.cooperate()?;
                    if self.needs_context(item, env)? {
                        return Ok(true);
                    }
                }
                false
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => self.needs_context(then_branch, env)? && self.needs_context(else_branch, env)?,
            ExprKind::Dotted(parts) => parts.len() == 1 && self.is_unknown_short(&parts[0], env)?,
            ExprKind::Call { callee, .. } => match &self.parser.exprs[callee].kind {
                ExprKind::Dotted(parts) if parts.len() == 1 => {
                    let p = parts[0].clone();
                    !BUILTIN_OPS.contains(&p.name.as_str()) && self.is_unknown_short(&p, env)?
                }
                _ => false,
            },
            _ => false,
        })
    }
    fn is_unknown_short(&mut self, p: &Ident, env: &Env) -> CResult<bool, E> {
        Ok(matches!(self.lookup(env, &p.name)?, Lookup::Missing)
            && self.resolve_prefix_silent_ref(p)?.is_none())
    }
    fn resolve_prefix_silent_ref(&mut self, p: &Ident) -> CResult<Option<(Target, usize)>, E> {
        let reading = self.current_reading;
        self.resolve_prefix_silent(reading, std::slice::from_ref(p))
    }

    /// 二つの被演算子の共通の型。文脈の要る側を後に読む。
    fn pair_type(&mut self, l: ExprId, r: ExprId, env: &mut Env, ctx: &Ctx) -> CResult<Type, E> {
        if self.needs_context(l, env)? && !self.needs_context(r, env)? {
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
    ) -> CResult<Type, E> {
        let span = self.span(id);
        let kind = self.parser.exprs[id].kind.clone();
        match kind {
            ExprKind::Int(text) => match expected
                .map(|ty| self.erase_type(ty))
                .transpose()?
                .as_ref()
            {
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
                Some(other) => {
                    self.type_error(span, other, &Type::Z, "整数 literal の型が合わない")
                }
            },
            ExprKind::Str(_) => Ok(Type::Text),
            ExprKind::Bool(_) => Ok(Type::Bool),
            ExprKind::Unit => Ok(Type::Unit),
            ExprKind::Group(inner) => self.check(inner, expected, env, ctx),
            ExprKind::Tuple(items) => {
                let parts = match expected.map(|ty| self.erase_type(ty)).transpose()?.as_ref() {
                    Some(Type::Tuple(ts)) if ts.len() == items.len() => {
                        ts.iter().cloned().map(Some).collect()
                    }
                    _ => vec![None; items.len()],
                };
                let mut out = Vec::new();
                for (i, t) in items.iter().zip(parts) {
                    self.cooperate()?;
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
                self.require_numeric(&t, span, &Type::Z, &t, "単項 - は Z・Q・Fp とその組")?;
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
                    other => self.type_error(
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
                    self.cooperate()?;
                    self.check(i, Some(&t), env, ctx)?;
                }
                Ok(Type::List(Box::new(t)))
            }
            ExprKind::SetLit { ty, items } => {
                let t = self.resolve_type_in(&ty, env, ctx)?;
                self.reject_term_or_path(&t, ty.span())?;
                for i in items {
                    self.cooperate()?;
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
                    return self.type_error(
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
                self.reject_term_or_path(&t, self.span(elem))?;
                Ok(Type::Set(Box::new(t)))
            }
            ExprKind::None(ty) => Ok(Type::Option(Box::new(self.resolve_type_in(&ty, env, ctx)?))),
            ExprKind::Some(inner) => {
                let inner_expected =
                    match expected.map(|ty| self.erase_type(ty)).transpose()?.as_ref() {
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
                let target = match self.resolve_prefix(ctx.reading, &name.parts)? {
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
    ) -> CResult<Type, E> {
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
                self.require_numeric(&t, span, &Type::Z, &t, "算術は Z・Q・Fp とその組")?;
                Ok(t)
            }
            BinOp::Eq | BinOp::Ne => {
                self.pair_type(lhs, rhs, env, ctx)?;
                Ok(Type::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let t = self.pair_type(lhs, rhs, env, ctx)?;
                if t != Type::Z && t != Type::Q {
                    return self.type_error(span, &Type::Z, &t, "順序は Z と Q だけ");
                }
                Ok(Type::Bool)
            }
            BinOp::In => {
                let c = self.check(rhs, None, env, ctx)?;
                let Some(e) = collection_elem(&c) else {
                    return self.type_error(
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

    fn project_field(&mut self, base: &Type, name: &Ident, ctx: &Ctx) -> CResult<Type, E> {
        if ctx.term {
            return reference(name.span, "Term の本体は field を読めない");
        }
        let Some(decl) = base.ref_target().map(str::to_owned) else {
            return syntax(
                name.span,
                format!("field `{}` は参照型の値から読む", name.name),
            );
        };
        let field = match self.sigs.get(&decl) {
            Some(signature) => self.signature_field(signature, &name.name)?,
            None => None,
        };
        let Some(field) = field else {
            return reference(
                name.span,
                format!("`{decl}` に field `{}` はない", name.name),
            );
        };
        self.record(name.span, full(&decl, &[&name.name]));
        self.erase_type(&field.ty)
    }

    fn check_dotted(
        &mut self,
        parts: &[Ident],
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type, E> {
        let head = &parts[0];
        match self.lookup(env, &head.name)? {
            Lookup::Found(b) => {
                let mut t = b.ty.clone();
                for p in &parts[1..] {
                    self.cooperate()?;
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
            if let Some((data, index)) =
                self.short_ctor(&head.name, expected, ctx.reading, head.span)?
            {
                return self.ctor_value(&data, index, head.span, &[], env, ctx);
            }
            if BUILTIN_OPS.contains(&head.name.as_str()) {
                return syntax(
                    head.span,
                    format!("組込み演算 `{}` は適用して使う", head.name),
                );
            }
        }
        match self.resolve_prefix(ctx.reading, parts)? {
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

    fn short_ctor(
        &self,
        name: &str,
        expected: Option<&Type>,
        reading: usize,
        span: Span,
    ) -> CResult<Option<(String, usize)>, E> {
        let expected = expected.map(|ty| self.erase_type(ty)).transpose()?;
        let Some(Type::Data(d)) = expected.as_ref() else {
            return Ok(None);
        };
        let Some(Signature::Data { constructors }) = self.sigs.get(d) else {
            return Ok(None);
        };
        let mut constructor_index = None;
        for (index, constructor) in constructors.iter().enumerate() {
            self.cooperate()?;
            if constructor.name == name {
                constructor_index = Some(index);
                break;
            }
        }
        let Some(i) = constructor_index else {
            return Ok(None);
        };
        if !self.primitive_visible(reading, d, true)? {
            return reference(
                span,
                format!("constructor `{name}` の短名をこの scope で使えない"),
            );
        }
        Ok(Some((d.clone(), i)))
    }

    fn ctor_value(
        &mut self,
        data: &str,
        index: usize,
        span: Span,
        args: &[ExprId],
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<Type, E> {
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
            self.cooperate()?;
            self.check(*a, Some(t), env, ctx)?;
        }
        Ok(Type::Data(data.to_owned()))
    }

    fn strip_groups(&self, mut id: ExprId) -> CResult<ExprId, E> {
        while let ExprKind::Group(inner) = self.parser.exprs[id].kind {
            self.cooperate()?;
            id = inner;
        }
        Ok(id)
    }

    fn resolve_callee(
        &mut self,
        callee: ExprId,
        expected: Option<&Type>,
        env: &mut Env,
        ctx: &Ctx,
    ) -> CResult<(Callee, Span), E> {
        let inner = self.strip_groups(callee)?;
        let span = self.span(inner);
        match self.parser.exprs[inner].kind.clone() {
            ExprKind::ThenOp => Ok((Callee::Builtin("then"), span)),
            ExprKind::Dotted(parts) => {
                let head = &parts[0];
                match self.lookup(env, &head.name)? {
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
                    if let Some((data, index)) =
                        self.short_ctor(&head.name, expected, ctx.reading, head.span)?
                    {
                        return Ok((Callee::Ctor(data, index), span));
                    }
                    if let Some(b) = BUILTIN_OPS.iter().find(|b| **b == head.name) {
                        return Ok((Callee::Builtin(b), span));
                    }
                }
                match self.resolve_prefix(ctx.reading, &parts)? {
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

    fn arity(&self, span: Span, args: &[ExprId], n: usize, what: &str) -> CResult<(), E> {
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
    ) -> CResult<Type, E> {
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
                    self.cooperate()?;
                    let expected = self.erase_type(&p.ty)?;
                    self.check(*a, Some(&expected), env, ctx)?;
                }
                self.erase_type(&returns)
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
                        self.cooperate()?;
                        self.check(*a, Some(p), env, ctx)?;
                    }
                    Ok((**r).clone())
                }
                other => self.non_callable_error(name_span, other),
            },
            Callee::Builtin(b) => self.check_builtin(b, args, span, name_span, expected, env, ctx),
        }
    }

    fn non_callable_error<T>(&self, span: Span, ty: &Type) -> CResult<T, E> {
        let diagnostic = (|| {
            let wire = ty.wire_controlled::<E>(&mut self.control.clone(), self.semantic_point)?;
            wire.canonical_controlled::<E>(&mut self.control.clone(), self.semantic_point)
        })();
        match diagnostic {
            Ok(text) => syntax(span, format!("型 {text} の値は適用できない")),
            // Applicability was already rejected. A display budget cannot
            // replace this known input failure or start a new derivation.
            Err(stop) if stop.is_budget_stop() => syntax(span, "この型の値は適用できない"),
            Err(stop) => Err(stop),
        }
    }

    fn check_structural_call(
        &mut self,
        args: &[ExprId],
        span: Span,
        env: &Env,
        ctx: &Ctx,
    ) -> CResult<(), E> {
        let rec = ctx.rec.clone();
        let Some((index, data)) = rec else {
            return cycle(span, "view の自己再帰には左端の data parameter が要る");
        };
        let arg = self.strip_groups(args[index])?;
        if let ExprKind::Dotted(parts) = &self.parser.exprs[arg].kind
            && parts.len() == 1
            && let Lookup::Found(b) = self.lookup(env, &parts[0].name)?
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
    ) -> CResult<Type, E> {
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
                    return self.type_error(
                        self.span(args[0]),
                        &Type::List(Box::new(c.clone())),
                        &c,
                        format!("{b} の引数は List か Set"),
                    );
                };
                if b == "count" {
                    return Ok(Type::Z);
                }
                self.require_numeric(
                    &e,
                    self.span(args[0]),
                    &Type::List(Box::new(Type::Z)),
                    &c,
                    "sum の要素は数値",
                )?;
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
                    Type::Path(_, c) => self.type_error(
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
    ) -> CResult<Type, E> {
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
                self.cooperate()?;
                let t = self.resolve_type_in(&p.ty, env, &term_ctx)?;
                self.bind(env, &p.name, t.clone(), Origin::Other)?;
                types.push(t);
            }
            let ret_expected = match expected.map(|ty| self.erase_type(ty)).transpose()?.as_ref() {
                Some(Type::Term(_, r)) => Some((**r).clone()),
                _ => None,
            };
            self.check(body, ret_expected.as_ref(), env, &term_ctx)
        })();
        env.vars.truncate(mark);
        env.boundary = saved_boundary;
        let ret = result?;
        self.reject_reference(
            &ret,
            self.span(body),
            "Term の戻り型は参照・Map・Path を含まない値型",
        )?;
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
    ) -> CResult<Type, E> {
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
        let rec_scrutinee = match &self.parser.exprs[self.strip_groups(scrutinee)?].kind {
            ExprKind::Dotted(parts) if parts.len() == 1 => {
                match (self.lookup(env, &parts[0].name)?, &ctx.rec) {
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
        let mut result: Option<Type> = expected.map(|ty| self.erase_type(ty)).transpose()?;
        let mut pending = Vec::new();
        for arm in arms {
            self.cooperate()?;
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
                None if self.needs_context(arm.body, env)? => {
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
            self.cooperate()?;
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
    ) -> CResult<Option<PatternCover>, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || match p {
            Pattern::Wild(_) => Ok(None),
            Pattern::Name(id) => {
                if let Some((data, index)) =
                    self.short_ctor(&id.name, Some(ty), ctx.reading, id.span)?
                {
                    if !matches!(self.lookup(env, &id.name)?, Lookup::Missing) {
                        return syntax(
                            id.span,
                            format!(
                                "変数名と衝突する constructor の短名 `{}` は修飾する",
                                id.name
                            ),
                        );
                    }
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
                    let hit =
                        self.short_ctor(&name.parts[0].name, Some(ty), ctx.reading, name.span())?;
                    if hit.is_some()
                        && !matches!(self.lookup(env, &name.parts[0].name)?, Lookup::Missing)
                    {
                        return syntax(
                            name.span(),
                            format!(
                                "変数名と衝突する constructor の短名 `{}` は修飾する",
                                name.parts[0].name
                            ),
                        );
                    }
                    hit
                } else {
                    None
                };
                let (data, index) = match resolved {
                    Some(hit) => hit,
                    None => match self.resolve_prefix(ctx.reading, &name.parts)? {
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
                    return self.type_error(
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
                    self.cooperate()?;
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
    ) -> CResult<(), E> {
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
    ) -> CResult<(), E> {
        let (domain, body) = match split {
            QuantSplit::Fixed { domain, body } => (domain.clone(), *body),
            QuantSplit::Candidates(cands) => {
                let mut valid = Vec::new();
                let mut first_error = None;
                for (domain, body) in cands {
                    self.cooperate()?;
                    let cp = self.checkpoint(env);
                    let candidate = match domain {
                        QuantDomain::In(d) => self.quant_domain(*d, env, ctx).map(|_| ()),
                        QuantDomain::Type(t) => self.resolve_type_in(t, env, ctx).map(|_| ()),
                    };
                    self.rollback(cp, env);
                    match candidate {
                        Ok(()) => valid.push((domain.clone(), *body)),
                        Err(error) if error.is_stopped() => return Err(error),
                        Err(error) => {
                            first_error.get_or_insert(error);
                        }
                    }
                }
                // 候補は `.` の位置の順。複数の域が読めるときは、名前の最長一致と同じく最も長い域を選ぶ。
                match valid.len() {
                    0 => {
                        // All domains failed. Rechecking the first domain could
                        // replace its known diagnostic with a latched budget.
                        if let Some(error) = first_error {
                            return Err(error);
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

    fn quant_domain(&mut self, d: ExprId, env: &mut Env, ctx: &Ctx) -> CResult<Type, E> {
        let t = self.check(d, None, env, ctx)?;
        match collection_elem(&t) {
            Some(e) => Ok(e),
            None => self.type_error(
                self.span(d),
                &Type::List(Box::new(t.clone())),
                &t,
                "量化の域は List か Set",
            ),
        }
    }
}

#[cfg(test)]
mod semantic_finish_tests {
    use super::*;
    use crate::{
        definition::CheckedDefinitions,
        issue::{Code, Details, Issue},
        law::parser::Parser,
        observed::control::{
            CheckFailure, Checkpoint as StopPoint, Control, Limits, StopReason, Usage,
        },
        result::Signal,
    };
    use std::{cell::Cell, rc::Rc};
    type Failure = CheckFailure<Box<Issue>>;
    fn checker(control: &mut Control) -> Checker<Failure> {
        Checker::with_definitions(
            Parser::with_error(Vec::new(), 4, control.clone()),
            Vec::new(),
            &CheckedDefinitions::default(),
            control,
            StopPoint::LawSemantics,
        )
        .unwrap()
    }
    fn monitored(at: usize, mode: usize) -> (Control, Rc<Cell<bool>>, Rc<Cell<usize>>) {
        let armed = Rc::new(Cell::new(false));
        let count = Rc::new(Cell::new(0));
        let a = armed.clone();
        let c = count.clone();
        let control = Control::new(
            Limits {
                time_ms: (mode == 1).then_some(1),
                memory_mib: (mode == 2).then_some(1),
            },
            move |point| {
                if a.get() && point == StopPoint::LawSemantics {
                    c.set(c.get() + 1);
                }
                let stop = a.get() && c.get() == at;
                Usage {
                    signal: (stop && mode == 0).then_some(Signal::Term),
                    elapsed_ms: u128::from(stop && mode == 1),
                    memory_mib: u128::from(stop && mode == 2),
                }
            },
        );
        (control, armed, count)
    }
    fn ctx() -> Ctx {
        Ctx {
            reading: 0,
            decl: "R.v".into(),
            is_view: true,
            rec: None,
            term: false,
        }
    }
    fn bool_mismatch(checker: &mut Checker<Failure>) -> CResult<Type, Failure> {
        checker.parser.exprs.push(Expr {
            kind: ExprKind::Bool(true),
            span: (0, 4),
        });
        checker.check(0, Some(&Type::Z), &mut Env::default(), &ctx())
    }
    // Enter each expectation-reading branch directly. The small ASTs avoid
    // unrelated parsing/name-resolution work, so the recorded trace includes
    // the expected type's erasure rather than only its surrounding checks.
    fn expected_branch(check: &mut Checker<Failure>, branch: usize) -> CResult<Type, Failure> {
        check.parser.exprs.push(Expr {
            kind: ExprKind::Bool(true),
            span: (0, 4),
        });
        let mut env = Env::default();
        match branch {
            0 => {
                check.parser.exprs.push(Expr {
                    kind: ExprKind::Int("1".into()),
                    span: (5, 6),
                });
                check.check_inner(1, Some(&Type::Q), &mut env, &ctx())
            }
            1 => {
                check.parser.exprs.push(Expr {
                    kind: ExprKind::Tuple(Vec::new()),
                    span: (5, 7),
                });
                check.check_inner(1, Some(&Type::Tuple(Vec::new())), &mut env, &ctx())
            }
            2 => {
                check.parser.exprs.push(Expr {
                    kind: ExprKind::Some(0),
                    span: (0, 10),
                });
                check.check_inner(
                    1,
                    Some(&Type::Option(Box::new(Type::Bool))),
                    &mut env,
                    &ctx(),
                )
            }
            3 => check
                .short_ctor("Missing", Some(&Type::Data("V.Unknown".into())), 0, (0, 4))
                .map(|found| {
                    assert!(found.is_none());
                    Type::Unit
                }),
            4 => check.check_fn(
                &[],
                0,
                Some(&Type::Term(Vec::new(), Box::new(Type::Bool))),
                &mut env,
                &ctx(),
            ),
            5 => check.check_match(
                0,
                &[Arm {
                    pattern: Pattern::Wild((0, 1)),
                    body: 0,
                }],
                (0, 4),
                Some(&Type::Bool),
                &mut env,
                &ctx(),
            ),
            _ => unreachable!(),
        }
    }
    fn assert_expected_branch_interruptible(branch: usize, steps: usize, expected: Type) {
        let (mut control, armed, count) = monitored(usize::MAX, 0);
        let mut check = checker(&mut control);
        armed.set(true);
        assert_eq!(expected_branch(&mut check, branch).unwrap(), expected);
        // These six minimal traces lose respectively 2, 2, 4, 2, 4, and 2
        // checkpoints if the expected type goes through the unlimited wrapper.
        assert_eq!(count.get(), steps);
        for at in 1..=steps {
            for mode in 0..3 {
                let (mut control, armed, seen) = monitored(at, mode);
                let mut check = checker(&mut control);
                armed.set(true);
                let failure = expected_branch(&mut check, branch).unwrap_err();
                assert_eq!(seen.get(), at);
                let Failure::Stopped(reason) = failure else {
                    panic!("unfinished inference must stop before producing a type")
                };
                assert_eq!(control.stop_reason(), Some(reason.clone()));
                if mode == 0 {
                    assert_eq!(reason, StopReason::Cancelled(Signal::Term));
                } else {
                    assert!(matches!(reason, StopReason::BudgetExhausted { .. }));
                }
            }
        }
    }
    #[test]
    fn integer_expected_erasure_uses_shared_control() {
        assert_expected_branch_interruptible(0, 2, Type::Q);
    }
    #[test]
    fn tuple_expected_erasure_uses_shared_control() {
        assert_expected_branch_interruptible(1, 2, Type::Tuple(Vec::new()));
    }
    #[test]
    fn some_expected_erasure_uses_shared_control() {
        assert_expected_branch_interruptible(2, 10, Type::Option(Box::new(Type::Bool)));
    }
    #[test]
    fn short_constructor_expected_erasure_uses_shared_control() {
        assert_expected_branch_interruptible(3, 2, Type::Unit);
    }
    #[test]
    fn function_expected_erasure_uses_shared_control() {
        // Term erasure: entry + Bool entry/exit + exit = 4.
        // Body check: entry + actual Bool erasure + expected Bool erasure
        // + finish = 6. has_reference: Bool entry/exit + final exit = 3.
        assert_expected_branch_interruptible(4, 13, Type::Term(Vec::new(), Box::new(Type::Bool)));
    }
    #[test]
    fn match_expected_erasure_uses_shared_control() {
        // Scrutinee check = 4; expected Bool erasure = 2; arm iteration = 1;
        // body check with expected Bool = 6. Wild patterns add no checkpoints.
        assert_expected_branch_interruptible(5, 13, Type::Bool);
    }
    #[test]
    fn checker_errors_reach_post_checkpoints_and_keep_known_invalid_above_budget() {
        let (mut control, armed, count) = monitored(usize::MAX, 0);
        let mut check = checker(&mut control);
        armed.set(true);
        let ordinary = bool_mismatch(&mut check).unwrap_err();
        assert!(
            matches!(ordinary,Failure::Input(ref issue) if issue.code==Code::Type && matches!(issue.details,Details::Type{expected:Type::Z,actual:Type::Bool}))
        );
        let final_step = count.get();
        assert!(final_step >= 4);
        for mode in 0..3 {
            let (mut control, armed, seen) = monitored(final_step, mode);
            let mut check = checker(&mut control);
            armed.set(true);
            let failure = bool_mismatch(&mut check).unwrap_err();
            assert_eq!(seen.get(), final_step);
            if mode == 0 {
                assert!(matches!(
                    failure,
                    Failure::Stopped(StopReason::Cancelled(Signal::Term))
                ));
            } else {
                assert!(
                    matches!(failure,Failure::Input(ref issue) if issue.code==Code::Type && matches!(issue.details,Details::Type{expected:Type::Z,actual:Type::Bool}))
                );
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::BudgetExhausted { .. })
                ));
            }
        }
    }
    #[test]
    fn resolve_type_error_checks_its_exit_before_returning_invalid() {
        let ast = TypeAst::Fp {
            modulus: "4".into(),
            span: (0, 4),
        };
        let ctx = TypeCtx {
            reading: 0,
            index: &[],
            allow_path: true,
            ref_free: false,
            validate: true,
        };
        let (mut baseline, armed, total) = monitored(usize::MAX, 0);
        let mut check = checker(&mut baseline);
        armed.set(true);
        assert!(matches!(
            check.resolve_type(&ast, &ctx),
            Err(Failure::Input(ref issue)) if issue.code == Code::Syntax
        ));
        let exit = total.get();
        assert!(exit > 2, "primality now has its own internal checkpoints");
        for mode in 0..3 {
            let (mut control, armed, count) = monitored(exit, mode);
            let mut check = checker(&mut control);
            armed.set(true);
            let failure = check.resolve_type(&ast, &ctx).unwrap_err();
            assert_eq!(count.get(), exit);
            if mode == 0 {
                assert!(matches!(
                    failure,
                    Failure::Stopped(StopReason::Cancelled(Signal::Term))
                ));
            } else {
                assert!(matches!(failure,Failure::Input(ref issue) if issue.code==Code::Syntax));
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::BudgetExhausted { .. })
                ));
            }
        }
    }
    #[test]
    fn known_type_mismatch_diagnostic_keeps_erased_details_when_budget_expires() {
        let expected = Type::Tuple(vec![
            Type::Owned("V.Item".into(), "owner".into()),
            Type::Option(Box::new(Type::Bool)),
        ]);
        let actual = Type::Tuple(vec![Type::Z, Type::Unit]);
        let (mut control, armed, count) = monitored(usize::MAX, 0);
        let check = checker(&mut control);
        armed.set(true);
        assert!(matches!(
            check.type_error::<()>((0, 4), &expected, &actual, "mismatch"),
            Err(Failure::Input(_))
        ));
        for at in 1..=count.get() {
            for mode in 0..3 {
                let (mut control, armed, _) = monitored(at, mode);
                let check = checker(&mut control);
                armed.set(true);
                let failure = check
                    .type_error::<()>((0, 4), &expected, &actual, "mismatch")
                    .unwrap_err();
                if mode == 0 {
                    assert!(matches!(
                        failure,
                        Failure::Stopped(StopReason::Cancelled(Signal::Term))
                    ));
                } else {
                    let Failure::Input(issue) = failure else {
                        panic!("known mismatch replaced")
                    };
                    assert_eq!(
                        issue.details,
                        Details::Type {
                            expected: expected.erase(),
                            actual: actual.erase()
                        }
                    );
                    assert!(matches!(
                        control.stop_reason(),
                        Some(StopReason::BudgetExhausted { .. })
                    ));
                }
            }
        }
    }
    #[test]
    fn invalid_call_diagnostic_checks_nested_wire_and_canonical_components() {
        let ty = Type::Tuple(vec![
            Type::Z,
            Type::Option(Box::new(Type::Tuple(vec![Type::Bool, Type::Unit]))),
        ]);
        let (mut control, armed, count) = monitored(usize::MAX, 0);
        let check = checker(&mut control);
        armed.set(true);
        let Failure::Input(issue) = check.non_callable_error::<()>((0, 4), &ty).unwrap_err() else {
            panic!("syntax expected")
        };
        assert_eq!(
            issue.message,
            format!("型 {} の値は適用できない", ty.wire().canonical())
        );
        assert!(count.get() > 20);
        for at in 1..=count.get() {
            for mode in 0..3 {
                let (mut control, armed, _) = monitored(at, mode);
                let check = checker(&mut control);
                armed.set(true);
                let failure = check.non_callable_error::<()>((0, 4), &ty).unwrap_err();
                if mode == 0 {
                    assert!(matches!(
                        failure,
                        Failure::Stopped(StopReason::Cancelled(Signal::Term))
                    ));
                } else {
                    assert!(
                        matches!(failure,Failure::Input(ref issue) if issue.code==Code::Syntax)
                    );
                    assert!(matches!(
                        control.stop_reason(),
                        Some(StopReason::BudgetExhausted { .. })
                    ));
                }
            }
        }
    }

    fn quant_candidate_fixture(
        control: &mut Control,
        typed: bool,
        valid: [bool; 2],
    ) -> (
        Checker<super::super::parser::candidate_priority_tests::Failure>,
        ExprId,
    ) {
        use super::super::parser::candidate_priority_tests::Failure as CandidateFailure;
        let mut check = Checker::<CandidateFailure>::with_definitions(
            Parser::with_error(Vec::new(), 32, control.clone()),
            Vec::new(),
            &CheckedDefinitions::default(),
            control,
            StopPoint::LawSemantics,
        )
        .unwrap();
        let mut domains = Vec::new();
        for (index, is_valid) in valid.into_iter().enumerate() {
            let span = (index * 5, index * 5 + 4);
            let domain = if typed {
                QuantDomain::Type(if is_valid {
                    TypeAst::Builtin(Builtin::Bool, span)
                } else {
                    TypeAst::Fp {
                        modulus: if index == 0 { "4" } else { "6" }.into(),
                        span,
                    }
                })
            } else {
                check.parser.exprs.push(Expr {
                    kind: if is_valid {
                        ExprKind::ListLit {
                            ty: TypeAst::Builtin(Builtin::Bool, span),
                            items: Vec::new(),
                        }
                    } else if index == 0 {
                        ExprKind::Bool(true)
                    } else {
                        ExprKind::Unit
                    },
                    span,
                });
                QuantDomain::In(check.parser.exprs.len() - 1)
            };
            domains.push(domain);
        }
        check.parser.exprs.push(Expr {
            kind: ExprKind::Bool(true),
            span: (10, 14),
        });
        let body = check.parser.exprs.len() - 1;
        check.parser.exprs.push(Expr {
            kind: ExprKind::Quant {
                kind: QuantKind::Forall,
                var: Ident {
                    name: "x".into(),
                    span: (20, 21),
                    tok: 0,
                },
                split: QuantSplit::Candidates(
                    domains.into_iter().map(|domain| (domain, body)).collect(),
                ),
            },
            span: (0, 32),
        });
        let root = check.parser.exprs.len() - 1;
        (check, root)
    }
    #[test]
    fn all_failed_quantifier_domains_keep_first_diagnostic_when_last_error_hits_budget() {
        use super::super::parser::candidate_priority_tests::{
            Failure as CandidateFailure, stop_after_issue,
        };
        for typed in [false, true] {
            let (mut baseline, root) =
                quant_candidate_fixture(&mut Control::unlimited(), typed, [false, false]);
            let CandidateFailure(CheckFailure::Input(expected)) = baseline
                .check(root, None, &mut Env::default(), &ctx())
                .unwrap_err()
            else {
                panic!("domain error expected")
            };
            assert_eq!(
                expected.location,
                crate::issue::Location::Law { span: (0, 4) }
            );
            if !typed {
                assert_eq!(expected.code, Code::Type);
                assert_eq!(expected.message, "量化の域は List か Set");
                assert_eq!(
                    expected.details,
                    Details::Type {
                        expected: Type::List(Box::new(Type::Bool)),
                        actual: Type::Bool,
                    }
                );
            }
            for mode in 0..3 {
                let (mut control, _arm, observed) = stop_after_issue((5, 9), mode);
                let (mut check, root) =
                    quant_candidate_fixture(&mut control, typed, [false, false]);
                let failure = check
                    .check(root, None, &mut Env::default(), &ctx())
                    .unwrap_err();
                assert!(observed.get(), "last candidate error was not constructed");
                if mode == 0 {
                    assert!(matches!(
                        failure.0,
                        CheckFailure::Stopped(StopReason::Cancelled(Signal::Term))
                    ));
                } else {
                    let CheckFailure::Input(actual) = failure.0 else {
                        panic!("all domains failed, but diagnostic was replaced")
                    };
                    assert_eq!(actual, expected);
                    assert!(matches!(
                        control.stop_reason(),
                        Some(StopReason::BudgetExhausted { .. })
                    ));
                }
            }
        }
    }
    #[test]
    fn speculative_domain_failure_does_not_become_invalid_with_other_candidates() {
        use super::super::parser::candidate_priority_tests::stop_after_issue;
        for typed in [false, true] {
            for (valid, target) in [([false, true], (0, 4)), ([true, false], (5, 9))] {
                let (mut baseline, root) =
                    quant_candidate_fixture(&mut Control::unlimited(), typed, valid);
                assert_eq!(
                    baseline
                        .check(root, None, &mut Env::default(), &ctx())
                        .unwrap(),
                    Type::Bool
                );
                for mode in 0..3 {
                    let (mut control, _arm, observed) = stop_after_issue(target, mode);
                    let (mut check, root) = quant_candidate_fixture(&mut control, typed, valid);
                    let failure = check
                        .check(root, None, &mut Env::default(), &ctx())
                        .unwrap_err();
                    assert!(observed.get(), "speculative domain failure was not reached");
                    assert!(
                        matches!(failure.0, CheckFailure::Stopped(_)),
                        "an untried or valid domain exists"
                    );
                    assert!(control.stop_reason().is_some());
                }
            }
        }
    }
}
