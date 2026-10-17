//! 閉じたTermの検査済みbodyとparameter。表示上の構文比較をLawの等値へ使わない。
use super::{
    control::{Checkpoint, Control},
    data, environment, numeric,
    result::{Scalar, ValidationFailure},
};
use crate::{
    canonical::Json,
    law::{
        CheckedLaw, TermBody,
        ast::{BinOp, Expr, ExprKind, Pattern, QuantDomain, QuantKind, QuantSplit, Span},
    },
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Term {
    pub params: Vec<(String, Type)>,
    pub returns: Type,
    pub body: String,
    pub root: usize,
    pub offset: usize,
    pub nodes: BTreeMap<usize, Expr>,
    pub types: BTreeMap<usize, Type>,
    pub references: Vec<(Span, String)>,
    pub quantifier_types: BTreeMap<usize, Type>,
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone().checkpoint(Checkpoint::Expression)?;
    Ok(())
}
pub(super) fn contains(
    ty: &Type,
    law: &CheckedLaw,
    c: &Control,
) -> Result<bool, ValidationFailure> {
    fn visit(
        ty: &Type,
        law: &CheckedLaw,
        c: &Control,
        active: &mut BTreeSet<String>,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            Ok(match ty {
                Type::Term(..) => true,
                Type::Tuple(items) => {
                    for t in items {
                        if visit(t, law, c, active)? {
                            return Ok(true);
                        }
                    }
                    false
                }
                Type::List(t) | Type::Set(t) | Type::Option(t) => visit(t, law, c, active)?,
                Type::Data(family) => {
                    if active.contains(family) {
                        return Ok(false);
                    }
                    active.insert(family.clone());
                    let mut found = false;
                    for ctor in data::constructors(law, family)? {
                        for t in &ctor.arguments {
                            tick(c)?;
                            found |= visit(t, law, c, active)?;
                        }
                    }
                    active.remove(family);
                    found
                }
                _ => false,
            })
        })
    }
    visit(ty, law, c, &mut BTreeSet::new())
}
fn copy_variables(
    vars: &BTreeMap<String, Scalar>,
    c: &Control,
) -> Result<BTreeMap<String, Scalar>, ValidationFailure> {
    let mut copied = BTreeMap::new();
    for (n, v) in vars {
        tick(c)?;
        copied.insert(n.clone(), v.clone());
        tick(c)?;
    }
    Ok(copied)
}
pub(super) fn value_type(ty: &Type, c: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(c)?;
        Ok(match ty {
            Type::Ref(_) | Type::Owned(..) | Type::Map(..) | Type::Path(..) => false,
            Type::Tuple(v) => {
                for t in v {
                    if !value_type(t, c)? {
                        return Ok(false);
                    }
                }
                true
            }
            Type::List(t) | Type::Set(t) | Type::Option(t) => value_type(t, c)?,
            Type::Term(a, r) => {
                for t in a {
                    if !value_type(t, c)? {
                        return Ok(false);
                    }
                }
                value_type(r, c)?
            }
            _ => true,
        })
    })
}
fn children(e: &Expr) -> Result<Vec<usize>, ValidationFailure> {
    Ok(match &e.kind {
        ExprKind::Let { value, body, .. } => vec![*value, *body],
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => vec![*cond, *then_branch, *else_branch],
        ExprKind::Match { scrutinee, arms } => std::iter::once(*scrutinee)
            .chain(arms.iter().map(|a| a.body))
            .collect(),
        ExprKind::Quant {
            split: QuantSplit::Fixed { domain, body },
            ..
        } => match domain {
            QuantDomain::In(d) => vec![*d, *body],
            QuantDomain::Type(_) => vec![*body],
        },
        ExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
        ExprKind::Unary { operand, .. }
        | ExprKind::Group(operand)
        | ExprKind::Some(operand)
        | ExprKind::Index { base: operand, .. } => vec![*operand],
        ExprKind::Call { callee, args } => std::iter::once(*callee)
            .chain(args.iter().copied())
            .collect(),
        ExprKind::Tuple(v)
        | ExprKind::ListLit { items: v, .. }
        | ExprKind::SetLit { items: v, .. } => v.clone(),
        ExprKind::SetComp {
            elem,
            domain,
            filter,
            ..
        } => std::iter::once(*domain)
            .chain(*filter)
            .chain([*elem])
            .collect(),
        ExprKind::Fn { body, .. } => vec![*body],
        ExprKind::Dotted(_)
        | ExprKind::Int(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Unit
        | ExprKind::None(_) => vec![],
        _ => return Err("閉じたTermの検査済みbodyに禁止式がある".into()),
    })
}
impl Term {
    #[allow(clippy::too_many_arguments)]
    fn capture<'a>(
        expr: impl Fn(usize) -> Option<&'a Expr>,
        ty: impl Fn(usize) -> Option<&'a Type>,
        quant: impl Fn(usize) -> Option<&'a Type>,
        refs: &[(Span, String)],
        root: usize,
        params: Vec<(String, Type)>,
        returns: Type,
        body: String,
        offset: usize,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        let span = expr(root).ok_or("Term rootがない")?.span;
        let mut result = Self {
            params,
            returns,
            body,
            root,
            offset,
            nodes: BTreeMap::new(),
            types: BTreeMap::new(),
            references: Vec::new(),
            quantifier_types: BTreeMap::new(),
        };
        let mut pending = vec![root];
        while let Some(i) = pending.pop() {
            tick(c)?;
            if result.nodes.contains_key(&i) {
                continue;
            }
            let e = expr(i).ok_or("Term子ASTがない")?;
            pending.extend(children(e)?);
            result.nodes.insert(i, e.clone());
            if let Some(t) = ty(i) {
                result.types.insert(i, t.clone());
            }
            if let Some(t) = quant(i) {
                result.quantifier_types.insert(i, t.clone());
            }
            tick(c)?;
        }
        for (s, n) in refs {
            tick(c)?;
            if s.0 >= span.0 && s.1 <= span.1 {
                result.references.push((*s, n.clone()));
            }
            tick(c)?;
        }
        result.check(c)?;
        Ok(result)
    }
    pub(super) fn from_input(
        term: &crate::archmap::value::TermValue,
        args: &[Type],
        ret: &Type,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        if term.params.len() != args.len() {
            return Err("Term parameter個数が元型と違う".into());
        }
        let TermBody {
            exprs,
            root,
            types,
            references,
            quantifier_types,
        } = &term.checked;
        Self::capture(
            |i| exprs.get(i),
            |i| types.get(i).and_then(Option::as_ref),
            |i| quantifier_types.get(i).and_then(Option::as_ref),
            references,
            *root,
            term.params
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect(),
            ret.clone(),
            term.body.clone(),
            0,
            c,
        )
    }
    pub(super) fn from_law(
        law: &CheckedLaw,
        raw: &[u8],
        id: usize,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        let ExprKind::Fn { params, body } = &law.exprs.get(id).ok_or("fn ASTがない")?.kind
        else {
            return Err("元fnでない".into());
        };
        let Type::Term(args, ret) = law.expr_type(id).ok_or("fn型がない")? else {
            return Err("元fn型でない".into());
        };
        if params.len() != args.len() {
            return Err("元fn parameter数が違う".into());
        }
        let span = law.exprs[*body].span;
        let text = std::str::from_utf8(raw.get(span.0..span.1).ok_or("fn body spanが違う")?)
            .map_err(|_| ValidationFailure::from("fn body UTF-8が違う"))?
            .to_string();
        let mut refs = Vec::new();
        for info in &law.infos {
            for (s, n) in &info.references {
                tick(c)?;
                if s.0 >= span.0 && s.1 <= span.1 {
                    refs.push((*s, n.clone()));
                }
            }
        }
        Self::capture(
            |i| law.exprs.get(i),
            |i| law.expr_type(i),
            |i| law.quantifier_types.get(i).and_then(Option::as_ref),
            &refs,
            *body,
            params
                .iter()
                .map(|p| p.name.name.clone())
                .zip(args.iter().cloned())
                .collect(),
            (**ret).clone(),
            text,
            span.0,
            c,
        )
    }
    pub(super) fn wire(&self) -> Json {
        Json::obj([
            (
                "params",
                Json::Arr(self.params.iter().map(|(n, _)| Json::str(n)).collect()),
            ),
            ("body", Json::str(&self.body)),
        ])
    }
    pub(super) fn ty(&self) -> Type {
        Type::Term(
            self.params.iter().map(|(_, t)| t.clone()).collect(),
            Box::new(self.returns.clone()),
        )
    }
    pub(super) fn check(&self, c: &Control) -> Result<(), ValidationFailure> {
        tick(c)?;
        let mut names = BTreeSet::new();
        for (n, t) in &self.params {
            tick(c)?;
            if !names.insert(n) || !value_type(t, c)? {
                return Err("Term parameterが重複・参照型".into());
            }
        }
        if !value_type(&self.returns, c)? || self.types.get(&self.root) != Some(&self.returns) {
            return Err("Term bodyの結果型が違う".into());
        }
        fn visit(
            t: &Term,
            id: usize,
            active: &mut BTreeSet<usize>,
            seen: &mut BTreeSet<usize>,
            c: &Control,
        ) -> Result<(), ValidationFailure> {
            stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
                tick(c)?;
                if active.contains(&id) {
                    return Err("Term ASTが循環する".into());
                }
                if seen.contains(&id) {
                    return Ok(());
                }
                active.insert(id);
                let e = t.nodes.get(&id).ok_or("Term子ASTがない")?;
                if e.span.0 < t.offset || e.span.1 < e.span.0 || e.span.1 - t.offset > t.body.len()
                {
                    return Err("Term元body spanが違う".into());
                }
                for id in children(e)? {
                    visit(t, id, active, seen, c)?
                }
                active.remove(&id);
                seen.insert(id);
                tick(c)?;
                Ok(())
            })
        }
        let mut seen = BTreeSet::new();
        visit(self, self.root, &mut BTreeSet::new(), &mut seen, c)?;
        if seen.len() != self.nodes.len() {
            return Err("Termにbody外のASTがある".into());
        }
        tick(c)?;
        Ok(())
    }
    fn reference(&self, span: Span, c: &Control) -> Result<Option<&str>, ValidationFailure> {
        let mut found = None;
        for (s, n) in &self.references {
            tick(c)?;
            if *s == span {
                if found.is_some_and(|old| old != n) {
                    return Err("Termの元静的参照が重複する".into());
                }
                found = Some(n.as_str());
            }
        }
        Ok(found)
    }
    fn pattern(
        &self,
        p: &Pattern,
        v: &Scalar,
        vars: &mut BTreeMap<String, Scalar>,
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            let (name, args) = match p {
                Pattern::Wild(_) => return Ok(true),
                Pattern::Name(n) => match self.reference(n.span, c)? {
                    None => {
                        if vars.insert(n.name.clone(), v.clone()).is_some() {
                            return Err("Term pattern束縛が重複する".into());
                        }
                        return Ok(true);
                    }
                    Some(name) => (name, &[][..]),
                },
                Pattern::Ctor { name, args, .. } => (
                    self.reference(name.span(), c)?
                        .ok_or("Term constructorの元参照がない")?,
                    args.as_slice(),
                ),
            };
            let Scalar::Data {
                constructor,
                args: values,
                ..
            } = v
            else {
                return Err("Term constructor patternの値型が違う".into());
            };
            if constructor != name {
                return Ok(false);
            }
            if args.len() != values.len() {
                return Err("Term pattern引数数が違う".into());
            }
            for (p, v) in args.iter().zip(values) {
                if !self.pattern(p, v, vars, c)? {
                    return Ok(false);
                }
            }
            Ok(true)
        })
    }
    pub(super) fn apply(
        &self,
        args: &[Scalar],
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        self.check(c)?;
        if args.len() != self.params.len() {
            return Err("Term適用の引数数が違う".into());
        }
        let mut vars = BTreeMap::new();
        for ((name, ty), v) in self.params.iter().zip(args) {
            tick(c)?;
            if *ty != v.ty() {
                return Err("Term実引数型が違う".into());
            }
            data::check(v, law, c)?;
            vars.insert(name.clone(), v.clone());
        }
        let value = self.eval(self.root, &vars, law, c)?;
        if value.ty() != self.returns {
            return Err("Term適用の戻り型が違う".into());
        }
        data::check(&value, law, c)?;
        Ok(value)
    }
    fn eval(
        &self,
        id: usize,
        vars: &BTreeMap<String, Scalar>,
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Scalar, ValidationFailure> {
        stacker::maybe_grow(128 * 1024, 1024 * 1024, || {
            tick(c)?;
            #[cfg(test)]
            data::observe_iteration("term_body", id);
            tick(c)?;
            let e = self.nodes.get(&id).ok_or("Term元式がない")?;
            let ty = self.types.get(&id).ok_or("Term元式の型がない")?;
            let value = match &e.kind {
                ExprKind::Int(n) => numeric::literal(n, ty, c)?,
                ExprKind::Str(s) => Scalar::Text(s.clone()),
                ExprKind::Bool(b) => Scalar::Bool(*b),
                ExprKind::Unit => Scalar::Unit,
                ExprKind::Dotted(parts) => {
                    if parts.len() == 1 && vars.contains_key(&parts[0].name) {
                        vars[&parts[0].name].clone()
                    } else {
                        let Type::Data(family) = ty else {
                            return Err("Termの元名前が束縛・constructorでない".into());
                        };
                        let name = self
                            .reference(e.span, c)?
                            .ok_or("Term零constructorの元参照がない")?;
                        let ctor = data::constructor(law, family, name, c)?;
                        if !ctor.arguments.is_empty() {
                            return Err("Term零constructorの引数数が違う".into());
                        }
                        Scalar::Data {
                            family: family.clone(),
                            constructor: name.into(),
                            args: vec![],
                        }
                    }
                }
                ExprKind::Group(i) => self.eval(*i, vars, law, c)?,
                ExprKind::Unary { op, operand } => {
                    environment::unary(*op, &self.eval(*operand, vars, law, c)?, c)?
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let a = self.eval(*lhs, vars, law, c)?;
                    let short = match (op, &a) {
                        (BinOp::And, Scalar::Bool(false)) => Some(false),
                        (BinOp::Or, Scalar::Bool(true)) | (BinOp::Implies, Scalar::Bool(false)) => {
                            Some(true)
                        }
                        _ => None,
                    };
                    if let Some(b) = short {
                        Scalar::Bool(b)
                    } else {
                        let b = self.eval(*rhs, vars, law, c)?;
                        if !environment::supports_binary(*op, &a.ty(), law, c)? {
                            return Err(ValidationFailure::UnsupportedExpression {
                                location: crate::issue::Location::Law { span: e.span },
                                feature: "Term bodyの未対応の型・演算".into(),
                            });
                        }
                        environment::binary(*op, &a, &b, c)?
                    }
                }
                ExprKind::Let { name, value, body } => {
                    let v = self.eval(*value, vars, law, c)?;
                    let mut local = copy_variables(vars, c)?;
                    if local.insert(name.name.clone(), v).is_some() {
                        return Err("Term let束縛が重複する".into());
                    }
                    self.eval(*body, &local, law, c)?
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => match self.eval(*cond, vars, law, c)? {
                    Scalar::Bool(true) => self.eval(*then_branch, vars, law, c)?,
                    Scalar::Bool(false) => self.eval(*else_branch, vars, law, c)?,
                    _ => return Err("Term if条件がBoolでない".into()),
                },
                ExprKind::Match { scrutinee, arms } => {
                    let v = self.eval(*scrutinee, vars, law, c)?;
                    let mut result = None;
                    for a in arms {
                        tick(c)?;
                        let mut local = copy_variables(vars, c)?;
                        if self.pattern(&a.pattern, &v, &mut local, c)? {
                            result = Some(self.eval(a.body, &local, law, c)?);
                            break;
                        }
                    }
                    result.ok_or("Term matchの元選択枝がない")?
                }
                ExprKind::Index { base, index, .. } => {
                    let Scalar::Tuple(ref v) = self.eval(*base, vars, law, c)? else {
                        return Err("Term数値射影元がTupleでない".into());
                    };
                    v.get(*index).ok_or("Term Tuple位置が違う")?.clone()
                }
                ExprKind::Tuple(items) => Scalar::Tuple(self.eval_items(items, vars, law, c)?),
                ExprKind::ListLit { items, .. } => {
                    let Type::List(element) = ty else {
                        return Err("Term List型がない".into());
                    };
                    Scalar::List {
                        element: (**element).clone(),
                        items: self.eval_items(items, vars, law, c)?,
                    }
                }
                ExprKind::SetLit { items, .. } => {
                    let Type::Set(element) = ty else {
                        return Err("Term Set型がない".into());
                    };
                    data::set(
                        (**element).clone(),
                        &self.eval_items(items, vars, law, c)?,
                        c,
                    )?
                }
                ExprKind::None(_) => {
                    let Type::Option(element) = ty else {
                        return Err("Term Option型がない".into());
                    };
                    Scalar::Option {
                        element: (**element).clone(),
                        value: None,
                    }
                }
                ExprKind::Some(i) => {
                    let Type::Option(element) = ty else {
                        return Err("Term Option型がない".into());
                    };
                    Scalar::Option {
                        element: (**element).clone(),
                        value: Some(Box::new(self.eval(*i, vars, law, c)?)),
                    }
                }
                ExprKind::Call { callee, args } => {
                    let values = self.eval_items(args, vars, law, c)?;
                    let mut callee = *callee;
                    while let ExprKind::Group(inner) =
                        self.nodes.get(&callee).ok_or("Term calleeがない")?.kind
                    {
                        tick(c)?;
                        callee = inner;
                    }
                    let source = &self.nodes[&callee];
                    if let Some(target) = self.reference(source.span, c)? {
                        let Type::Data(family) = ty else {
                            return Err("Term constructor戻り型がない".into());
                        };
                        let ctor = data::constructor(law, family, target, c)?;
                        if ctor.arguments.len() != values.len() {
                            return Err("Term constructor引数数が違う".into());
                        }
                        Scalar::Data {
                            family: family.clone(),
                            constructor: target.into(),
                            args: values,
                        }
                    } else {
                        let ExprKind::Dotted(parts) = &source.kind else {
                            return Err("Term calleeが固定演算でない".into());
                        };
                        match parts.first().map(|p| p.name.as_str()) {
                            Some("rat") if parts.len() == 1 && values.len() == 2 => {
                                numeric::rational(&values[0], &values[1], c)?
                            }
                            Some(name @ ("count" | "sum"))
                                if parts.len() == 1 && values.len() == 1 =>
                            {
                                data::aggregate(name, &values[0], c)?
                            }
                            _ => return Err("Term bodyに禁止された呼出しがある".into()),
                        }
                    }
                }
                ExprKind::SetComp {
                    elem,
                    var,
                    domain,
                    filter,
                } => {
                    let input = self.eval(*domain, vars, law, c)?;
                    let values = match &input {
                        Scalar::List { items, .. } | Scalar::Set { items, .. } => items,
                        _ => return Err("Term内包域がList/Setでない".into()),
                    };
                    let mut result = Vec::new();
                    for v in values {
                        tick(c)?;
                        let mut local = copy_variables(vars, c)?;
                        if local.insert(var.name.clone(), v.clone()).is_some() {
                            return Err("Term内包束縛が重複する".into());
                        }
                        let keep = match filter {
                            None => true,
                            Some(f) => match self.eval(*f, &local, law, c)? {
                                Scalar::Bool(b) => b,
                                _ => return Err("Term内包filterがBoolでない".into()),
                            },
                        };
                        if keep {
                            result.push(self.eval(*elem, &local, law, c)?);
                        }
                    }
                    let Type::Set(t) = ty else {
                        return Err("Term内包結果型がSetでない".into());
                    };
                    data::set((**t).clone(), &result, c)?
                }
                ExprKind::Quant {
                    kind,
                    var,
                    split: QuantSplit::Fixed { domain, body },
                } => {
                    let element = self
                        .quantifier_types
                        .get(&id)
                        .ok_or("Term量化の元binder型がない")?;
                    let values = match domain {
                        QuantDomain::In(i) => match self.eval(*i, vars, law, c)? {
                            Scalar::List { ref items, .. } | Scalar::Set { ref items, .. } => {
                                items.clone()
                            }
                            _ => return Err("Term量化域がList/Setでない".into()),
                        },
                        QuantDomain::Type(_) => {
                            if !super::finite::completion_supported(element, law, c)? {
                                return Err(ValidationFailure::UnsupportedExpression {
                                    location: crate::issue::Location::Law { span: e.span },
                                    feature: "Term bodyの非有限な型量化".into(),
                                });
                            }
                            super::finite::values(
                                element,
                                law,
                                c,
                                &mut |_| Err("Termに参照族は置けない".into()),
                                &mut |_| {},
                            )?
                            .values
                        }
                    };
                    let mut result = *kind == QuantKind::Forall;
                    for v in values {
                        tick(c)?;
                        let mut local = copy_variables(vars, c)?;
                        if local.insert(var.name.clone(), v).is_some() {
                            return Err("Term量化束縛が重複する".into());
                        }
                        let Scalar::Bool(b) = self.eval(*body, &local, law, c)? else {
                            return Err("Term量化bodyがBoolでない".into());
                        };
                        if (*kind == QuantKind::Forall && !b) || (*kind == QuantKind::Exists && b) {
                            result = b;
                            break;
                        }
                    }
                    Scalar::Bool(result)
                }
                ExprKind::Fn { params, body } => {
                    let Type::Term(a, r) = ty else {
                        return Err("Term内fn型がない".into());
                    };
                    let s = self.nodes.get(body).ok_or("Term内fn bodyがない")?.span;
                    let text = self
                        .body
                        .get(s.0 - self.offset..s.1 - self.offset)
                        .ok_or("Term内fn文字列がない")?
                        .into();
                    Scalar::Term(Box::new(Self::capture(
                        |i| self.nodes.get(&i),
                        |i| self.types.get(&i),
                        |i| self.quantifier_types.get(&i),
                        &self.references,
                        *body,
                        params
                            .iter()
                            .map(|p| p.name.name.clone())
                            .zip(a.iter().cloned())
                            .collect(),
                        (**r).clone(),
                        text,
                        s.0,
                        c,
                    )?))
                }
                _ => return Err("閉じたTermに禁止された式形がある".into()),
            };
            if value.ty() != *ty {
                return Err("Term原式の評価結果型が違う".into());
            }
            data::check(&value, law, c)?;
            tick(c)?;
            Ok(value)
        })
    }
    fn eval_items(
        &self,
        items: &[usize],
        vars: &BTreeMap<String, Scalar>,
        law: &CheckedLaw,
        c: &Control,
    ) -> Result<Vec<Scalar>, ValidationFailure> {
        let mut values = Vec::new();
        for i in items {
            tick(c)?;
            values.push(self.eval(*i, vars, law, c)?);
            tick(c)?;
        }
        Ok(values)
    }
}
