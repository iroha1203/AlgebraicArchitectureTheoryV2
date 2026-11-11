//! 元の有理parameter上で作用とLawを正規化し、完全な線形fiberを求める。
use super::change_affine::{Pending, capture_missing, with_missing};
use super::*;
use crate::observed::{
    affine::{self, Form, NumberType, Parameter},
    field_fiber::{self, Fiber, Matrix},
    field_polyhedron::{self, Halfspace, Outcome},
    numeric,
};
use archsig_input::law::model::{Declaration, Signature};
#[derive(Clone, Debug)]
pub(in crate::observed) struct Linear {
    pub parameter_count: usize,
    pub axes: Vec<Parameter>,
    pub guard_fiber: Fiber,
    pub slots: Vec<Fact>,
    pub action: Matrix,
    pub offset: Vec<Scalar>,
    pub equations: Matrix,
    pub rhs: Vec<Scalar>,
    pub quantifiers: Vec<(Quantifier, Vec<Scalar>)>,
    pub constraint_support: BTreeSet<Fact>,
    pub scope: Scope,
    pub solutions: Solutions,
}

#[derive(Clone, Debug)]
pub(in crate::observed) enum Solutions {
    Affine(Fiber),
    Polyhedron(Polyhedron),
}

#[derive(Clone, Debug)]
pub(in crate::observed) struct Polyhedron {
    pub inequalities: Vec<Halfspace>,
    pub outcome: Outcome,
}

#[derive(Default)]
struct Constraints {
    equalities: Matrix,
    rhs: Vec<Option<Scalar>>,
    inequalities: Option<Vec<Halfspace>>,
    quantifiers: Vec<(Quantifier, Vec<Scalar>)>,
    refuted: bool,
    capture_reads: bool,
    constraint_support: BTreeSet<Fact>,
    scope: Scope,
    pending_failure: Option<ValidationFailure>,
}

impl Constraints {
    fn contradiction(&mut self, n: usize, env: &Environment<'_>) -> Result<(), ValidationFailure> {
        self.equalities
            .push(vec![numeric::zero(&Type::Q, &env.control)?; n]);
        self.rhs
            .push(Some(numeric::literal("1", &Type::Q, &env.control)?));
        self.refuted = true;
        Ok(())
    }
}
fn unsupported(env: &Environment<'_>, id: usize, feature: &str) -> ValidationFailure {
    ValidationFailure::UnsupportedExpression {
        location: Location::Law {
            span: env.indexes.inputs.law().exprs()[id].span,
        },
        feature: feature.into(),
    }
}
fn value(env: &Environment<'_>, scalar: Scalar) -> Result<SourceValue, ValidationFailure> {
    Ok(SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        affine: affine::constant(&scalar, &env.control)?.map(Box::new),
        scope: Scope::default(),
        known_value: Some(scalar),
        support: vec![].into(),
        scalar_scope: Some(Scope::default()),
    })
}
fn usable(env: &Environment<'_>, id: usize, v: &SourceValue) -> Result<(), ValidationFailure> {
    if v.condition_failed || v.condition_pending {
        return Err(unsupported(env, id, "有理changeの式の構成条件が未成立"));
    }
    Ok(())
}
#[derive(Clone, Copy)]
enum Axes<'a> {
    Parameters(&'a [Parameter]),
    State(&'a [Fact]),
}
impl Axes<'_> {
    fn len(self) -> usize {
        match self {
            Self::Parameters(v) => v.len(),
            Self::State(v) => v.len(),
        }
    }
}
fn coordinates(
    env: &Environment<'_>,
    id: usize,
    form: &Form,
    axes: Axes<'_>,
    missing: &mut Pending,
) -> Result<(Option<Scalar>, Vec<Scalar>), ValidationFailure> {
    (match axes {
        Axes::Parameters(axes) => form
            .rational_coordinates(axes, &env.control)?
            .map(|(v, row)| (Some(v), row)),
        Axes::State(slots) => {
            missing.facts.extend(form.missing_facts());
            form.rational_state_coordinates(slots, &env.control)?
        }
    })
    .ok_or_else(|| {
        missing.facts.extend(form.missing_facts());
        unsupported(
            env,
            id,
            "有理changeの係数に欠測または元parameter以外の記号がある",
        )
    })
}
// A diagnostic distinguishes the dependence of a value on a candidate
// from the observations needed to obtain it. It never supplies values to
// the solver. Affine cancellation takes precedence over syntactic reads.
#[derive(Clone, Copy, Default, Eq, Ord, PartialEq, PartialOrd)]
enum Dependence {
    #[default]
    Fixed,
    Affine,
    Other,
}

#[derive(Clone, Default)]
struct Dependency {
    dependence: Dependence,
    facts: BTreeSet<Fact>,
    components: Vec<Dependency>,
    affine_equality: bool,
    closed_constraint: bool,
    term_bodies: Vec<(usize, Vec<String>)>,
}

type LexicalDependencies = BTreeMap<String, Dependency>;

impl Dependency {
    fn merge(&mut self, other: Self) {
        self.dependence = self.dependence.max(other.dependence);
        self.facts.extend(other.facts);
        self.components.clear();
        self.affine_equality = false;
        self.closed_constraint = false;
        self.term_bodies.clear();
    }

    fn product(components: Vec<Self>) -> Self {
        let mut result = Self::default();
        for item in &components {
            result.dependence = result.dependence.max(item.dependence);
            result.facts.extend(item.facts.iter().cloned());
        }
        result.components = components;
        result
    }

    fn alternatives(
        test: &Self,
        branches: &[&Self],
        env: &Environment<'_>,
    ) -> Result<Self, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            env.tick()?;
            let mut result = Self {
                dependence: test.dependence,
                facts: test.facts.clone(),
                affine_equality: test.dependence == Dependence::Fixed
                    && branches.iter().all(|branch| {
                        branch.dependence == Dependence::Fixed || branch.affine_equality
                    }),
                ..Self::default()
            };
            if branches.iter().all(|branch| !branch.term_bodies.is_empty()) {
                for branch in branches {
                    for term in &branch.term_bodies {
                        env.tick()?;
                        if !result.term_bodies.contains(term) {
                            result.term_bodies.push(term.clone());
                        }
                    }
                }
            }
            for branch in branches {
                env.tick()?;
                result.dependence = result.dependence.max(branch.dependence);
            }
            if let Some(first) = branches.first()
                && branches
                    .iter()
                    .all(|branch| branch.components.len() == first.components.len())
            {
                for index in 0..first.components.len() {
                    let members = branches
                        .iter()
                        .map(|branch| &branch.components[index])
                        .collect::<Vec<_>>();
                    result
                        .components
                        .push(Self::alternatives(test, &members, env)?);
                }
            }
            result.closed_constraint = result.affine_equality;
            Ok(result)
        })
    }

    fn component_at(&self, path: &[usize]) -> &Self {
        let mut selected = self;
        for &index in path {
            let Some(component) = selected.components.get(index) else {
                break;
            };
            selected = component;
        }
        selected
    }

    fn record(self, missing: &mut Pending, maximum: Dependence) {
        missing.awaiting_observation = !self.facts.is_empty() && self.dependence <= maximum;
        missing.facts.extend(self.facts);
    }

    fn extractable(&self) -> bool {
        self.dependence == Dependence::Fixed || self.closed_constraint
    }

    fn record_constraint(self, missing: &mut Pending) {
        missing.awaiting_observation = !self.facts.is_empty() && self.extractable();
        missing.facts.extend(self.facts);
    }

    fn record_equality(self, missing: &mut Pending) {
        missing.awaiting_observation = !self.facts.is_empty()
            && (self.dependence == Dependence::Fixed || self.affine_equality);
        missing.facts.extend(self.facts);
    }
}

struct DependencyAnalysis<'a, 'input> {
    env: &'a Environment<'input>,
    axes: &'a [Parameter],
}

impl DependencyAnalysis<'_, '_> {
    fn source(
        &self,
        id: usize,
        vars: &BTreeMap<String, SourceValue>,
        reading: &str,
    ) -> Result<SourceValue, ValidationFailure> {
        self.env.scoped_ast(id, vars, &Scope::default(), reading)
    }

    fn form(&self, form: &Form) -> Result<Dependency, ValidationFailure> {
        let control = &self.env.control;
        let dependence = match form.rational_parameter_dependence(self.axes, control)? {
            Some(true) => Dependence::Affine,
            Some(false) => Dependence::Fixed,
            None => Dependence::Other,
        };
        Ok(Dependency {
            dependence,
            facts: form.missing_facts().into_iter().collect(),
            ..Dependency::default()
        })
    }

    fn unknown_member(&self) -> Result<SourceValue, ValidationFailure> {
        let mut value = value(self.env, Scalar::Unit)?;
        value.known_value = None;
        value.scalar_scope = None;
        Ok(value)
    }

    fn law_term_body(&self, term: &crate::observed::term::Term) -> Option<usize> {
        let inputs = self.env.indexes.inputs;
        let root = term.root;
        let source = inputs.law().exprs().get(root)?;
        let end = term.offset.checked_add(term.body.len())?;
        (term.nodes.get(&root) == Some(source)
            && inputs.sources().law().bytes().get(term.offset..end) == Some(term.body.as_bytes()))
        .then_some(root)
    }

    fn read(
        &self,
        id: usize,
        vars: &BTreeMap<String, SourceValue>,
        lexical: &LexicalDependencies,
        reading: &str,
    ) -> Result<Dependency, ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            let env = self.env;
            env.tick()?;
            let law = env.indexes.inputs.law();
            let (source, absent) = capture_missing(env, || self.source(id, vars, reading))?;
            let source = source?;
            if !source.condition_pending && !source.condition_failed {
                if let Some(value) = &source.known_value {
                    let mut result = Dependency::default();
                    if let Scalar::Term(term) = value
                        && let Some(body) = self.law_term_body(term)
                    {
                        result.term_bodies.push((
                            body,
                            term.params.iter().map(|(name, _)| name.clone()).collect(),
                        ));
                    }
                    return Ok(result);
                }
                if law.expr_type(id) == Some(&Type::Q)
                    && let Some(form) = source.affine.as_deref()
                {
                    return self.form(form);
                }
            }
            let child = |id| self.read(id, vars, lexical, reading);
            let fallback = || Dependency {
                dependence: if source.scope.assignments || source.condition_failed {
                    Dependence::Other
                } else {
                    Dependence::Fixed
                },
                facts: absent.into_iter().collect(),
                ..Dependency::default()
            };
            match &law.exprs()[id].kind {
                ExprKind::Dotted(parts) => {
                    let Some(bound) = parts.first().and_then(|name| lexical.get(&name.name)) else {
                        return Ok(fallback());
                    };
                    if parts.len() == 1 {
                        let mut result = bound.clone();
                        result.closed_constraint = result.affine_equality;
                        return Ok(result);
                    }
                    let mut result = fallback();
                    result.merge(bound.clone());
                    Ok(result)
                }
                ExprKind::Group(body) => child(*body),
                ExprKind::Unary { operand, .. } => {
                    let mut result = child(*operand)?;
                    result.affine_equality = false;
                    result.closed_constraint = false;
                    Ok(result)
                }
                ExprKind::Index { base, index, .. } => {
                    let base = child(*base)?;
                    if let Some(element) = base.components.get(*index) {
                        return Ok(element.clone());
                    }
                    let mut result = fallback();
                    result.merge(base);
                    Ok(result)
                }
                ExprKind::Field { base, .. } | ExprKind::Family { owner: base, .. } => {
                    let mut result = fallback();
                    result.merge(child(*base)?);
                    Ok(result)
                }
                ExprKind::Let { name, value, body } => {
                    let mut local = env.copy_variables(vars)?;
                    let mut dependencies = lexical.clone();
                    let value_source = self.source(*value, vars, reading)?;
                    let dependency = child(*value)?;
                    local.insert(name.name.clone(), value_source);
                    dependencies.insert(name.name.clone(), dependency);
                    self.read(*body, &local, &dependencies, reading)
                }
                ExprKind::Call { callee, args } => {
                    if let Some(declaration) = env.named_view(id)?
                        && let Signature::View { params, body, .. } = &declaration.signature
                    {
                        let mut local = BTreeMap::new();
                        let mut dependencies = BTreeMap::new();
                        let mut checks = Dependency::default();
                        for (parameter, arg) in params.iter().zip(args) {
                            let argument = self.source(*arg, vars, reading)?;
                            let dependency = child(*arg)?;
                            if argument.condition_pending
                                || argument.condition_failed
                                || matches!(parameter.ty, Type::Ref(_))
                                || env.call_type_has_owned(&parameter.ty)?
                            {
                                checks.merge(dependency.clone());
                            }
                            local.insert(parameter.name.clone(), argument);
                            dependencies.insert(parameter.name.clone(), dependency);
                        }
                        let mut result =
                            self.read(*body, &local, &dependencies, &declaration.reading)?;
                        if source.condition_pending || source.condition_failed {
                            result.facts.extend(fallback().facts);
                            result.facts.extend(checks.facts);
                            result.dependence = result.dependence.max(checks.dependence);
                            result.affine_equality &= checks.dependence == Dependence::Fixed;
                        }
                        result.closed_constraint = result.affine_equality;
                        Ok(result)
                    } else if data::expression(law, id, &env.control)?.is_some() {
                        let items = args.iter().map(|id| child(*id)).collect::<Result<_, _>>()?;
                        Ok(Dependency::product(items))
                    } else if matches!(
                        law.program().callees.get(callee),
                        Some(archsig_input::law::ir::Callee::Builtin("sum"))
                    ) && law.expr_type(id) == Some(&Type::Q)
                    {
                        child(args[0])
                    } else {
                        let callee_dependency =
                            if matches!(law.expr_type(*callee), Some(Type::Term(..))) {
                                child(*callee)?
                            } else {
                                Dependency::default()
                            };
                        if !callee_dependency.term_bodies.is_empty() {
                            let arguments = args
                                .iter()
                                .map(|arg| Ok((self.source(*arg, vars, reading)?, child(*arg)?)))
                                .collect::<Result<Vec<_>, ValidationFailure>>()?;
                            let mut branches = Vec::new();
                            for (body, params) in &callee_dependency.term_bodies {
                                let mut local = BTreeMap::new();
                                let mut dependencies = BTreeMap::new();
                                for (name, (source, dependency)) in params.iter().zip(&arguments) {
                                    env.tick()?;
                                    local.insert(name.clone(), source.clone());
                                    dependencies.insert(name.clone(), dependency.clone());
                                }
                                branches.push(self.read(*body, &local, &dependencies, reading)?);
                            }
                            if branches.len() == 1
                                && callee_dependency.facts.is_empty()
                                && callee_dependency.dependence == Dependence::Fixed
                            {
                                return branches
                                    .pop()
                                    .ok_or(internal!("Termの元本体がない").into());
                            }
                            let branches = branches.iter().collect::<Vec<_>>();
                            return Dependency::alternatives(&callee_dependency, &branches, env);
                        }
                        let mut result = fallback();
                        result.merge(callee_dependency);
                        for arg in args {
                            result.merge(child(*arg)?);
                        }
                        if result.dependence == Dependence::Affine {
                            result.dependence = Dependence::Other;
                        }
                        Ok(result)
                    }
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    let numeric_comparison = matches!(
                        op,
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                    ) && law.expr_type(*lhs) == Some(&Type::Q)
                        && law.expr_type(*rhs) == Some(&Type::Q);
                    if numeric_comparison && !source.condition_failed && !source.condition_pending {
                        let lhs = self.source(*lhs, vars, reading)?;
                        let rhs = self.source(*rhs, vars, reading)?;
                        if let Some(form) = affine::binary(
                            BinOp::Sub,
                            lhs.affine.as_deref(),
                            rhs.affine.as_deref(),
                            &env.control,
                        )? {
                            let mut result = self.form(&form)?;
                            result.affine_equality =
                                *op == BinOp::Eq && result.dependence <= Dependence::Affine;
                            result.closed_constraint =
                                matches!(op, BinOp::Eq | BinOp::Le | BinOp::Ge)
                                    && result.dependence <= Dependence::Affine;
                            if result.dependence == Dependence::Affine {
                                result.dependence = Dependence::Other;
                            }
                            return Ok(result);
                        }
                    }
                    let mut left = child(*lhs)?;
                    let right = child(*rhs)?;
                    let nonlinear = left.dependence != Dependence::Fixed
                        && right.dependence != Dependence::Fixed;
                    let closed = match op {
                        BinOp::And => left.extractable() && right.extractable(),
                        BinOp::Implies => {
                            left.dependence == Dependence::Fixed && right.extractable()
                        }
                        BinOp::Eq | BinOp::Le | BinOp::Ge if numeric_comparison => {
                            left.dependence.max(right.dependence) <= Dependence::Affine
                        }
                        _ => false,
                    };
                    left.merge(right);
                    left.closed_constraint = closed;
                    left.affine_equality = numeric_comparison
                        && *op == BinOp::Eq
                        && left.dependence <= Dependence::Affine;
                    if left.dependence == Dependence::Affine
                        && (!matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
                            || (*op == BinOp::Mul && nonlinear))
                    {
                        left.dependence = Dependence::Other;
                    }
                    Ok(left)
                }
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    match self.source(*cond, vars, reading)?.known_value {
                        Some(Scalar::Bool(true)) => child(*then_branch),
                        Some(Scalar::Bool(false)) => child(*else_branch),
                        _ => {
                            // Only the test is read until the branch is chosen.
                            let test = child(*cond)?;
                            let then_value = child(*then_branch)?;
                            let else_value = child(*else_branch)?;
                            Dependency::alternatives(&test, &[&then_value, &else_value], env)
                        }
                    }
                }
                ExprKind::Match { scrutinee, arms } => {
                    let input = self.source(*scrutinee, vars, reading)?;
                    let dependency = child(*scrutinee)?;
                    let ty = law
                        .expr_type(*scrutinee)
                        .ok_or(internal!("matchの元型がない"))?;
                    let dependencies =
                        |arm: usize| -> Result<LexicalDependencies, ValidationFailure> {
                            let mut result = lexical.clone();
                            for binder in data::binders(&arms[arm].pattern, ty, law, &env.control)?
                            {
                                result.insert(
                                    binder.name,
                                    dependency.component_at(&binder.path).clone(),
                                );
                            }
                            Ok(result)
                        };
                    if let Some((arm, local)) = env.scoped_match_bindings(id, &input, vars)? {
                        return self.read(arms[arm].body, &local, &dependencies(arm)?, reading);
                    }
                    let mut branches = Vec::new();
                    for (arm, branch) in arms.iter().enumerate() {
                        let mut local = env.copy_variables(vars)?;
                        for binder in data::binders(&branch.pattern, ty, law, &env.control)? {
                            local.insert(binder.name, self.unknown_member()?);
                        }
                        branches.push(self.read(
                            branch.body,
                            &local,
                            &dependencies(arm)?,
                            reading,
                        )?);
                    }
                    let branches = branches.iter().collect::<Vec<_>>();
                    Dependency::alternatives(&dependency, &branches, env)
                }
                ExprKind::Quant { .. } => {
                    let spec = quantifier::spec(law, id, &env.control)?;
                    let (domain, absent) = capture_missing(env, || {
                        env.scoped_quantifier_domain(&spec, vars, &Scope::default(), reading)
                    })?;
                    let (_, members) = domain?;
                    let mut result = if let Some(domain) = spec.domain {
                        child(domain)?
                    } else {
                        Dependency {
                            facts: absent.into_iter().collect(),
                            ..Dependency::default()
                        }
                    };
                    let mut closed = spec.kind == archsig_input::law::ast::QuantKind::Forall
                        && spec.domain.is_some()
                        && result.dependence == Dependence::Fixed;
                    let mut local = env.copy_variables(vars)?;
                    if let Some(members) = members {
                        for member in members {
                            env.tick()?;
                            local.insert(spec.name.into(), value(env, member)?);
                            let body = self.read(spec.body, &local, lexical, reading)?;
                            closed &= body.extractable();
                            result.merge(body);
                        }
                    } else {
                        local.insert(spec.name.into(), self.unknown_member()?);
                        let mut dependencies = lexical.clone();
                        dependencies.insert(spec.name.into(), result.clone());
                        let body = self.read(spec.body, &local, &dependencies, reading)?;
                        closed &= body.extractable();
                        result.dependence = result.dependence.max(body.dependence);
                    }
                    result.closed_constraint = closed;
                    Ok(result)
                }
                ExprKind::Comprehension {
                    var,
                    domain,
                    filter,
                    elem,
                    ..
                } => {
                    let input = self.source(*domain, vars, reading)?;
                    let mut result = child(*domain)?;
                    if let Some(container) = input.known_value.as_ref() {
                        let items = match container {
                            Scalar::List { items, .. } | Scalar::Set { items, .. } => items,
                            _ => return Err(internal!("内包元域がList/Setでない").into()),
                        };
                        let output = law.expr_type(id).ok_or(internal!("内包結果型がない"))?;
                        let mut local = env.copy_variables(vars)?;
                        for position in
                            data::comprehension_positions(container, output, &env.control)?
                        {
                            env.tick()?;
                            local.insert(var.name.clone(), value(env, items[position].clone())?);
                            let member = |id| self.read(id, &local, lexical, reading);
                            if let Some(filter) = filter {
                                result.merge(member(*filter)?);
                                match self.source(*filter, &local, reading)?.known_value {
                                    Some(Scalar::Bool(true)) => {}
                                    Some(Scalar::Bool(false)) => continue,
                                    _ => {
                                        result.dependence =
                                            result.dependence.max(member(*elem)?.dependence);
                                        continue;
                                    }
                                }
                            }
                            result.merge(member(*elem)?);
                        }
                    } else {
                        let mut local = env.copy_variables(vars)?;
                        local.insert(var.name.clone(), self.unknown_member()?);
                        let mut dependencies = lexical.clone();
                        dependencies.insert(var.name.clone(), result.clone());
                        let member = |id| self.read(id, &local, &dependencies, reading);
                        if let Some(filter) = filter {
                            result.dependence = result.dependence.max(member(*filter)?.dependence);
                            if self.source(*filter, &local, reading)?.known_value
                                == Some(Scalar::Bool(false))
                            {
                                return Ok(result);
                            }
                        }
                        result.dependence = result.dependence.max(member(*elem)?.dependence);
                    }
                    Ok(result)
                }
                ExprKind::Tuple(items) => {
                    let items = items
                        .iter()
                        .map(|id| child(*id))
                        .collect::<Result<_, _>>()?;
                    Ok(Dependency::product(items))
                }
                ExprKind::ListLit { items, .. } | ExprKind::SetLit { items, .. } => {
                    let mut result = Dependency::default();
                    for item in items {
                        result.merge(child(*item)?);
                    }
                    Ok(result)
                }
                ExprKind::Some(item) => Ok(Dependency::product(vec![child(*item)?])),
                _ => Ok(fallback()),
            }
        })
    }
}

fn dependency_axes<'a>(axes: Axes<'a>, missing: &Pending) -> std::borrow::Cow<'a, [Parameter]> {
    let parameters = match axes {
        Axes::Parameters(parameters) => parameters,
        Axes::State(_) => &[],
    };
    if missing.universal.is_empty() {
        return std::borrow::Cow::Borrowed(parameters);
    }
    std::borrow::Cow::Owned([parameters, &missing.universal].concat())
}

fn equations(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    reading: &str,
    axes: Axes<'_>,
    rows: &mut Constraints,
    missing: &mut Pending,
) -> Result<(), ValidationFailure> {
    collect_equations(
        env,
        id,
        vars,
        &LexicalDependencies::new(),
        reading,
        axes,
        rows,
        missing,
    )
}

// A fixed refutation of any conjunct survives a different conjunct's
// missing observation or unsupported construction.
#[derive(Default)]
struct Conjuncts {
    blocked: Option<(ValidationFailure, Pending)>,
}

impl Conjuncts {
    fn record(
        &mut self,
        outcome: Result<(), ValidationFailure>,
        allow_bounds: bool,
        missing: &mut Pending,
        control: &Control,
    ) -> Result<(), ValidationFailure> {
        if let Err(error) = outcome {
            let ValidationFailure::UnsupportedExpression { location, .. } = &error else {
                return Err(error);
            };
            if !allow_bounds {
                return Err(error);
            }
            let mut pending = Pending {
                facts: std::mem::take(&mut missing.facts),
                unsupported: missing.unsupported.take(),
                awaiting_observation: std::mem::take(&mut missing.awaiting_observation),
                additional: std::mem::take(&mut missing.additional),
                ..missing.clone()
            };
            if let Some((first_error, first)) = self.blocked.as_mut() {
                let ValidationFailure::UnsupportedExpression {
                    location: first_location,
                    ..
                } = first_error
                else {
                    return Err(internal!("有理制約の停止位置がない").into());
                };
                let additional = std::mem::take(&mut pending.additional);
                for (location, mut pending) in
                    std::iter::once((location.clone(), pending)).chain(additional)
                {
                    control.checkpoint(Checkpoint::RationalPolyhedron)?;
                    let same_source = |other: &Pending| {
                        other.expression == pending.expression
                            && other.bindings == pending.bindings
                            && other.parameters == pending.parameters
                            && other.unsupported == pending.unsupported
                            && other.awaiting_observation == pending.awaiting_observation
                    };
                    if first_location == &location && same_source(first) {
                        first.facts.append(&mut pending.facts);
                    } else {
                        let mut same = None;
                        for (old, other) in &mut first.additional {
                            control.checkpoint(Checkpoint::RationalPolyhedron)?;
                            if old == &location && same_source(other) {
                                same = Some(other);
                                break;
                            }
                        }
                        if let Some(other) = same {
                            other.facts.append(&mut pending.facts);
                        } else {
                            first.additional.push((location, pending));
                        }
                    }
                }
            } else {
                self.blocked = Some((error, pending));
            }
        }
        Ok(())
    }

    fn finish(
        self,
        rows: &mut Constraints,
        missing: &mut Pending,
    ) -> Result<(), ValidationFailure> {
        if let Some((error, pending)) = self.blocked {
            if !rows.refuted {
                *missing = pending;
                return Err(error);
            }
            rows.scope.completions |= needs_observation(&pending);
        }
        Ok(())
    }
}
fn needs_observation(pending: &Pending) -> bool {
    !pending.facts.is_empty()
        || pending
            .additional
            .iter()
            .any(|(_, pending)| !pending.facts.is_empty())
}

fn record_scope(env: &Environment<'_>, rows: &mut Constraints, value: &SourceValue, first: usize) {
    let mut scope = value.scope.clone();
    // Symbolic update coefficients quantify only inside extraction, not
    // over the concrete architecture yielded by an accepted repair.
    scope.assignments = false;
    scope.quantifiers.retain(|q| {
        q.domain.is_none()
            && !rows.quantifiers[first..]
                .iter()
                .any(|(finite, _)| finite.occurrence == q.occurrence)
            && !env
                .indexes
                .inputs
                .law()
                .program()
                .expressions
                .contains_key(&q.occurrence)
    });
    rows.scope.merge(&scope);
}

fn observed_source(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
    rows: &mut Constraints,
    missing: &mut Pending,
) -> Result<SourceValue, ValidationFailure> {
    let read = || env.scoped_ast(id, vars, base, reading);
    if !rows.capture_reads {
        return read();
    }
    let first = rows.quantifiers.len();
    let result = env.with_finite_domain_reads(&mut rows.quantifiers, read);
    if let Ok(value) = &result
        && !value.condition_failed
        && !value.condition_pending
    {
        record_scope(env, rows, value, first);
    }
    if let Err(ValidationFailure::UnsupportedExpression {
        location: Location::Law { span },
        ..
    }) = &result
        && let Some(&expression) = env.indexes.inputs.law().program().expressions.get(span)
        && matches!(
            env.indexes.inputs.law().exprs()[expression].kind,
            ExprKind::Quant { .. }
        )
    {
        missing.unsupported = Some("rational_change_quantification");
    }
    result
}

fn collect_equations(
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    lexical: &LexicalDependencies,
    reading: &str,
    axes: Axes<'_>,
    rows: &mut Constraints,
    missing: &mut Pending,
) -> Result<(), ValidationFailure> {
    stacker::maybe_grow(256 * 1024, 1024 * 1024, || {
        env.tick()?;
        let base = Scope::default();
        let law = env.indexes.inputs.law();
        let kind = &law.exprs()[id].kind;
        let allow_bounds = rows.inequalities.is_some();
        let diagnose = allow_bounds || missing.selective_missing;
        let parameters = dependency_axes(axes, missing);
        let analysis = DependencyAnalysis {
            env,
            axes: &parameters,
        };
        if allow_bounds
            && matches!(
                kind,
                ExprKind::Quant {
                    kind: archsig_input::law::ast::QuantKind::Forall,
                    split: archsig_input::law::ast::QuantSplit::Fixed {
                        domain: archsig_input::law::ast::QuantDomain::In(_),
                        ..
                    },
                    ..
                }
            )
        {
            let spec = quantifier::spec(law, id, &env.control).inspect_err(|error| {
                if matches!(error, ValidationFailure::UnsupportedExpression { .. }) {
                    missing.unsupported = Some("rational_change_quantification");
                }
            })?;
            let domain = spec.domain.ok_or(internal!("有理量化の元域がない"))?;
            let domain_start = rows.quantifiers.len();
            let (domain_value, members) = env
                .with_finite_domain_reads(&mut rows.quantifiers, || {
                    env.scoped_quantifier_domain(&spec, vars, &base, reading)
                })?;
            let Some(members) = members else {
                let domain_dependency = analysis.read(domain, vars, lexical, reading)?;
                let mut local = env.copy_variables(vars)?;
                local.insert(spec.name.into(), analysis.unknown_member()?);
                let mut dependencies = lexical.clone();
                dependencies.insert(spec.name.into(), domain_dependency.clone());
                let body = analysis.read(spec.body, &local, &dependencies, reading)?;
                domain_dependency.record(missing, Dependence::Fixed);
                missing.awaiting_observation &= body.extractable();
                missing.unsupported = Some("rational_change_quantification");
                return Err(unsupported(env, domain, "有理changeの有限量化域が未確定"));
            };
            usable(env, domain, &domain_value).inspect_err(|_| {
                missing.unsupported = Some("rational_change_quantification");
            })?;
            record_scope(env, rows, &domain_value, domain_start);
            rows.constraint_support
                .extend(domain_value.support.iter().cloned());
            rows.quantifiers
                .insert(domain_start, (spec.descriptor(None, None), members.clone()));
            let mut local = env.copy_variables(vars)?;
            let mut conjuncts = Conjuncts::default();
            for member in members {
                env.tick()?;
                if member.ty() != spec.element {
                    return Err(internal!("有理量化の元要素型が異なる").into());
                }
                let mut v = value(env, member)?;
                v.scope = domain_value.scope.clone();
                v.scalar_scope = Some(domain_value.scope.clone());
                local.insert(spec.name.to_owned(), v);
                let result = collect_equations(
                    env, spec.body, &local, lexical, reading, axes, rows, missing,
                );
                conjuncts.record(result, allow_bounds, missing, &env.control)?;
                if rows.refuted {
                    break;
                }
            }
            return conjuncts.finish(rows, missing);
        }

        let structural = matches!(
            kind,
            ExprKind::Group(_)
                | ExprKind::Let { .. }
                | ExprKind::Binary {
                    op: BinOp::And | BinOp::Implies,
                    ..
                }
        );
        missing.awaiting_observation = false;
        let value = if !allow_bounds || !structural {
            let v = observed_source(env, id, vars, &base, reading, rows, missing)?;
            if !v.condition_pending
                && !v.condition_failed
                && let Some(Scalar::Bool(holds)) = v.known_value
            {
                if !holds {
                    rows.contradiction(axes.len(), env)?;
                    rows.constraint_support.extend(v.support.iter().cloned());
                }
                return Ok(());
            }
            if !allow_bounds {
                if diagnose && (v.condition_pending || v.condition_failed) {
                    analysis
                        .read(id, vars, lexical, reading)?
                        .record(missing, Dependence::Fixed);
                    missing.awaiting_observation &= !v.condition_failed;
                }
                usable(env, id, &v)?;
            }
            Some(v)
        } else {
            None
        };
        match kind {
            ExprKind::Group(body) => {
                collect_equations(env, *body, vars, lexical, reading, axes, rows, missing)
            }
            ExprKind::Let { name, value, body } => {
                let mut local = env.copy_variables(vars)?;
                let v = observed_source(env, *value, vars, &base, reading, rows, missing)?;
                if diagnose && v.condition_pending {
                    let dependency = analysis.read(*value, vars, lexical, reading)?;
                    local.insert(name.name.clone(), v.clone());
                    let mut dependencies = lexical.clone();
                    dependencies.insert(name.name.clone(), dependency.clone());
                    let result = analysis.read(*body, &local, &dependencies, reading)?;
                    dependency.record(missing, Dependence::Affine);
                    missing.awaiting_observation &= result.extractable();
                }
                usable(env, *value, &v)?;
                let known = v.known_value.is_some();
                local.insert(name.name.clone(), v);
                if !diagnose {
                    return collect_equations(
                        env, *body, &local, lexical, reading, axes, rows, missing,
                    );
                }
                let mut dependencies = lexical.clone();
                dependencies.insert(
                    name.name.clone(),
                    if known {
                        Dependency::default()
                    } else {
                        analysis.read(*value, vars, lexical, reading)?
                    },
                );
                collect_equations(
                    env,
                    *body,
                    &local,
                    &dependencies,
                    reading,
                    axes,
                    rows,
                    missing,
                )
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let mut conjuncts = Conjuncts::default();
                let mut remaining = vec![*rhs, *lhs];
                while let Some(body) = remaining.pop() {
                    env.tick()?;
                    if allow_bounds {
                        match &law.exprs()[body].kind {
                            ExprKind::Group(inner) => {
                                remaining.push(*inner);
                                continue;
                            }
                            ExprKind::Binary {
                                op: BinOp::And,
                                lhs,
                                rhs,
                            } => {
                                remaining.extend([*rhs, *lhs]);
                                continue;
                            }
                            _ => {}
                        }
                    }
                    let result =
                        collect_equations(env, body, vars, lexical, reading, axes, rows, missing);
                    conjuncts.record(result, allow_bounds, missing, &env.control)?;
                    if rows.refuted && allow_bounds {
                        break;
                    }
                }
                conjuncts.finish(rows, missing)
            }
            ExprKind::Binary {
                op: BinOp::Implies,
                lhs,
                rhs,
            } if allow_bounds => {
                let first = rows.quantifiers.len();
                let guard = observed_source(env, *lhs, vars, &base, reading, rows, missing)?;
                match guard
                    .known_value
                    .as_ref()
                    .filter(|_| !guard.condition_pending && !guard.condition_failed)
                {
                    Some(Scalar::Bool(true)) => {
                        rows.constraint_support
                            .extend(guard.support.iter().cloned());
                        collect_equations(env, *rhs, vars, lexical, reading, axes, rows, missing)
                    }
                    Some(Scalar::Bool(false)) => Ok(()),
                    _ => {
                        // The complete implication reads the antecedent again.
                        rows.quantifiers.truncate(first);
                        let actual = observed_source(env, id, vars, &base, reading, rows, missing)?;
                        if !actual.condition_failed
                            && !actual.condition_pending
                            && let Some(Scalar::Bool(holds)) = actual.known_value
                        {
                            if !holds {
                                rows.contradiction(axes.len(), env)?;
                                rows.constraint_support
                                    .extend(actual.support.iter().cloned());
                            }
                            return Ok(());
                        }
                        analysis
                            .read(*lhs, vars, lexical, reading)?
                            .record(missing, Dependence::Fixed);
                        missing.unsupported = Some("rational_change_implication");
                        Err(unsupported(env, *lhs, "有理changeの含意の前件が未確定"))
                    }
                }
            }
            ExprKind::Quant { .. } => {
                if diagnose {
                    analysis
                        .read(id, vars, lexical, reading)?
                        .record(missing, Dependence::Fixed);
                }
                missing.unsupported = Some("rational_change_quantification");
                Err(unsupported(
                    env,
                    id,
                    "有理changeで既知の有限In全称量化以外を線形系に展開する算法は未対応",
                ))
            }
            _ => {
                let v = value.ok_or(internal!("有理制約の元値がない"))?;
                if v.condition_pending || v.condition_failed {
                    if diagnose {
                        analysis
                            .read(id, vars, lexical, reading)?
                            .record_constraint(missing);
                        missing.awaiting_observation &= v.condition_pending && !v.condition_failed;
                    }
                    return usable(env, id, &v);
                }
                let ordered = match kind {
                    ExprKind::Binary {
                        op: BinOp::Le,
                        lhs,
                        rhs,
                    } if allow_bounds => Some((*lhs, *rhs)),
                    ExprKind::Binary {
                        op: BinOp::Ge,
                        lhs,
                        rhs,
                    } if allow_bounds => Some((*rhs, *lhs)),
                    _ => None,
                };
                let form = if let Some(predicate) = v.comparison.as_ref().filter(|p| {
                    p.bound_axes.is_empty()
                        && if ordered.is_some() {
                            p.expression == id && matches!(p.op, BinOp::Le | BinOp::Ge)
                        } else {
                            p.op == BinOp::Eq
                        }
                }) {
                    let (left, right) = if predicate.op == BinOp::Ge {
                        (&predicate.right, &predicate.left)
                    } else {
                        (&predicate.left, &predicate.right)
                    };
                    affine::binary(BinOp::Sub, Some(left), Some(right), &env.control)?
                } else {
                    None
                };
                let Some(form) = form else {
                    if diagnose {
                        if matches!(axes, Axes::Parameters(_))
                            && let ExprKind::Binary { op, lhs, rhs } = kind
                            && (*op == BinOp::Eq || ordered.is_some())
                            && law.expr_type(*lhs) == Some(&Type::Q)
                            && law.expr_type(*rhs) == Some(&Type::Q)
                        {
                            let mut combined = analysis.read(*lhs, vars, lexical, reading)?;
                            let right = analysis.read(*rhs, vars, lexical, reading)?;
                            combined.merge(right);
                            combined.record(missing, Dependence::Affine);
                        } else {
                            analysis
                                .read(id, vars, lexical, reading)?
                                .record_equality(missing);
                        }
                    }
                    if change_affine::numeric_condition(env, id, &v)? {
                        missing.unsupported = Some("numeric_change_condition");
                    }
                    return Err(unsupported(
                        env,
                        id,
                        "有理changeの全解は既知係数のアフィン等式・対応する非狭義不等式の連言を要する",
                    ));
                };
                if form.varies_over(&missing.universal, &env.control)? {
                    rows.contradiction(axes.len(), env)?;
                    rows.constraint_support.extend(v.support.iter().cloned());
                    return Ok(());
                }
                if diagnose && let Axes::Parameters(parameters) = axes {
                    missing.awaiting_observation =
                        form.awaiting_rational_observation(parameters, &env.control)?;
                }
                let (constant, coefficients) = coordinates(env, id, &form, axes, missing)?;
                let rhs = constant
                    .as_ref()
                    .map(|c| numeric::unary(archsig_input::law::ast::UnOp::Neg, c, &env.control))
                    .transpose()?;
                rows.constraint_support.extend(v.support.iter().cloned());
                if ordered.is_none() {
                    rows.equalities.push(coefficients);
                    rows.rhs.push(rhs);
                } else {
                    rows.inequalities
                        .as_mut()
                        .ok_or(internal!("有理局所等式に不等式がある"))?
                        .push(Halfspace {
                            coefficients,
                            rhs: rhs.ok_or(internal!("有理不等式の右辺が未確定"))?,
                        });
                }
                Ok(())
            }
        }
    })
}

/// Local declarations use the same rational equation extraction and full fiber.
pub(super) fn parameter_guard_domain(
    env: &Environment<'_>,
    guard: Option<usize>,
    vars: &BTreeMap<String, SourceValue>,
    axes: &[Parameter],
    reading: &str,
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Scalar>, Fiber), ValidationFailure> {
    if axes.iter().any(|axis| axis.kind != NumberType::Q) {
        return Err(internal!("rational guard requires Q parameters").into());
    }
    let mut rows = Constraints::default();
    if let Some(id) = guard {
        missing.expression = Some(id);
        let value = env.scoped_ast(id, vars, &Scope::default(), reading)?;
        missing.support.extend(value.support.into_vec());
        missing.scope.merge(&value.scope);
        equations(
            env,
            id,
            vars,
            reading,
            Axes::Parameters(axes),
            &mut rows,
            missing,
        )?;
    }
    let rhs = rows
        .rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(internal!("rational guard constant is undetermined"))?;
    let fiber = field_fiber::solve(&Type::Q, &rows.equalities, axes.len(), &rhs, &env.control)?;
    Ok((rows.equalities, rhs, fiber))
}

pub(in crate::observed) fn compute(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    with_missing(env, missing, |missing| {
        compute_inner(env, change, subjects, requirements, false, missing)
    })
}
pub(in crate::observed) fn compute_with_bounds(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    with_missing(env, missing, |missing| {
        compute_inner(env, change, subjects, requirements, true, missing)
    })
}

fn compute_inner(
    env: &Environment<'_>,
    change: &Declaration,
    subjects: &[Scalar],
    requirements: &[(String, Vec<(String, Scalar)>)],
    allow_bounds: bool,
    missing: &mut Pending,
) -> Result<Linear, ValidationFailure> {
    missing.coefficient_type = Some(Type::Q);
    missing.selective_missing = allow_bounds;
    let Signature::Change {
        params,
        guard,
        body,
    } = &change.signature
    else {
        return Err(internal!("有理候補がchangeでない").into());
    };
    if params.is_empty() || params[1..].iter().any(|p| p.ty != Type::Q) {
        return Err(unsupported(
            env,
            *body,
            "有理changeの混合parameter型は未実装",
        ));
    }
    let mut axes = vec![];
    for (i, _) in subjects.iter().enumerate() {
        for p in &params[1..] {
            env.tick()?;
            axes.push(Parameter {
                binder: p.span,
                name: p.name.clone(),
                context: crate::observed::call::Context {
                    instance: Some(i),
                    ..Default::default()
                },
                kind: NumberType::Q,
            });
        }
    }
    let mut updates = BTreeMap::<Fact, (Form, Scalar, Vec<Scalar>)>::new();
    let mut guards = Constraints {
        capture_reads: allow_bounds,
        ..Constraints::default()
    };
    let update_result = (|| {
        for (i, subject) in subjects.iter().enumerate() {
            let mut vars = BTreeMap::from([(params[0].name.clone(), value(env, subject.clone())?)]);
            for (p, axis) in params[1..]
                .iter()
                .zip(&axes[i * (params.len() - 1)..(i + 1) * (params.len() - 1)])
            {
                env.tick()?;
                let mut v = value(env, numeric::zero(&Type::Q, &env.control)?)?;
                v.known_value = None;
                v.scalar_scope = None;
                v.affine = affine::parameter(&Type::Q, axis, &env.control)?.map(Box::new);
                vars.insert(p.name.clone(), v);
            }
            missing.bindings = vec![(params[0].name.clone(), subject.clone())];
            missing.parameters = params[1..]
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            if let Some(guard) = guard {
                missing.expression = Some(*guard);
                equations(
                    env,
                    *guard,
                    &vars,
                    &change.reading,
                    Axes::Parameters(&axes),
                    &mut guards,
                    missing,
                )?;
            }
            missing.expression = Some(*body);
            let mut current = *body;
            let mut lexical = LexicalDependencies::new();
            let analysis = DependencyAnalysis { env, axes: &axes };
            loop {
                env.tick()?;
                match &env.indexes.inputs.law().exprs()[current].kind {
                    ExprKind::Group(inner) => current = *inner,
                    ExprKind::Let { name, value, body } => {
                        let v = observed_source(
                            env,
                            *value,
                            &vars,
                            &Scope::default(),
                            &change.reading,
                            &mut guards,
                            missing,
                        )?;
                        if allow_bounds {
                            let dependency = if v.known_value.is_some()
                                && !v.condition_pending
                                && !v.condition_failed
                            {
                                Dependency::default()
                            } else {
                                analysis.read(*value, &vars, &lexical, &change.reading)?
                            };
                            if v.condition_pending || v.condition_failed {
                                dependency.record(missing, Dependence::Fixed);
                            } else {
                                lexical.insert(name.name.clone(), dependency);
                            }
                        }
                        usable(env, *value, &v)?;
                        vars.insert(name.name.clone(), v);
                        current = *body;
                    }
                    ExprKind::If {
                        cond,
                        then_branch,
                        else_branch,
                    } => {
                        let v = observed_source(
                            env,
                            *cond,
                            &vars,
                            &Scope::default(),
                            &change.reading,
                            &mut guards,
                            missing,
                        )?;
                        if allow_bounds
                            && (v.known_value.is_none()
                                || v.condition_pending
                                || v.condition_failed)
                        {
                            analysis
                                .read(*cond, &vars, &lexical, &change.reading)?
                                .record(missing, Dependence::Fixed);
                        }
                        usable(env, *cond, &v)?;
                        if allow_bounds {
                            guards.constraint_support.extend(v.support.iter().cloned());
                        }
                        current = match v.known_value {
                            Some(Scalar::Bool(true)) => *then_branch,
                            Some(Scalar::Bool(false)) => *else_branch,
                            _ => {
                                missing.expression = Some(*cond);
                                if change_affine::numeric_condition(env, *cond, &v)? {
                                    missing.unsupported = Some("numeric_change_condition");
                                }
                                return Err(unsupported(
                                    env,
                                    *cond,
                                    "有理changeの未確定分岐は未実装",
                                ));
                            }
                        };
                    }
                    ExprKind::With {
                        base,
                        updates: fields,
                    } => {
                        let target = observed_source(
                            env,
                            *base,
                            &vars,
                            &Scope::default(),
                            &change.reading,
                            &mut guards,
                            missing,
                        )?;
                        if allow_bounds
                            && (target.known_value.is_none()
                                || target.condition_pending
                                || target.condition_failed)
                        {
                            analysis
                                .read(*base, &vars, &lexical, &change.reading)?
                                .record(missing, Dependence::Fixed);
                        }
                        usable(env, *base, &target)?;
                        if allow_bounds {
                            guards
                                .constraint_support
                                .extend(target.support.iter().cloned());
                        }
                        let Some(Scalar::Subject {
                            snapshot,
                            subject,
                            entity,
                        }) = &target.known_value
                        else {
                            return Err(unsupported(env, *base, "有理changeの更新先が未確定"));
                        };
                        for (field, id) in fields {
                            let v = observed_source(
                                env,
                                *id,
                                &vars,
                                &Scope::default(),
                                &change.reading,
                                &mut guards,
                                missing,
                            )?;
                            if allow_bounds
                                && (v.affine.is_none() || v.condition_pending || v.condition_failed)
                            {
                                analysis
                                    .read(*id, &vars, &lexical, &change.reading)?
                                    .record(missing, Dependence::Affine);
                            }
                            usable(env, *id, &v)?;
                            if allow_bounds {
                                guards.constraint_support.extend(v.support.iter().cloned());
                            }
                            let form = v.affine.ok_or_else(|| {
                                if matches!(env.indexes.inputs.law().expr_type(*id), Some(Type::Q))
                                {
                                    missing.unsupported = Some("nonlinear_numeric_change");
                                }
                                unsupported(env, *id, "有理changeの更新式がQアフィンでない")
                            })?;
                            let position = Fact::from(archsig_input::archmap::FactData {
                                snapshot: snapshot.clone(),
                                subject: subject.clone(),
                                field: Some(env.input_name(&format!("{entity}.{}", field.name))?),
                                atom: None,
                            });
                            if let Some((prior, _, _)) = updates.get(&position) {
                                if prior != form.as_ref() {
                                    return Err(unsupported(
                                        env,
                                        *id,
                                        "有理changeの同時更新衝突のfiberは未実装",
                                    ));
                                }
                            } else {
                                if allow_bounds {
                                    missing.awaiting_observation =
                                        form.awaiting_rational_observation(&axes, &env.control)?;
                                }
                                let (constant, row) =
                                    coordinates(env, *id, &form, Axes::Parameters(&axes), missing)?;
                                let constant =
                                    constant.ok_or(internal!("有理作用の固定項が未確定"))?;
                                updates.insert(position, (*form, constant, row));
                            }
                        }
                        break;
                    }
                    _ => return Err(internal!("有理changeのwithがない").into()),
                }
            }
        }
        Ok(())
    })();
    if let Err(error) = update_result {
        missing.scope.merge(&guards.scope);
        missing.finite_domains = guards.quantifiers;
        return Err(error);
    }
    let mut slots = vec![];
    let mut action = vec![];
    let mut offset = vec![];
    let mut valuation = BTreeMap::new();
    for (slot, (form, constant, row)) in updates {
        env.tick()?;
        slots.push(slot.clone());
        action.push(row);
        offset.push(constant);
        valuation.insert(slot, form);
    }

    let mut guard_matrix = guards.equalities;
    let mut guard_rhs = guards
        .rhs
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(internal!("有理guardの固定項が未確定"))?;
    let guard_fiber = field_fiber::solve(
        &Type::Q,
        &guard_matrix,
        axes.len(),
        &guard_rhs,
        &env.control,
    )?;
    let candidates_empty = guard_fiber.particular.is_none();
    let mut updated = Environment::with_primitive_valuation(
        env.indexes.inputs,
        &env.fixed_values(),
        &env.control,
    )?;
    updated.indexes.object = env.object_domain();
    updated.indexes.affine_valuation = valuation;
    let result = if candidates_empty {
        Ok(Constraints::default())
    } else {
        with_missing(&updated, missing, |missing| {
            requirement_equations(
                &updated,
                Axes::Parameters(&axes),
                requirements,
                allow_bounds,
                missing,
            )
        })
    };
    let mut rows = match result {
        Ok(rows) => rows,
        Err(error) => {
            missing.scope.merge(&guards.scope);
            guards.quantifiers.append(&mut missing.finite_domains);
            missing.finite_domains = guards.quantifiers;
            return Err(error);
        }
    };
    guards.quantifiers.append(&mut rows.quantifiers);
    rows.quantifiers = guards.quantifiers;
    guards.scope.merge(&rows.scope);
    rows.scope = guards.scope;
    rows.constraint_support
        .append(&mut guards.constraint_support);
    guard_matrix.extend(rows.equalities);
    guard_rhs.extend(
        rows.rhs
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(internal!("有理要求の固定項が未確定"))?,
    );
    let mut pending_failure = rows.pending_failure.take();
    let solutions = if requirements.is_empty() {
        Solutions::Affine(guard_fiber.clone())
    } else if let Some(inequalities) = rows.inequalities
        && !inequalities.is_empty()
    {
        let original =
            field_polyhedron::halfspaces(&guard_matrix, &guard_rhs, &inequalities, &env.control)?;
        let outcome = if let Some(error) = pending_failure.take() {
            let Some(outcome) =
                field_polyhedron::contradiction(&original, axes.len(), &env.control)?
            else {
                missing.scope.merge(&rows.scope);
                missing.finite_domains = rows.quantifiers;
                return Err(error);
            };
            rows.scope.completions |= needs_observation(missing);
            missing.facts.clear();
            missing.additional.clear();
            missing.unsupported = None;
            outcome
        } else {
            field_polyhedron::solve(&original, axes.len(), &env.control)?
        };
        field_polyhedron::verify(&original, axes.len(), &outcome, &env.control)?;
        Solutions::Polyhedron(Polyhedron {
            inequalities,
            outcome,
        })
    } else {
        Solutions::Affine(field_fiber::solve(
            &Type::Q,
            &guard_matrix,
            axes.len(),
            &guard_rhs,
            &env.control,
        )?)
    };
    if let Some(error) = pending_failure {
        let empty = match &solutions {
            Solutions::Affine(fiber) => fiber.particular.is_none(),
            Solutions::Polyhedron(polyhedron) => matches!(polyhedron.outcome, Outcome::Empty(_)),
        };
        if !empty {
            missing.scope.merge(&rows.scope);
            missing.finite_domains = rows.quantifiers;
            return Err(error);
        }
        rows.scope.completions |= needs_observation(missing);
        missing.facts.clear();
        missing.additional.clear();
        missing.unsupported = None;
    }
    Ok(Linear {
        parameter_count: axes.len(),
        axes,
        guard_fiber,
        slots,
        action,
        offset,
        equations: guard_matrix,
        rhs: guard_rhs,
        quantifiers: rows.quantifiers,
        constraint_support: rows.constraint_support,
        scope: rows.scope,
        solutions,
    })
}
pub(in crate::observed) fn state_equations(
    env: &Environment<'_>,
    slots: &[Fact],
    requirements: &[(String, Vec<(String, Scalar)>)],
    missing: &mut Pending,
) -> Result<(Matrix, Vec<Option<Scalar>>), ValidationFailure> {
    let mut state = Environment::with_primitive_valuation(
        env.indexes.inputs,
        &env.fixed_values(),
        &env.control,
    )?;
    state.indexes.object = env.object_domain();
    for slot in slots {
        env.tick()?;
        if env
            .indexes
            .field(
                &env.state,
                &slot.snapshot,
                &slot.subject,
                slot.field
                    .as_ref()
                    .ok_or(internal!("自由位置にfieldがない"))?,
            )?
            .ty
            .erase()
            != Type::Q
        {
            return Err(internal!("有理局所状態の自由位置がQでない").into());
        }
        state.indexes.affine_valuation.insert(
            slot.clone(),
            Form::typed_state(&Type::Q, slot, &env.control)?,
        );
    }
    with_missing(&state, missing, |missing| {
        let rows = requirement_equations(&state, Axes::State(slots), requirements, false, missing)?;
        Ok((rows.equalities, rows.rhs))
    })
}
fn requirement_equations(
    env: &Environment<'_>,
    axes: Axes<'_>,
    requirements: &[(String, Vec<(String, Scalar)>)],
    allow_bounds: bool,
    missing: &mut Pending,
) -> Result<Constraints, ValidationFailure> {
    let _value_read = allow_bounds.then(|| env.state.value_read.scoped(true));
    missing.selective_missing = allow_bounds;
    let mut rows = Constraints {
        inequalities: allow_bounds.then(Vec::new),
        capture_reads: allow_bounds,
        ..Default::default()
    };
    let mut conjuncts = Conjuncts::default();
    for (name, bindings) in requirements {
        env.tick()?;
        let outcome = (|| {
            let law = &env.indexes.inputs.law().declarations()[name];
            let Signature::Law {
                body,
                guard,
                params: law_params,
                ..
            } = &law.signature
            else {
                return Err(internal!("有理候補の要求がLawでない").into());
            };
            let mut checked = BTreeMap::new();
            let mut checks = owned_call::Checks::default();
            for (name, v) in bindings {
                let p = law_params
                    .iter()
                    .find(|p| p.name == *name)
                    .ok_or(internal!("有理Lawの束縛名が異なる"))?;
                env.owned_call_value_check(
                    &p.ty,
                    &crate::observed::term::affine::Value::Known(v.clone()),
                    &checked,
                    &law.reading,
                    law.span,
                    &mut checks,
                )?;
                checked.insert(name.as_str(), Some(v));
            }
            if checks.failure.is_some() {
                return Ok(());
            }
            if checks.blocked {
                missing.expression = Some(*body);
                missing.bindings = bindings.clone();
                missing.facts.extend(checks.missing);
                missing.awaiting_observation = !missing.facts.is_empty();
                return Err(unsupported(env, *body, "有理Lawの適用条件が未確定"));
            }
            if allow_bounds {
                rows.constraint_support.extend(checks.support);
                rows.scope.merge(&checks.scope);
            }
            let (vars, universal) = change_affine::law_variables(env, law_params, bindings)?;
            missing.universal = universal;
            if let Some(guard) = guard {
                missing.expression = Some(*guard);
                missing.bindings = bindings.clone();
                missing.parameters = law_params
                    .iter()
                    .filter(|p| !bindings.iter().any(|(name, _)| *name == p.name))
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect();
                let v = observed_source(
                    env,
                    *guard,
                    &vars,
                    &Scope::default(),
                    &law.reading,
                    &mut rows,
                    missing,
                )?;
                if allow_bounds
                    && (v.known_value.is_none() || v.condition_pending || v.condition_failed)
                {
                    let parameters = dependency_axes(axes, missing);
                    DependencyAnalysis {
                        env,
                        axes: &parameters,
                    }
                    .read(*guard, &vars, &LexicalDependencies::new(), &law.reading)?
                    .record(missing, Dependence::Fixed);
                    missing.awaiting_observation &= !v.condition_failed;
                }
                usable(env, *guard, &v)?;
                match v.known_value {
                    Some(Scalar::Bool(false)) => return Ok(()),
                    Some(Scalar::Bool(true)) => {
                        rows.constraint_support.extend(v.support.iter().cloned());
                    }
                    _ => {
                        if change_affine::numeric_condition(env, *guard, &v)? {
                            missing.unsupported = Some("numeric_change_condition");
                        }
                        return Err(unsupported(
                            env,
                            *guard,
                            "有理候補で未確定のLaw guardの全解は未実装",
                        ));
                    }
                }
            }
            missing.awaiting_observation = false;
            missing.expression = Some(*body);
            missing.bindings = bindings.clone();
            missing.parameters = law_params
                .iter()
                .filter(|p| !bindings.iter().any(|(n, _)| *n == p.name))
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect();
            equations(env, *body, &vars, &law.reading, axes, &mut rows, missing)
        })();
        conjuncts.record(outcome, allow_bounds, missing, &env.control)?;
        if allow_bounds && rows.refuted {
            break;
        }
    }
    if let Err(error) = conjuncts.finish(&mut rows, missing) {
        if !allow_bounds {
            return Err(error);
        }
        rows.pending_failure = Some(error);
    }
    Ok(rows)
}
