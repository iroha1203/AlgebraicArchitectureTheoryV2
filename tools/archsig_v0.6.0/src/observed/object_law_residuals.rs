//! 元数値等式の差をscalar成分で読み、同じ完全patternの全代入で照合する。
use super::{
    numeric,
    numeric_transport::NumericTransportValue,
    object_evaluate::ObjectEvaluationOutcome,
    object_law_compatibility::{
        ObjectLawCompatibility, ObjectLawCompatibilityFailure, object_law_compatibility,
    },
    object_law_transport::{LawBooleanReading, native_case_reading},
    result::{NodeRef, ObservedEvaluation, Payload, Scalar, ValidationFailure},
    value_transport::FiniteTransportValue,
};
use crate::{
    construction::ConstructionFailure,
    law::{
        ast::{BinOp, ExprKind},
        model::Signature,
    },
    observed::object_evaluation_table::ObjectEvaluationPosition,
    types::Type,
};
use crate::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
};
use std::sync::Arc;
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(s.into())
}
fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawResiduals)
        .map_err(Into::into)
}
fn invalid(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => s.into(),
        f => bad(&format!("数値Lawの元値: {f:?}")),
    }
}
pub(in crate::observed) fn predicate_call(inputs: &CheckedInputs, id: usize) -> Option<(&[crate::law::model::Param], usize, &[usize])> {
    let ExprKind::Call { callee, args } = &inputs.law().exprs[id].kind else { return None };
    let mut callee = *callee;
    while let ExprKind::Group(child) = inputs.law().exprs[callee].kind { callee = child; }
    let span = inputs.law().exprs[callee].span;
    let target = inputs.law().infos.iter().find_map(|info| info.references.iter().find_map(|(at,name)| (*at == span).then_some(name)))?;
    let Signature::View { params, body, .. } = &inputs.law().declarations.get(target)?.signature else { return None };
    if params.len() != args.len() || params.iter().any(|p| matches!(p.ty, Type::Owned(..))) || inputs.law().expr_type(*body) != Some(&Type::Bool) { return None; }
    Some((params, *body, args))
}
pub(in crate::observed) fn predicate_equation(inputs: &CheckedInputs, mut id: usize, c: &mut Control) -> Result<Option<usize>, ConstructionFailure> {
    loop {
        tick(c)?;
        match &inputs.law().exprs[id].kind {
            ExprKind::Group(child) | ExprKind::Let { body: child, .. } => id = *child,
            ExprKind::Call { .. } => { let Some((_, body, _)) = predicate_call(inputs,id) else { return Ok(None) }; id = body; }
            ExprKind::Match { scrutinee, arms } => { let Some(body) = binding_match_body(inputs,*scrutinee,arms,c)? else { return Ok(None) }; id = body; }
            ExprKind::Binary { op: BinOp::Eq, .. } => return Ok(Some(id)),
            _ => return Ok(None),
        }
    }
}
/// 数値等式以外も、元bodyと型付き通常条件をbaseに保持する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawNumericShape {
    Equality {
        body: usize,
        equality: usize,
        left: usize,
        right: usize,
        ty: Type,
        explicit_guard: bool,
    },
    Conjunction {
        terms: Vec<LawNumericShape>,
        ty: Type,
        explicit_guard: bool,
    },
    Unsupported {
        body: usize,
        ty: Type,
        explicit_guard: bool,
    },
}
impl LawNumericShape {
    pub(super) fn ty(&self) -> &Type {
        match self {
            Self::Equality { ty, .. } | Self::Conjunction { ty, .. } | Self::Unsupported { ty, .. } => ty,
        }
    }
    pub(super) fn component<'a>(&'a self, path: &'a [usize]) -> Option<(&'a Self, &'a [usize])> {
        match self {
            Self::Conjunction { terms, .. } => {
                let (&index, rest) = path.split_first()?;
                terms.get(index).map(|term| (term, rest))
            }
            _ => Some((self, path)),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawResidualComponent {
    pub path: Vec<usize>,
    pub ty: Type,
    pub left: Option<NumericTransportValue>,
    pub right: Option<NumericTransportValue>,
    pub epsilon: Option<NumericTransportValue>,
    pub residual: Option<NumericTransportValue>,
}
/// 参照はevaluation()の元DAG内のnode位置。Noneは未評価であり零ではない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawResidualCase {
    pub evaluation: Option<usize>,
    pub body_evaluation: Option<usize>,
    pub operand_evaluations: Vec<usize>,
    pub operand_values: Vec<Option<usize>>,
    pub epsilon_producer: Option<usize>,
    pub reading: LawBooleanReading,
    pub components: Vec<LawResidualComponent>,
    pub complete: bool,
    /// 各等式の元operandを保持し、連言のBool値を数値残差へ流用しない。
    pub conjuncts: Vec<LawResidualCase>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawResidualRow {
    pub cases: Vec<LawResidualCase>,
    pub complete: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawResidualEvaluation {
    pub position: ObjectEvaluationPosition,
    pub shape: LawNumericShape,
    pub rows: Vec<LawResidualRow>,
    /// parameter付き対象外/条件付き所属の読取り。架空の引数行は作らない。
    pub uniform: Option<LawResidualRow>,
    pub complete: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawResidualOutcome {
    Compatible,
    Refuted { component: Vec<usize> },
    ArgumentsDiffer,
    Undetermined,
    Unsupported,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawResidualPoint {
    pub arguments: Vec<FiniteTransportValue>,
    pub source_row: Option<usize>,
    pub target_row: Option<usize>,
    /// 各scalar成分の結論。零成分を別成分の不一致へ混ぜない。
    pub components: Vec<LawResidualOutcome>,
    pub outcome: Option<LawResidualOutcome>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawResidualComparison {
    pub source_object: usize,
    pub target_object: usize,
    pub instance: usize,
    pub points: Vec<LawResidualPoint>,
    pub outcome: Option<LawResidualOutcome>,
}
#[derive(Debug)]
pub struct ObjectLawResiduals {
    base: ObjectLawCompatibility,
    evaluations: Vec<LawResidualEvaluation>,
    comparisons: Vec<LawResidualComparison>,
    complete: bool,
    outcome: Option<LawResidualOutcome>,
}
impl ObjectLawResiduals {
    pub fn base(&self) -> &ObjectLawCompatibility {
        &self.base
    }
    pub fn evaluations(&self) -> &[LawResidualEvaluation] {
        &self.evaluations
    }
    pub fn comparisons(&self) -> &[LawResidualComparison] {
        &self.comparisons
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn outcome(&self) -> Option<&LawResidualOutcome> {
        self.outcome.as_ref()
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectLawResidualsFailure> {
        self.base
            .recheck(Arc::clone(&inputs), c)
            .map_err(ObjectLawResidualsFailure::Original)?;
        let root = self.base.readings().construction().root();
        let expected = object_law_residuals(
            inputs,
            self.base.readings().construction().reading(),
            &root.snapshot,
            &root.subject,
            c,
        )?;
        let checked = same(self, &expected, c);
        match checked {
            Ok(true) => Ok(()),
            other => Err(ObjectLawResidualsFailure::Reading {
                cause: other
                    .err()
                    .unwrap_or_else(|| bad("数値Law残差が現在入力の元評価・全成分・比較と違う")),
                partial: Box::new(expected),
            }),
        }
    }
}
#[derive(Debug)]
pub enum ObjectLawResidualsFailure {
    Original(ObjectLawCompatibilityFailure),
    Reading {
        cause: ConstructionFailure,
        partial: Box<ObjectLawResiduals>,
    },
}
impl ObjectLawResidualsFailure {
    pub fn partial(&self) -> Option<&ObjectLawResiduals> {
        match self {
            Self::Reading { partial, .. } => Some(partial),
            _ => None,
        }
    }
}
pub(super) fn binding_match_body(
    inputs: &CheckedInputs,
    scrutinee: usize,
    arms: &[crate::law::ast::Arm],
    c: &mut Control,
) -> Result<Option<usize>, ConstructionFailure> {
    let [arm] = arms else { return Ok(None) };
    match &arm.pattern {
        crate::law::ast::Pattern::Wild(_) => Ok(Some(arm.body)),
        crate::law::ast::Pattern::Name(_) => {
            let ty = inputs
                .law()
                .expr_type(scrutinee)
                .ok_or_else(|| bad("match元型がない"))?;
            let bindings =
                super::data::binders(&arm.pattern, ty, inputs.law(), c).map_err(invalid)?;
            Ok((bindings.len() == 1 && bindings[0].path.is_empty()).then_some(arm.body))
        }
        _ => Ok(None),
    }
}
fn numeric_terms(
    inputs: &CheckedInputs, body: usize, expression: usize, explicit_guard: bool,
    terms: &mut Vec<LawNumericShape>, c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        tick(c)?;
        match &inputs.law().exprs[expression].kind {
            ExprKind::Group(child) | ExprKind::Let { body: child, .. } =>
                numeric_terms(inputs, body, *child, explicit_guard, terms, c),
            ExprKind::Match { scrutinee, arms } => {
                let Some(child) = binding_match_body(inputs, *scrutinee, arms, c)? else { return Ok(false) };
                numeric_terms(inputs, body, child, explicit_guard, terms, c)
            }
            ExprKind::Binary { op: BinOp::And, lhs, rhs } => {
                Ok(numeric_terms(inputs, body, *lhs, explicit_guard, terms, c)?
                    && numeric_terms(inputs, body, *rhs, explicit_guard, terms, c)?)
            }
            ExprKind::Binary { op: BinOp::Eq, lhs, rhs } => {
                let ty = inputs.law().expr_type(*lhs).ok_or_else(|| bad("元等式の左右型がない"))?;
                if !numeric::is_numeric_type(ty, c).map_err(invalid)? { return Ok(false) }
                terms.push(LawNumericShape::Equality {
                    body, equality: expression, left: *lhs, right: *rhs,
                    ty: ty.clone(), explicit_guard,
                });
                Ok(true)
            }
            _ => Ok(false),
        }
    })
}
fn shape(
    inputs: &CheckedInputs, name: &str, c: &mut Control,
) -> Result<LawNumericShape, ConstructionFailure> {
    tick(c)?;
    let Signature::Law { body, guard, .. } = inputs.law().declarations
        .get(name).ok_or_else(|| bad("元Law宣言がない"))?.signature else {
        return Err(bad("元Law署名がない"));
    };
    let mut terms = vec![];
    if numeric_terms(inputs, body, body, guard.is_some(), &mut terms, c)? {
        if terms.len() == 1 { return Ok(terms.remove(0)) }
        let ty = Type::Tuple(terms.iter().map(|term| term.ty().clone()).collect());
        return Ok(LawNumericShape::Conjunction { terms, ty, explicit_guard: guard.is_some() });
    }
    Ok(LawNumericShape::Unsupported {
        body, explicit_guard: guard.is_some(),
        ty: inputs.law().expr_type(body).ok_or_else(|| bad("元body型がない"))?.clone(),
    })
}
/// 元の連言内で、指定された等式を含む側を選ぶ。
pub(super) fn conjunction_child(inputs: &CheckedInputs, expression: usize, equality: usize) -> Option<(usize, usize)> {
    let ExprKind::Binary { op: BinOp::And, lhs, rhs } = inputs.law().exprs[expression].kind else { return None };
    let at = inputs.law().exprs[equality].span;
    [lhs, rhs].into_iter().enumerate().find_map(|(index, child)| {
        let span = inputs.law().exprs[child].span;
        (span.0 <= at.0 && at.1 <= span.1).then_some((child, index))
    })
}
fn graph(e: &super::object_evaluate::ObjectEvaluation) -> Option<&ObservedEvaluation> {
    match e.outcome() {
        ObjectEvaluationOutcome::Evaluated(g) => Some(g),
        _ => None,
    }
}
fn eval_parts(
    g: &ObservedEvaluation,
    r: NodeRef,
) -> Result<&[super::result::Part], ConstructionFailure> {
    match g.nodes.get(r.0).and_then(|n| n.payload.as_ref()) {
        Some(Payload::Evaluation { parts, .. }) => Ok(parts),
        _ => Err(bad("元数値Lawの評価nodeがない")),
    }
}
fn flatten(
    g: &ObservedEvaluation,
    r: NodeRef,
    out: &mut Vec<NodeRef>,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        tick(c)?;
        let Some(Payload::Evaluation {
            expression, parts, ..
        }) = g.nodes.get(r.0).and_then(|n| n.payload.as_ref())
        else {
            return Err(bad("元Law case評価がない"));
        };
        if matches!(
            g.nodes.get(expression.0).and_then(|n| n.payload.as_ref()),
            Some(Payload::CompletionSeed { .. })
        ) {
            let [part] = parts.as_slice() else {
                return Err(bad("元Law補完族が不正"));
            };
            if part.children.is_empty() {
                return Err(bad("空の補完族を残差へ使わない"));
            }
            for &child in &part.children {
                if child.0 >= r.0 {
                    return Err(bad("元caseが導出順でない"));
                }
                flatten(g, child, out, c)?;
            }
        } else {
            out.push(r);
        }
        Ok(())
    })
}
fn scalar(
    g: &ObservedEvaluation,
    mut r: Option<NodeRef>,
    c: &mut Control,
) -> Result<Option<Scalar>, ConstructionFailure> {
    while let Some(at) = r {
        tick(c)?;
        match g.nodes.get(at.0).and_then(|n| n.payload.as_ref()) {
            Some(Payload::Scalar(s)) => {
                numeric::check(s, c).map_err(invalid)?;
                return Ok(Some(s.clone()));
            }
            Some(Payload::Evaluation { value, .. }) => {
                if value.is_some_and(|v| v.0 >= at.0) {
                    return Err(bad("元数値producerが導出順でない"));
                }
                r = *value;
            }
            _ => return Err(bad("元数値producerがScalar/Evaluationでない")),
        }
    }
    Ok(None)
}
/// 同じ元Evaluatorの補完前のoperandからだけ実εを読む。caseの合意値で代用しない。
pub(in crate::observed) fn observed_epsilon(
    inputs: &CheckedInputs,
    source: &super::object_law_compatibility::LawReadingEvaluation,
    shape: &LawNumericShape,
    row: Option<usize>,
    component: &[usize],
    c: &mut Control,
) -> Result<Option<NumericTransportValue>, ConstructionFailure> {
    if row.is_none() && component.is_empty()
        && let Some((_, _, value)) = super::object_law_transport::constant_numeric_family(source.evaluation(), c)? {
        return Ok(Some(NumericTransportValue::observed(value)));
    }
    let refs = source
        .family()
        .observed_row_evaluations(source.evaluation(), row, c)?;
    let [reference] = refs.as_slice() else {
        return if refs.is_empty() {
            Ok(None)
        } else {
            Err(bad("元観測のLaw行が一意でない"))
        };
    };
    let explicit = match shape {
        LawNumericShape::Equality { explicit_guard, .. }
        | LawNumericShape::Conjunction { explicit_guard, .. }
        | LawNumericShape::Unsupported { explicit_guard, .. } => *explicit_guard,
    };
    let reading = native_case_reading(source.evaluation(), *reference, explicit, c)?;
    let mut value = LawResidualCase {
        evaluation: Some(reference.0),
        body_evaluation: None,
        operand_evaluations: vec![],
        operand_values: vec![],
        epsilon_producer: None,
        reading,
        components: vec![],
        conjuncts: vec![],
        complete: false,
    };
    read_case(&mut value, shape, inputs, graph(source.evaluation()), c)?;
    Ok(value
        .components
        .iter()
        .find(|v| v.path == component)
        .and_then(|v| v.epsilon.clone()))
}
fn leaves(
    ty: &Type,
    path: &mut Vec<usize>,
    out: &mut Vec<(Vec<usize>, Type)>,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        tick(c)?;
        match ty {
            Type::Tuple(items) => {
                for (i, t) in items.iter().enumerate() {
                    path.push(i);
                    leaves(t, path, out, c)?;
                    path.pop();
                }
            }
            Type::Z | Type::Q | Type::Fp(_) => out.push((path.clone(), ty.clone())),
            _ => return Err(bad("元数値等式に非数値leafがある")),
        }
        Ok(())
    })
}
fn component(
    value: Option<&Scalar>,
    path: &[usize],
    ty: &Type,
    c: &mut Control,
) -> Result<Option<NumericTransportValue>, ConstructionFailure> {
    let Some(mut v) = value else { return Ok(None) };
    for &i in path {
        tick(c)?;
        let Scalar::Tuple(items) = v else {
            return Err(bad("元数値積の成分型が違う"));
        };
        v = items.get(i).ok_or_else(|| bad("元数値積の成分がない"))?;
    }
    if &v.ty() != ty {
        return Err(bad("元数値成分の環が違う"));
    }
    Ok(Some(NumericTransportValue::observed(v.clone())))
}
fn read_case(
    r: &mut LawResidualCase,
    shape: &LawNumericShape,
    inputs: &CheckedInputs,
    g: Option<&ObservedEvaluation>,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    tick(c)?;
    if let LawNumericShape::Conjunction { terms, .. } = shape {
        for (index, term) in terms.iter().enumerate() {
            tick(c)?;
            let mut case = LawResidualCase {
                evaluation: r.evaluation, body_evaluation: None,
                operand_evaluations: vec![], operand_values: vec![], epsilon_producer: None,
                reading: r.reading.clone(), components: vec![], complete: false, conjuncts: vec![],
            };
            read_case(&mut case, term, inputs, g, c)?;
            for component in &case.components {
                let mut component = component.clone();
                component.path.insert(0, index);
                r.components.push(component);
            }
            r.conjuncts.push(case);
        }
        r.complete = true;
        return Ok(());
    }
    let LawNumericShape::Equality {
        body,
        equality,
        ty,
        explicit_guard,
        ..
    } = shape
    else {
        r.complete = true;
        return Ok(());
    };
    let mut lhs = None;
    let mut rhs = None;
    let mut epsilon = None;
    if let (Some(g), Some(reference)) = (g, r.evaluation) {
        let mut at = Some(NodeRef(reference));
        if *explicit_guard {
            let parts = eval_parts(g, at.ok_or_else(|| bad("元Law評価がない"))?)?;
            let part = parts.get(1).ok_or_else(|| bad("元Law body partがない"))?;
            if let Some(&child) = part.children.first() {
                at = Some(child);
            } else {
                // 元評価がguard偽でbodyを実行しなかった場合だけ読取りを省く。
                if r.reading.application().value() != Some(false) {
                    return Err(bad("元Law body評価がない"));
                }
                at = None;
            }
        }
        if let Some(mut at) = at {
            let mut expression = *body;
            let mut evaluated = true;
            while expression != *equality {
                tick(c)?;
                let (child, index) = match &inputs.law().exprs[expression].kind {
                    ExprKind::Group(child) => (*child, 0),
                    ExprKind::Let { body: child, .. } => (*child, 1),
                    ExprKind::Match { scrutinee, arms } => (
                        binding_match_body(inputs, *scrutinee, arms, c)?
                            .ok_or_else(|| bad("元数値等式のmatchが全体束縛でない"))?,
                        1,
                    ),
                    ExprKind::Binary { op: BinOp::And, .. } =>
                        conjunction_child(inputs, expression, *equality)
                            .ok_or_else(|| bad("元連言に等式がない"))?,
                    _ => return Err(bad("元数値等式の外側導出が違う")),
                };
                let p = eval_parts(g, at)?
                    .first()
                    .ok_or_else(|| bad("元数値等式の外側partがない"))?;
                if let Some(&next) = p.children.get(index) {
                    at = next;
                } else if matches!(inputs.law().exprs[expression].kind, ExprKind::Match { .. })
                    && p.children.len() == 1
                    && p.value.is_none()
                {
                    // 未観測scrutineeでは元Evaluatorがbodyを実行しない。式・支持を残し値は作らない。
                    evaluated = false;
                    break;
                } else {
                    return Err(bad("元数値等式の外側評価の子がない"));
                }
                expression = child;
            }
            if evaluated {
                r.body_evaluation = Some(at.0);
                let [part] = eval_parts(g, at)? else {
                    return Err(bad("元数値等式partが違う"));
                };
                let [l, rr] = part.children.as_slice() else {
                    return Err(bad("元数値等式の左右評価がない"));
                };
                r.operand_evaluations = vec![l.0, rr.0];
                for operand in [l, rr] {
                    let Some(Payload::Evaluation { value, .. }) =
                        g.nodes.get(operand.0).and_then(|n| n.payload.as_ref())
                    else {
                        return Err(bad("元operand評価がない"));
                    };
                    r.operand_values.push(value.map(|v| v.0));
                }
                lhs = scalar(g, Some(*l), c)?;
                rhs = scalar(g, Some(*rr), c)?;
                r.epsilon_producer = part.residual.map(|v| v.0);
                epsilon = scalar(g, part.residual, c)?;
                // 元producerは保つが、未観測operandを定数零の生差へ読み替えない。
                if lhs.is_none() || rhs.is_none() {
                    epsilon = None;
                }
                for value in [&lhs, &rhs, &epsilon].into_iter().flatten() {
                    if &value.ty() != ty {
                        return Err(bad("元数値等式の値/差の型が違う"));
                    }
                }
            }
        }
    }
    let mut coords = vec![];
    leaves(ty, &mut vec![], &mut coords, c)?;
    for (path, ty) in coords {
        tick(c)?;
        let raw = component(epsilon.as_ref(), &path, &ty, c)?;
        let residual = match r.reading.application().value() {
            Some(false) => Some(NumericTransportValue::observed(
                numeric::zero(&ty, c).map_err(invalid)?,
            )),
            Some(true) => raw.clone(),
            None => None,
        };
        r.components.push(LawResidualComponent {
            left: component(lhs.as_ref(), &path, &ty, c)?,
            right: component(rhs.as_ref(), &path, &ty, c)?,
            epsilon: raw,
            residual,
            path,
            ty,
        });
    }
    r.complete = true;
    Ok(())
}
fn extract(
    result: &mut ObjectLawResiduals,
    index: usize,
    inputs: &CheckedInputs,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    let src = &result.base.evaluations()[index];
    let shape = shape(inputs, &src.evaluation().instance().declaration().name, c)?;
    result.evaluations.push(LawResidualEvaluation {
        position: src.position(),
        shape,
        rows: vec![],
        uniform: None,
        complete: false,
    });
    let out = &mut result.evaluations[index];
    let g = graph(src.evaluation());
    for row in src.family().rows() {
        tick(c)?;
        out.rows.push(LawResidualRow {
            cases: vec![],
            complete: false,
        });
        let dest = out.rows.last_mut().ok_or_else(|| bad("残差行がない"))?;
        let mut refs = vec![];
        for &reference in &row.evaluations {
            flatten(
                g.ok_or_else(|| bad("元caseのDAGがない"))?,
                reference,
                &mut refs,
                c,
            )?;
        }
        let cases = if refs.is_empty() {
            vec![None]
        } else {
            refs.into_iter().map(Some).collect()
        };
        let case_count = cases.len();
        for (case_index, reference) in cases.into_iter().enumerate() {
            tick(c)?;
            let reading = match reference {
                Some(reference) => native_case_reading(
                    src.evaluation(),
                    reference,
                    matches!(
                        &out.shape,
                        LawNumericShape::Equality {
                            explicit_guard: true,
                            ..
                        } | LawNumericShape::Conjunction {
                            explicit_guard: true,
                            ..
                        } | LawNumericShape::Unsupported {
                            explicit_guard: true,
                            ..
                        }
                    ),
                    c,
                )?,
                None => row.reading().clone(),
            };
            dest.cases.push(LawResidualCase {
                evaluation: reference.map(|v| v.0),
                body_evaluation: None,
                operand_evaluations: vec![],
                operand_values: vec![],
                epsilon_producer: None,
                reading,
                components: vec![],
                conjuncts: vec![],
                complete: false,
            });
            read_case(
                dest.cases.last_mut().ok_or_else(|| bad("残差caseがない"))?,
                &out.shape,
                inputs,
                g,
                c,
            )?;
            if case_index + 1 == case_count {
                dest.complete = true;
            }
            c.checkpoint(Checkpoint::ObjectLawResidualCase)?;
        }
        dest.complete = true;
        tick(c)?;
    }
    if out.rows.is_empty() {
        if let Some(reading) = src.family().uniform() {
            out.uniform = Some(LawResidualRow {
                cases: vec![LawResidualCase {
                    evaluation: None,
                    body_evaluation: None,
                    operand_evaluations: vec![],
                    operand_values: vec![],
                    epsilon_producer: None,
                    reading: reading.clone(),
                    components: vec![],
                    conjuncts: vec![],
                    complete: false,
                }],
                complete: false,
            });
            let row = out
                .uniform
                .as_mut()
                .ok_or_else(|| bad("一様残差読取りがない"))?;
            read_case(&mut row.cases[0], &out.shape, inputs, g, c)?;
            if reading.application().value() == Some(false) {
                row.cases[0].evaluation = g.and_then(|graph| graph.answers.first())
                    .and_then(|answer| answer.outputs.get("evaluation")).map(|root| root.0);
            }
            if let Some((root, producer, value)) = super::object_law_transport::constant_numeric_family(src.evaluation(), c)? {
                let case = &mut row.cases[0];
                let [component] = case.components.as_mut_slice() else { return Err(bad("一様数値差の成分数が違う")) };
                if !component.path.is_empty() || component.ty != value.ty() { return Err(bad("一様数値差の型が違う")) }
                case.evaluation = Some(root.0);
                case.epsilon_producer = Some(producer.0);
                component.epsilon = Some(NumericTransportValue::observed(value.clone()));
                component.residual = Some(NumericTransportValue::observed(value));
            }
            row.complete = true;
            c.checkpoint(Checkpoint::ObjectLawResidualCase)?;
        }
    }
    out.complete = src.family().is_complete();
    tick(c)
}
fn combine<'a>(values: impl Iterator<Item = &'a LawResidualOutcome>) -> LawResidualOutcome {
    let mut unknown = false;
    let mut unsupported = false;
    for value in values {
        match value {
            LawResidualOutcome::Refuted { .. } | LawResidualOutcome::ArgumentsDiffer => {
                return value.clone();
            }
            LawResidualOutcome::Undetermined => unknown = true,
            LawResidualOutcome::Unsupported => unsupported = true,
            _ => {}
        }
    }
    if unknown {
        LawResidualOutcome::Undetermined
    } else if unsupported {
        LawResidualOutcome::Unsupported
    } else {
        LawResidualOutcome::Compatible
    }
}
fn known(
    row: &LawResidualRow,
    i: usize,
    c: &mut Control,
) -> Result<Option<NumericTransportValue>, ConstructionFailure> {
    if !row.complete || row.cases.is_empty() {
        return Ok(None);
    }
    let mut value = None;
    let mut application = None;
    for case in &row.cases {
        tick(c)?;
        if !case.complete {
            return Ok(None);
        }
        let Some(applies) = case.reading.application().value() else {
            return Ok(None);
        };
        if application.is_some_and(|previous| previous != applies) {
            return Ok(None);
        }
        application = Some(applies);
        let Some(v) = case.components.get(i).and_then(|v| v.residual.as_ref()) else {
            return Ok(None);
        };
        if let Some(previous) = &value {
            if previous != v {
                return Ok(None);
            }
        } else {
            value = Some(v.clone());
        }
    }
    Ok(value)
}
fn lookup(
    result: &ObjectLawResiduals,
    object: usize,
    instance: usize,
) -> Result<usize, ConstructionFailure> {
    result
        .evaluations
        .iter()
        .position(|e| e.position == ObjectEvaluationPosition { object, instance })
        .ok_or_else(|| bad("数値Lawの元評価位置がない"))
}
fn point(
    result: &mut ObjectLawResiduals,
    index: usize,
    left: usize,
    right: usize,
    ai: Option<usize>,
    bi: Option<usize>,
    args: Vec<FiniteTransportValue>,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    result.comparisons[index].points.push(LawResidualPoint {
        arguments: args,
        source_row: ai,
        target_row: bi,
        components: vec![],
        outcome: None,
    });
    let a = &result.evaluations[left];
    let b = &result.evaluations[right];
    fn pick(e: &LawResidualEvaluation, i: Option<usize>) -> Option<&LawResidualRow> {
        match i {
            Some(i) => e.rows.get(i),
            None => e.uniform.as_ref(),
        }
    }
    let ar = pick(a, ai).ok_or_else(|| bad("元数値Law行がない"))?;
    let br = pick(b, bi).ok_or_else(|| bad("比較数値Law行がない"))?;
    let p = result.comparisons[index]
        .points
        .last_mut()
        .ok_or_else(|| bad("数値Law比較点がない"))?;
    match (&a.shape, &b.shape) {
        (LawNumericShape::Equality { ty, .. } | LawNumericShape::Conjunction { ty, .. },
         LawNumericShape::Equality { ty: other, .. } | LawNumericShape::Conjunction { ty: other, .. })
            if ty == other =>
        {
            let mut coords = vec![];
            leaves(ty, &mut vec![], &mut coords, c)?;
            for (i, (path, _)) in coords.iter().enumerate() {
                tick(c)?;
                let outcome = match (known(ar, i, c)?, known(br, i, c)?) {
                    (Some(av), Some(bv)) => {
                        if av == bv {
                            LawResidualOutcome::Compatible
                        } else {
                            LawResidualOutcome::Refuted {
                                component: path.clone(),
                            }
                        }
                    }
                    _ => LawResidualOutcome::Undetermined,
                };
                if matches!(outcome, LawResidualOutcome::Refuted { .. }) && result.outcome.is_none()
                {
                    result.outcome = Some(outcome.clone());
                }
                p.components.push(outcome);
            }
            p.outcome = Some(combine(p.components.iter()));
        }
        _ => p.outcome = Some(LawResidualOutcome::Unsupported),
    }
    Ok(())
}
fn calculate(
    result: &mut ObjectLawResiduals,
    inputs: &CheckedInputs,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    for i in 0..result.base.evaluations().len() {
        extract(result, i, inputs, c)?;
    }
    for index in 0..result.base.comparisons().len() {
        tick(c)?;
        let src = &result.base.comparisons()[index];
        let (a, b, instance) = (src.source_object(), src.target_object(), src.instance());
        let left = lookup(result, a, instance)?;
        let right = lookup(result, b, instance)?;
        result.comparisons.push(LawResidualComparison {
            source_object: a,
            target_object: b,
            instance,
            points: vec![],
            outcome: None,
        });
        let points = src
            .points()
            .iter()
            .map(|p| (p.source_row(), p.target_row(), p.arguments().to_vec()))
            .collect::<Vec<_>>();
        let unmatched = !src.unmatched_source().is_empty() || !src.unmatched_target().is_empty();
        let ready = result.evaluations[left].complete
            && result.evaluations[right].complete
            && result.base.evaluations()[left]
                .family()
                .missing()
                .is_empty()
            && result.base.evaluations()[right]
                .family()
                .missing()
                .is_empty();
        if ready {
            let count = points.len();
            for (j, (ai, bi, args)) in points.into_iter().enumerate() {
                point(result, index, left, right, ai, bi, args, c)?;
                if j + 1 < count {
                    c.checkpoint(Checkpoint::ObjectLawResidualPoint)?;
                }
            }
            if result.comparisons[index].points.is_empty()
                && result.evaluations[left].uniform.is_some()
                && result.evaluations[right].uniform.is_some()
            {
                point(result, index, left, right, None, None, vec![], c)?;
            }
        }
        let p = &mut result.comparisons[index];
        p.outcome = Some(if !ready {
            LawResidualOutcome::Undetermined
        } else if unmatched {
            LawResidualOutcome::ArgumentsDiffer
        } else {
            combine(p.points.iter().filter_map(|p| p.outcome.as_ref()))
        });
        if matches!(
            p.outcome,
            Some(LawResidualOutcome::Refuted { .. } | LawResidualOutcome::ArgumentsDiffer)
        ) && result.outcome.is_none()
        {
            result.outcome = p.outcome.clone();
        }
        if index + 1 == result.base.comparisons().len() {
            finish_all(result, c)?;
        }
        c.checkpoint(Checkpoint::ObjectLawResidualPoint)?;
        tick(c)?;
    }
    if result.base.comparisons().is_empty() {
        finish_all(result, c)?;
    }
    tick(c)
}
fn finish_all(result: &mut ObjectLawResiduals, c: &mut Control) -> Result<(), ConstructionFailure> {
    let mut outcome = combine(result.comparisons.iter().filter_map(|v| v.outcome.as_ref()));
    // 比較対が空でも未実現/欠測を全域の読取り成功にはしない。
    for e in &result.evaluations {
        tick(c)?;
        if matches!(
            outcome,
            LawResidualOutcome::Compatible | LawResidualOutcome::Unsupported
        ) {
            if !e.complete {
                outcome = LawResidualOutcome::Undetermined;
            } else if matches!(e.shape, LawNumericShape::Unsupported { .. }) {
                outcome = LawResidualOutcome::Unsupported;
            } else {
                for row in e.rows.iter().chain(e.uniform.iter()) {
                    for i in 0..row.cases.first().map_or(0, |v| v.components.len()) {
                        if known(row, i, c)?.is_none() {
                            outcome = LawResidualOutcome::Undetermined;
                        }
                    }
                }
            }
        }
    }
    if outcome == LawResidualOutcome::Compatible && !result.base.profiles().is_complete() {
        outcome = LawResidualOutcome::Undetermined;
    }
    result.outcome = Some(outcome);
    result.complete = true;
    tick(c)
}
pub fn object_law_residuals(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    c: &mut Control,
) -> Result<ObjectLawResiduals, ObjectLawResidualsFailure> {
    let base = object_law_compatibility(Arc::clone(&inputs), reading, snapshot, root, c)
        .map_err(ObjectLawResidualsFailure::Original)?;
    let mut result = ObjectLawResiduals {
        base,
        evaluations: vec![],
        comparisons: vec![],
        complete: false,
        outcome: None,
    };
    match calculate(&mut result, &inputs, c) {
        Ok(()) => Ok(result),
        Err(cause) => Err(ObjectLawResidualsFailure::Reading {
            cause,
            partial: Box::new(result),
        }),
    }
}
fn same(
    a: &ObjectLawResiduals,
    b: &ObjectLawResiduals,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.complete != b.complete
        || a.outcome != b.outcome
        || a.evaluations.len() != b.evaluations.len()
        || a.comparisons.len() != b.comparisons.len()
    {
        return Ok(false);
    }
    fn rows(
        a: &LawResidualRow,
        b: &LawResidualRow,
        c: &mut Control,
    ) -> Result<bool, ConstructionFailure> {
        tick(c)?;
        if a.complete != b.complete || a.cases.len() != b.cases.len() {
            return Ok(false);
        }
        for (a, b) in a.cases.iter().zip(&b.cases) {
            tick(c)?;
            if a.evaluation != b.evaluation
                || a.body_evaluation != b.body_evaluation
                || a.operand_evaluations != b.operand_evaluations
                || a.operand_values != b.operand_values
                || a.epsilon_producer != b.epsilon_producer
                || a.reading != b.reading
                || a.complete != b.complete
                || a.conjuncts != b.conjuncts
                || a.components.len() != b.components.len()
            {
                return Ok(false);
            }
            for (a, b) in a.components.iter().zip(&b.components) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
    for (a, b) in a.evaluations.iter().zip(&b.evaluations) {
        tick(c)?;
        if a.position != b.position
            || a.shape != b.shape
            || a.complete != b.complete
            || a.rows.len() != b.rows.len()
        {
            return Ok(false);
        }
        match (&a.uniform, &b.uniform) {
            (Some(a), Some(b)) => {
                if !rows(a, b, c)? {
                    return Ok(false);
                }
            }
            (None, None) => {}
            _ => return Ok(false),
        }
        for (a, b) in a.rows.iter().zip(&b.rows) {
            if !rows(a, b, c)? {
                return Ok(false);
            }
        }
    }
    for (a, b) in a.comparisons.iter().zip(&b.comparisons) {
        tick(c)?;
        if a.source_object != b.source_object
            || a.target_object != b.target_object
            || a.instance != b.instance
            || a.outcome != b.outcome
            || a.points.len() != b.points.len()
        {
            return Ok(false);
        }
        for (a, b) in a.points.iter().zip(&b.points) {
            tick(c)?;
            if a.arguments != b.arguments
                || a.source_row != b.source_row
                || a.target_row != b.target_row
                || a.outcome != b.outcome
                || a.components.len() != b.components.len()
            {
                return Ok(false);
            }
            for (a, b) in a.components.iter().zip(&b.components) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
        }
    }
    tick(c)?;
    Ok(true)
}
