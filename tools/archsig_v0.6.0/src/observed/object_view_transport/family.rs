//! 元の有限view族の全型域を対応させ、各代入で値の可換性を検査する。
use super::*;
use crate::law::model::Param;
use crate::observed::{
    environment::Environment,
    result::{ObservedEvaluation, Scope},
    value_transport,
};

fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectViewTransportFamily)
        .map_err(Into::into)
}
fn bad(message: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(message.into())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FamilyTypeFailure {
    OutsideTarget {
        source: usize,
    },
    Collision {
        image: ViewTransportValue,
        target: Option<usize>,
        sources: Vec<usize>,
    },
    Unreached {
        target: usize,
    },
}
/// 対応する元instanceの固定束縛から列挙した全型域。表の各添字はこの順序を使う。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteViewTypeMap {
    position: DeclarationValuePosition,
    source_parameter: Param,
    target_parameter: Param,
    source_scope: Scope,
    target_scope: Scope,
    source_support: Vec<FactPointer>,
    target_support: Vec<FactPointer>,
    source_type: Type,
    target_type: Type,
    source: Vec<ViewTransportValue>,
    target: Vec<ViewTransportValue>,
    images: Vec<ViewTransportValue>,
    forward: Option<Vec<usize>>,
    inverse: Option<Vec<usize>>,
    missing: Vec<FactPointer>,
    failures: Vec<FamilyTypeFailure>,
}
impl FiniteViewTypeMap {
    pub fn position(&self) -> DeclarationValuePosition {
        self.position
    }
    pub fn source_parameter(&self) -> &Param {
        &self.source_parameter
    }
    pub fn target_parameter(&self) -> &Param {
        &self.target_parameter
    }
    pub fn source_support(&self) -> &[FactPointer] {
        &self.source_support
    }
    pub fn target_support(&self) -> &[FactPointer] {
        &self.target_support
    }
    pub fn source_type(&self) -> &Type {
        &self.source_type
    }
    pub fn target_type(&self) -> &Type {
        &self.target_type
    }
    pub fn source(&self) -> &[ViewTransportValue] {
        &self.source
    }
    pub fn target(&self) -> &[ViewTransportValue] {
        &self.target
    }
    pub fn images(&self) -> &[ViewTransportValue] {
        &self.images
    }
    pub fn forward(&self) -> Option<&[usize]> {
        self.forward.as_deref()
    }
    pub fn inverse(&self) -> Option<&[usize]> {
        self.inverse.as_deref()
    }
    pub fn missing(&self) -> &[FactPointer] {
        &self.missing
    }
    pub fn failures(&self) -> &[FamilyTypeFailure] {
        &self.failures
    }
    fn image(&self, value: &Scalar, c: &mut Control) -> Result<Scalar, ConstructionFailure> {
        if self.forward.is_none() || self.inverse.is_none() {
            return Err(bad("有限view型の順逆が未確認"));
        }
        for (source, image) in self.source.iter().zip(&self.images) {
            tick(c)?;
            if data::equal(&source.value, value, c).map_err(invalid)? {
                return Ok(image.value.clone());
            }
        }
        Err(bad("view実値が元の全型域にない"))
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewFamilyReturnMap {
    Finite(Box<FiniteViewTypeMap>),
    Numeric(Box<NumericValueTransport>),
    PrimitiveIdentity(PrimitiveValueIdentity),
    Structural(Box<StructuralValueEquivalence>),
}
impl ViewFamilyReturnMap {
    fn image(
        &self,
        value: &Scalar,
        inputs: &CheckedInputs,
        c: &mut Control,
    ) -> Result<Scalar, ConstructionFailure> {
        match self {
            Self::Finite(map) => map.image(value, c),
            Self::Numeric(map) => Ok(map.forward().apply_scalar(value, c)?.scalar().clone()),
            Self::PrimitiveIdentity(map) => map.image(value, c),
            Self::Structural(map) => map.image(inputs, value, c),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewParameterComparison {
    source_row: usize,
    target_row: usize,
    source_arguments: Vec<ViewTransportValue>,
    target_arguments: Vec<ViewTransportValue>,
    source: Option<ViewTransportValue>,
    image: Option<ViewTransportValue>,
    target: Option<ViewTransportValue>,
    outcome: ViewTransportOutcome,
}
impl ViewParameterComparison {
    /// 親transportが保持するsource/targetの元FiniteObjectView内の行番号。
    pub fn source_row(&self) -> usize {
        self.source_row
    }
    pub fn target_row(&self) -> usize {
        self.target_row
    }
    pub fn source_arguments(&self) -> &[ViewTransportValue] {
        &self.source_arguments
    }
    pub fn target_arguments(&self) -> &[ViewTransportValue] {
        &self.target_arguments
    }
    pub fn source(&self) -> Option<&ViewTransportValue> {
        self.source.as_ref()
    }
    pub fn image(&self) -> Option<&ViewTransportValue> {
        self.image.as_ref()
    }
    pub fn target(&self) -> Option<&ViewTransportValue> {
        self.target.as_ref()
    }
    pub fn outcome(&self) -> &ViewTransportOutcome {
        &self.outcome
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct FiniteViewTransport {
    parameters: Vec<FiniteViewTypeMap>,
    returns: Option<ViewFamilyReturnMap>,
    rows: Vec<ViewParameterComparison>,
    complete: bool,
}
impl FiniteViewTransport {
    /// 元instanceの残るparameter順。名前が異なっても元署名の位置で対応する。
    pub fn parameters(&self) -> &[FiniteViewTypeMap] {
        &self.parameters
    }
    pub fn returns(&self) -> Option<&ViewFamilyReturnMap> {
        self.returns.as_ref()
    }
    pub fn rows(&self) -> &[ViewParameterComparison] {
        &self.rows
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
}

fn type_map(
    inputs: &CheckedInputs,
    declarations: &DeclarationCorrespondence,
    source_instance: &ObjectInstance,
    target_instance: &ObjectInstance,
    source: &Param,
    target: &Param,
    position: DeclarationValuePosition,
    c: &mut Control,
) -> Result<Option<FiniteViewTypeMap>, ConstructionFailure> {
    let env = Environment::new(inputs, c)?;
    let Some((source_domain, mut missing)) = env
        .object_view_domain(source, source_instance)
        .map_err(invalid)?
    else {
        return Ok(None);
    };
    let Some((target_domain, target_missing)) = env
        .object_view_domain(target, target_instance)
        .map_err(invalid)?
    else {
        return Ok(None);
    };
    missing.extend(target_missing);
    missing.sort();
    missing.dedup();
    let mut r = FiniteViewTypeMap {
        position,
        source_parameter: source.clone(),
        target_parameter: target.clone(),
        source_scope: source_domain.scope,
        target_scope: target_domain.scope,
        source_support: source_domain.support,
        target_support: target_domain.support,
        source_type: source.ty.clone(),
        target_type: target.ty.clone(),
        source: source_domain
            .values
            .into_iter()
            .map(|value| ViewTransportValue { value })
            .collect(),
        target: target_domain
            .values
            .into_iter()
            .map(|value| ViewTransportValue { value })
            .collect(),
        images: vec![],
        forward: None,
        inverse: None,
        missing,
        failures: vec![],
    };
    if !r.missing.is_empty() {
        return Ok(Some(r));
    }
    let mut forward = Vec::new();
    let mut fibers = vec![vec![]; r.target.len()];
    let mut candidate_fibers: Vec<(usize, Option<usize>, Vec<usize>)> = Vec::new();
    for (index, source) in r.source.iter().enumerate() {
        tick(c)?;
        let image = value_transport::candidate_image(
            inputs,
            declarations,
            &source_instance.declaration().name,
            &source.value,
            c,
        )?;
        let mut target_index = None;
        let valid_shape = match data::check(&image, inputs.law(), c) {
            Ok(()) => true,
            Err(ValidationFailure::Internal(_)) => false,
            Err(failure) => return Err(invalid(failure)),
        };
        for (j, target) in r.target.iter().enumerate().filter(|_| valid_shape) {
            tick(c)?;
            if image.ty() == target.value.ty()
                && data::candidate_equal(&image, &target.value, c).map_err(invalid)?
            {
                target_index = Some(j);
                break;
            }
        }
        if let Some(j) = target_index {
            fibers[j].push(index);
            forward.push(j);
        } else {
            r.failures
                .push(FamilyTypeFailure::OutsideTarget { source: index });
        }
        let mut found_fiber = false;
        for (representative, _, sources) in &mut candidate_fibers {
            tick(c)?;
            if data::candidate_equal(&r.images[*representative].value, &image, c)
                .map_err(invalid)?
            {
                sources.push(index);
                found_fiber = true;
                break;
            }
        }
        if !found_fiber {
            candidate_fibers.push((index, target_index, vec![index]));
        }
        r.images.push(ViewTransportValue { value: image });
    }
    for (representative, target, sources) in candidate_fibers {
        tick(c)?;
        if sources.len() > 1 {
            r.failures.push(FamilyTypeFailure::Collision {
                image: r.images[representative].clone(),
                target,
                sources,
            });
        }
    }
    for (target, sources) in fibers.iter().enumerate() {
        tick(c)?;
        if sources.is_empty() {
            r.failures.push(FamilyTypeFailure::Unreached { target });
        }
    }
    if r.failures.is_empty() {
        let inverse: Vec<_> = fibers.iter().map(|f| f[0]).collect();
        for (a, &b) in forward.iter().enumerate() {
            tick(c)?;
            if inverse.get(b) != Some(&a) {
                return Err(bad("view型の逆順合成が恒等でない"));
            }
        }
        for (b, &a) in inverse.iter().enumerate() {
            tick(c)?;
            if forward.get(a) != Some(&b) {
                return Err(bad("view型の順合成が恒等でない"));
            }
        }
        r.forward = Some(forward);
        r.inverse = Some(inverse);
    }
    Ok(Some(r))
}
fn value(e: &ObservedEvaluation) -> Result<Option<ViewTransportValue>, ConstructionFailure> {
    scalar_evaluation(e).map(|v| v.map(|value| ViewTransportValue { value }))
}

pub(super) fn evaluate(
    inputs: Arc<CheckedInputs>,
    r: &mut ObjectViewTransport,
    to: usize,
    ti: usize,
    c: &mut Control,
) -> Result<(), ObjectViewTransportFailure> {
    r.family = Some(FiniteViewTransport::default());
    r.source = Some(
        evaluate_object_instance(
            Arc::clone(&inputs),
            &r.source_readings,
            r.object,
            r.instance,
            c,
        )
        .map_err(|failure| ObjectViewTransportFailure::Evaluation {
            operation: Box::new(r.operation().clone()),
            partial: None,
            failure: Box::new(failure),
        })?,
    );
    tick(c)?;
    r.target = Some(
        evaluate_object_instance(Arc::clone(&inputs), &r.target_readings, to, ti, c).map_err(
            |failure| ObjectViewTransportFailure::Evaluation {
                operation: Box::new(r.operation().clone()),
                partial: None,
                failure: Box::new(failure),
            },
        )?,
    );
    let source = r
        .source
        .as_ref()
        .ok_or_else(|| bad("source view族がない"))?;
    let target = r
        .target
        .as_ref()
        .ok_or_else(|| bad("target view族がない"))?;
    let conditional = matches!(source.outcome(), ObjectEvaluationOutcome::Conditional(_))
        || matches!(target.outcome(), ObjectEvaluationOutcome::Conditional(_));
    let source_na = matches!(source.outcome(), ObjectEvaluationOutcome::NotApplicable);
    let target_na = matches!(target.outcome(), ObjectEvaluationOutcome::NotApplicable);
    if !conditional && source_na != target_na {
        r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::Applicability);
        return Ok(());
    }
    let source_instance = r.instance().clone();
    let target_instance = r
        .target_instance()
        .ok_or_else(|| bad("target instanceがない"))?
        .clone();
    if source_instance.parameters().len() != target_instance.parameters().len() {
        return Err(bad("対応viewの残parameter数が違う").into());
    }
    let f = r.family.as_mut().ok_or_else(|| bad("view保存族がない"))?;
    let mut parameter_missing = false;
    let mut parameter_failure = None;
    for (a, b) in source_instance
        .parameters()
        .iter()
        .zip(target_instance.parameters())
    {
        let position = source_instance
            .declaration()
            .parameters
            .iter()
            .position(|(name, _)| name == &a.name)
            .ok_or_else(|| bad("元viewのparameter位置がない"))?;
        tick(c)?;
        let Some(map) = type_map(
            &inputs,
            &r.declarations,
            &source_instance,
            &target_instance,
            a,
            b,
            DeclarationValuePosition::Parameter(position),
            c,
        )?
        else {
            return Err(not_implemented(r)?);
        };
        let missing = !map.missing.is_empty();
        let failed = !map.failures.is_empty();
        f.parameters.push(map);
        parameter_missing |= missing;
        if failed && parameter_failure.is_none() {
            parameter_failure = Some(position);
        }
    }
    if let Some(position) = parameter_failure {
        r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::ParameterType { position });
        return Ok(());
    }
    if parameter_missing {
        return Ok(());
    }
    let source_type = source_instance
        .declaration()
        .returns
        .clone()
        .ok_or_else(|| bad("view戻り型がない"))?;
    let target_type = target_instance
        .declaration()
        .returns
        .clone()
        .ok_or_else(|| bad("target戻り型がない"))?;
    if numeric::is_numeric_type(&source_type, c).map_err(invalid)? {
        f.returns = Some(ViewFamilyReturnMap::Numeric(Box::new(
            numeric_declaration_value_transport(
                &inputs,
                &r.declarations,
                &source_instance.declaration().name,
                DeclarationValuePosition::Return,
                c,
            )?,
        )));
    } else if !finite::supported(&source_type, inputs.law(), c).map_err(invalid)?
        && let Some(identity) = PrimitiveValueIdentity::checked(
            &inputs,
            &r.declarations,
            &source_instance.declaration().name,
            c,
        )?
    {
        f.returns = Some(ViewFamilyReturnMap::PrimitiveIdentity(identity));
    } else if !finite::supported(&source_type, inputs.law(), c).map_err(invalid)?
        && let Some(map) = StructuralValueEquivalence::checked(
            &inputs,
            &r.declarations,
            &source_instance.declaration().name,
            c,
        )?
    {
        let complete = map.is_bijection();
        f.returns = Some(ViewFamilyReturnMap::Structural(Box::new(map)));
        if !complete {
            r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::ValueType);
            return Ok(());
        }
    } else {
        let a = Param {
            name: "return".into(),
            ty: source_type,
            span: (0, 0),
        };
        let b = Param {
            name: "return".into(),
            ty: target_type,
            span: (0, 0),
        };
        let Some(map) = type_map(
            &inputs,
            &r.declarations,
            &source_instance,
            &target_instance,
            &a,
            &b,
            DeclarationValuePosition::Return,
            c,
        )?
        else {
            return Err(not_implemented(r)?);
        };
        let missing = !map.missing.is_empty();
        let failed = !map.failures.is_empty();
        f.returns = Some(ViewFamilyReturnMap::Finite(Box::new(map)));
        if missing {
            return Ok(());
        }
        if failed {
            r.outcome = ViewTransportOutcome::Refuted(ViewConditionFailure::ValueType);
            return Ok(());
        }
    }
    if conditional {
        return Ok(());
    }
    if source_na && target_na {
        f.complete = true;
        r.outcome = ViewTransportOutcome::Preserved;
        return Ok(());
    }
    let (ObjectEvaluationOutcome::FiniteView(source), ObjectEvaluationOutcome::FiniteView(target)) =
        (source.outcome(), target.outcome())
    else {
        return Err(bad("有限view族の実評価でない").into());
    };
    if !source.is_complete() || !target.is_complete() {
        return Ok(());
    }
    let mut target_used = vec![false; target.rows().len()];
    for (source_row, row) in source.rows().iter().enumerate() {
        tick(c)?;
        let mut moved = Vec::new();
        if row.arguments().len() != f.parameters.len() {
            return Err(bad("view引数数が元署名と違う").into());
        }
        for (arg, map) in row.arguments().iter().zip(&f.parameters) {
            moved.push(map.image(arg.scalar(), c)?);
        }
        let mut matched = None;
        for (j, target_row) in target.rows().iter().enumerate() {
            tick(c)?;
            if target_row.arguments().len() != moved.len() {
                continue;
            }
            let mut same = true;
            for (a, b) in moved.iter().zip(target_row.arguments()) {
                tick(c)?;
                same &= data::equal(a, b.scalar(), c).map_err(invalid)?;
            }
            if same {
                if matched.is_some() {
                    return Err(bad("対応viewの代入が重複").into());
                }
                matched = Some(j);
            }
        }
        let target_row = matched.ok_or_else(|| bad("対応viewの代入がない"))?;
        if target_used[target_row] {
            return Err(bad("view代入の対応が一対一でない").into());
        }
        let target_evaluation = &target.rows()[target_row];
        let source_value = value(row.evaluation())?;
        let target_value = value(target_evaluation.evaluation())?;
        let image = source_value
            .as_ref()
            .map(|s| {
                f.returns
                    .as_ref()
                    .ok_or_else(|| bad("view戻り値写像がない"))?
                    .image(&s.value, &inputs, c)
                    .map(|value| ViewTransportValue { value })
            })
            .transpose()?;
        let mut comparison = ViewParameterComparison {
            source_row,
            target_row,
            source_arguments: row
                .arguments()
                .iter()
                .map(|a| ViewTransportValue {
                    value: a.scalar().clone(),
                })
                .collect(),
            target_arguments: target_evaluation
                .arguments()
                .iter()
                .map(|a| ViewTransportValue {
                    value: a.scalar().clone(),
                })
                .collect(),
            source: source_value,
            image,
            target: target_value,
            outcome: ViewTransportOutcome::Undetermined,
        };
        let mut finished = false;
        let checked = match (&comparison.image, &comparison.target) {
            (Some(a), Some(b)) => data::equal_retained(&a.value, &b.value, c, |equal| {
                comparison.outcome = if equal {
                    ViewTransportOutcome::Preserved
                } else {
                    ViewTransportOutcome::Refuted(ViewConditionFailure::Value)
                };
                finished = true;
            })
            .map(|_| ())
            .map_err(invalid),
            _ => {
                finished = true;
                Ok(())
            }
        };
        if finished {
            f.rows.push(comparison);
            target_used[target_row] = true;
            if f.rows.len() == source.rows().len() && target_used.iter().all(|used| *used) {
                f.complete = true;
                r.outcome = aggregate(f);
            }
        }
        checked?;
        c.checkpoint(Checkpoint::ObjectViewTransportFamilyRow)
            .map_err(ConstructionFailure::from)?;
    }
    if target_used.iter().any(|used| !used) {
        return Err(bad("view族の未対応target代入がある").into());
    }
    f.complete = true;
    r.outcome = aggregate(f);
    Ok(())
}

fn aggregate(f: &FiniteViewTransport) -> ViewTransportOutcome {
    f.rows
        .iter()
        .find_map(|row| {
            if let ViewTransportOutcome::Refuted(reason) = &row.outcome {
                Some(ViewTransportOutcome::Refuted(reason.clone()))
            } else {
                None
            }
        })
        .unwrap_or_else(|| {
            if f.rows
                .iter()
                .all(|row| row.outcome == ViewTransportOutcome::Preserved)
            {
                ViewTransportOutcome::Preserved
            } else {
                ViewTransportOutcome::Undetermined
            }
        })
}

fn same_values(
    a: &[ViewTransportValue],
    b: &[ViewTransportValue],
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        tick(c)?;
        if !data::candidate_equal(&a.value, &b.value, c).map_err(invalid)?
            || !data::candidate_equal(&b.value, &a.value, c).map_err(invalid)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}
fn same_type_map(
    a: &FiniteViewTypeMap,
    b: &FiniteViewTypeMap,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    if a.position != b.position
        || a.source_parameter != b.source_parameter
        || a.target_parameter != b.target_parameter
        || a.source_type != b.source_type
        || a.target_type != b.target_type
        || a.source_scope != b.source_scope
        || a.target_scope != b.target_scope
    {
        return Ok(false);
    }
    for (a, b) in [
        (&a.source, &b.source),
        (&a.target, &b.target),
        (&a.images, &b.images),
    ] {
        if !same_values(a, b, c)? {
            return Ok(false);
        }
    }
    for (a, b) in [
        (&a.source_support, &b.source_support),
        (&a.target_support, &b.target_support),
        (&a.missing, &b.missing),
    ] {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            tick(c)?;
            if a != b {
                return Ok(false);
            }
        }
    }
    for (a, b) in [(&a.forward, &b.forward), (&a.inverse, &b.inverse)] {
        match (a, b) {
            (Some(a), Some(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    tick(c)?;
                    if a != b {
                        return Ok(false);
                    }
                }
            }
            (None, None) => {}
            _ => return Ok(false),
        }
    }
    if a.failures.len() != b.failures.len() {
        return Ok(false);
    }
    for (a, b) in a.failures.iter().zip(&b.failures) {
        tick(c)?;
        match (a, b) {
            (
                FamilyTypeFailure::OutsideTarget { source: a },
                FamilyTypeFailure::OutsideTarget { source: b },
            ) if a == b => {}
            (
                FamilyTypeFailure::Unreached { target: a },
                FamilyTypeFailure::Unreached { target: b },
            ) if a == b => {}
            (
                FamilyTypeFailure::Collision {
                    image: ai,
                    target: at,
                    sources: a,
                },
                FamilyTypeFailure::Collision {
                    image: bi,
                    target: bt,
                    sources: b,
                },
            ) => {
                if at != bt
                    || a.len() != b.len()
                    || !same_values(std::slice::from_ref(ai), std::slice::from_ref(bi), c)?
                {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    tick(c)?;
                    if a != b {
                        return Ok(false);
                    }
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}
fn same_optional_value(
    a: Option<&ViewTransportValue>,
    b: Option<&ViewTransportValue>,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    match (a, b) {
        (Some(a), Some(b)) => same_values(std::slice::from_ref(a), std::slice::from_ref(b), c),
        (None, None) => Ok(true),
        _ => Ok(false),
    }
}
pub(super) fn same(
    a: Option<&FiniteViewTransport>,
    b: Option<&FiniteViewTransport>,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    let (Some(a), Some(b)) = (a, b) else {
        return Ok(a.is_none() && b.is_none());
    };
    if a.parameters.len() != b.parameters.len()
        || a.rows.len() != b.rows.len()
        || a.complete != b.complete
    {
        return Ok(false);
    }
    for (a, b) in a.parameters.iter().zip(&b.parameters) {
        tick(c)?;
        if !same_type_map(a, b, c)? {
            return Ok(false);
        }
    }
    tick(c)?;
    match (&a.returns, &b.returns) {
        (Some(ViewFamilyReturnMap::Finite(a)), Some(ViewFamilyReturnMap::Finite(b))) => {
            if !same_type_map(a, b, c)? {
                return Ok(false);
            }
        }
        (Some(ViewFamilyReturnMap::Numeric(a)), Some(ViewFamilyReturnMap::Numeric(b))) => {
            if a != b {
                return Ok(false);
            }
        }
        (
            Some(ViewFamilyReturnMap::PrimitiveIdentity(a)),
            Some(ViewFamilyReturnMap::PrimitiveIdentity(b)),
        ) => {
            if a != b {
                return Ok(false);
            }
        }
        (Some(ViewFamilyReturnMap::Structural(a)), Some(ViewFamilyReturnMap::Structural(b))) => {
            if a != b {
                return Ok(false);
            }
        }
        (None, None) => {}
        _ => return Ok(false),
    }
    for (a, b) in a.rows.iter().zip(&b.rows) {
        tick(c)?;
        if a.source_row != b.source_row
            || a.target_row != b.target_row
            || a.outcome != b.outcome
            || !same_values(&a.source_arguments, &b.source_arguments, c)?
            || !same_values(&a.target_arguments, &b.target_arguments, c)?
            || !same_optional_value(a.source.as_ref(), b.source.as_ref(), c)?
            || !same_optional_value(a.image.as_ref(), b.image.as_ref(), c)?
            || !same_optional_value(a.target.as_ref(), b.target.as_ref(), c)?
        {
            return Ok(false);
        }
    }
    tick(c)?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::result::Signal;
    use std::{
        cell::{Cell, RefCell},
        rc::Rc,
    };
    fn example() -> (Arc<CheckedInputs>, ObjectViewTransport) {
        super::super::tests::example_named("Before.family")
    }
    fn stop_at(point: Checkpoint, at: usize, signal: Signal) -> (Control, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&count);
        let c = Control::new(move |p| {
            if p == point {
                seen.set(seen.get() + 1);
            }
            (seen.get() >= at).then_some(signal)
        });
        (c, count)
    }
    #[test]
    fn recheck_rejects_changed_family_map_row_and_outcome() {
        // 改竄の確認は仕様の再検査の代表に限る: 型写像の像、行の実引数、全体の結論。
        for mode in 0..3 {
            let (i, mut r) = example();
            let f = r.family.as_mut().unwrap();
            match mode {
                0 => f.parameters[0].images[0].value = Scalar::Bool(true),
                1 => f.rows[0].source_arguments[0].value = Scalar::Bool(true),
                _ => r.outcome = ViewTransportOutcome::Undetermined,
            }
            r.operation()
                .recheck(&i, &mut Control::unlimited())
                .unwrap();
            assert!(
                r.recheck(i, &mut Control::unlimited()).is_err(),
                "mode={mode}"
            );
        }
    }
    #[test]
    fn collision_evidence_recheck_compares_the_image_target_and_entire_source_fiber() {
        let (_, r) = example();
        let mut a = r.family.unwrap().parameters.remove(0);
        a.failures = vec![FamilyTypeFailure::Collision {
            image: a.images[0].clone(),
            target: None,
            sources: vec![0, 1],
        }];
        assert!(same_type_map(&a, &a, &mut Control::unlimited()).unwrap());
        for mode in 0..7 {
            let mut b = a.clone();
            let FamilyTypeFailure::Collision {
                image,
                target,
                sources,
            } = &mut b.failures[0]
            else {
                unreachable!()
            };
            match mode {
                0 => image.value = Scalar::Bool(true),
                1 => *target = Some(0),
                2 => {
                    sources.pop();
                }
                3 => sources.push(2),
                4 => sources.swap(0, 1),
                5 => sources[1] = 2,
                _ => b.failures.clear(),
            }
            assert!(
                !same_type_map(&a, &b, &mut Control::unlimited()).unwrap(),
                "mode={mode}"
            );
        }
        let (mut c, probes) = stop_at(Checkpoint::ObjectViewTransportFamily, 1, Signal::Term);
        assert!(matches!(
            same_type_map(&a, &a, &mut c),
            Err(ConstructionFailure::Stopped(_))
        ));
        assert!(same_type_map(&a, &a, &mut c).is_err());
        assert_eq!(probes.get(), 1);
    }
    #[test]
    fn family_fixed_stops_keep_evaluations_and_completed_comparisons_without_new_probes() {
        let (i, r) = example();
        for point in [
            Checkpoint::ObjectViewTransportFamily,
            Checkpoint::ObjectViewTransportFamilyRow,
            Checkpoint::ObjectViewFamilyRow,
        ] {
            let count = Rc::new(Cell::new(0_usize));
            let seen = Rc::clone(&count);
            let mut c = Control::new(move |p| {
                if p == point {
                    seen.set(seen.get() + 1);
                }
                None
            });
            let normal = object_view_transport(
                Arc::clone(&i),
                &r.declarations,
                r.object,
                r.instance,
                &mut c,
            )
            .unwrap();
            assert_eq!(normal.outcome(), &ViewTransportOutcome::Preserved);
            let total = count.get();
            assert!(total > 0);
            for at in [1, total.div_ceil(2), total] {
                for signal in [Signal::Int, Signal::Term] {
                    let (mut c, count) = stop_at(point, at, signal);
                    let Err(ObjectViewTransportFailure::Stopped {
                        reason,
                        operation,
                        partial,
                        evaluation,
                        ..
                    }) = object_view_transport(
                        Arc::clone(&i),
                        &r.declarations,
                        r.object,
                        r.instance,
                        &mut c,
                    )
                    else {
                        panic!("{point:?}/{at}/{signal:?}")
                    };
                    assert_eq!(c.stop_reason(), Some(reason));
                    operation.recheck(&i, &mut Control::unlimited()).unwrap();
                    let p = partial.unwrap();
                    let f = p.family().unwrap();
                    if point == Checkpoint::ObjectViewFamilyRow {
                        assert!(evaluation.is_some());
                    } else {
                        assert!(p.source().is_some());
                        if point == Checkpoint::ObjectViewTransportFamily && at == 1 {
                            assert!(p.target().is_none());
                            assert!(f.rows.is_empty());
                        } else {
                            assert!(p.target().is_some());
                        }
                    }
                    assert!(f.rows.len() <= 2);
                    for (index, row) in f.rows.iter().enumerate() {
                        assert_eq!(row.source_row, index);
                        assert_eq!(row.source.as_ref().unwrap().value, Scalar::Bool(index == 1));
                        assert_eq!(row.outcome, ViewTransportOutcome::Preserved);
                    }
                    if f.complete {
                        assert_eq!(f.rows.len(), 2);
                        assert_eq!(p.outcome(), Some(&ViewTransportOutcome::Preserved));
                    } else {
                        assert!(p.outcome().is_none());
                    }
                    let stopped = count.get();
                    assert!(c.checkpoint(point).is_err());
                    assert_eq!(count.get(), stopped);
                }
            }
        }
    }
    #[test]
    fn comparison_final_checkpoint_retains_the_just_completed_point_and_final_outcome() {
        let (i, r) = example();
        let count = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&count);
        let boundaries = Rc::new(RefCell::new(vec![]));
        let record = Rc::clone(&boundaries);
        let mut c = Control::new(move |point| {
            if point == Checkpoint::FiniteIteration {
                seen.set(seen.get() + 1);
            }
            if point == Checkpoint::ObjectViewTransportFamilyRow {
                record.borrow_mut().push(seen.get());
            }
            None
        });
        object_view_transport(
            Arc::clone(&i),
            &r.declarations,
            r.object,
            r.instance,
            &mut c,
        )
        .unwrap();
        let boundaries = boundaries.borrow().clone();
        assert_eq!(boundaries.len(), 2);
        for (index, at) in boundaries.into_iter().enumerate() {
            for signal in [Signal::Int, Signal::Term] {
                let (mut c, count) = stop_at(Checkpoint::FiniteIteration, at, signal);
                let Err(ObjectViewTransportFailure::Stopped {
                    partial: Some(p), ..
                }) = object_view_transport(
                    Arc::clone(&i),
                    &r.declarations,
                    r.object,
                    r.instance,
                    &mut c,
                )
                else {
                    panic!("{index}/{at}/{signal:?}")
                };
                let f = p.family().unwrap();
                assert_eq!(f.rows.len(), index + 1);
                assert_eq!(f.rows[index].outcome, ViewTransportOutcome::Preserved);
                assert_eq!(
                    f.rows[index].target.as_ref().unwrap().value,
                    Scalar::Bool(index == 1)
                );
                assert_eq!(f.complete, index == 1);
                assert_eq!(
                    p.outcome(),
                    if index == 1 {
                        Some(&ViewTransportOutcome::Preserved)
                    } else {
                        None
                    }
                );
                let stopped = count.get();
                assert!(c.checkpoint(Checkpoint::FiniteIteration).is_err());
                assert_eq!(count.get(), stopped);
            }
        }
    }
    #[test]
    fn family_recheck_comparison_stop_retains_the_entire_current_recomputed_result() {
        let (i, r) = example();
        let count = Rc::new(Cell::new(0_usize));
        let seen = Rc::clone(&count);
        let mut c = Control::new(move |point| {
            if point == Checkpoint::ObjectViewTransportFamily {
                seen.set(seen.get() + 1);
            }
            None
        });
        object_view_transport(
            Arc::clone(&i),
            &r.declarations,
            r.object,
            r.instance,
            &mut c,
        )
        .unwrap();
        let calculated = count.get();
        for offset in [1, 2, 3] {
            for signal in [Signal::Int, Signal::Term] {
                let (mut c, count) = stop_at(
                    Checkpoint::ObjectViewTransportFamily,
                    calculated + offset,
                    signal,
                );
                let Err(ObjectViewTransportFailure::Stopped {
                    partial: Some(p), ..
                }) = r.recheck(Arc::clone(&i), &mut c)
                else {
                    panic!("{offset}/{signal:?}")
                };
                assert_eq!(p.outcome(), Some(&ViewTransportOutcome::Preserved));
                let f = p.family().unwrap();
                assert!(f.complete);
                assert_eq!(f.rows.len(), 2);
                p.state
                    .recheck(Arc::clone(&i), &mut Control::unlimited())
                    .unwrap();
                let stopped = count.get();
                assert!(c.checkpoint(Checkpoint::ObjectViewTransportFamily).is_err());
                assert_eq!(count.get(), stopped);
            }
        }
    }
}
