//! 明示In/有限型量化の静的出現と、未知を補わない有限Bool集約。
use super::{
    control::{Checkpoint, Control},
    data, finite,
    result::{Quantifier, ValidationFailure},
};
use crate::{
    issue::Location,
    law::{
        CheckedLaw,
        ast::{ExprKind, QuantDomain, QuantKind, QuantSplit},
    },
    types::Type,
};

pub(super) struct Spec<'a> {
    pub kind: QuantKind,
    pub name: &'a str,
    pub domain: Option<usize>,
    pub body: usize,
    pub element: Type,
    pub span: (usize, usize),
}
pub(super) fn spec<'a>(
    law: &'a CheckedLaw,
    id: usize,
    control: &Control,
) -> Result<Spec<'a>, ValidationFailure> {
    let expression = &law.exprs[id];
    let ExprKind::Quant { kind, var, split } = &expression.kind else {
        return Err("量化の元ASTでない".into());
    };
    let QuantSplit::Fixed { domain, body } = split else {
        return Err("検査済み量化の区切りがない".into());
    };
    let element = law
        .quantifier_types
        .get(id)
        .and_then(Option::as_ref)
        .ok_or("量化の元解決済みbinder型がない")?;
    let (domain, supported) = match domain {
        QuantDomain::In(domain) => {
            let Some(Type::List(actual) | Type::Set(actual)) = law.expr_type(*domain) else {
                return Err("In量化の元域がList/Setでない".into());
            };
            if actual.as_ref() != element {
                return Err("In量化の元binder型が違う".into());
            }
            (Some(*domain), data::supported(element, law, control)?)
        }
        QuantDomain::Type(_) => (None, finite::supported(element, law, control)?),
    };
    if !supported {
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law {
                span: expression.span,
            },
            feature: if domain.is_some() {
                "未対応要素型のIn量化"
            } else {
                "未対応・無限型の型全域量化"
            }
            .into(),
        });
    }
    Ok(Spec {
        kind: *kind,
        name: &var.name,
        domain,
        body: *body,
        element: element.clone(),
        span: expression.span,
    })
}
impl Spec<'_> {
    pub fn descriptor(
        &self,
        domain: Option<super::result::NodeRef>,
        context: Option<super::call::Context>,
    ) -> Quantifier {
        Quantifier {
            kind: self.kind,
            name: self.name.into(),
            ty: self.element.clone(),
            domain,
            occurrence: self.span,
            context,
        }
    }
}
pub(super) fn reduce(
    kind: QuantKind,
    values: &[Option<bool>],
    control: &Control,
) -> Result<Option<bool>, ValidationFailure> {
    let decisive = kind == QuantKind::Exists;
    let mut result = Some(!decisive);
    for value in values {
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
        if *value == Some(decisive) {
            result = Some(decisive)
        } else if value.is_none() && result != Some(decisive) {
            result = None;
        }
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
    }
    Ok(result)
}
