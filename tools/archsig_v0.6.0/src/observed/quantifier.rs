//! 明示In量化の静的出現と、未知を補わない有限Bool集約。
use super::{
    control::{Checkpoint, Control},
    data,
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
    pub domain: usize,
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
    let QuantSplit::Fixed {
        domain: QuantDomain::In(domain),
        body,
    } = split
    else {
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law {
                span: expression.span,
            },
            feature: "型全域の量化評価".into(),
        });
    };
    let Some(Type::List(element) | Type::Set(element)) = law.expr_type(*domain) else {
        return Err("In量化の元域がList/Setでない".into());
    };
    if !data::supported(element, law, control)? {
        return Err(ValidationFailure::UnsupportedExpression {
            location: Location::Law {
                span: expression.span,
            },
            feature: "未対応要素型のIn量化".into(),
        });
    }
    Ok(Spec {
        kind: *kind,
        name: &var.name,
        domain: *domain,
        body: *body,
        element: (**element).clone(),
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
