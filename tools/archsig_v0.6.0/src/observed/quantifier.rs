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
        ast::{ExprKind, QuantDomain, QuantKind, QuantSplit, TypeAst},
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
    pub domain_type: Type,
    pub owners: Vec<OwnerLeaf>,
    pub type_span: Option<(usize, usize)>,
}
pub(super) struct OwnerLeaf {
    pub entity: String,
    pub name: String,
    pub span: (usize, usize),
    pub type_span: (usize, usize),
    pub root: String,
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
    let mut domain_type = element.clone();
    let mut owners = Vec::new();
    let mut type_span = None;
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
        QuantDomain::Type(original) => {
            if has_owner(original, control)? {
                domain_type = restore_owned_type(law, original, element, &mut owners, control)?;
            }
            type_span = Some(original.span());
            (None, finite::supported(element, law, control)?)
        }
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
        domain_type,
        owners,
        type_span,
    })
}

fn restore_owned_type(
    law: &CheckedLaw,
    original: &TypeAst,
    erased: &Type,
    owners: &mut Vec<OwnerLeaf>,
    control: &Control,
) -> Result<Type, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
        let ty = match (original, erased) {
            (TypeAst::Named { name, index, span }, Type::Ref(entity) | Type::Data(entity)) => {
                let mut resolved = None;
                for info in &law.infos {
                    control.clone().checkpoint(Checkpoint::FiniteIteration)?;
                    for (at, target) in &info.references {
                        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
                        if *at == name.span()
                            && resolved
                                .replace(target.clone())
                                .is_some_and(|old| old != *target)
                        {
                            return Err("型量化の元静的解決名が一意でない".into());
                        }
                    }
                }
                if resolved.as_ref() != Some(entity) {
                    return Err("型量化の元TypeAst名と消去型が違う".into());
                }
                if let Some(index) = index {
                    let root = match law
                        .definitions
                        .declarations
                        .get(entity)
                        .map(|d| &d.signature)
                    {
                        Some(
                            crate::definition::PrimitiveSignature::Entity {
                                owner: Some(root), ..
                            }
                            | crate::definition::PrimitiveSignature::Arrow { owner: root, .. },
                        ) => root.clone(),
                        _ => return Err("Owned型leafの元宣言に根ownerがない".into()),
                    };
                    if erased != &Type::Ref(entity.clone()) {
                        return Err("Owned型leafの元型がRefでない".into());
                    }
                    owners.push(OwnerLeaf {
                        entity: entity.clone(),
                        name: index.name.clone(),
                        span: index.span,
                        type_span: *span,
                        root,
                    });
                    Type::Owned(entity.clone(), index.name.clone())
                } else {
                    erased.clone()
                }
            }
            (TypeAst::Tuple(items, _), Type::Tuple(types)) if items.len() == types.len() => {
                let mut restored = Vec::new();
                for (item, ty) in items.iter().zip(types) {
                    restored.push(restore_owned_type(law, item, ty, owners, control)?);
                }
                Type::Tuple(restored)
            }
            (TypeAst::Option(item, _), Type::Option(ty)) => Type::Option(Box::new(
                restore_owned_type(law, item, ty, owners, control)?,
            )),
            (TypeAst::Set(item, _), Type::Set(ty)) => Type::Set(Box::new(restore_owned_type(
                law, item, ty, owners, control,
            )?)),
            (TypeAst::List(item, _), Type::List(ty)) => Type::List(Box::new(restore_owned_type(
                law, item, ty, owners, control,
            )?)),
            (TypeAst::Map(key, value, _), Type::Map(from, to)) => Type::Map(
                Box::new(restore_owned_type(law, key, from, owners, control)?),
                Box::new(restore_owned_type(law, value, to, owners, control)?),
            ),
            (TypeAst::Builtin(builtin, _), _) => {
                let expected = match builtin {
                    crate::law::ast::Builtin::Unit => Type::Unit,
                    crate::law::ast::Builtin::Bool => Type::Bool,
                    crate::law::ast::Builtin::Z => Type::Z,
                    crate::law::ast::Builtin::Q => Type::Q,
                    crate::law::ast::Builtin::Text => Type::Text,
                };
                if &expected != erased {
                    return Err("元型量化のBuiltinと消去型が違う".into());
                }
                expected
            }
            (TypeAst::Fp { modulus, .. }, _) => {
                let expected = Type::Fp(modulus.clone());
                if &expected != erased {
                    return Err("元型量化のFpと消去型が違う".into());
                }
                expected
            }
            _ => {
                return Err(ValidationFailure::UnsupportedExpression {
                    location: Location::Law {
                        span: original.span(),
                    },
                    feature: "Ownedを含む未対応の型全域量化".into(),
                });
            }
        };
        if ty.erase() != *erased {
            return Err("元Owned型の復元と消去後binder型が違う".into());
        }
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
        Ok(ty)
    })
}
pub(super) fn has_owner(original: &TypeAst, control: &Control) -> Result<bool, ValidationFailure> {
    let mut pending = vec![original];
    while let Some(ty) = pending.pop() {
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
        match ty {
            TypeAst::Named { index: Some(_), .. } => return Ok(true),
            TypeAst::Tuple(types, _) => pending.extend(types),
            TypeAst::List(element, _) | TypeAst::Set(element, _) | TypeAst::Option(element, _) => {
                pending.push(element)
            }
            TypeAst::Map(key, value, _) => pending.extend([key.as_ref(), value.as_ref()]),
            TypeAst::Term(arguments, returns, _) => {
                pending.extend(arguments);
                pending.push(returns);
            }
            _ => {}
        }
        control.clone().checkpoint(Checkpoint::FiniteIteration)?;
    }
    Ok(false)
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
