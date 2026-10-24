//! 未実行の原式を同じ型付きASTから多項式へ翻訳する。原式の評価値は生成しない。
use super::*;
use crate::{archmap::Slot, construction::readings::ObjectInstance, law::model::Signature};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone)]
enum Binding {
    Reference {
        snapshot: String,
        subject: String,
    },
    Polynomial(EquationPolynomial),
    Tuple(Vec<Binding>),
    Lexical {
        expression: usize,
        variables: Arc<BTreeMap<String, Binding>>,
    },
}
struct Compiler<'a> {
    inputs: &'a CheckedInputs,
    ring: &'a mut EquationRing,
    variables: BTreeMap<String, Binding>,
}
impl Compiler<'_> {
    // Scalar環への翻訳は使用箇所のcomponent pathが判明してから行う。
    // initializerの環境を保存し、後続letやhelperの局所名を捕獲しない。
    fn lexical(&self, expression: usize) -> Binding {
        Binding::Lexical {
            expression,
            variables: Arc::new(self.variables.clone()),
        }
    }
    fn binding(
        &mut self,
        value: Binding,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<Binding>, ConstructionFailure> {
        tick(c)?;
        match value {
            Binding::Lexical {
                expression,
                variables,
            } => {
                let previous = std::mem::replace(&mut self.variables, (*variables).clone());
                let result = self.expression(expression, path, c);
                self.variables = previous;
                result
            }
            Binding::Tuple(items) if !path.is_empty() => {
                let item = items
                    .get(path[0])
                    .cloned()
                    .ok_or_else(|| bad("原式のtuple束縛が範囲外"))?;
                self.binding(item, &path[1..], c)
            }
            value if path.is_empty() => Ok(Some(value)),
            _ => Ok(None),
        }
    }
    fn field(
        &mut self,
        reference: Binding,
        name: &str,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<Binding>, ConstructionFailure> {
        tick(c)?;
        let Binding::Reference { snapshot, subject } = reference else {
            return Ok(None);
        };
        let selected = self
            .inputs
            .archmap()
            .snapshots
            .iter()
            .find(|s| s.id == snapshot)
            .and_then(|s| s.subjects.iter().find(|s| s.id == subject))
            .ok_or_else(|| bad("原式の固定参照先がない"))?;
        let field = format!("{}.{name}", selected.ty);
        let selected = selected
            .fields
            .iter()
            .find(|f| f.name == field)
            .ok_or_else(|| bad("原式の固定fieldがない"))?;
        if let (Slot::Known { value, .. }, Type::Ref(_) | Type::Owned(..)) =
            (&selected.slot, &selected.ty)
            && let crate::archmap::Value::Ref { snapshot, subject } = value
        {
            return Ok(Some(Binding::Reference {
                snapshot: snapshot.clone(),
                subject: subject.clone(),
            }));
        }
        let mut ty = &selected.ty;
        for &i in path {
            let Type::Tuple(items) = ty else {
                return Ok(None);
            };
            ty = items.get(i).ok_or_else(|| bad("原式fieldの成分が範囲外"))?;
        }
        if ty != &self.ring.ty {
            return Ok(None);
        }
        let observed = match &selected.slot {
            Slot::Known { value, .. } => numeric::from_input(value, &selected.ty, c)
                .map_err(invalid)?
                .and_then(|v| projected(&v, path))
                .map(NumericTransportValue::observed),
            Slot::Missing => None,
        };
        let slot = EquationSlot {
            snapshot,
            subject,
            field,
            component: path.to_vec(),
        };
        let position = if let Some(i) = self.ring.symbols.iter().position(|s| s.slot == slot) {
            if self.ring.symbols[i].value != observed {
                return Err(bad("原式の同じslotに異なる観測値がある"));
            }
            i
        } else {
            if let Some(value) = &observed {
                if let Some(images) = &mut self.ring.evaluation_images {
                    images.push(EquationPolynomial::constant(value.scalar().clone(), c)?);
                }
            } else {
                self.ring.evaluation_images = None;
            }
            self.ring.symbols.push(EquationSymbol {
                slot,
                value: observed,
                // 未実行の式に、架空の元Evaluation参照を与えない。
                readings: vec![],
            });
            self.ring.symbols.len() - 1
        };
        Ok(Some(Binding::Polynomial(EquationPolynomial::variable(
            &self.ring.ty,
            position,
            c,
        )?)))
    }
    fn expression(
        &mut self,
        id: usize,
        path: &[usize],
        c: &mut Control,
    ) -> Result<Option<Binding>, ConstructionFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            let expression = self
                .inputs
                .law()
                .exprs
                .get(id)
                .ok_or_else(|| bad("原式IDがない"))?;
            Ok(match &expression.kind {
                ExprKind::Group(child) => self.expression(*child, path, c)?,
                ExprKind::Int(n) if path.is_empty() => {
                    let ty = self
                        .inputs
                        .law()
                        .expr_type(id)
                        .ok_or_else(|| bad("原式の数値型がない"))?;
                    if ty != &self.ring.ty {
                        return Ok(None);
                    }
                    Some(Binding::Polynomial(EquationPolynomial::constant(
                        numeric::literal(n, ty, c).map_err(invalid)?,
                        c,
                    )?))
                }
                ExprKind::Dotted(names) => {
                    let Some(first) = names.first() else {
                        return Ok(None);
                    };
                    let Some(value) = self.variables.get(&first.name).cloned() else {
                        return Ok(None);
                    };
                    if names.len() == 1 {
                        return self.binding(value, path, c);
                    }
                    let Some(mut value) = self.binding(value, &[], c)? else {
                        return Ok(None);
                    };
                    for (i, name) in names.iter().enumerate().skip(1) {
                        let tail = if i + 1 == names.len() { path } else { &[] };
                        let Some(next) = self.field(value, &name.name, tail, c)? else {
                            return Ok(None);
                        };
                        value = next;
                    }
                    Some(value)
                }
                ExprKind::Field { base, name } => {
                    let Some(value) = self.expression(*base, &[], c)? else {
                        return Ok(None);
                    };
                    self.field(value, &name.name, path, c)?
                }
                ExprKind::Index { base, index, .. } => {
                    let mut component = vec![*index];
                    component.extend(path);
                    self.expression(*base, &component, c)?
                }
                ExprKind::Tuple(items) => {
                    if let Some((&i, tail)) = path.split_first() {
                        self.expression(
                            *items.get(i).ok_or_else(|| bad("原式tupleの成分が範囲外"))?,
                            tail,
                            c,
                        )?
                    } else {
                        let mut values = vec![];
                        for &item in items {
                            let Some(value) = self.expression(item, &[], c)? else {
                                return Ok(None);
                            };
                            values.push(value);
                        }
                        Some(Binding::Tuple(values))
                    }
                }
                ExprKind::Unary {
                    op: UnOp::Neg,
                    operand,
                } => {
                    let Some(Binding::Polynomial(value)) = self.expression(*operand, path, c)?
                    else {
                        return Ok(None);
                    };
                    let zero = EquationPolynomial::constant(
                        numeric::zero(&self.ring.ty, c).map_err(invalid)?,
                        c,
                    )?;
                    Some(Binding::Polynomial(zero.binary(BinOp::Sub, &value, c)?))
                }
                ExprKind::Binary {
                    op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul),
                    lhs,
                    rhs,
                } => {
                    let Some(Binding::Polynomial(left)) = self.expression(*lhs, path, c)? else {
                        return Ok(None);
                    };
                    let Some(Binding::Polynomial(right)) = self.expression(*rhs, path, c)? else {
                        return Ok(None);
                    };
                    Some(Binding::Polynomial(left.binary(*op, &right, c)?))
                }
                ExprKind::Let { name, value, body } => {
                    let value = self.lexical(*value);
                    let previous = self.variables.insert(name.name.clone(), value);
                    let result = self.expression(*body, path, c);
                    if let Some(previous) = previous {
                        self.variables.insert(name.name.clone(), previous);
                    } else {
                        self.variables.remove(&name.name);
                    }
                    result?
                }
                ExprKind::Call { callee, args } => {
                    let mut callee = *callee;
                    while let ExprKind::Group(inner) = self.inputs.law().exprs[callee].kind {
                        tick(c)?;
                        callee = inner;
                    }
                    let span = self.inputs.law().exprs[callee].span;
                    let target = self.inputs.law().infos.iter().find_map(|info| {
                        info.references
                            .iter()
                            .find_map(|(at, name)| (*at == span).then_some(name))
                    });
                    let Some(target) = target else {
                        return Ok(None);
                    };
                    let declaration = self
                        .inputs
                        .law()
                        .declarations
                        .get(target)
                        .ok_or_else(|| bad("原式helperの宣言がない"))?;
                    let Signature::View { params, body, .. } = &declaration.signature else {
                        return Ok(None);
                    };
                    if params.len() != args.len()
                        || params.iter().any(|p| matches!(p.ty, Type::Owned(..)))
                    {
                        return Ok(None);
                    }
                    let mut bindings = BTreeMap::new();
                    for (parameter, argument) in params.iter().zip(args) {
                        let Some(value) = self.expression(*argument, &[], c)? else {
                            return Ok(None);
                        };
                        bindings.insert(parameter.name.clone(), value);
                    }
                    let previous = std::mem::replace(&mut self.variables, bindings);
                    let result = self.expression(*body, path, c);
                    self.variables = previous;
                    result?
                }
                _ => None,
            })
        })
    }
}

pub(super) fn operands(
    inputs: &CheckedInputs,
    instance: &ObjectInstance,
    left: usize,
    right: usize,
    path: &[usize],
    ring: &mut EquationRing,
    c: &mut Control,
) -> Result<Option<(EquationPolynomial, EquationPolynomial)>, ConstructionFailure> {
    let variables = instance
        .bindings()
        .iter()
        .map(|b| {
            (
                b.parameter().name.clone(),
                Binding::Reference {
                    snapshot: b.subject().snapshot.clone(),
                    subject: b.subject().subject.clone(),
                },
            )
        })
        .collect();
    let mut candidate = ring.clone();
    let mut compiler = Compiler {
        inputs,
        ring: &mut candidate,
        variables,
    };
    // shapeは外側のletを除いた左右を指す。元bodyから同じlexical束縛を
    // 順に復元してから翻訳し、局所名を未束縛の原始変数に変えない。
    let Signature::Law { body, .. } = &inputs
        .law()
        .declarations
        .get(&instance.declaration().name)
        .ok_or_else(|| bad("原式のLaw宣言がない"))?
        .signature
    else {
        return Err(bad("原式の宣言がLawでない"));
    };
    let mut cursor = *body;
    loop {
        tick(c)?;
        match &inputs.law().exprs[cursor].kind {
            ExprKind::Group(child) => cursor = *child,
            ExprKind::Let { name, value, body } => {
                let value = compiler.lexical(*value);
                compiler.variables.insert(name.name.clone(), value);
                cursor = *body;
            }
            _ => break,
        }
    }
    let Some(Binding::Polynomial(left)) = compiler.expression(left, path, c)? else {
        return Ok(None);
    };
    let Some(Binding::Polynomial(right)) = compiler.expression(right, path, c)? else {
        return Ok(None);
    };
    *ring = candidate;
    Ok(Some((left, right)))
}
