//! 元導出から得た多項式の正確な正規化。原式の評価は既存Evaluatorが担う。
use super::{
    control::{Checkpoint, Control},
    numeric,
    numeric_transport::NumericTransportValue,
    result::{Scalar, ValidationFailure},
};
use crate::{construction::ConstructionFailure, law::ast::BinOp, types::Type};
use std::collections::BTreeMap;

pub(super) fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::EquationPresentation)
        .map_err(Into::into)
}
pub(super) fn invalid(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => s.into(),
        f => ConstructionFailure::Inconsistent(format!("方程式表示の数値演算: {f:?}")),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationMonomial {
    /// 同じringのsymbols()の添字。重複は冪、空列は定数項。
    pub variables: Vec<usize>,
    pub coefficient: NumericTransportValue,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationPolynomial {
    pub ty: Type,
    /// 辞書順、係数零の項を除く。零多項式は空列。
    pub terms: Vec<EquationMonomial>,
}
impl EquationPolynomial {
    pub(super) fn constant(s: Scalar, c: &mut Control) -> Result<Self, ConstructionFailure> {
        tick(c)?;
        let zero = numeric::zero(&s.ty(), c).map_err(invalid)?;
        Ok(Self {
            ty: s.ty(),
            terms: if s == zero {
                vec![]
            } else {
                vec![EquationMonomial {
                    variables: vec![],
                    coefficient: NumericTransportValue::observed(s),
                }]
            },
        })
    }
    pub(super) fn variable(
        ty: &Type,
        index: usize,
        c: &mut Control,
    ) -> Result<Self, ConstructionFailure> {
        tick(c)?;
        Ok(Self {
            ty: ty.clone(),
            terms: vec![EquationMonomial {
                variables: vec![index],
                coefficient: NumericTransportValue::observed(
                    numeric::literal("1", ty, c).map_err(invalid)?,
                ),
            }],
        })
    }
    pub(super) fn binary(
        &self,
        op: BinOp,
        rhs: &Self,
        c: &mut Control,
    ) -> Result<Self, ConstructionFailure> {
        tick(c)?;
        if self.ty != rhs.ty {
            return Err(ConstructionFailure::Inconsistent(
                "多項式の係数環が違う".into(),
            ));
        }
        let zero = numeric::zero(&self.ty, c).map_err(invalid)?;
        let mut terms = BTreeMap::<Vec<usize>, Scalar>::new();
        let mut add =
            |vars: Vec<usize>, s: Scalar, c: &mut Control| -> Result<(), ConstructionFailure> {
                tick(c)?;
                let old = terms.remove(&vars).unwrap_or_else(|| zero.clone());
                let sum = numeric::binary(BinOp::Add, &old, &s, c).map_err(invalid)?;
                if sum != zero {
                    terms.insert(vars, sum);
                }
                tick(c)
            };
        match op {
            BinOp::Add | BinOp::Sub => {
                for t in &self.terms {
                    add(t.variables.clone(), t.coefficient.scalar().clone(), c)?;
                }
                for t in &rhs.terms {
                    let coefficient = if op == BinOp::Sub {
                        numeric::binary(BinOp::Sub, &zero, t.coefficient.scalar(), c)
                            .map_err(invalid)?
                    } else {
                        t.coefficient.scalar().clone()
                    };
                    add(t.variables.clone(), coefficient, c)?;
                }
            }
            BinOp::Mul => {
                for a in &self.terms {
                    for b in &rhs.terms {
                        tick(c)?;
                        let mut variables = Vec::new();
                        let (mut i, mut j) = (0, 0);
                        while i < a.variables.len() || j < b.variables.len() {
                            tick(c)?;
                            if j == b.variables.len()
                                || (i < a.variables.len() && a.variables[i] <= b.variables[j])
                            {
                                variables.push(a.variables[i]);
                                i += 1;
                            } else {
                                variables.push(b.variables[j]);
                                j += 1;
                            }
                        }
                        add(
                            variables,
                            numeric::binary(
                                BinOp::Mul,
                                a.coefficient.scalar(),
                                b.coefficient.scalar(),
                                c,
                            )
                            .map_err(invalid)?,
                            c,
                        )?;
                    }
                }
            }
            _ => return Err(ConstructionFailure::Inconsistent("多項式でない演算".into())),
        }
        Ok(Self {
            ty: self.ty.clone(),
            terms: terms
                .into_iter()
                .map(|(variables, coefficient)| EquationMonomial {
                    variables,
                    coefficient: NumericTransportValue::observed(coefficient),
                })
                .collect(),
        })
    }
    pub(super) fn evaluate(
        &self,
        values: &[Option<NumericTransportValue>],
        c: &mut Control,
    ) -> Result<Option<NumericTransportValue>, ConstructionFailure> {
        let mut result = numeric::zero(&self.ty, c).map_err(invalid)?;
        for term in &self.terms {
            tick(c)?;
            let mut value = term.coefficient.scalar().clone();
            for &index in &term.variables {
                tick(c)?;
                let Some(Some(argument)) = values.get(index) else {
                    return Ok(None);
                };
                if argument.ty() != self.ty {
                    return Err(ConstructionFailure::Inconsistent(
                        "代入の係数環が違う".into(),
                    ));
                }
                value =
                    numeric::binary(BinOp::Mul, &value, argument.scalar(), c).map_err(invalid)?;
            }
            result = numeric::binary(BinOp::Add, &result, &value, c).map_err(invalid)?;
        }
        Ok(Some(NumericTransportValue::observed(result)))
    }
}
