//! 検査済みLaw IRの連言走査。結果の数値表現と適用条件は解釈側に置く。
use super::*;

pub(super) trait Interpretation {
    type Output;
    fn value(
        &mut self,
        env: &Environment<'_>,
        id: usize,
        vars: &BTreeMap<String, SourceValue>,
        reading: &str,
        value: &SourceValue,
    ) -> Result<Option<Self::Output>, ValidationFailure>;
    fn bind(
        &mut self,
        env: &Environment<'_>,
        value: usize,
        name: &str,
        vars: &BTreeMap<String, SourceValue>,
        base: &Scope,
        reading: &str,
    ) -> Result<Option<BTreeMap<String, SourceValue>>, ValidationFailure>;
    fn unavailable(&self) -> Self::Output;
    fn combine(&self, left: Self::Output, right: Self::Output) -> Self::Output;
    fn leaf(
        &mut self,
        env: &Environment<'_>,
        id: usize,
        value: &SourceValue,
    ) -> Result<Self::Output, ValidationFailure>;
}

pub(super) fn walk<I: Interpretation>(
    interpreter: &mut I,
    env: &Environment<'_>,
    id: usize,
    vars: &BTreeMap<String, SourceValue>,
    base: &Scope,
    reading: &str,
) -> Result<I::Output, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        env.tick()?;
        let value = env.scoped_ast(id, vars, base, reading)?;
        if let Some(output) = interpreter.value(env, id, vars, reading, &value)? {
            return Ok(output);
        }
        match &env.indexes.inputs.law().program().nodes[id].kind {
            ExprKind::Group(body) => walk(interpreter, env, *body, vars, base, reading),
            ExprKind::Let { name, value, body } => {
                let Some(local) = interpreter.bind(env, *value, &name.name, vars, base, reading)?
                else {
                    return Ok(interpreter.unavailable());
                };
                walk(interpreter, env, *body, &local, base, reading)
            }
            ExprKind::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let left = walk(interpreter, env, *lhs, vars, base, reading)?;
                let right = walk(interpreter, env, *rhs, vars, base, reading)?;
                Ok(interpreter.combine(left, right))
            }
            _ => interpreter.leaf(env, id, &value),
        }
    })
}
