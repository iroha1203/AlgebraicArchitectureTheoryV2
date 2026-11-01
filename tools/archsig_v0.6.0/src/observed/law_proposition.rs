//! 検査済み元Law行の実評価から、通常の成立命題と反例を構成する。
use super::{environment::Environment, law_evaluation as frames, result::*};
use crate::control::Control;
#[derive(Clone, Debug)]
pub(super) struct Reading {
    pub origin: NodeRef,
    pub instance: Option<usize>,
    pub answer: Option<Answer>,
}
pub(super) fn check(
    env: &Environment<'_>,
    graph: &mut Graph,
    origin: NodeRef,
    architecture: NodeRef,
    c: &mut Control,
) -> Result<Reading, ValidationFailure> {
    let Some((row, index)) = frames::prepare_instance(env, graph, origin, architecture, c)? else {
        return Ok(Reading {
            origin,
            instance: None,
            answer: None,
        });
    };
    let record = graph
        .instances
        .get(index)
        .ok_or("元Law判断のinstanceがない")?;
    let request = graph
        .requests
        .get(record.caller.request)
        .ok_or("元Law判断のRequestがない")?
        .clone();
    let declaration = env
        .indexes.inputs
        .law()
        .declarations
        .get(&row.declaration)
        .ok_or("元Law判断の宣言がない")?;
    let answer = super::evaluate::instance_law(env, graph, c, &request, declaration, index)?;
    Ok(Reading {
        origin,
        instance: Some(index),
        answer: Some(answer),
    })
}
#[cfg(test)]
mod tests;
