//! 種類ごとの生成・保持・検算を登録する。生成と検算の実装は独立に保つ。
use super::{
    construction_result::{ConstructionData, ConstructionValue},
    environment::Environment,
    result::*,
};
pub(super) trait ResultKind {
    type Input<'a, 'input: 'a>;
    type Output;
    fn compute_and_retain<'a, 'input: 'a>(
        input: Self::Input<'a, 'input>,
    ) -> Result<Self::Output, ValidationFailure>;
    fn validate(
        &self,
        graph: &Graph,
        node: &Node,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure>;
    fn recheck(
        &self,
        env: &Environment<'_>,
        graph: &Graph,
        value: &ConstructionValue,
        limit: usize,
    ) -> Result<(), ValidationFailure>;
}
macro_rules! registered {
    ($data:expr, $method:ident $(, $args:expr)*) => {
        match $data {
            ConstructionData::FiniteLaw(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::PolynomialLaw(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::LawFrame(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::ObjectReadingFrame(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::ViewFamily(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::LawFamily(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::LawInstantiation(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::OutsideLaw(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::ObjectComponents(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::InternalArrows(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::EquationFamily(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::CircuitPattern(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::Build(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::ObjectMap(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::Change(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::Quotient(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::Local(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::ViewInvariant(data) => Some(ResultKind::$method(data $(, $args)*)),
            ConstructionData::PredicateInvariant(data) => Some(ResultKind::$method(data $(, $args)*)),
            _ => None,
        }
    };
}
pub(super) fn validate(
    graph: &Graph,
    node: &Node,
    value: &ConstructionValue,
) -> Option<Result<(), ValidationFailure>> {
    registered!(&value.data, validate, graph, node, value)
}
pub(super) fn recheck(
    env: &Environment<'_>,
    graph: &Graph,
    value: &ConstructionValue,
    limit: usize,
) -> Result<(), ValidationFailure> {
    registered!(&value.data, recheck, env, graph, value, limit).unwrap_or(Ok(()))
}
