//! 支持contextと有限局所系。係数計算は整数実装を使う。
use super::*;
#[path = "../local_finite_state.rs"] mod finite_state;
mod mixed_equation {
    use super::*;
    use crate::observed::change_result::linear_result as wire;
    use crate::observed::{environment::change_affine, integer_fiber::{self,Matrix}};
    use num_bigint::BigInt as Z;
    use num_traits::Zero;
    include!("../local_mixed_equation.rs");
}
mod mixed_read {
    use super::*;
    use crate::observed::{environment::change_affine, integer_fiber::Matrix};
    use integer::linear::Reading;
    use num_bigint::BigInt as Z;
    use num_traits::Zero;
    include!("../local_mixed_read.rs");
}
pub(super) use mixed_read::Information;
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct Support {
    pub carrier: Vec<Json>,
    pub positions: Vec<Fact>,
    pub visible: Vec<Fact>,
}
impl Support {
    pub(super) fn contains(&self, other: &Self) -> bool {
        other.carrier.iter().all(|v| self.carrier.contains(v))
            && other.positions.iter().all(|v| self.positions.contains(v))
            && other.visible.iter().all(|v| self.visible.contains(v))
    }
    pub(super) fn intersect(&self, other: &Self) -> Self {
        Self {
            visible: self
                .visible
                .iter()
                .filter(|v| other.visible.contains(v))
                .cloned()
                .collect(),
            carrier: self
                .carrier
                .iter()
                .filter(|v| other.carrier.contains(v))
                .cloned()
                .collect(),
            positions: self
                .positions
                .iter()
                .filter(|v| other.positions.contains(v))
                .cloned()
                .collect(),
        }
    }
}
pub(in crate::observed) struct Projection {
    pub read: usize,
    pub path: Vec<usize>,
    pub arguments: Vec<NodeRef>,
    pub field: Option<(Scalar, Location)>,
    pub values: Vec<Scalar>,
    pub ty: Type,
    pub support: Support,
}
pub(super) struct Local {
    pub support: Support,
    pub instances: Vec<Json>,
    pub arguments: Vec<NodeRef>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FiniteSide {
    pub global: NodeRef,
    pub domain: NodeRef,
    pub solution_domain: NodeRef,
    pub values: Vec<(Scalar, NodeRef)>,
    pub matching: Vec<Scalar>,
    pub matching_type: Type,
    pub all: NodeRef,
    pub checked: usize,
    pub restriction: Vec<(NodeRef, Scalar)>,
    pub parameters: Vec<(NodeRef, Vec<NodeRef>)>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Finite {
    pub semantic: FiniteSide,
    pub equation: Option<FiniteSide>,
}
include!("../local_geometry_build.rs");
