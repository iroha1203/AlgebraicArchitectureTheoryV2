//! 同じ局所構成をQ上の正確な計算で行う。
use super::*;
use super::rational as integer;
pub(super) use super::geometry::{Support,Projection,Local,FiniteSide,Finite};
#[path = "../local_finite_state.rs"] mod finite_state;
mod mixed_equation {
    use super::*;
    use crate::observed::local_result::rational::{wire, change_affine, integer_fiber, Z};
    use integer_fiber::Matrix;
    use num_traits::Zero;
    include!("../local_mixed_equation.rs");
}
mod mixed_read {
    use super::*;
    use crate::observed::local_result::rational::{change_affine, integer_fiber::Matrix, Z};
    use integer::linear::Reading;
    use num_traits::Zero;
    include!("../local_mixed_read.rs");
}
pub(super) use mixed_read::Information;
include!("../local_geometry_build.rs");
