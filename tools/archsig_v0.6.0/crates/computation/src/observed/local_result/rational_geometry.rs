//! 同じ局所構成をQ上の正確な計算で行う。
pub(super) use super::geometry::{Finite, FiniteSide, Local, Projection, Support};
use super::rational as integer;
use super::*;
#[path = "../local_finite_state.rs"]
mod finite_state;
mod mixed_equation {
    use super::*;
    use crate::observed::local_result::rational::{Z, change_affine, integer_fiber, wire};
    use integer_fiber::Matrix;
    use num_traits::Zero;
    include!("../local_mixed_equation.rs");
}
mod mixed_read {
    use super::*;
    use crate::observed::local_result::rational::{Z, change_affine, integer_fiber::Matrix};
    use integer::linear::Reading;
    use num_traits::Zero;
    include!("../local_mixed_read.rs");
}
pub(super) use mixed_read::Information;
include!("../local_geometry_build.rs");
