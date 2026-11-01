//! Q係数の局所診断比較。
use crate::observed::local_result::rational::{
    Diagram, Z, integer_fiber, linear, read_coefficient, wire,
};
fn coefficient_value(v: Z) -> crate::observed::result::Scalar {
    v.scalar()
}
fn diagram(system: &super::super::System) -> Option<&Diagram> {
    system.rational.as_ref()
}
include!("../../local_affine_compare.rs");
