//! 整数係数の局所診断比較。
use crate::observed::local_result::integer::{linear, read_coefficient, Diagram};
use crate::observed::{change_result::linear_result as wire, integer_fiber};
use num_bigint::BigInt as Z;
fn coefficient_value(v: Z) -> crate::observed::result::Scalar {
    crate::observed::result::Scalar::Z(v)
}
fn diagram(system: &super::super::System) -> Option<&Diagram> {
    system.integer.as_ref()
}
include!("../../local_affine_compare.rs");
