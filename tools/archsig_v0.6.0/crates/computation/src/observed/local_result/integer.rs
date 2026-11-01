//! 整数係数の局所状態と診断。
mod wire {
    pub(super) use crate::observed::change_result::linear_result::{
        domain, map, module, smith as certificate, vector,
    };
}
use crate::observed::environment::{change_affine, local_read};
use crate::observed::integer_fiber::{self, Matrix};
use num_bigint::BigInt as Z;
pub(in crate::observed::local_result) fn coefficient_type() -> archsig_common::types::Type {
    archsig_common::types::Type::Z
}
pub(in crate::observed::local_result) fn coefficient_name() -> &'static str {
    "Z"
}
pub(in crate::observed::local_result) fn coefficient_value(
    v: Z,
) -> crate::observed::result::Scalar {
    crate::observed::result::Scalar::Z(v)
}
pub(in crate::observed::local_result) fn read_coefficient(
    v: &crate::observed::result::Scalar,
) -> Result<Z, crate::observed::result::ValidationFailure> {
    match v {
        crate::observed::result::Scalar::Z(v) => Ok(v.clone()),
        _ => Err("整数読取りの係数がZでない".into()),
    }
}
fn reduce_torsion(v: &mut Z, m: &Z) {
    *v = ((&*v % m) + m) % m;
}
fn save_diagram(system: &mut super::System, diagram: Diagram) {
    system.integer = Some(diagram);
}
include!("../local_affine.rs");
