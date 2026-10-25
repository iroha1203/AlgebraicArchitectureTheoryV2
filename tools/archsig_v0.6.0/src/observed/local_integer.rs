//! 整数係数の局所状態と診断。
mod wire { pub(super) use crate::observed::change_result::linear_result::{module, map, vector, domain, smith as certificate}; }
use crate::observed::environment::{change_affine, local_read};
use crate::observed::integer_fiber::{self, Matrix};
use num_bigint::BigInt as Z;
fn coefficient_type() -> crate::types::Type {
    crate::types::Type::Z
}
fn coefficient_name() -> &'static str {
    "Z"
}
fn coefficient_value(v: Z) -> crate::observed::result::Scalar {
    crate::observed::result::Scalar::Z(v)
}
fn read_coefficient(v: &crate::observed::result::Scalar) -> Result<Z,crate::observed::result::ValidationFailure> {
    match v {crate::observed::result::Scalar::Z(v)=>Ok(v.clone()),_=>Err("整数読取りの係数がZでない".into())}
}
fn reduce_torsion(v: &mut Z, m: &Z) {
    *v = ((&*v % m) + m) % m;
}
fn save_diagram(system: &mut super::System, diagram: Diagram) {
    system.integer = Some(diagram);
}
include!("local_affine.rs");
