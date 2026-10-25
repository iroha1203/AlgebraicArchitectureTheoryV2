//! Q係数の局所状態。整数の整除性を使わず、正確な体上の消去を使う。
#[path = "local_rational_number.rs"]
mod number;
use crate::observed::environment::local_read;
pub(super) use number::Q as Z;
#[path = "local_rational_fiber.rs"]
pub(super) mod integer_fiber;
use integer_fiber::Matrix;
#[path = "local_rational_action.rs"]
pub(super) mod change_affine;
#[path = "local_rational_wire.rs"]
pub(super) mod wire;
pub(in crate::observed::local_result) fn coefficient_type() -> crate::types::Type {
    crate::types::Type::Q
}
pub(in crate::observed::local_result) fn coefficient_name() -> &'static str {
    "Q"
}
pub(in crate::observed::local_result) fn coefficient_value(v: Z) -> crate::observed::result::Scalar {
    v.scalar()
}
pub(in crate::observed::local_result) fn read_coefficient(v: &crate::observed::result::Scalar) -> Result<Z,crate::observed::result::ValidationFailure> {
    Z::from_scalar(v)
}
fn reduce_torsion(_: &mut Z, _: &Z) {
    unreachable!("体上の商にtorsionはない")
}
fn save_diagram(system: &mut super::System, diagram: Diagram) {
    system.rational = Some(diagram);
}
include!("local_affine.rs");
