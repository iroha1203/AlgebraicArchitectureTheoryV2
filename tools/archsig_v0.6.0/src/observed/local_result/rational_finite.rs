//! 有限作用のQ状態を既存の有理数fiberへ接続する。
use super::rational_geometry as geometry;
use super::*;
fn split_diagram(
    d: Option<rational::Diagram>,
) -> (Option<integer::Diagram>, Option<rational::Diagram>) {
    (None, d)
}
include!("../local_finite_build.rs");
