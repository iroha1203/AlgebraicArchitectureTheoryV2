//! ArchSig v0.6.0。共通Atom定義を参照するLawとArchMapを検査し、型付きの結果を返す。

#[cfg(test)]
extern crate self as archsig;

pub mod archmap;
pub mod canonical;
pub mod construction;
pub mod control;
pub mod definition;
pub mod input;
pub mod issue;
pub mod json;
pub mod law;
pub(crate) mod names;
pub use names::QualifiedName;
pub mod observed;
pub mod prime;
pub mod result;
pub mod run;
pub mod types;
