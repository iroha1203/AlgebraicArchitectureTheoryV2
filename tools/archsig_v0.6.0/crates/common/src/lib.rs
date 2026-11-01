//! 共通の型・canonical表現・入力診断・中断制御。
#[cfg(test)]
extern crate self as archsig_common;
pub mod canonical;
pub mod control;
pub mod internal;
pub mod issue;
pub mod json;
pub mod names;
pub mod prime;
pub mod types;
pub use names::QualifiedName;
