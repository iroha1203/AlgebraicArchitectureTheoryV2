//! ArchSig CLIと既存のライブラリ経路。各層の実装は一方向の別クレートに置く。
#[cfg(test)]
extern crate self as archsig;
pub use archsig_computation::{
    QualifiedName, archmap, canonical, construction, control, definition, input, issue, json, law,
    names, observed, prime, result, types,
};
pub mod run;
