//! 検査済み入力からの構成と観測計算。CLIには依存しない。
#[cfg(test)]
extern crate self as archsig_computation;
pub mod construction;
pub mod observed;
mod owner_completion;
