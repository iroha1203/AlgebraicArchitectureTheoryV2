//! SHIGURE 原始表示・多項式条件付き解空間・意味保存変更・相互作用解析クレート。
//!
//! 依存の向きは `archsig-common` / `archsig-input` → `archsig-shigure` → `archsig` とし、
//! 既存の `crates/computation/src/observed/` には依存しない独立境界を保つ。

pub mod algebra;
pub mod convert;
pub mod ir;
pub mod solver;
