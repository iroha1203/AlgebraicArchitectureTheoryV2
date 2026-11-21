//! 多項式・ideal 計算核のモジュール境界（Step 2 で実装）。
//!
//! 責務:
//! - Z / Q / F_p 上の単項式・多変数多項式と単項式順序
//! - Q 上の Gröbner 基底、ideal 所属判定と witness（`f = sum h_i f_i`）
//! - Rabinowitsch 補助式 `u * g - 1 = 0` による可逆条件処理と代数閉包空性判定（`1 in I`）
//! - 商環上の ideal 所属判定（ambient 零へ強めない）
//! - Z / Q アフィン系および F_p 有限全列挙
//! - 座標面支持による相互作用参加変数数 r と極小不成立部分族（G-141 F11–F12）

/// 単項式順序の種別。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MonomialOrder {
    /// Graded reverse lexicographic order（既定の Gröbner 基底順序）。
    Grevlex,
    /// Lexicographic order（消去・逐次復元用）。
    Lex,
}
