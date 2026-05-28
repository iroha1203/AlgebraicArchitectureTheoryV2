# 2026-05-09 first-class docs archive

このディレクトリには、第一級文書を次の 3 文書へ固定した後に、
後方互換のためだけに残っていた facade 文書を退避する。

現行の第一級文書:

1. [AAT 数学理論](../../aat/mathematical_theory/README.md)
2. [AAT / SFT Interface](../../sft/aat_interface.md)
3. [ソフトウェアの場の理論](../../sft/software_field_theory.md)

現行の status / ledger:

- [証明義務と実証仮説](../../aat/proof_obligations.md)
- [Lean 定義・定理索引](../../aat/lean_theorem_index.md)

`math_README.md` は、第一級文書への薄い索引だけになっていた `docs/math/README.md` を
退避したものである。

`prd_README.md` と PRD 本文は、tooling 構想の履歴として残す。
現行の要求・設計は、対象に応じて `docs/aat/`, `docs/sft/`, `docs/tool/`,
または GitHub Issues へ分解して管理する。

`aat_chaos_game_dynamics_memo.md` は、SFT へ整理する前の chaos-game / dynamics 研究メモである。
現行の力学・場・予測・制御の本文は [ソフトウェアの場の理論](../../sft/software_field_theory.md) に置く。

`flatness_obstruction_lean_design.md` と `lean_module_organization.md` は、
零曲率 theorem package と Lean module 移行の過去設計メモである。
現行の Lean status と主要 API は [証明義務と実証仮説](../../aat/proof_obligations.md) と
[Lean 定義・定理索引](../../aat/lean_theorem_index.md) で確認する。

`design/` は、旧 `docs/design/` にあった既存 design note 群を退避したものである。
今後の design 系文書は、対象に応じて `docs/aat/`, `docs/sft/`, `docs/tool/`,
または GitHub Issues に置く。

`empirical/` は、旧 `docs/empirical/` にあった empirical pilot と case-study skeleton を
退避したものである。現行の empirical hypothesis は
[証明義務と実証仮説](../../aat/proof_obligations.md) と GitHub Issues で管理する。

この archive 内の facade、薄い索引、旧 PRD、旧 memo、旧 design note、旧 empirical pilot は、
旧リンクの歴史的記録であり、現行入口としては使わない。
