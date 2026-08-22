# atlas-reduction-toy

還元(G-107 (i): law 全量化 → 有限個の非空領域 `A`)を、外部ライブラリなしの
ℚ 線形代数で見せる説明用の玩具。証拠ではない。定理の正本は
[G-107 report](../../reports/G-107-aat-uniform-invariance-characterization.md) と Lean。
設計意図と読み方は
[docs/note/n1006_aat_atlas_reinforcement_plan.md](../../../docs/note/n1006_aat_atlas_reinforcement_plan.md) §7。

```bash
python3 depth_map_toy.py
```

系 A(4 サービス 11 モジュール 3 概念)と系 B(サービス内部の輪が 2 概念に
またがる変種)について、配線だけから領域ごとの `J_A = (phantom, hidden)` を
計算し、観点(law)を入れた直接計算が深さマップの値の和に一致することを確認する。
