# G-104 条件 C ハント

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**

Issue #3912 のための有限列挙器である。G-104 の GOAL カード、tracking Issue #3902 の
proof state、`research/reports/`、`research/lean/ResearchLean/` は変更しない。

## 結論

停止条件 **B（自由係数近似における構造的否定）** に到達した。

暫定候補 `C0–C5 + self-loop endpoint reflection` は、定数座標係数の bounded
normal form 6,086 件では反例を持たず、非退化正例と7条項の独立反例を持つ。一方、
同一 incidence data の cellwise 自由係数だけを変えると、比較写像が同型の例と
非同型の例を同時に作れる。特に fine 側の非零係数座標を複製すると、incidence を
一切変えずに `H¹` の余分な直和成分が生じる。このため、自由係数を無制限に許す
近似では incidence-only の条件 C は同型を強制できない。

この否定は law 由来係数での実現可能性を確認していない。したがって G-104 の
target theorem の反証、条件 C の確定、proof state の変更には使わない。

## ファイル

- `condition_hunt.py`: 有理数上の exact linear algebra、3件の calibration fixture、
  nerve / nerve 射の全数探索、cellwise 係数探索を実装する。
- `test_condition_hunt.py`: calibration、非退化発火、条項独立性、構造的否定の回帰テスト。
- `results.json`: 既定 bound での決定的な実行結果。
- `hunt-report.md`: 全ラウンド、最終判定、手証明スケッチ、独立性、coverage limit。

## 計算モデル

有限 nerve は chart、向き付き edge、向き付き face からなる。face
`(e₀,e₁,e₂)` の境界を `e₀ - e₁ + e₂` とし、次を満たすデータだけを受理する。

```text
d₀(x)(e) = x(right(e)) - x(left(e))
d₁(y)(f) = y(e₀) - y(e₁) + y(e₂)
d₁ ∘ d₀ = 0
H¹ = ker(d₁) / im(d₀)
```

nerve 射の mapped cell は coarse cell の cochain を pullback し、degenerate edge / face
では零にする。kernel、image、comparison rank はすべて `fractions.Fraction` による
exact Gaussian elimination で計算する。

reading comparison には review 済みの proper adequate pair を固定する。canonical factor
`π : Fin 4 → Fin 3` は `(0, 0, 1, 2)` で、nerve chart map `φ` とは別データ・別 assertion
として検査する。Target support も係数座標 support から分離し、C0 は actual Target 上の
`π`-像で判定する。非退化正例の3座標は、同じ pair の非定数 law descent の実値から生成する。

C3 の条項自体は「fiber 1-cycle が internal face boundaries で張られる」という
incidence 文であり、コード内の `H¹` 次元計算は有限データ上でその文を判定する手段に
すぎない。cohomology の消滅を候補条件として追加してはいない。

係数には二つの層がある。

1. 定数座標層: 全 cell が同じ自由 `ℚ`-rank 1 または2を持ち、座標 pullback は恒等。
2. cellwise 層: 各 cell の次元は、その support に含まれる自由座標数。edge support は
   両 endpoint support の共通部分、face support は3 boundary edge support の共通部分に
   含め、係数写像を座標ごとの零写像または恒等写像として全数列挙する。

## 再現手順

リポジトリ root から実行する。

```bash
python3 research/experiments/g104-condition-hunt/condition_hunt.py calibrate
python3 research/experiments/g104-condition-hunt/condition_hunt.py coefficients
python3 -m unittest discover \
  -s research/experiments/g104-condition-hunt -p 'test_*.py' -v
python3 research/experiments/g104-condition-hunt/condition_hunt.py run \
  --output research/experiments/g104-condition-hunt/results.json
```

既定の定数座標探索 bound は coarse chart `≤ 3`、edge `≤ 4`、face `≤ 1`、
fine chart `≤ 4`、係数 rank `≤ 2` である。112,562 refinement を生成し、候補を満たす
3,043 refinement × 2 ranks = 6,086 件を判定する。cellwise 探索は固定した一つの
非退化 incidence comparison 上で、1座標の fine edge / face 次元 `0/1` の全72件を
判定する。

結果の解釈と探索空間の正確な normal form は `hunt-report.md` を参照する。
