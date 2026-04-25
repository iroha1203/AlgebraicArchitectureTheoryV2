# spectral radius bridge 設計

Lean status: `future proof obligation` / design decision.

Issue [#79](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/79)
の設計判断として、`rho(A)` は既存の `NatMatrix` bridge や
`nilpotencyIndex` axis には混ぜず、mathlib 依存を持つ解析的拡張として分離する。

## 決定

既存 Lean core は、有限 `ComponentUniverse` 上の自然数値 adjacency power を使う。

```text
NatMatrix C := C -> C -> Nat
adjacencyPowerEntry U k c d
AdjacencyNilpotent U
```

これは `A^k` の entry と長さ `k` の `Walk` の存在を接続するための
count-preserving bridge であり、`Decomposable` の定義には入れない。

spectral radius 側では、この `NatMatrix` を直接拡張せず、有限 list を添字化した
正方行列へ写す別の bridge を置く。

```text
SpectralIndex U := Fin U.components.length
spectralAdjacencyMatrix U : Matrix (SpectralIndex U) (SpectralIndex U) Complex
rho(A) := spectral radius of A over Complex
```

係数体は最初から `Complex` とする。実数非負行列として始めると、固有値や
spectral radius の標準補題で結局 `Complex` 化が必要になるためである。

このリポジトリの現在の `lakefile.toml` は mathlib 依存を持たない。したがって
`rho(A)` bridge theorem の実装 PR では、mathlib を導入するか、mathlib 依存を持つ
別パッケージに切り出すかを最初に決める。#79 では Lean core に半端な独自
spectral radius 定義を追加しない。

## theorem statement の分割

`rho(A)` に関する theorem は、次の 2 つに分割する。

1. `DAG -> rho(A) = 0`
2. `cycle -> rho(A) > 0`

同一 Issue で扱わない。前者は nilpotence から spectral radius 0 への標準線形代数
補題に依存する。後者は非空閉 walk から正の spectral radius を得る補題に依存し、
Perron-Frobenius 型の事実や trace / diagonal entry の評価が必要になる可能性がある。

後続 Issue:

- [#94](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/94):
  `DAG` / adjacency nilpotence から `rho(A) = 0` への bridge theorem。
- [#95](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/95):
  cycle / closed walk から `rho(A) > 0` への bridge theorem。

## empirical claim との分離

`rho(A)` を変更波及や障害伝播の増幅指標として読む主張は
`empirical hypothesis` とする。Lean theorem が扱うのは有限 adjacency matrix の
構造的事実だけであり、障害修正コスト、変更コスト、運用リスクとの相関は
実証プロトコル側で検証する。

したがって Signature v1 では、現時点で次の境界を維持する。

| 軸 | 扱い | Lean status |
| --- | --- | --- |
| `nilpotencyIndex` | finite `ComponentUniverse` 上の executable matrix bridge axis | `defined only` / `proved` |
| `rho(A)` | mathlib-backed spectral bridge の後続候補 | `future proof obligation` |
| `rho(A)` と変更・障害コストの関係 | 実データで検証する研究仮説 | `empirical hypothesis` |

## Lean core へ入れないもの

- `Decomposable` の定義への spectral condition の混入。
- `ArchitectureSignatureV1.nilpotencyIndex` への `rho(A)` の混入。
- mathlib なしの独自 spectral radius 定義。
- 実証上の増幅解釈を Lean theorem として主張すること。
