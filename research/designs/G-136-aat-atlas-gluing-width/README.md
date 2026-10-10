# G-136：二領域の診断欠損と観測幅

研究目的・固定target・完了条件は[GOALカード](../../goals/G-136-aat-atlas-gluing-width.md)にある。
本設計は、原始セルからの構成経路、証明の依存、既存APIとの接続を定める。

| 文書 | 内容 |
| --- | --- |
| [完全列](exact-sequence.md) | セル交差、cochain/錐SES、Q/P比較、phantom/hiddenの式 |
| [幅と指定例](witnesses.md) | 原始Source・reading・台・部分セル比較、全kの証明方針、Law幅 |
| [再利用対応](reuse-map.md) | 参照版、実宣言の型と仮定、接続補題、新規構成、G-130との差 |

## 1. 構成の順序

```text
Source / reading / K1台 / 原始部分incidence比較
  → 各領域の既存targetSubsetComplex + 真のセル交差複体
  → セル評価による短完全列と粗細可換図式
  → 標準錐のSES・LES / H⁰,H¹のMV列
  → Q/Pの短完全列比較・snake → 同じT_Uの核・余核
  → 実blockDefect・Law値分解 / G-135の同じ固定X分解
```

幅の指定族は、この経路へ原始表を入力する。H¹やJを指定値として入力する構成は採らない。
初回の対象は二領域と支持幅である。多領域spectral sequence、半径、計算量の問題は
それぞれの入力と目標を定める別の研究に属する。ArchSigの観測・法入力や実装受入条件は
このAAT定理群の証明義務へ追加しない。

## 2. 新しいセル選択の表現

既存 `ChartInTargetSubset` 等は、一つのtarget部分集合と台の交わりを表す。
新たに三次数の元セル述語とincidence閉性を持つ選択を用意すると、和と交差を扱える。
閉性は、所属辺の両端、所属面の三つの辺に対して要求する。
全セル名とincidenceの出現位置を残し、loop・平行辺・重複slotを商で消さない。

これは設計上の内部表現であり、閉性を新しい数学的仮定にしない。
`N_A` の閉性はK1から、和・交差の閉性は各選択の閉性から生成する。
交差の選択述語は

```math
\mathrm{Selected}_A(\sigma)\land\mathrm{Selected}_B(\sigma),\qquad
\mathrm{Selected}_X(\sigma)\iff\exists t\in S(\sigma),\ t\in X.
```

所属証拠はproof dataであり、二つの証拠の組を新しいセル名にしない。
cochainは選択された元セル上の関数とし、元の符号付き微分を制限する。
通常の `N_X` で既存 `targetSubsetComplex` と三次数・微分を同定する。
交差上でchart台から辺を再生成すると、元の選択と異なる辺を入れるおそれがあるため、
交差の辺・面は元セルの積述語で選ぶ。

部分セル比較Mの制限は、mappedセルのK1台輸送をAとBの両所属証拠に適用して作る。
`none` は元の零写像を保持する。退化面の自由加群零和も同じセル名で移送する。
比較のchain条件や交差制限の可換性を別fieldとして受け取らない。

## 3. 実装単位と接続義務

以下は予定moduleであり、実装済み宣言の一覧ではない。

| 順 | 予定module | 成果と先行依存 |
| --- | --- | --- |
| 1 | `CellSelection`, `IntersectionComparison` | 元セルの和・交差、閉性、既存subsetとの同定、Mの制限 |
| 2 | `RegionShortExact`, `RegionNaturality` | 全三次数のSES、同じ制限射、粗細正方形 |
| 3 | `RegionConeSequence` | 標準錐SES・全整数次数LES、代表式と符号 |
| 4 | `GluingShortExact`, `GluingDefect` | Q/P、snake、局所J零からの同型・短完全列・保存iff |
| 5 | `LawGluing`, `FiberDecompositionBridge` | 同じ実Law/H¹/錐、G-135の固定X核商への接続 |
| 6 | `WidthFamily`, `WidthCohomology`, `WidthLaw`, `WidthGluing` | 任意kの原始族、全低幅一致、定数Law、同じ生成元のMV評価 |

Researchから本体への既存import方向を維持し、既存G-133〜135の一般APIを再証明しない。
特にG-135の順像係数・fiber適合・transgressionを、領域交差用に作り直す工程は置かない。
必要な対象はA・B・Uの既存固定X分解と、新しいセル交差のMVデータである。

## 4. 検証の焦点

- 原始入力からの完全性、同じuの可換性、標準連結射の符号を別々に検査する。
- Cの仮定は局所H¹同型であり、H⁰同型や局所錐消滅へ置換されていないことを確認する。
- 全kの帰納・forest・閉路積分証明と、小さいkの原始行列検算を区別する。
- Lawの値クラス、細側の逆像、同じ値の重複発生、異なるラベルの重複度を検査する。
- `blockDefect` への接続は次元だけでなく、同じH¹写像・核商の同定で確認する。

将来のLean検証は[AAT guideline](../../../docs/aat/guideline.md)のfocused checkと
必要な公理監査に従う。設計段階の有限計算は観測結果であり、Lean証明として表示しない。
