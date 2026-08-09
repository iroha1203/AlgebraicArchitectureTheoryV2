# G-104 条件 C 必要性地図ハント報告

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**

本報告は Issue #3948 の計算探索を記録する。G-104 のカード、完了 report、
ResearchLean の確定実体は変更しない。

## R0: 値部分集合還元

### 還元する命題

有限 `Source` 上の well-formed comparison data を固定する。粗側 reading を `q`、
細側 reading を `q'`、canonical factor を `π : q'.Target → q.Target` とする。
chart support から K1 により edge support と face support を導く。

非空 `A ⊆ q.Target` に対し、粗側の各 cell の K1 support が `A` と交わる cell
だけを残した複体を `K_A`、細側で `π⁻¹(A)` と交わる cell だけを残した複体を
`K'_{π⁻¹(A)}` と書く。係数はいずれも定数 `ℚ` とする。このとき次が成り立つ。

```text
任意の adequate FiniteLawFamily で generatedComparisonH1Map が全単射
  ⇔
任意の非空 A ⊆ q.Target で K_A → K'_{π⁻¹(A)} の H¹ map が全単射
```

これは本 artifact の一般手証明である。現行 Lean には還元全体を一つにした theorem は
なく、下記の既存 declaration と3つの手証明 conjunct を組み合わせる。

### 既存 declaration との対応

| conjunct | 現行 declaration | 本報告で補う点 |
| --- | --- | --- |
| `π` と law descend の可換性 | `ComparisonData.lean` の `comparisonFactor_commutes`、`comparisonFactor_surjective`、`lawDescend_unique`、`lawDescend_comparisonFactor` | indicator family の canonical descend を `lawDescend_unique` で同定する |
| K0/K1 cell support | `LawGeneratedComplex.lean` の `edgeSupport`、`faceSupport`、`CellCoordinate` | A-filter は chart だけでなく各次数の K1 support へ適用する |
| cell ごとの block occurrence | `LawValueCoordinateSubnerve.lean` の `block_cell_injective`、`exists_block_coordinate_cell_iff`、3つの occurrence iff theorem | A-filtered cell subtype との全単射と incidence 保存をまとめる |
| cochain 直和分解 | `LawValueBlockDecomposition.lean` の `cochainBlockEquiv`、`lawGeneratedD0_block_intertwining`、`lawGeneratedD1_block_intertwining` | H¹ の主根拠とは区別して使う |
| H¹ block 分解 | `LawValueBlockCohomology.lean` の `lawGeneratedH1BlockEquiv` | 各 block を A-subnerve の定数 `ℚ` 複体と同定する |
| block comparison | `LawValueBlockComparison.lean` の `generatedBlockComparisonHom`、`generatedBlockComparisonH1Map` | partial cell map と `none → 0` が A-subnerve map と一致することを確認する |
| quotient-level naturality | `LawValueBlockComparisonNaturality.lean` の `generatedBlockComparisonH1DirectSumMap`、`generatedComparisonH1Map_block_naturality` | global 全単射と blockwise 全単射の一般 iff を手証明する |
| indicator family | `CanonicalResolution/Reading.lean` の `FiniteLawFamily`、`Adequate` | singleton law、2値 `Bool`、両 reading の adequacy、任意非空 A の実現を手証明する |

`LawValueBlockComparisonInjectivity.lean`、`LawValueBlockComparisonSurjectivity.lean`、
`LawValueBlockComparisonBijectivity.lean` の C0–C6 相対 theorem は、ここで必要な
assumption-free の blockwise criterion の代用には用いない。

### 手証明 1: law-value block と A-subnerve

law-value label `λ = (law, value)` に対し

```text
A_λ = { target | lawDescend law target = value }
```

と置く。`λ` は source-generated なので、`lawDescend_commutes` から `A_λ` は非空である。
`lawDescend_comparisonFactor` により、細側で同じ value を取る target は正確に
`π⁻¹(A_λ)` になる。

`exists_block_coordinate_cell_iff` は、各 chart / edge / face が `λ` block に現れる
ことと、その cell の K1 support 上に `A_λ` の target が存在することを同値にする。
`block_cell_injective` は同じ cell と label に複数の occurrence witness があっても
座標が重複しないことを与える。従って block の cell 型は A-filtered cell subtype と
全単射である。endpoint と face incidence は元の K1 incidence を保つため、
`lawValueBlockComplex` は `K_{A_λ}` 上の定数 `ℚ` 複体に一致する。block comparison も
mapped cell では pullback、`none` cell では零となり、A-subnerve comparison と一致する。

### 手証明 2: global 全単射と blockwise 全単射

粗側・細側の `lawGeneratedH1BlockEquiv` を `E_c`、`E_f`、global map を `F`、
block map の有限直和を `B` とする。`generatedComparisonH1Map_block_naturality` は

```text
E_f ∘ F = B ∘ E_c
```

を与える。`E_c` と `E_f` は linear equivalence なので、`F` が全単射であることと
`B` が全単射であることは同値である。

さらに有限直和の component formula から、`B` が全単射であることと全 `λ` の block map が
全単射であることは同値になる。単射方向は `λ` 成分だけに支えを持つ元を使う。
全射方向は細側の `λ` 成分だけに支えを持つ元の global preimage を取り、その `λ` 成分を読む。
label 型が空の場合も両主張は自動的に成立する。

### 手証明 3: 任意非空 A の indicator 実現

非空 `A ⊆ q.Target` に対し singleton law family を次で作る。

```lean
Law := PUnit
Value := fun _ => Bool
eval := fun _ source => decide (q.read source ∈ A)
```

`PUnit` は有限、`Bool` は decidable equality と相異なる `false` / `true` を持つ。
粗側 descend は `χ_A`、細側 descend は `χ_A ∘ π` とする。
`comparisonFactor_commutes` により両 reading は adequate であり、`lawDescend_unique` により
canonical descend は指定した関数と一致する。`A` の元と `q.read` の全射性から `true` label は
source-generated であり、その block は正確に A-subnerve である。`A = q.Target` の場合に
`false` が実際の値として現れなくても、Value 型が2値を持つという構成要件は保たれる。

### 両方向

一様不変性から全非空 A の判定を得るには、A の indicator family に一様不変性を適用し、
global/block iff の `true` 成分を読む。逆向きは任意の adequate family と任意の label `λ` に
非空 `A_λ` の仮定を適用し、全 block map の全単射から有限直和、さらに naturality を通して
global map の全単射を得る。

この証明は `Source` の有限性を使って部分集合走査を有限化する。論理的な block 対応は同じ
形で読めるが、本 PRD の計算還元は有限 regime に固定する。

## R0 calibration の固定 oracle

engine は次の5群を別々の oracle として検査する。

| gate | 固定対象 | 期待する中心結果 |
| --- | --- | --- |
| (a) | `FaceLiftObstruction` / `EdgeFiberObstruction` / `LoopLiftObstruction` | それぞれ C4 / C5 / C6 の既知 failure と H¹ map の非全単射 / 非単射を再現 |
| (b) | 値分配 derived support hole | global `dim H¹ = 4 / 1`、rank 1。A-block で相対 C2 が発火し、この例を除外 |
| (c) | 非定数 law の block 直和 | global の H¹ 次元と rank が各 law-value block の和に一致し、cell signature が A-subnerve と一致 |
| (d) | 全非空 A の indicator law | singleton Law、2値 Value、両 adequacy、`π`-可換、true block と A-subnerve の cell signature が一致 |
| (e) | 現行 `ResolutionInvarianceFiringWitness` | 現行 C0–C6、zero/one block、global `dim H¹ = 1 / 1`、rank 1、nonvacuity を再現 |

現行 oracle の reading factor は `π = (0, 0, 1)`、nerve chart map は
`φ = (0, 0, 1)` である。値が同じでも型と責務が異なるため、engine では別 field として保持する。
歴史的3 fixture の `π = (0, 0, 1, 2)` とも分けて記録する。

### R0 実行結果と補正履歴

初回実装は obstruction 3件の incidence と H¹ を再現したが、reading factor を便宜的な
`1 → 1` にしていた。独立レビューでこれを modeling 欠陥として検出し、初回 R1 出力を
証拠から除外した。3件を Target `3 / 4`、`π = (0,0,1,2)`、full chart support に直し、
R0 を先に再実行してから R1 をやり直した。

- 有効 R0 payload SHA-256:
  `f56a210eba2647dd0e14b34e0532da4d62efc966c1335ccce51e3f1d3290f8c4`
- (a)–(e): 全 pass
- 現行 zero block: coarse/fine H¹ `1 / 1`、rank `1`
- 現行 one block: coarse/fine H¹ `0 / 0`、rank `0`
- 現行 law-value 直和: `1 / 1`、rank `1`
- derived support hole: `4 / 1`、rank `1`、相対 C2 failure は
  `A={0}` と `A={1}`

この補正と再実行は Issue #3948 の comment `5230365884` に固定した。

## R1: 必要性地図

### 事前登録 normal form

Issue #3948 の comment `5230270861` で、実行前に次を登録した。

- incidence core は `identity point`、`split point`、`interval edge omission`、
  `identity self-loop` の4 template。
- coarse Target `1..2`、fine Target `coarse..3`。
- Target relabel を除いた nondecreasing surjection 6件。
- 各 chart の全非空 support assignment を走査し、`π` / `φ` compatibility で filter。
- edge/face support は K1 の共通部分から導出。
- C0/C5/C6 は whole nerve、C1–C4 は全非空 A ごとに評価。
- 歴史的 obstruction、derived support hole、現行 firing oracle、旧 positive、
  7 necessity witness は別 catalog として全件評価。

有効 R1 payload SHA-256 は
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`。

| population | 件数 |
| --- | ---: |
| raw support assignments | 1,526 |
| compatible comparisons | 590 |
| uniform | 580 |
| nonuniform | 10 |
| required fixture catalog | 13 |

### 7条項の verdict

| 条項 | verdict | witness | 同じ非退化 A での H¹ |
| --- | --- | --- | --- |
| C0 | `not-necessary` | `C0_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |
| C1 | `not-necessary` | `C1_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |
| C2 | `not-necessary` | `C2_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |
| C3 | `not-necessary` | `C3_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |
| C4 | `not-necessary` | `C4_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |
| C5 | `not-necessary` | `C5_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |
| C6 | `not-necessary` | `C6_not_necessary` | `A={0,1}`、`1 → 1`、rank 1 |

各 witness は全非空 A で comparison が全単射であり、named clause failure と両側 H¹
非零が同じ `A={0,1}` で成立する。従って零 H¹ だけの必要性反例ではない。ただし破れの
機構は、独立な H¹ componentを保ったまま別の incidence/support component が
H¹-neutral になることであり、現行条項そのものを必要条件にできない。

## R2: C* 研磨ラウンド

### incidence/support 候補の共通部分

候補は以下の有限 syntactic data だけを読む。

1. exact ordered face triple と derived Target support が同じ face を `FaceTwin` class にする。
2. self-loop `e` と class `(e,e,e)` があり、`e` が他 class に出ないとき、その pair を
   snapshot 上で同時に1回だけ除く。
3. 残る self-loop、または自身を除いても endpoints 間に path がある edge を
   cycle-critical とする。
4. C0* は critical chart support、C1* は critical port connectivity、C2* は
   critical edge lift、C3* は `edgeMap=None` の局所 fiber cycle filling、C4* は
   retained FaceTwin class liftを要求する。
5. C5*/C6* は fine edge lift の syntactic swap relationを使う。

候補定義に H¹、comparison rank、kernel/cokernel、全 A comparison の全単射を使わない。
H¹ は候補とは独立な二方向 query のラベルとしてだけ計算する。

### progress round

| round | candidate SHA / result SHA | population | 結果 | 判定 |
| --- | --- | ---: | --- | --- |
| 1 `DIRECT-v1` | `5e8835…` / `82aa4a…` | 604 | Chain3 が uniform だが direct graph は path で C5* false | 新規必要性反例、progress |
| 2 `COMPONENT-v2` | `b16b93…` / `ebc6f4…` | 605 | UnkilledTwin は C* true だが H¹ `1 → 2`、rank 1 | 新規十分性反例、progress |
| 3 `CERTIFIED-v3` | `cbb026…` / `bcd340…` | 605 | 二方向反例 0。Chain3 を含み UnkilledTwin を除外 | 実質改訂、progress |

Round 1 の `Chain3` は local swap `x0~x1~x2` の推移性を示す。Round 2 の
`UnkilledTwin` は同一 fine face への共出現だけでは差 cochain が消えないことを示す。
最終 `CERTIFIED-v3` は次の2つだけを直接証明書にする。

- `SLOT`: 同じ coarse FaceTwin class へ写る2 fine face が同じ1 slotの liftだけ異なり、
  他2 edgeと support signatureが一致する。
- `KILL`: fine face が `(u,v,z)` または `(v,u,z)` で、別の fine face `(z,z,z)` があり、
  mapped coarse face がそれぞれ `(E,E,Z)` と `(Z,Z,Z)` になる。

`CertifiedSwap` はこの無向関係の反射推移閉包である。C5* は lift が高々1 class、
C6* は各 class が fine self-loop代表を持つことを要求する。

### 候補固定後の監査訂正

| round | strict expansion | query | progress audit |
| --- | --- | --- | --- |
| 4 | closed 2D identity core 3件、total 608 | 二方向0、新反例0 | 4項目すべて空、no-progress 1/2 |
| 5 | identity square、Target `4/5`、chart mask `6^4=1,296`、全15 A、total 1,904 | 新規19,440 A-blockで二方向0 | faceを持たず、同一blocker roundとして無効 |

独立レビューは、Round 5 が face-chain blockerを試していないこと、case IDが fixture nameを
含むこと、Round 1 payload hashが final sourceから再現できないことを指摘した。停止 C の初回判定を
撤回し、name-free semantic IDへ変更して全件を再計算した。この補正は progress として streakを
resetした。再同期後の Round 1–5 hash は Issue #3948 comment `5230523348` に固定している。

### 同一blockerを直接含む最終2ラウンド

| round | strict expansion | query | progress audit |
| --- | --- | --- | --- |
| 6 | nonidentity linear face-chain、lift数4/5、free pair 0、raw total 1,906 | 二方向0、新反例0 | 4項目すべて空、no-progress 1/2 |
| 7 | nonidentity branching tree / cycle face-chain、Target `4/5`、全15 A、free pair 0、raw total 1,908 | 二方向0、新反例0 | 4項目すべて空、no-progress 2/2 |

Round 6 result SHA-256 は
`26de136bd3ace9b399560242655ad7027be2e82d67749aeaa4e199163f7d2429`、
Round 7 は
`6cd110d05b6e1537589ac5f002818a68d0778f3534190f125abd14438eac4c56`。

## 停止条件 C

終端は **C(停滞)** である。最後の進展は Round 5 後の独立監査に伴う provenance / ID補正であり、
その後 Round 6 と Round 7 は同じ blocker
`PB-R2-NONFREE-GLOBAL-FACE-CHAIN` に帰着して2ラウンド連続で進展がなかった。

blocker は、固定半径の `FaceTwin` / one-pass free pair / `SLOT` / `KILL` だけから、
free pair を持たない任意の2次元 coreで遠方の face-chain が cycleを消すかを導く一般手証明が
閉じないことである。これは固定した有限 local grammar と有限母集団の coverage blocker であり、
incidence/support 条項全体についての2点分離一般論法ではない。従って停止 B とは判定しない。

coverage limit:

- R1 core は4 templateと登録 Target boundだけを全数化した。
- R2 Round 6 はlinear relation graph 2件、Round 7 はbranching tree / cycle各1件だけである。
- 最終4 fixtureはnonidentityでfree pairを持たないが、任意graph size・任意support分配は覆わない。
- arbitrary large nerve、nonidentity refinement、任意 face multiplicity、全 support grammarは
  未被覆である。

この checkpoint は task完了ではない。Issue #3948は open、PRDは削除・改訂せず、
人間裁定を待つ。`CERTIFIED-v3` を必要十分条件として主張せず、第二段 GOAL も起票しない。

## 再現契約

canonical生成:

```bash
cd research/experiments/g104-necessity-map
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest test_necessity_map.py test_r2_hunt.py
PYTHONDONTWRITEBYTECODE=1 python3 build_results.py --output results.json
shasum -a 256 results.json
```

- Python standard libraryのみ。
- exact linear algebraは `fractions.Fraction` 上。
- 乱数なし。
- serializationは UTF-8、LF、`indent=2`、`sort_keys=True`、末尾改行あり。
- canonical `results.json` SHA-256:
  `d55b2f2650e6b799ba3a0bf00324ea274c9bcef6760838f51565606a8d6532dd`
