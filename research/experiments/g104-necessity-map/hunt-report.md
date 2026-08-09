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
| (c) | 非定数 law の block 直和 | law-generated global K0/K1 basis・`d0`・`d1`・3次数の pullback・H¹ map を A-subnerve block 直和とは独立に構成し、全行列と basis が exact 一致 |
| (d) | 全非空 A の indicator law | singleton Law、2値 Value、両 adequacy、`π`-可換に加え、true block と A-subnerve の全 cell・incidence・partial map・行列・H¹ が一致 |
| (e) | 現行 `ResolutionInvarianceFiringWitness` | 完全固定 data、`Law=PUnit`、`Value=Fin 2`、現行 C0–C6、zero/one block、具体的 firing cochain と fine image、global `dim H¹ = 1 / 1`、rank 1、nonvacuity を再現 |

現行 oracle の reading factor は `π = (0, 0, 1)`、nerve chart map は
`φ = (0, 0, 1)` である。値が同じでも型と責務が異なるため、engine では別 field として保持する。
歴史的3 fixture の `π = (0, 0, 1, 2)` とも分けて記録する。

### R0 実行結果と補正履歴

初回実装は obstruction 3件の incidence と H¹ を再現したが、reading factor を便宜的な
`1 → 1` にしていた。独立レビューでこれを modeling 欠陥として検出し、初回 R1 出力を
証拠から除外した。3件を Target `3 / 4`、`π = (0,0,1,2)`、full chart support に直し、
R0 を先に再実行してから R1 をやり直した。この補正は Issue #3948 comment
`5230365884` に固定した。

その後、固定 head の4本独立査読で、(c) の global 側が A-block 直和から再定義されていたこと、
(d) が indicator の factor/adequacy だけを検査して cell-level 同一性を検査していなかったこと、
engine の face well-formedness が Lean の3 endpoint equality より弱かったことを検出した。
これは還元の数学的反例ではなく calibration/modeling failure であるため、旧 stop-C streak を
checkpoint 根拠から外し、次を実装して R0 を再校正した。

- global law-generated basis・`d0`・`d1`・partial pullback・H¹ map を block 経路と独立構成。
- 両 canonical factor の全10非空 A で indicator true block と A-subnerve の
  chart/edge/face、incidence、partial map、行列、H¹ を exact 比較。
- Lean と同じ3つの face endpoint equality を `Nerve` constructor invariant に追加。
- canonical firing fixture の全配列・support・`π`・`φ`・cell map、
  `Law=PUnit`、carrier singleton、`Value=Fin 2` を fail-closed 固定。
- coarse firing cochain `(1,0,0,0)` と generated fine image
  `(1,0,0,0,0,0)` の cycle/nonboundary と H¹ map `[[1]]` を計算。

最終結果:

- 有効 R0 payload SHA-256:
  `dd982e5ded6395371c421e1d6223c2bf7489a07b723797fdeda55d99a172b455`
- 有効 R1 payload SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- (a)–(e): 全 pass
- 現行 zero block: coarse/fine H¹ `1 / 1`、rank `1`
- 現行 one block: coarse/fine H¹ `0 / 0`、rank `0`
- 現行 law-value 直和: `1 / 1`、rank `1`
- derived support hole: `4 / 1`、rank `1`、相対 C2 failure は
  `A={0}` と `A={1}`

最終 calibration と時系列訂正は Issue #3948 comment `5230818358` に固定した。
これは PRD の「calibration 不一致の解消」に当たる進展であり、それ以前の no-progress streak を
resetする。

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

### 候補固定後の監査と時系列訂正

| round | strict expansion | query | 監査上の扱い |
| --- | --- | --- | --- |
| 4 | closed 2D identity core 3件、total 608 | 二方向0、新反例0 | no-progress |
| 5 | identity square、Target `4/5`、chart mask `6^4=1,296`、全15 A、total 1,904 | 新規19,440 A-blockで二方向0 | face-chain blockerを試さず、stop streakには不適格 |
| 6 | nonidentity linear face-chain、lift数4/5、free pair 0、total 1,906 | 二方向0、新反例0 | historical no-progress |
| 7 | nonidentity branching tree / cycle、Target `4/5`、全15 A、free pair 0、total 1,908 | 二方向0、新反例0 | historical no-progress |

独立レビューは、Round 5 が同一 blockerを試していないこと、case IDが fixture nameを含むこと、
Round 1 payload hashが final sourceから再現できないことを指摘した。初回 stop-C 判定を撤回し、
name-free semantic IDへ変更して全件を再計算した。再同期後の Round 1–7 hash は Issue #3948
comment `5230523348` に固定している。この provenance / ID補正は PRD が列挙する4種の
「進展」には数えず、独立した監査訂正として記録する。

Round 6/7 の result SHA-256 はそれぞれ
`26de136bd3ace9b399560242655ad7027be2e82d67749aeaa4e199163f7d2429` と
`6cd110d05b6e1537589ac5f002818a68d0778f3534190f125abd14438eac4c56` である。
ただし、その後に R0(c)/(d)/(e) の calibration failureを修正したことは PRD 上の進展なので、
この2 roundを最終 stop streakには用いない。

### 最終 R0 補正後のラウンド

| round | strict expansion | payload SHA-256 | query / progress | stop streak |
| --- | --- | --- | --- | --- |
| 8 | full-support KILL path 6 lifts、SLOT circular ladder、total 1,910 | `a239fbd921b7fd97de25ad0d00a43b5d5195116c9ecbf8d83e1f1911dffe3178` | 二方向0、4項目空 | 最終R0 Issue同期・実行許可前にqueryしたため diagnostic only、0/2 |
| 9 | mixed KILL/SLOT diamond、split-support figure-eight、全15 A、total 1,912 | `596fe4631155389798e5590953f7582048b3b37da7766859115f66a197f8aceb` | 二方向0、4項目空 | valid no-progress 1/2 |
| 10 | overlapping-support mixed K2,3、3-chart K4+star face-chain、全15 A、total 1,914 | `6f2a6287ae3f9c85300711b01b701ba6393dd2d5d44b3e2ebb748df923017a6f` | 二方向0、4項目空 | valid no-progress 2/2 |

Round 8 は数学的な finite diagnostic として母集団に保持するが、停止条件の監査単位には数えない。
Round 9 は最終 R0 comment `5230818358` の後に事前登録・実行し、result comment
`5230876303` に固定した。Round 10 は comment `5230881464` で事前登録し、実行前の
静的敵対レビューを通してから初回 queryを行った。初回実行記録は21 tests成功
（参考 wall time 124.093秒）であり、result comment `5230966215` に固定した。

Round 10 の strict-expansion auditは次を同時に満たした。

- prior/total raw・full semantic SHA・20-hex unique は `1912 / 1914`、collision 0。
- 新規2 fixtureの30 A-blockと既存1,912件で十分性破れ・必要性破れはいずれも0。
- lift/chart/許容target relabelに不変な colored graph/support canonical codeは
  R6–R10の10 fixtureで全て異なり、support driftを検出する。
- free pairはwhole/全Aで0。wholeで C0*/C5*/C6*、全Aで C1*–C4*が成立し、
  全Aのcomparisonが同型。
- 新規 verdict、新規 canonical counterexample、candidate改訂、追加 calibration fixは全て空。

## 停止条件 C

終端は **C(停滞)** である。最後の進展は Issue #3948 comment `5230818358` に固定した
最終 R0 calibration failure の解消である。その後、Round 8は無効な diagnosticとして除外し、
Round 9とRound 10が同じ blocker
`PB-R2-NONFREE-GLOBAL-FACE-CHAIN` に帰着して2ラウンド連続で進展なしとなった。

blocker は、固定半径の `FaceTwin` / one-pass free pair / `SLOT` / `KILL` だけから、
free pairを持たない任意の retained 2次元 face-chain graphが cycleを消すかを導く一般手証明が
閉じないことである。これは固定した有限 local grammar と有限母集団の coverage blockerであり、
incidence/support 条項全体についての2点分離一般論法ではない。従って停止 Bとは判定しない。
`CERTIFIED-v3` の characterization statusは `undecided` である。

coverage limit:

- R1の全数化は4 core template、登録 Target bound、590 compatible comparisonsと
  required fixture catalog 13件に限る。
- R2はname-free semantic case 1,914件と、linear / branching / cycle / ladder / diamond /
  figure-eight / K2,3 / K4+star の固定 fixtureだけを exact 評価した。
- Round 10の chart block間には非loop edgeやfaceがなく、cross-chart coupled incidenceは未被覆である。
- 任意graph size、任意chart数、任意 face multiplicity、任意 compatible support distribution、
  arbitrary large nerveとnonidentity refinementの一般形は未被覆である。

この checkpoint は task完了ではない。Issue #3948は open、PRDは保持し、draft PRのまま
人間裁定を待つ。有限 zero-resultを証明または停止 Bとは称さず、`CERTIFIED-v3` を必要十分条件や
確定 theorem candidateとして主張せず、第二段 GOALも起票しない。

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
  `3d0173edac824dc04d661e4846d50937f52fdf3d29cc84ddec00fda629f23453`
