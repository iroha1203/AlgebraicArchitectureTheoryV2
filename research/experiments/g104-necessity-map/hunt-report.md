# G-104 必要性地図ハント最終報告（停止条件 B）

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**
> `G_local-v1` 相対の数学的terminal Bを記録する。

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
形で読めるが、本探索の計算還元は有限 regime に固定する。

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
  `37873129ed7d2d6fc0375b721e6e95bd213966836ed8b29484224fd88321d3cf`
- 有効 R1 payload SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- (a)–(e): 全 pass
- 現行 zero block: coarse/fine H¹ `1 / 1`、rank `1`
- 現行 one block: coarse/fine H¹ `0 / 0`、rank `0`
- 現行 law-value 直和: `1 / 1`、rank `1`
- derived support hole: `4 / 1`、rank `1`、相対 C2 failure は
  `A={0}` と `A={1}`

`Law=PUnit`、unit singleton carrier、`Value=Fin 2` の provenanceを含む最終 calibration と
時系列訂正は Issue #3948 comment `5231149474` に固定した。これは登録済みの
「calibration 不一致の解消」に当たる最後の進展であり、それ以前の no-progress streak をresetする。

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

候補定義に global / A-block H¹、comparison rank、global kernel/cokernel、全 A
comparison の全単射を使わない。唯一の例外は登録済み C3* の局所 fiber
cycle/boundary linear algebraである。global / A-block H¹ とcomparison rankは、候補とは
独立な二方向 query のラベルとしてだけ計算する。

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
comment `5230523348` に固定している。この provenance / ID補正は登録済みの4種の
「進展」には数えず、独立した監査訂正として記録する。

Round 6/7 の result SHA-256 はそれぞれ
`26de136bd3ace9b399560242655ad7027be2e82d67749aeaa4e199163f7d2429` と
`6cd110d05b6e1537589ac5f002818a68d0778f3534190f125abd14438eac4c56` である。
ただし、その後に R0(c)/(d)/(e) の calibration failureを修正したことは探索上の進展なので、
この2 roundを最終 stop streakには用いない。

### calibration進展をまたぐラウンド履歴

| round | strict expansion | payload SHA-256 | query / progress | stop streakでの扱い |
| --- | --- | --- | --- | --- |
| 8 | full-support KILL path 6 lifts、SLOT circular ladder、total 1,910 | `a239fbd921b7fd97de25ad0d00a43b5d5195116c9ecbf8d83e1f1911dffe3178` | 二方向0、4項目空 | diagnostic only |
| 9 | mixed KILL/SLOT diamond、split-support figure-eight、total 1,912 | `596fe4631155389798e5590953f7582048b3b37da7766859115f66a197f8aceb` | 二方向0、4項目空 | historical |
| 10 | overlapping-support mixed K2,3、3-chart K4+star face-chain、total 1,914 | `6f2a6287ae3f9c85300711b01b701ba6393dd2d5d44b3e2ebb748df923017a6f` | 二方向0、4項目空 | historical。旧Stop Cは撤回 |
| 11 | full-support six-lift W5 / K3,3 mixed relation graph、total 1,916 | `a9960aa342e67462fdef6ada3918424fe3b78d308d19888f7090deee977a4336` | 二方向0、4項目空 | post-PUnit valid no-progress 1/2 |
| 12 | octahedral / partitioned multichart house-star graph、total 1,918 | `c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90` | 二方向0、4項目空 | post-PUnit valid no-progress 2/2 |

Round 8–10 の finite payloadは履歴として保持する。ただし Round 9/10 による旧Stop Cの後、
`Law=PUnit` provenance calibrationの解消が Issue #3948 comment `5231149474` に
最後の進展として固定されたため、そのStop C判定を撤回し、両roundをhistoricalへ移した。
統合回帰は `47 tests / 633.323s / OK`、査読後のprojection強化に対するfocused
再検証は `3 tests / 316.488s / OK` であり、Round 10当時の実行数を最終値として
再利用していない。

post-PUnitの有効ラウンドは次のIssue記録に固定した。

- Round 11: preregistration comment `5231154236`、result comment `5231263023`、
  payload `a9960aa342e67462fdef6ada3918424fe3b78d308d19888f7090deee977a4336`。
- Round 12: preregistration comment `5231270132`、result comment `5231343121`、
  payload `c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90`。

両roundは同じ blockerを直接扱うstrict expansionであり、新規verdict、新規canonical
counterexample、candidate改訂、追加calibration fixはいずれも生じなかった。有限母集団は
Round 11で1,916件、Round 12で1,918件になった。

## Round 13–15: Stop C後の進展

Round 12のStop C checkpoint後、人間裁定はcandidate grammarの校正と局所表現可能性の
監査を続行した。次の3 roundはいずれも登録済みの進展定義を満たしたため、Round 11/12の
no-progress streakを最終終端には用いない。

| round | candidate / strict expansion | population | payload SHA-256 | 進展 |
| --- | --- | ---: | --- | --- |
| 13 | `R2-CSTAR-SUPPORT-ACTIVE-JOINT-COLLAPSE-v4`、cross-chart triangle support | 2,160 | `e15fc8dcb99ea7e8e17b1a52cc045379f9757c558a92f25e9d1bfc2bda5450e3` | candidate semantic change、guard calibration fix |
| 14 | v4、`NONFREE-MUTUAL-KILL-SPLIT` | 2,161 | `17c9907928a63cdf97e474e7f8813447601010ede07bbe7a43b525ef8551b450` | canonical necessity counterexample |
| 15 | `R2-CSTAR-COORDINATE-DOUBLED-CYCLE-v5`、固定control 5件追加 | 2,166 | `21b59632026d5ec0f104700f26808a8455e2ca607802a108c6934f68e8911969` | candidate semantic change、`TERNARY-CYCLE-3` counterexample |

Round 13は、各support-active scopeでcoarse/fineをjoint stateとして縮約し、全irreducible
terminalを普遍量化するv4へ候補を改訂した。C5/C6は、coarse critical edgeとfine critical
edgeのmapped imageの和をguard domainとする。固定boundの242新規caseを全数評価し、二方向
反例は0だったが、v3からv4へのsemantic changeとguard calibration fixが進展である。
resultは Issue #3948 comment `5234839619` に固定した。

Round 14の `NONFREE-MUTUAL-KILL-SPLIT` は全非空 A でH¹ mapが同型だが、v4 aggregateが
`[false,false,false,true,false,true,true]` となる。この1件でv4は必要条件でないことが確定し、
category verdict `CSTAR-not-necessary` を得た。resultは comment `5235064396` に固定した。

Round 15は、coordinate dependency packetとclosed doubled-cycle atomを追加してv5へ改訂した。
`WEIGHTED-2` は通る一方、singular perfect match、orphan self-loop、ternary cycleのnegative
controlを区別する。15個の新規A-blockを全数評価した結果、`TERNARY-CYCLE-3` はuniformだが
v5 candidate false、`TERNARY-CYCLE-6` はnonuniformかつcandidate falseだった。従ってv5も
必要条件ではない。resultは comment `5235636358` に固定した。

## historical Stop C checkpoint

Round 12時点の終端は、post-PUnitのRound 11/12が同一blocker
`PB-R2-NONFREE-GLOBAL-FACE-CHAIN` で2 round連続no-progressとなったため有効なStop C
checkpointだった。ただしRound 13–15がcandidate改訂、calibration fix、新規canonical
counterexampleを生じたため、これは最終terminalではない。Round 12までの1,918 caseと
parent artifactは履歴・admission evidenceとして不変に保持する。

## `G_local-v1`: 固定有限観測 grammar

人間裁定は、候補をさらに改訂してblind finite searchを続ける代わりに、Round 15で分離した
2 fixtureが同じ有限local observationを持つことを一般factorizationに持ち上げる経路を選んだ。
semantic IDは `G_local-v1` である。

### 観測する構造

`Obs_G` はfull support-active scopeを1回、全非空 A-scopeを順序なしで全件読む。各scopeでは
v5の全irreducible terminalを対象にし、removed cellやcertificate argumentを観測しない。
観測成分は次で閉じる。

1. retained chart / vertex / edge / actual face memberをrootとするradius-one typed incidence ball。
2. chart-at、endpoint slot `0/1`、face slot `0/1/2` と符号 `+/-/+`。同じneighborへの全relationは
   まとめて保持し、radius外のstubはcell typeとslotだけに落とす。
3. critical、guard、port、bridge、self-loop、`FaceTwin` の6 flag。各retained `FaceTwin`
   classのactual memberは別々のface rootとし、class multiplicityは `FaceTwin` flagだけで読む。
4. scoped supportとその `π` image。coarse cell、fine chart/vertexはmapped、fine edge/faceだけを
   actual `None` / mappedの2値で読む。
5. `v4-coarse`、`v4-fine-only`、`coordinate-dependency`、`closed-doubled-cycle` の全reachable
   collapse pathに現れるpacket kindの和集合。
6. outward stub、equal neighbor descriptor、rooted ball、equal A-recordの個数を
   `0 / 1 / at-least-2` にclipしたhistogram。
7. `π` を保つcoarse/fine target relabelで最小化したwhole record、A-record histogram、
   whole C0/C5/C6、AごとのC1–C4とそのAND vector。

raw cell ID、A label、fixture name、semantic hash、2を超える正確な個数、global cycle length、
full graph lookup、global / A-block H¹、comparison rank、uniformity truthは観測しない。
登録済みC3の局所unmapped-fiber linear algebraだけが例外である。

### source bundleと恒久contract

current permanent structural contractは Issue #3948 comment `5246699114`、timestamp
`2026-08-10T22:22:12Z`、compact canonical bytes `314821`、SHA-256
`955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af`
に固定した。contract生成はfixture constructor、`Obs_G`、v5 candidate/terminal query、
H¹、Round 13–15 report、populationを呼ばない。移行後regressionは Issue #3948 comment
`5246749681`、timestamp `2026-08-10T22:28:47Z` に同期した。
`immutable_round15_label_ledger.sha256` はledger自体のcanonical SHAであり、
`round15_immutable_ledger_provenance.sha256` はwitness projectionを認証したRound 15
registered manifestのSHAであってledger SHAではない。

source bundleは次を一つのsemantic packetに固定する。

- `g_local_v1.py` のnormalized full sourceとreachable structural helper closure。
- immutableな `r2_hunt.py` / `necessity_map.py` のnormalized full-source fingerprint、import binding、
  referenced dataclass field、runtime source binding。
- `Q = Fraction`、Matrix/Nerveのexact source、C3直達symbolとbase推移locator。
- current contract registration 4 fieldのRHSだけを `None` に正規化したchecker
  full-source fingerprint。
- top-level rebind禁止、closed packet/flag/relation registry、serialization contract。

これにより、候補・H¹ label・Round 15 ledgerを観測器へ逆流させず、同時に観測意味を担う
sourceの1-bit driftをcurrent permanent contract gateで拒否する。旧実行記録はcurrent sourceから
再構成したとは主張せず、opaque Git / Issue provenanceとしてだけ保持する。

### immutable ledgerとcomponent equality

label ledgerはRound 15 result payload
`21b59632026d5ec0f104700f26808a8455e2ca607802a108c6934f68e8911969`
だけをtruth sourceにし、次のexact fieldを固定する。

```text
exact_verification.fixtures[name="TERNARY-CYCLE-3"].uniform = true
exact_verification.fixtures[name="TERNARY-CYCLE-6"].uniform = false
```

checkerの依存順は固定されている。

```text
current permanent contract admission
  → exact witness structure admission
  → 2件の Obs_G とhand-authored component calibration
  → component-wise equalityとfinal canonical bytes equality
  → historical common Obs SHA / bytes bridge
  → immutable ledger admission
  → label separationとStop B
```

両fixtureのaggregateはともに
`[false,false,false,true,false,true,true]`、wholeは
`C0=false,C5=true,C6=true`、A0は `C1=false,C2=false,C3=true,C4=false`、
A1/fullはC1–C4が全てtrueである。packet union、whole condition、全A histogram、全side/type
root histogram、最終canonical bytesを個別比較し、すべて一致した後でのみledgerを読む。

この検証で実行する `Obs_G` structural evaluationは2件である。新しいRound 15 candidate
classification call、global / A-block H¹ query、population queryはすべて0であり、既知truthを
探索候補へ混入させていない。

current checkerのcompact canonical bytesは `56940`、SHA-256は
`834d97547d037ebe76fea942a95996f2b2a0bdcfe9f14eda73bc450c4ac9ebca` である。両fixtureの
common `Obs_G` はcompact canonical bytes `53279`、SHA-256
`742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc` に一致する。

## 一般factorization証明

`G_local-v1` で表現可能な任意の admissible condition family `P` を取る。「表現可能」とは、
ある関数 `f` が存在して

```text
P(comparison) = f(Obs_G(comparison))
```

と因子化することである。`TERNARY-CYCLE-3` と `TERNARY-CYCLE-6` はcomponent-wiseにも
canonical bytesとしても同じ `Obs_G` を持つため、任意のそのような `P` は両者に同じ値を返す。
一方、immutable ledger上の一様不変性は `true / false` と異なる。従って、一様不変性と同値な
必要十分condition familyは `G_local-v1` では表現できない。

この証明は有限母集団のzero-resultを一般化したものではなく、二点分離と関数の因子化だけを使う。
結論は登録した有限観測grammarに相対的である。radiusを増やす、global/nonlocal certificateを読む、
別のunbounded invariantを加えるなど、`G_local-v1` 外のgrammarに対する絶対不可能性は主張しない。

## 最終停止条件 B

| 停止条件 | 判定 | 根拠 |
| --- | --- | --- |
| A | false | characterization theoremとしての必要十分条件は得られていない |
| B | true | uniformity truthの異なる2件が同じ `Obs_G` を持つため、全 `G_local-v1`-expressible familyを一般factorizationで排除した |
| C | false | Round 13–15が新規反例・candidate改訂・calibration fixを生じ、historical no-progress streakを最終終端に使わない |

数学的な探索はfinal terminal Bに到達した。artifactはA=false、B=true、C=falseと
`G_local-v1` 相対の数学的根拠だけを固定する。Issue / PR の可変なlifecycle stateはartifactの
正本にせず、旧実行・同期記録はopaque Git / Issue provenanceとして分離する。

coverage limit:

- R1全数化は4 core template、登録Target bound、590 compatible comparisonsとrequired catalog。
- Round 15までのfinite queryはname-free semantic case 2,166件と登録fixtureに限る。
- Stop Bはradius-one、closed 4 packet kind、closed 6 flag、multiplicity clip2、
  `π`-preserving target orbitからなるexact `G_local-v1` に相対的である。
- 任意graph size、任意nonlocal certificate coloring、任意face multiplicity、任意chart数、
  任意compatible support distribution、別のglobal invariantを読むgrammarは未判定である。

## 再現契約

repository rootをworking directoryとする。

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s research/experiments/g104-necessity-map
PYTHONDONTWRITEBYTECODE=1 python3 \
  research/experiments/g104-necessity-map/build_results.py \
  --output /tmp/g104-necessity-map-results-through-round12.json \
  --summary-output research/experiments/g104-necessity-map/results-summary.json
PYTHONDONTWRITEBYTECODE=1 python3 \
  research/experiments/g104-necessity-map/build_stop_b_results.py \
  --output /tmp/g104-necessity-map-stop-b-results.json \
  --summary-output research/experiments/g104-necessity-map/results-stop-b-summary.json
shasum -a 256 \
  research/experiments/g104-necessity-map/results-summary.json \
  /tmp/g104-necessity-map-results-through-round12.json \
  research/experiments/g104-necessity-map/results-stop-b-summary.json \
  /tmp/g104-necessity-map-stop-b-results.json
```

- Python standard libraryのみ。global / A-block exact linear algebraは `fractions.Fraction` 上。
- 乱数なし。
- parent / final result serializationは UTF-8、LF、`indent=2`、`sort_keys=True`、末尾改行あり。
- `Obs_G` serializationはUTF-8、`ensure_ascii=True`、compact sorted JSON、末尾改行なし。
- immutable parent `results-summary.json` SHA-256:
  `afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5`
- immutable parent regenerated full `results.json` SHA-256:
  `cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306`
- final `results-stop-b-summary.json` SHA-256:
  `9de3a00f37c20393df01985f5c43eeec6ec21f6906083e01636dd8dfdab93502`
- final regenerated full Stop-B JSON SHA-256:
  `b8ac9461efe3dc4a039f986fa70daa0ab95842d83d7c9ddcb77d7024ffefc95e`

Issue #3948 comment `5231857267` のcheckpoint amendmentにより、Round 12までのfull JSONは
hashで固定された導出物、slim summaryはcommit対象となった。旧repo fileのSHA
`cabfbcae…2306` は regenerated parent full JSON の期待値へ役割を変更しただけである。
このparent artifactを変更せず、Stop-B generator / summaryを別artifactとして積み上げる。
