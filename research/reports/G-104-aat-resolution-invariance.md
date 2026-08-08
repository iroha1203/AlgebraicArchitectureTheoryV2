# G-104-aat-resolution-invariance — 診断の解像度不変性

- 一次仕様: [`research/goals/G-104-aat-resolution-invariance.md`](../goals/G-104-aat-resolution-invariance.md)
- tracking Issue: [#3902](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3902)
- target theorem: Diagnostic Resolution Invariance Theorem
- proof state: `target-proof-checkpoint`(現行 statement の claim (i) canonical
  comparison map は Cycle 9、有限 `(law, 値)` block の複体・次数別直和分解は
  Cycle 10、actual `H^1` quotient の block 有限直和同型は Cycle 11 で証明済み。
  label 別 comparison Hom / `h1Map` と global pullback の3次数 block 成分一致は
  Cycle 12、global comparison `H^1` map の quotient-level block 直和 naturality は
  Cycle 13、K0 / K1 exact block からの canonical 座標 subnerve は Cycle 14 で
  証明済み。whole-nerve C0 / C5 / C6 と全座標 subnerve 相対の C1–C4 からなる
  incidence / support-only の条件 C package と、各 principal 条件・補助条件を
  識別する有限な正例 / 反例 instance pair は Cycle 15 で固定済み。exact block
  comparison `H^1` map の単射性は Cycle 16、C3 の局所 face filling を actual block
  cocycle の fiber-period 消滅へ接続する discrete Stokes theorem は Cycle 17 で
  証明済み。finite directed multigraph dualityにより、その period 消滅を actual
  block `d0` の coordinate-fiber primitiveへ変換する theorem は Cycle 18 で
  証明済み。coarse block chartごとのprimitiveをproof内で選び、canonical chart
  block mapに沿って一つのfine zero-cochainへ組み立て、actual residualが全
  coordinate-fiber edge上で零になる normalization theorem は Cycle 19 で
  証明済み。C2のproof-local edge liftとC5のexact block uniquenessにより、その
  normalized residualをcoarse one-cochainのactual generated block pullbackとして
  表すdescent theoremはCycle 20で証明済み。C4のexact fine face liftから
  degree-two pullbackの単射性を導き、actual `comm1`でCycle 20のcoarse
  one-cochainをcoarse block cocycleへ昇格するtheoremはCycle 21、そのkernel
  representativeをactual quotientへ送り、Cycle 21 primitiveの負をactual `d0`
  image witnessとして使うlabel別comparison `H^1` mapの全射性はCycle 22で
  証明済み。fixed Condition Cからlabel別mapと既存finite DirectSum mapの
  bijectivityを導き、Cycle 13 naturalityでactual global comparison `H^1` mapの
  bijectivityへ輸送するclaim (ii)はCycle 23、全fine diagnostic classがactual
  canonical mapによる一意なcoarse preimageを持つclaim (iii)はCycle 24で
  証明済み。G-103 `Factors`を満たすlawのexact subtypeから有限law族を作り、
  既存K0/K1複体とactual G-102 `H^1`へ接続するcanonical inadequate-reading
  diagnosticはCycle 25で固定済み。非単射な粗側readingがexact subtypeに
  非定数lawを残し、そのcanonical diagnosticに非零self-loop classを作る一方、
  actual comparison mapがそのclassを零へ送り、元law族によるfine側canonical
  diagnosticの`H^1`が消滅するclaim (iv)(a)の有限反例はCycle 26で固定済み。
  coarse treeのcanonical diagnosticが消滅する一方、same retained familyのfine
  parallel-edge classが非零でactual comparison mapが全射でなく、元law族全体の
  fine canonical diagnosticにも非零classがあるclaim (iv)(b)の有限反例はCycle 27で
  固定済み。そのexact retained familyを両readingにadequateなlaw族として固定し、
  二本のfine parallel edgeが同一coarse edgeへ写ることでcurrent C5とfull Condition Cが
  破れ、同じactual generated comparison `H^1` mapが非全単射となるclaim (iv)(c)の
  有限反例はCycle 28で固定済み。Cycle 7 の
  `target-refuted` は改訂前の退化 face
  宣言規則に対する歴史証拠)
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria の正本は GOAL カードであり、この
report はそれらを再定義しない。

> **注記(2026-08-07、カード改訂)**: 本 report の Cycle 1–4 packet と
> `target-refuted` 判定は、改訂前カード(条件 C = C0–C5、nerve 全体への
> 条項、係数生成契約なし。commit `88321001` 時点)の固定 statement に
> 対する歴史証拠である。カードはその後の改訂(PR #3915: 係数生成契約
> K0 / K1、係数体 `ℚ` 固定、C6 追加、C1–C4 の座標 subnerve 相対化)で
> statement を再固定した。Cycle 2–4 の反例は改訂後 statement の反証では
> ない(これらの Lean 反例は改訂後カードの (iv)(c) 素材として転用
> 可能なまま残る)。改訂後 statement は Cycle 5 から再開し、Cycle 7 で
> claim (i) の退化 face 規則そのものが `comm1` を壊すことを現行
> K0 / K1 上で固定した。runtime state の正本は tracking Issue #3902。

> **注記(2026-08-08、カード改訂)**: Cycle 7 の claim (i) 反証は、改訂前の
> 退化 face 宣言規則(「boundary edge がすべて fiber 内 edge」で宣言可。
> commit `2ede7da2` 時点)に対する歴史証拠である。カードはその後の改訂
> (退化宣言の hereditary 化: 退化 face はその3本の boundary edge が
> すべて退化成分として宣言済みの場合に限り宣言可)で statement を
> 再固定した。改訂後の規則の下では Cycle 7 witness の comparison data は
> well-formed でない(`DegenerateFaceComm1Obstruction` は改訂後規則の
> 根拠として存続し、(iv) の素材ではない)。Cycle 5 の K0 / K1
> `lawGeneratedComplex` は nerve 射に依存しない per-reading の構成で
> あり、改訂後 statement でもそのまま再利用する。改訂後 statement の
> cycle は Cycle 8 から再開する。

## Proof obligation state

- 完了: H0a `CoarserThan` からの canonical comparison factor、その可換性・
  一意性・全射性。
- 完了: H0b `Adequate` から生成した各 law descend、その可換性・一意性、
  comparison factor に沿う coarse / fine descend の可換性。
- 完了(現行 statement): Cycle 5 の K0 / K1 base complex。chart 台と face
  endpoint coherence だけを入力に、edge / face 台、実際の law-descend 値の
  `(cell, law, 値)` 座標、`ℚ` 上の `d₀` / `d₁`、`d₁ ∘ d₀ = 0`、
  `ThreeCochainComplex ℚ` を生成した。
- 完了(現行 statement): Cycle 8 の supported-nerve comparison geometry。
  partial edge / face map、endpoint / boundary 可換、fiber 内 edge の退化宣言、
  face から boundary edge への hereditary な退化宣言、canonical `π` に沿う
  chart 台包含だけを入力に持つ一般の `TargetSupportedNerveMorphism` を定義した。
  mapped edge / face の台包含は K1 の交わりと incidence から theorem として
  導出し、独立な edge / face 台対応 field は持たない。
- 完了(現行 statement): Cycle 9 の claim (i)。canonical `comparisonFactor` と
  `lawDescend_comparisonFactor`、Cycle 8 の morphism から同一 `(law, 値)` label の
  coordinate transport と、mapped cell 上の評価 / 退化 cell 上の零からなる
  degreewise pullback を生成した。`edge_none_fiber` と hereditary な3本の
  face-none field を実使用して `comm0` / `comm1` を証明し、coarse から fine の
  `ThreeCochainComplex.Hom` と canonical `H^1` map を構成した。
- 完了(現行 statement): Cycle 10 の有限 `(law, 値)` block 複体と次数別直和分解。
  `FiniteLawFamily.Value` を有限と仮定せず、有限 Source 上の law evaluation の像を
  reading 非依存な共通 label 型として生成した。各 K0 coordinate の label fiber、
  label を保つ endpoint / face incidence、label ごとの `ThreeCochainComplex`、
  全3次数の finite `DirectSum` equivalence を構成し、実際の `lawGeneratedD0` / `D1`
  と componentwise block differential の intertwining を証明した。Cycle 9 の
  mapped chart / edge / face coordinate transport も同じ label を保つ。
- 完了(現行 statement): Cycle 11 の quotient-level `H^1` block 有限直和分解。
  Cycle 10 の componentwise differential を aggregate `ThreeCochainComplex` にまとめ、
  global complex と aggregate complex の cycle 同型、global / aggregate の boundary range 対応、
  aggregate cycle / boundary と label 別の product との対応を証明した。G-102 の実際の
  `H1 = ker d1 / range boundaryToCycles` に `Submodule.Quotient.equiv` と
  `Submodule.quotientPi` を適用し、global `H^1` と block `H^1` の finite
  `DirectSum` の canonical `LinearEquiv` と representative の成分公式を得た。
- 完了(現行 statement): Cycle 12 の label 別 generated comparison Hom。
  Cycle 9 の canonical chart / edge / face coordinate transport を Cycle 10 の exact
  `LawValueLabel` fiber へ制限し、mapped cell は同一 label の coarse coordinate を評価、
  退化 edge / face は零とする block pullback を全3次数で生成した。
  `comm0` / `comm1` を incidence と hereditary 退化宣言から証明し、label ごとの
  actual `ThreeCochainComplex.Hom` と G-102 `h1Map` を構成した。global
  `generatedPullback0/1/2` の canonical block 成分がそれぞれ label 別 pullback と
  一致することも theorem として固定した。
- 完了(現行 statement): Cycle 13 の quotient-level comparison naturality。
  Cycle 12 の label 別 actual `generatedBlockComparisonH1Map` だけから finite
  `DirectSum` map を componentwise に生成した。global cycle map と block cycle map の
  成分一致を degree-one component theorem から導き、Cycle 11 の representative
  成分公式と global / block 両側の G-102 `h1Map_mk` から quotient
  representative 公式を証明した。これを quotient extensionality で全 class へ拡張し、
  coarse / fine `lawGeneratedH1BlockEquiv` の下で global comparison `H^1` map が
  label 別 block `H^1` map の有限直和と一致する naturality square を得た。
- 完了(現行 statement): Cycle 14 の canonical 座標 subnerve。
  各 source-generated `LawValueLabel` について、chart / edge / face を既存 K0
  block coordinate そのものとし、K1 由来の endpoint / face incidence と
  underlying overlap component を継承する `CoverNerve` を構成した。3次数の
  underlying-cell projection は単射であり、各 cell が subnerve に現れることを、
  chart support / K1 edge support / K1 face support 上で exact label value が実際に
  出現することとそれぞれ iff で特徴づけた。有限 Source regime の全 cell 型に
  `Fintype` instance も生成した。
- 完了(現行 statement): Cycle 15 の incidence / support-only 条件 C package。
  C0 / C5 / C6 を whole nerve、C1–C4 を全 source-generated label の canonical
  座標 subnerve 上で定義した。C1 の fiber graph は両 endpoint coordinate が
  同一 coarse block chart へ写る全 fine block edge を使い、C2 / C4 は canonical
  Option block transport の exact image を要求する。C3 は有限な全 fine block edge
  上の `ℚ` chainについて fiber 外で零、fiber chart ごとの incoming = outgoing、
  内部 face の oriented boundary `e₀ - e₁ + e₂` の span を要求する。C5 / C6 の
  exact block 制限を theorem として導き、C6 の endpoint reflection は C5 に
  依存しない。package は命題 field だけを持ち、同型・消滅・inverse・選択 lift / path /
  filling chain を入力しない。さらに、proper かつ非単射な target factor、
  coarse self-loop、宣言された退化 edge、repeated-edge face、非自明な chart fiber を
  同時に持つ有限 fixture 上で C0–C6 と aggregate C の正例を構成した。image 欠落、
  edge lift 重複、endpoint reflection 失敗、内部 face 欠落をそれぞれ分離する反例で、
  principal 条件と全補助条件の正負 instance pair を固定した。この fixture は
  constant law と whole-coordinate subnerve を使う API 品質証拠であり、claim (v) の
  nondegenerate 発火 witness には数えない。
- 完了(現行 statement): Cycle 16 の label 別単射性。C0 から粗側 block chart の
  K0 occurrence を細側 occurrence へ戻して canonical chart block map の全射性を
  導いた。fine zero-cochain が pulled coarse one-cochain の `d0` primitive なら、C1 の
  fiber path に沿って値が一定であることを証明した。退化 edge では zero pullback、
  mapped self-loop では C6 endpoint reflection を使用する。C0 から proof 内で選んだ
  chart representatives と C2 の exact edge lift により coarse primitive を構成し、
  G-102 の actual quotient `H^1` 上で generated block comparison map の単射性を得た。
  representative / path / primitive は theorem proof 内だけに現れ、data field として
  保存しない。C3 / C4 / C5 は全射性側へ残す。
- 完了(現行 statement): Cycle 17 の C3 fiber-period 消滅。actual exact block
  cocycle は任意の rational face chain の oriented incidence imageを有限和の交換と
  actual `lawValueBlockD1 = 0` により annihilate する。C3 の existential face chainを
  proof 内だけで取り出し、その exact equalityを代入して、任意の coordinate-fiber
  cycle の period が零であることを証明した。C3 が同時に返す internal-face support
  conjunct はこの scalar consequence では不要であり、未使用であることを明記する。
  primitive、section、path、inverse は構成せず、有限 graph dualityへ残す。
- 完了(現行 statement): Cycle 18 の coordinate-fiber primitive。有限 directed
  multigraph の supported incidence pairing と masked value functionalを構成し、
  period 消滅から value functional が incidence kernel の dual annihilator に属する
  ことを証明した。`LinearMap.dualAnnihilator_ker_eq_range_flip` により vertex potentialを
  existential に取得し、supported edge上で right-minus-left が元のedge valueに一致する。
  このgeneric theoremをCycle 17のactual block period theoremへ直接適用し、各 coarse
  block chart fiber上で `lawValueBlockD0 primitive = cycle` を得た。C1は不要であり、
  loop・parallel edge・非連結成分を除外しない。primitiveはproof outputだけに現れる。
- 完了(現行 statement): Cycle 19 の coordinate-fiber residual normalization。
  Cycle 18 のexistential primitiveを各 coarse block chartについてproof内で選び、各
  fine chartをcanonical `chartBlockCoordinateMap` の像に属するlocal primitiveで評価する
  一つのfine zero-cochainを構成した。`CoordinateFiberEdge` の左右endpointは同じcoarse
  chartへ写るため、actual `lawValueBlockD0` は同一local primitiveの差となり、元cocycle
  との差が全coordinate-fiber edge上で零になる。C0 / C1は不要で、primitive familyを
  theorem input、structure、certificateへ保存しない。
- 完了(現行 statement): Cycle 20 の normalized residual descent。C2から各coarse
  block edgeのfine liftをproof内で選び、fine cochainをそのliftで評価するcoarse
  one-cochainを構成した。mapped fine edgeはwhole-nerve C5のexact block uniquenessで
  selected liftと一致し、退化Option branchは零とするため、actual
  `generatedBlockPullback1` が元fine cochainに一致するgeneric theoremを得た。これを
  Cycle 19のactual residualへ適用し、退化edgeのzero premiseをendpoint-defined fiber
  normalizationから放電した。lift family、primitive、coarse cochainをdata fieldへ保存しない。
- 完了(現行 statement): Cycle 21 の coarse cocycle descent。C4のexact fine
  face liftを座標ごとにproof内で取り出し、actual `generatedBlockPullback2` の単射性を
  証明した。既存 `generatedBlockPullback_comm1` により、degree-one pullbackがfine
  cocycleに一致すれば元coarse one-cochainがactual `lawValueBlockD1` のkernelに入る
  ことを導いた。これをCycle 20のactual residual descentへ適用し、primitiveとactual
  coarse block kernel representativeをexistential outputとして構成した。C0 / C1 / C6、
  face lift uniqueness、selected face sectionを追加しない。
- 完了(現行 statement): Cycle 22 の label 別 `H^1` 全射性。任意のfine block
  `H^1` classをG-102のactual quotient surjectivityでkernel representativeへ戻し、
  Cycle 21からprimitiveとactual coarse kernel representativeを取得した。coarse
  representativeをactual coarse quotientへ送り、canonical generated comparison
  `h1Map`のrepresentative公式を直接使った。両representativeの差はCycle 21の
  pullback equalityによりactual `d0 (-primitive)`であるため、fine classを回収する。
  supplied preimage、inverse、dimension count、別comparison mapを使わない。
- 完了(現行 statement): Cycle 23 の claim (ii) global bijectivity。fixed
  `ConditionC`のC0–C6をCycle 16 / 22へlabelごとに投影し、actual block comparison
  mapのbijectivityを得た。既存componentwise finite DirectSum mapは成分公式を用いて
  単射性を反射し、各labelの全射性からproof内でpreimage familyを選んで全射性を
  構成した。Cycle 13 naturalityとcanonical Cycle 11 block equivalenceにより、この
  bijectivityをactual global `generatedComparisonH1Map`自身へ輸送した。comparison
  inverse、dimension equality、alternate conjugate mapを入力しない。
- 完了(現行 statement): Cycle 24 の claim (iii) overresolution corollary。任意の
  fine actual `H^1` classについて、Cycle 23のglobal surjectivityからcoarse preimageを
  proof内で取得し、global injectivityからその一意性を証明した。結論はactual
  canonical `generatedComparisonH1Map`を直接使う`∃!`であり、新しいdiagnostic set、
  inverse function、cardinality comparisonを導入しない。
- 完了(現行 statement): Cycle 26 の claim (iv)(a) canonical false-positive witness。
  `Fin 3`上の非単射な粗側readingについて、Cycle 25のexact `Factors` subtypeが
  非定数lawをちょうど一つ保持し、fiberを分離する別lawを除外することを証明した。
  one-chart self-loopのactual G-102 quotientに明示的な非零classを構成し、同じ
  retained familyのactual `generatedComparisonH1Map`がそのclassをfine tree上で零へ
  送ることを示した。さらに元の二law族全体によるfine側canonical diagnosticについて、
  任意cochainを積分するtree primitiveから`H^1`消滅を証明した。selected law list、
  別complex、型の不一致だけによる議論を使わない。
- 完了(現行 statement): Cycle 27 の claim (iv)(b) canonical hidden-class witness。
  Cycle 26と同じ非単射reading pair、二law族、exact `Factors` subtypeを用い、incidence
  geometryだけをcoarse one-edge treeとfine two-parallel-edge multigraphへ変更した。
  coarse canonical diagnosticのactual `H^1`消滅をexplicit tree primitiveで証明し、
  same retained familyのfine actual quotientにparallel-edge periodが一となる非零classを
  構成した。actual `generatedComparisonH1Map`はこのclassをcoverできず全射でない。
  さらに元law族全体のfine canonical `FactorsDiagnosticH1`にも同じperiod patternの
  非零classを別途構成し、型の不一致だけに依存しないことを固定した。historical
  custom complex、selected law list、dimension count、supplied H1 certificateを使わない。
- 完了(現行 statement): Cycle 28 の claim (iv)(c) adequate Condition-C failure witness。
  Cycle 27のexact `retainedLaws`を両readingでadequateな同一law族として用い、非定数lawと
  非単射なcanonical target factorを保持した。相異なる二本のfine parallel edgeがcurrent
  hereditary morphismのactual `edgeMap`で同一coarse edgeへ写るため、whole-nerve C5と
  full fixed Condition Cは偽である。同じdata・同じadequacy proofを用いるactual
  `generatedComparisonH1Map`は非全射であり、従ってclaim (ii)が結論する
  `Function.Bijective`の正確な否定を満たす。旧custom complex、任意map、selected law list、
  supplied nonisomorphism certificateを使わない。
- 歴史証拠(改訂前の退化宣言規則): Cycle 7 の claim (i) blocker。改訂前
  規則が許す endpoint-defined fiber-internal edge は coarse self-loop へ
  非退化に写り得る。
  その edge を boundary triple の3位置に持つ fine face だけを退化と
  宣言すると、generated
  degree-one pullback の fine `d₁` は `1 - 1 + 1 = 1`、退化 face 上で零の
  degree-two pullback は `0` となり、`ThreeCochainComplex.Hom.comm1` が破れる。
  改訂後カードは退化宣言の hereditary 性でこの comparison data を
  well-formedness から除外する。
- 歴史証拠(改訂前 statement): Cycle 2 の C0–C3 十分性 blocker。coarse face lift の欠落を有限反例で
  固定し、条件 C を C0–C4 へ改訂する根拠を得た。
- 歴史証拠(改訂前 statement): Cycle 3 の C0–C4 十分性 blocker。C4 face を actual differential と
  comparison map に使いながら、同一 coarse edge の parallel fine lift が作る
  追加 `H^1` class を Lean で固定した。
- 歴史証拠(改訂前 statement): Cycle 4 の C0–C5 十分性 blocker。coarse self-loop の唯一 fine lift が
  同一 chart fiber の異なる chart を結ぶことで、coarse の非零 `H^1` class が
  fine coboundary へ写る有限反例を Lean で固定した。
- 現 target(hereditary 退化宣言)に対する未完の数学 proof obligation:
  発火 witness。

## Cycle 28 — adequate Condition-C failure witness

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 28
decision: approve
result type: proof-obligation-discharged
proof obligation: claim (iv)(c)としてadequate pair上でfixed Condition Cとactual canonical comparison H1 bijectivityが同時に破れるfinite witnessを構成する
proof obligation delta: exact retained familyの両側adequacy、current C5とCondition Cの失敗、actual generated comparison H1 mapの非全単射を同一fixtureで固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/AdequateConditionCFailure.lean`
- principal declaration:
  `AAT.AG.ResolutionInvariance.AdequateConditionCFailure.fixed_claim_iv_c`
- law familyはCycle 25のexact G-103 `Factors` subtypeであるCycle 27
  `retainedLaws`そのものとする。`coarseRetainedAdequate`はsubtype propertyから、
  `retainedLawsFineAdequate`は元law族のfine adequacyから導出され、original two-law
  familyのcoarse inadequacyをadequate premiseへ読み替えない。
- `retainedLaw_nonconstant`はexact subtypeのevalが元の`factorLaw` evaluationを保つことから、
  retained family自身が非定数lawを含むことを示す。canonical target factorも同じ
  review済みreading pair上で非単射なので、adequacyは空familyや恒等比較のvacuityでない。
- `parallel_edge_lifts`はfine edge `0`と`1`が相異なりながら、actual
  `nerveMorphism.edgeMap`でともに`some PUnit.unit`へ写ることを公開する。
  `conditionC5_not`はこの3事実をcurrent whole-nerve `ConditionC5`へ直接適用し、
  `conditionC_not`はfull `ConditionC.c5` projectionを反証する。
- `generatedComparisonH1Map_not_surjective`はCycle 27のsame-family actual map theoremを
  definitionally exactなcurrent `generatedComparisonH1Map` statementへ接続する。
  predecessor proofはexplicit coarse tree primitiveから得たactual `H1Zero`と、parallel
  periodで検出したnamed fine quotient class非零を実使用する。
- `generatedComparisonH1Map_not_bijective`はactual mapの非全射性を
  `Function.Bijective`の全射成分へ適用する。任意map、別diagnostic、dimension argument、
  supplied inverse / nonisomorphism certificateを導入しない。
- principal theoremは両側adequacy、proper refinement、非単射factor、retained law非定数、
  coarse actual `H1Zero`、named fine class非零、C5 failure、full Condition C failure、
  actual canonical mapの非全単射を一つのclosed finite witnessへ束ねる。
- focused manifest / single-file check: pass。
- targeted module build: pass、3709 jobs。新規moduleのlinter warningなし。
- namespace axiom audit: 7 declarations、standard axioms only。

### Audit

- premise classification: finite Source、readings、supported nerves、review済みmorphismは
  existence witnessに許可された`ambient-boundary`。adequacy、C5 / Condition C failure、
  actual nonbijectivityをtheorem inputやstructure fieldとして受けない。
- proof use: distinct parallel edgesと二つのactual edgeMap equationをC5反証へ、C5反証を
  full Condition Cへ、actual non-surjectivityをnon-bijectivityへ直接使う。coarse `H1Zero`と
  named fine class非零はpredecessorのsame actual map proofで実使用済み。
- certificate provenance: retained familyはselected listでなくexact predicate subtype。
  comparison mapはcurrent generated cochain HomのG-102 `h1Map`であり、H1結果をmorphismや
  certificate fieldに保存しない。
- route integrity: pass。Cycle 25 exact subtype、Cycle 27 current K0 / K1、actual quotient、
  current hereditary morphism、actual generated comparisonへ直結する。historical
  `EdgeFiberObstruction`のparallel-edge機構を旧custom surfaceのまま再ラベルしない。
- anti-weakening: full Condition Cの否定だけで止めずfailure conjunct C5を公開し、
  「ある非同型」でなくclaim (ii)と同じactual mapの`¬ Function.Bijective`を結論に含める。
- vacuity / quality: retained familyは非定数lawを含み、target factorは非単射、fine classは
  actual quotient上で非零。face-free fixtureはclaim (iv)(c)だけに数え、claim (v)のC4、C6、
  hereditary degenerate face comm1発火へ流用しない。新規public Prop / certificate typeはなく、
  7宣言はすべてdeclaration docstringを持つ。
- common scans: `git diff --check` pass。hidden/BiDi、new Lean placeholder、private path、
  reverse `Formal -> ResearchLean.AG` import、禁止語の新規hitなし。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: claim (v)の全nondegenerate firing条件を同一current-surface finite witnessで
  構成し、fixed Condition Cとactual comparison bijectivityを非空虚に発火させる。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 28
decision: approve
result_type: proof-obligation-discharged
proof_obligation: construct claim (iv)(c) as an adequate-pair finite witness where fixed Condition C and actual H1 invariance fail
proof_obligation_delta: both-side adequacy, current C5 and Condition C failure, and actual generated comparison H1 nonbijectivity are now fixed on one current-surface fixture
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/AdequateConditionCFailure.lean
    declarations:
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.retainedLaw_nonconstant
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.parallel_edge_lifts
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.conditionC5_not
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.conditionC_not
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.generatedComparisonH1Map_not_surjective
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.generatedComparisonH1Map_not_bijective
      - AAT.AG.ResolutionInvariance.AdequateConditionCFailure.fixed_claim_iv_c
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - the exact retained family is adequate for both readings
    - two distinct fine edges have the same actual coarse edge image
    - current whole-nerve C5 and full fixed Condition C fail
    - the actual generated comparison H1 map is not bijective
    - claim (iv)(c) is fixed on the current canonical K0/K1 surface
  remaining:
    - claim (v) nondegenerate firing witness
certificate_provenance:
  discharged:
    - the law family is the Cycle 25 exact Factors predicate subtype
    - adequacy is derived from subtype membership and reviewed fine adequacy
    - coarse vanishing and fine nonvanishing come from an explicit primitive and period detector
    - nonbijectivity concerns the actual current generated comparison map
  unresolved: []
proof_use_audit:
  used_material_premises:
    - both adequacy proofs on the same retained family
    - distinct parallel fine edges and both actual edgeMap equations
    - the C5 field of full Condition C
    - actual nonsurjectivity as the obstruction to Function.Bijective
    - actual coarse H1Zero and named nonzero fine class in the predecessor proof
  unused_material_premises: []
instance_pair_audit:
  status: pass
  reason: no new public Prop or certificate type; the closed theorem is a substantive negative instance for existing C5 and Condition C
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  alternate_diagnostic_set: none-found
  cardinality_argument: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: construct claim (v) as the fixed nondegenerate firing witness satisfying every listed firing condition on the same witness
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 27 — canonical inadequate hidden-class witness

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 27
decision: approve
result type: proof-obligation-discharged
proof obligation: claim (iv)(b)としてfine canonical Factors diagnosticの非零classがinadequate coarse diagnosticから見えなくなるfinite witnessを構成する
proof obligation delta: coarse actual H1Zero、same-family actual comparison非全射、full fine canonical非零classを一つのfinite fixtureで固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateHiddenClass.lean`
- principal declaration:
  `AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.fixed_claim_iv_b`
- Source、coarse / fine readings、元の二law族、`factorLaw`のexact retention、粗側
  inadequacy、fine側adequacy、canonical target factorの非単射性はCycle 26のcurrent
  canonical fixtureから再利用する。retained familyは引き続きCycle 25の
  `descendableSubfamily coarseReading`そのものであり、selected law listを作らない。
- incidence geometryはcoarse二chart・一edgeのtree、fine二chart・同じ端点を持つ
  二parallel edges、両側faceなしとする。current hereditary
  `TargetSupportedNerveMorphism`は両fine edgesを唯一のcoarse edgeへ写し、全supportは
  K0 / K1の既存生成規則から導出する。
- `coarsePrimitive`は任意のactual coarse degree-one cochainを右chartへ積分し、
  `coarse_lawGeneratedD0_primitive`がactual generated `d0`で元cochainを回収する。
  これをG-102 quotientへ適用してcanonical coarse `FactorsDiagnosticH1`の`H1Zero`を得る。
- generic `fineParallelPeriod`は二parallel edge coordinateの評価差である。両edgeの
  actual endpoint coordinatesが一致するため全actual coboundary上で零だが、第二edgeの
  unit cochain上で一となる。fine側にfaceがないためunit cochainはactual cocycleであり、
  `fineParallelClass_ne_zero`がactual quotient classの非零性を証明する。
- `retainedFineClass`はsame exact coarse-retained familyをfine current K0/K1 complexへ
  入れたclassである。`retainedComparisonH1Map`は既存`generatedComparisonH1Map`を
  直接instantiateしたactual mapである。coarse source classはすべて零なので、
  named `retainedFineClass`をpreimageに持つと非零性に矛盾し、mapは全射でない。
- `fullFineClass`は元の二law族をfine readingのexact Factors subtypeへ入れたfull
  canonical `FactorsDiagnosticH1`に、元の`factorLaw`から同じparallel period classを
  構成する。same-family map非全射とfull canonical非零classの両方を公開するため、
  dependent law indexの型差だけを反例に数えない。
- principal theoremはcoarse inadequacy、fine adequacy、proper refinement、exact
  Factors characterization、retained lawの非定数性、coarse canonical `H1Zero`、
  retained fine class非零、actual map非全射、full fine class非零を一つに束ねる。
- focused manifest / single-file check: pass。
- targeted module build: pass、3700 jobs。新規moduleのlinter warningなし。
- namespace axiom audit: 51 declarations、standard axioms only。

### Audit

- premise classification: concrete finite Source、readings、law family、supported nerves、
  reviewed morphismは存在反例に許可された`ambient-boundary`。coarse `H1Zero`、fine
  nonzero class、comparison非全射をpremiseやfieldとして受けない。
- proof use: excluded lawがcoarse inadequacyを、retained nonconstant lawがboth fine
  classesのactual K0/K1 coordinateを作る。tree incidenceはexplicit primitive、parallel
  incidenceはperiod detector、nerve morphismはactual comparison mapへ実使用する。
- certificate provenance: exact subtype adequacyはsubtype propertyからtheoremとして
  導出する。tree primitive、parallel cycle、quotient classはproof-localまたはactual
  G-102 constructorであり、H1 vanishing / nonvanishing certificateをstructureへ保存しない。
- route integrity: pass。Cycle 25 canonical diagnostic、Cycle 26 law provenance、current
  K0/K1、actual quotient、actual generated comparisonへ直結する。historical
  `FaceLiftObstruction` / `EdgeFiberObstruction`の旧nerve型やcustom complexをimportしない。
- anti-weakening: `¬ Surjective`のproofはnamed `retainedFineClass`を直接surjectivityへ
  投入し、coarse `H1Zero`とその非零性から矛盾を得る。さらにfull fine canonical
  class非零を別途示すため、型差、cardinality、別diagnostic setへの弱化はない。
- vacuity / quality: exact retained familyは非空、lawは非定数、target factorは非単射、
  retained / full fine classはともに明示的に非零。新規public Prop predicateやcertificate
  typeはなく、51宣言はdeclaration docstringを持ち、Prop証明はtheoremで公開する。
  face-free geometryをclaim (iv)(c)やclaim (v)へ数えない。
- common scans: `git diff --check` pass。untracked Lean fileのwhitespace check、hidden/BiDi、
  new Lean placeholder、private path、reverse `Formal -> ResearchLean.AG` import、禁止語の
  新規hitなし。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: claim (iv)(c)のadequate pair finite witnessをfresh selectorで固定し、
  fixed Condition Cの少なくとも一条項が破れ、actual canonical comparison `H1` mapも
  同型でないことをcurrent surface上で示す。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 27
decision: approve
result_type: proof-obligation-discharged
proof_obligation: construct claim (iv)(b) as a canonical FactorsDiagnosticH1 hidden-class finite witness
proof_obligation_delta: coarse actual H1Zero, same-retained-family actual comparison nonsurjectivity, and a full fine canonical nonzero class are now fixed on one finite fixture
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateHiddenClass.lean
    declarations:
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.coarse_factors_iff
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.factorLaw_nonconstant
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.coarseFactorsDiagnosticH1Zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.fineParallelClass_ne_zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.retainedFineClass_ne_zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.fullFineClass_ne_zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.retainedComparisonH1Map_not_surjective
      - AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass.fixed_claim_iv_b
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - the canonical coarse Factors diagnostic has actual H1Zero
    - the same retained family has an explicit nonzero fine actual H1 class
    - the actual generated comparison H1 map is not surjective
    - the full fine canonical Factors diagnostic has an explicit nonzero class
  remaining:
    - claim (iv)(c) adequate Condition-C failure witness
    - claim (v) nondegenerate firing witness
certificate_provenance:
  discharged:
    - the retained family is the Cycle 25 exact predicate subtype
    - both fine classes are actual G-102 quotient classes detected by an explicit period
    - coarse vanishing is derived from an explicit tree primitive
    - comparison nonsurjectivity concerns the actual generated map on one retained family
  unresolved:
    - the current-surface class for claim (iv)(c)
proof_use_audit:
  used_material_premises:
    - positive and negative G-103 Factors proofs inherited from the same original law family
    - the retained nonconstant law in both retained and full fine coordinates
    - the current hereditary supported-nerve morphism in the actual comparison map
    - actual tree and parallel-edge incidence in the G-102 quotient proofs
  unused_material_premises: []
instance_pair_audit:
  status: pass
  reason: no new public Prop or certificate type; the closed finite theorem supplies retained and full fine nonzero witnesses and coarse vanishing
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  alternate_diagnostic_set: none-found
  cardinality_argument: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: construct claim (iv)(c) as an adequate-pair finite witness where fixed Condition C and actual H1 invariance fail
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 26 — canonical inadequate false-positive witness

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 26
decision: approve
result type: proof-obligation-discharged
proof obligation: claim (iv)(a)としてcanonical Factors diagnostic上のfalse-positive finite witnessを構成する
proof obligation delta: 粗側の明示的非零class、actual comparisonでの消滅、元law族によるfine側actual H1消滅を同じ有限fixtureで固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateFalsePositive.lean`
- principal declaration:
  `AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.fixed_claim_iv_a`
- `Source = Fin 3`とし、粗側readingはsource `0`と`1`を同じtargetへ写し、
  fine側readingは恒等とする。canonical `comparisonFactor`が非単射であることを
  source `0`と`1`の像から直接証明する。
- 元の二law族では、非定数な`factorLaw`が粗側readingを通してfactorし、
  `separatingLaw`は粗側fiberの`0`と`1`を分離するためfactorしない。
  `coarse_factors_iff`は粗側のCycle 25 exact subtypeが文字どおり`factorLaw`だけを
  保持することを両向きに固定する。粗側inadequacyとfine側adequacyもこの同じ
  law evaluationから導出し、selected subsetや外部adequacy certificateを入力しない。
- 粗側nerveは一chart・一self-loop、fine側nerveは二chart・一本のtree edgeである。
  current hereditary `TargetSupportedNerveMorphism`はfine edgeをcoarse self-loopへ写し、
  chart supportとK1 edge supportは既存生成規則を使う。
- `coarseLoopClass`はcanonical coarse `FactorsDiagnosticH1`、すなわちactual
  G-102 quotientのclassである。self-loop評価は全actual coboundary上で零だが
  `coarseLoopClass`上で一となるため、`coarseLoopClass_ne_zero`を得る。
- `retainedComparisonH1Map`は同じexact retained familyについて既存
  `generatedComparisonH1Map`を直接instantiateしたactual mapである。fine treeでは
  任意degree-one cochainを明示的なzero-cochainへ積分できるため、mapの像が零となる。
- `fineFactorsDiagnosticH1Zero`はretained familyだけでなく、元の二law族をfine側の
  exact Factors subtypeへ入れたfull canonical diagnosticについてactual `H1Zero`を
  証明する。そのため反例はcoarse/fine diagnostic型の不一致だけに依存しない。
- principal theoremはcoarse inadequacy、fine adequacy、proper refinement、
  exact Factors characterization、retained lawの非定数性、coarse class非零、
  actual comparison image零、full fine `H1Zero`を一つのPropとして公開する。
- focused manifest / single-file check: pass。
- targeted module build: pass、3699 jobs。新規moduleのlinter warningなし。
- namespace axiom audit: 49 declarations、standard axioms only。

### Audit

- premise classification: concrete finite Source、readings、law family、supported nerves、
  reviewed morphismは存在反例に許可された`ambient-boundary`。非零class、H1消滅、
  comparison image零をpremiseやstructure fieldとして受けない。
- proof use: `factorLaw` / `separatingLaw`はactual `Reading.Factors`の正負proofへ接続し、
  separating lawの除外をcoarse inadequacyに使用する。retained lawはactual K0/K1
  coordinateを作り、nerve morphismはactual comparison mapに使用する。
- certificate provenance: retained familyはCycle 25のpredicate subtypeであり、
  coarse adequacyはdocstring付きtheoremとしてsubtype propertyから導く。comparison map、
  quotient class、fine primitiveは既存APIまたはproof-local constructionで、選択済み
  law mask、inverse、H1 certificateを保存しない。
- route integrity: pass。G-103 `Factors`からCycle 25 canonical diagnostic、current K0/K1、
  actual G-102 `H1`、actual generated comparisonへ直結する。historical obstructionの
  custom complexや旧supported-nerve型を再利用しない。
- anti-weakening: coarse側非零だけで止めず、actual comparison image零とfull fine
  canonical `H1Zero`の両方を示す。dimension/cardinality、別diagnostic set、型差だけの
  argumentを使わない。
- vacuity / quality: retained familyは非空でlawは非定数、coarse H1 classは明示的に非零、
  target factorは非単射。新規宣言はすべてdeclaration docstringを持ち、named law defは
  Factors/adequacy proofへ接続し、Prop proofはtheoremとして公開する。このfixtureを
  claim (v)の発火witnessやclaim (iv)(c)へ数えない。
- common scans: `git diff --check` pass。untracked Lean fileのwhitespace check、hidden/BiDi、
  new Lean placeholder、private path、reverse `Formal -> ResearchLean.AG` import、禁止語の
  新規hitなし。
- blocking findings: none。初回T3の`separatingLaw` API非接続とProp `abbrev` findingは
  bounded repair後のfinding-limited再監査で実体解消した。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: claim (iv)(b)のcanonical hidden-class finite witnessをfresh selectorで
  固定し、fine側actual非零classがinadequate coarse diagnosticで見えなくなることを示す。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 26
decision: approve
result_type: proof-obligation-discharged
proof_obligation: construct claim (iv)(a) as a canonical FactorsDiagnosticH1 false-positive finite witness
proof_obligation_delta: an explicit nonzero coarse class, its zero image under the actual generated comparison map, and full fine canonical H1Zero are now fixed on one finite fixture
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateFalsePositive.lean
    declarations:
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.coarse_factors_iff
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.factorLaw_nonconstant
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.coarse_not_adequate
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.fine_adequate
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.comparisonFactor_not_injective
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.fineFactorsDiagnosticH1Zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.coarseLoopClass_ne_zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.retainedComparisonH1Map_coarseLoopClass_zero
      - AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive.fixed_claim_iv_a
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - the canonical coarse Factors subtype retains exactly one nonconstant law
    - the canonical coarse diagnostic has an explicit nonzero actual H1 class
    - the actual generated comparison map sends that class to zero
    - the full fine canonical Factors diagnostic has H1Zero
  remaining:
    - claim (iv)(b) canonical hidden-class witness
    - claim (iv)(c) adequate Condition-C failure witness
    - claim (v) nondegenerate firing witness
certificate_provenance:
  discharged:
    - the retained family is the Cycle 25 exact predicate subtype
    - coarse retained adequacy is derived from subtype properties
    - the quotient class and comparison map are the actual G-102 and generated constructions
    - the fine zero result is derived from an explicit tree primitive
  unresolved:
    - concrete classes for claim (iv)(b) and claim (iv)(c)
proof_use_audit:
  used_material_premises:
    - positive and negative G-103 Reading.Factors proofs for the named laws
    - coarse inadequacy and fine adequacy from the same original law family
    - the current hereditary supported-nerve morphism
    - the actual ThreeCochainComplex quotient and generated comparison H1 map
  unused_material_premises: []
instance_pair_audit:
  status: pass
  reason: no new public Prop or certificate type; the finite theorem itself supplies Factors retention and exclusion, nonzero and zero witnesses
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  alternate_diagnostic_set: none-found
  cardinality_argument: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: construct claim (iv)(b) as a canonical hidden-class finite witness
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 25 — canonical inadequate-reading diagnostic

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 25
decision: approve
result type: proof-obligation-discharged
proof obligation: G-103 Factorsが成立するlawのexact subtypeからcanonicalな有限law族を作り、既存K0/K1複体とactual H1をinadequate readingの診断として固定する
proof obligation delta: 選択依存のlaw subsetを導入せず、Factors判定から係数複体とactual quotientまでを一意に定めた
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateDiagnostic.lean`
- declarations:
  - `AAT.AG.CanonicalResolution.FiniteLawFamily.DescendableLaw`
  - `AAT.AG.CanonicalResolution.FiniteLawFamily.exists_descendableLaw_iff_factors`
  - `AAT.AG.CanonicalResolution.FiniteLawFamily.descendableSubfamily`
  - `AAT.AG.CanonicalResolution.FiniteLawFamily.descendableSubfamily_eval`
  - `AAT.AG.CanonicalResolution.FiniteLawFamily.descendableSubfamily_adequate`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.factorsDiagnosticComplex`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.FactorsDiagnosticH1`
- `DescendableLaw laws q`は文字どおり
  `{law : laws.Law // q.Factors (laws.eval law)}`である。
  `exists_descendableLaw_iff_factors`は元lawがこのsubtypeへ入ることとG-103
  `Factors`が同値であることを両向きに固定する。後から選んだlaw一覧や
  inclusion certificateを入力しない。
- `descendableSubfamily`のlaw indexはこのexact subtypeであり、有限性は元の
  `laws.Law`の有限性から`Fintype.ofFinite`で導く。`Factors`の
  `DecidablePred`、`q.Target`のdecidable equality、追加の有限性premiseを
  public inputにしない。
- retained lawの`Value`と`eval`は元familyのものをそのまま再利用する。
  adequacyは各subtype elementの`law.2`だけから証明し、descend functionや
  adequacy certificateを別fieldに保存しない。
- `factorsDiagnosticComplex`はこのderived adequacyを既存
  `TargetSupportedNerve.lawGeneratedComplex`へ渡す。そのためcell support、
  K0 `(cell, law, value)`座標、K1 support、differentialはreview済みの生成規則を
  そのまま使う。`FactorsDiagnosticH1`はG-102のactual
  `ThreeCochainComplex.H1 = ker d1 / range boundaryToCycles`であり、別quotientや
  diagnostic setではない。
- 定義は任意reading上でtotalに与える。`¬ laws.Adequate q`をphantom premiseに
  せず、次cycleのinadequate witnessが同じcanonical typeを直接instantiateする。
- focused manifest / single-file check: pass。
- targeted module build: pass、3696 jobs。新規moduleのlinter warningなし。
- namespace axiom audit: 7 declarations、standard axioms only。

### Audit

- premise classification: finite law family、reading、supported nerve、有限Sourceは
  `ambient-boundary`。新しいdirection hypothesisはない。各lawの`Factors` proofは
  canonical subtypeの要素そのもので、外部certificateではない。
- proof use: `Factors`はlaw indexの選別とderived adequacyの両方に実使用する。
  subtype propertyからadequacyを導き、そのproofをactual K0/K1 complex生成へ渡す。
- certificate provenance: retained subsetはpredicate subtypeからdefinitionally決まり、
  selected list、chosen section、law mask、supplied adequacyを受けない。
- instance-pair / vacuity: 新しいpublic Prop、structure、classは追加しない。既存
  `Reading.Factors`にはG-103の正負instance pairがあり、新exactness theoremが
  retention / exclusionをそのpredicateへ反射する。反例本体は次cycleへ残し、この
  surfaceだけをclaim (iv) witnessへ数えない。
- structure-field escape: none-found。subfamilyは元lawのValue/evalとFactors proof以外の
  dataを持たず、H1や反例結論に相当するfieldを追加しない。
- route integrity: pass。G-103 `Factors`から既存K0/K1 complex、actual G-102 H1へ直結する。
- anti-weakening: arbitrary selected subfamily、coefficient proxy、Set/cardinality diagnostic、
  別complexへ置換しない。claim (iv)の3反例は未主張のまま保持する。
- cheat routes: decidability premise、supplied subset、supplied adequacy、alternate quotient、
  zero-H1 vacuityはいずれもnone-found。
- common scans: `git diff --check` pass。hidden/BiDi、new Lean placeholder、private path、
  reverse `Formal -> ResearchLean.AG` import、禁止語の新規hitなし。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。exact subtype、
  unchanged evaluation、derived adequacy、actual H1、追加premise不在を独立承認した。
- next obligation: claim (iv)(a)のfinite witnessをfresh selectorで固定し、canonical
  coarse `FactorsDiagnosticH1`に非零classがある一方でfine側に対応する非零classが
  ないことを、型不一致だけに頼らずactual complexes上で証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 25
decision: approve
result_type: proof-obligation-discharged
proof_obligation: define the canonical inadequate-reading diagnostic from the exact G-103 Factors-selected law subtype and the existing K0/K1 complex
proof_obligation_delta: the Factors predicate now canonically determines the finite law family, actual coefficient complex, and actual G-102 H1 without a selected subset
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateDiagnostic.lean
    declarations:
      - AAT.AG.CanonicalResolution.FiniteLawFamily.DescendableLaw
      - AAT.AG.CanonicalResolution.FiniteLawFamily.exists_descendableLaw_iff_factors
      - AAT.AG.CanonicalResolution.FiniteLawFamily.descendableSubfamily
      - AAT.AG.CanonicalResolution.FiniteLawFamily.descendableSubfamily_eval
      - AAT.AG.CanonicalResolution.FiniteLawFamily.descendableSubfamily_adequate
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.factorsDiagnosticComplex
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.FactorsDiagnosticH1
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - the retained laws are exactly those satisfying G-103 Factors
    - the retained finite family preserves the original values and evaluations
    - subtype provenance derives adequacy and the existing K0/K1 complex
    - the canonical diagnostic is the actual G-102 H1 of that complex
  remaining:
    - the three finite counterexamples
    - the nondegenerate firing witness
certificate_provenance:
  discharged:
    - the law subfamily is a predicate subtype rather than a selected list
    - adequacy is derived from each subtype property
    - no descend section, mask, alternate quotient, or diagnostic certificate is supplied
  unresolved:
    - concrete nonzero and zero classes for the three claim-iv witnesses
proof_use_audit:
  used_material_premises:
    - G-103 Reading.Factors as the exact law-index predicate
    - the inherited finite law index for Fintype.ofFinite
    - each retained law property for adequacy
    - the existing lawGeneratedComplex and actual ThreeCochainComplex.H1
  unused_material_premises: []
instance_pair_audit:
  status: pass
  reason: no new public Prop or certificate type; existing Factors has positive and negative instances and exact retention is proved by an iff theorem
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  alternate_diagnostic_set: none-found
  cardinality_argument: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: construct claim (iv)(a) on the canonical FactorsDiagnosticH1 surface without type-mismatch vacuity
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 24 — overresolution corollary

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 24
decision: approve
result type: proof-obligation-discharged
proof obligation: claim (iii)をactual canonical global mapに対する各fine H1 classの一意なcoarse preimageとして導く
proof obligation delta: Cycle 23のsurjectivityを存在、injectivityを一意性に展開して精細化が新しいdiagnostic classを作らないことを固定する
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceCorollary.lean`
- declaration:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.overresolution_no_new_diagnostic_classes`
- theoremはfixed `ConditionC`の下で全fine actual `H^1` classを量化し、actual
  `generatedComparisonH1Map`へ写る一意なcoarse actual `H^1` classを返す。
- Cycle 23 `generatedComparisonH1Map_bijective`のsurjective成分を存在に、injective
  成分を一意性に実使用する。coarse witnessはproof内で取得し、inverse functionや
  chosen sectionとして保存しない。
- map方向はcoarseからfineである。全fine classがそのimageに入ることが「adequateな
  精細化で新しいdiagnostic classが増えない」を直接表し、一意性はclaim (ii)の既証明
  bijectivityをそのまま展開したものなので過大化ではない。
- 新しい`DiagnosticSet`、Set.range alias、別quotient、cardinality equalityを導入せず、
  K0 / K1から生成済みのactual G-102 `H^1`だけを使う。
- focused manifest / single-file check: pass。
- targeted module build: pass、3714 jobs。新規 module のlinter warningなし。
- namespace axiom audit: 1 declaration、standard axioms only。

### Audit

- premise classification: finite Source、law family、adequate pair、supported nerves、review済み
  morphismは`ambient-boundary`。fixed `ConditionC`は`direction-hypothesis`。
- proof use: `hbijective.2`はpreimage存在、`hbijective.1`は一意性に実使用する。
  `hother.trans hmap.symm`で二つのactual global imagesを一致させてinjectivityへ渡す。
- certificate provenance: bijectivityはCycle 23 theoremから導出し、theorem inputやfieldで
  受けない。coarse classはsurjectivity proof-local output。comparison inverseやclass
  correspondence certificateを新設しない。
- structure-field escape: none-found。結論はPropの`∃!`であり、新規 data surfaceではない。
- route integrity: pass。actual coarse/fine `lawGeneratedComplex.H1`とactual canonical mapを
  直接使う。
- anti-weakening: mere renamed surjectivityで止めず、全fine classのactual canonical
  preimageを明示する。別diagnostic setやcardinality equalityへ弱めない。
- vacuity: theoremは一般の有限Sourceに成立するが、これをnondegenerate発火 witnessへ
  数えない。発火 witnessは引き続き未完として保持する。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。actual map方向、
  existence / uniquenessの両proof-use、overstrength、provenance、alternate diagnostic
  surface不在を独立承認した。
- next obligation: G-103 `Factors`判定で定まるcanonical descend可能 law部分族に基づき、
  inadequate coarse reading側のlaw-generated coefficient complexとactual `H^1`診断を定義する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 24
decision: approve
result_type: proof-obligation-discharged
proof_obligation: derive claim (iii) as a unique coarse preimage for every fine H1 class under the actual canonical global comparison map
proof_obligation_delta: Cycle 23 surjectivity supplies existence and injectivity supplies uniqueness
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceCorollary.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.overresolution_no_new_diagnostic_classes
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - every fine actual H1 class has a coarse preimage under the actual canonical map
    - the coarse preimage is unique, closing claim (iii)
  remaining:
    - canonical inadequate diagnostics
    - three counterexamples and the nondegenerate firing witness
certificate_provenance:
  discharged:
    - bijectivity is derived by Cycle 23 rather than supplied
    - the coarse preimage remains proof-local
    - no inverse function, diagnostic set, or cardinality certificate is added
  unresolved:
    - canonical Factors provenance for inadequate diagnostics
proof_use_audit:
  used_material_premises:
    - Cycle 23 global surjectivity for existence
    - Cycle 23 global injectivity for uniqueness
    - the actual coarse-to-fine generatedComparisonH1Map
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  alternate_diagnostic_set: none-found
  cardinality_argument: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: define canonical inadequate diagnostics from the G-103 Factors-selected law subfamily
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 23 — global comparison `H^1` bijectivity

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 23
decision: approve
result type: proof-obligation-discharged
proof obligation: fixed Condition Cからlabel別・finite DirectSum・actual global comparison H1 mapのbijectivityを順に証明する
proof obligation delta: Cycle 16/22の両方向をCycle 13 naturalityでactual global map自身へ輸送しclaim (ii)を閉じる
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean`
- declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_bijective`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_bijective`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map_bijective`
- label別 theoremはfixed `ConditionC`のfieldを明示投影する。injectivity側は
  C0 / C1 / C2 / C6をCycle 16へ、surjectivity側はC2 / C3 / C4 / C5をCycle 22へ
  渡す。したがってC0–C6の全fieldがreview済みのactual proof routeで実使用される。
- finite DirectSum theoremのinjectivityはexisting component theoremで各labelへ評価し、
  label別injectivityを適用してcanonical coarse component functionを一致させる。
  surjectivityは各fine componentについてlabel別surjectivityからpreimageをproof内で
  `Classical.choose`し、canonical finite DirectSum equivalenceの逆で一つのcoarse classに
  組み立てる。preimage familyはoutput fieldやcertificateに保存しない。
- global theoremはCycle 13 naturality
  `fineEquiv (globalMap x) = blockMap (coarseEquiv x)`を点ごとに使う。global injectivityは
  fine image equalityをblock-map equalityへ反射し、block-map injectivityと
  `coarseEquiv.injective`で戻す。global surjectivityは`fineEquiv fineClass`のblock
  preimageを取得し、`coarseEquiv.symm`でactual global coarse classを構成し、naturalityと
  `fineEquiv.injective`で元fine classを回収する。
- 主結論はあるLinearEquivの存在ではなく、actual canonical
  `generatedComparisonH1Map`の`Function.Bijective`である。comparison inverse、dimension
  equality、global bijectivity certificateをinputやstructure fieldに持たない。
- focused manifest / single-file check: pass。
- targeted module build: pass、3713 jobs。新規 module のlinter warningなし。
- namespace axiom audit: 3 declarations、standard axioms only。

### Audit

- premise classification: finite Source、law family、adequate pair、supported nerves、review済み
  morphismは`ambient-boundary`。fixed C0–C6 packageは`direction-hypothesis`。
- proof use: C0–C6は各fieldがCycle 16 / 22へ明示投影される。existing DirectSum
  component theoremは両方向の成分比較、Cycle 13 naturalityはactual global mapとの
  bridgeとして実使用する。unused material premiseはない。
- certificate provenance: label別両方向はreview済みCycle 16 / 22 theorem、DirectSum
  preimage familyはproof-local choice、global preimageはcanonical block equivalenceと
  本cycleで証明したblock-map surjectivityから構成する。supplied comparison inverseはない。
- structure-field escape: none-found。`ConditionC`はincidence / support propositionのままで、
  H1 bijectivity、inverse、vanishingを追加しない。新規 public Prop / structure / certificateはない。
- route integrity: pass。existing block mapはCycle 13がcomponentwise actual mapから生成した
  ものをそのまま使用する。global mapから逆算したconjugate mapへ置換しない。
- anti-weakening: actual global canonical map自身のbijectivityを結論とし、ある同型の存在、
  blockwise結果だけ、dimension equalityへ弱めない。
- loop、parallel edge、repeated face position、退化成分はreview済みper-label actual mapの
  座標を同一視せず保持され、Cycle 13もactual quotient mapとの等式である。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。C0–C6 proof-use、
  proof-local DirectSum preimages、component formula、naturalityの向き、actual global mapへの
  injective / surjective transport、certificate provenanceとcheat routeを独立承認した。
- next obligation: claim (ii)のactual global surjectivityから、adequateな精細化は診断classを
  増やさないというclaim (iii)をcanonical mapのsurjectivityとして明示するcorollaryを導く。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 23
decision: approve
result_type: proof-obligation-discharged
proof_obligation: prove per-label, finite direct-sum, and actual global comparison H1 bijectivity from the fixed Condition C package
proof_obligation_delta: Cycle 16 and Cycle 22 are transported through Cycle 13 naturality to close claim (ii) for the actual global map
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_bijective
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_bijective
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map_bijective
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - all fixed C0-C6 fields are used through the reviewed per-label injectivity and surjectivity routes
    - the existing componentwise finite direct-sum comparison map is bijective
    - the actual global generatedComparisonH1Map is bijective, closing claim (ii)
  remaining:
    - claim (iii) corollary
    - canonical inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - DirectSum preimage families are selected only inside the proof
    - global preimages use the canonical block equivalence and proved block-map surjectivity
    - no comparison inverse or dimension certificate is supplied
  unresolved:
    - full GOAL witness artifacts
proof_use_audit:
  used_material_premises:
    - C0, C1, C2, and C6 through Cycle 16 injectivity
    - C2, C3, C4, and C5 through Cycle 22 surjectivity
    - the actual DirectSum component formula and Cycle 13 naturality
    - the canonical Cycle 11 coarse and fine block equivalences
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  alternate_conjugate_map: none-found
  dimension_argument: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: derive claim (iii) directly from the actual global comparison map surjectivity
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 22 — exact-block `H^1` surjectivity

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 22
decision: approve
result type: proof-obligation-discharged
proof obligation: Cycle 21のcoarse kernel representativeをactual quotientへ送り、label別canonical comparison H1 mapの全射性を証明する
proof obligation delta: Cycle 21 primitiveの負がquotient relationのactual d0 image witnessを与える
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonSurjectivity.lean`
- declaration:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_surjective`
- 任意のfine block `H^1` classをactual
  `(LinearMap.range boundaryToCycles).mkQ_surjective`でfine kernel representativeへ
  戻す。representativeはproof内だけで取り出し、theorem inputやcertificate fieldへ
  移さない。
- Cycle 21
  `lawValueBlockCycle_exists_coordinateFiberCocycleDescent`へC2 / C3 / C4 / C5と
  fine representativeを直接渡し、primitive、actual coarse kernel representative、
  actual `generatedBlockPullback1` equalityを取得する。
- coarse preimage classはactual coarse quotientの`mkQ coarseCycle`として明示構成する。
  `generatedBlockComparisonH1Map`をactual `generatedBlockComparisonHom.h1Map`へ展開し、
  G-102 `ThreeCochainComplex.Hom.h1Map_mk`を使ってrepresentativeの等式へ戻す。
- Cycle 21の式は
  `pullback(coarseCycle) = fineCycle - d0 primitive`である。quotient relationが要求する
  左右差は`pullback(coarseCycle) - fineCycle`なので、range witnessは`-primitive`である。
  proofはactual `lawValueBlockD0`上で`map_neg`と点ごとの加法計算によりこの符号を固定する。
- focused manifest / single-file check: pass。
- targeted module build: pass、3711 jobs。新規 module のlinter warningなし。
- namespace axiom audit: 1 declaration、standard axioms only。

### Audit

- premise classification: finite Source、law family、adequate readings、supported nerves、
  reviewed morphism、labelは`ambient-boundary`。C2 / C3 / C4 / C5は
  `direction-hypothesis`。
- proof use: C2 / C3 / C4 / C5はCycle 21 principal theoremへ直接渡される。
  fine class、fine representative、primitive、coarse kernel representative、actual
  pullback equalityはすべてquotient proofで実使用する。C0 / C1 / C6をdecorative
  premiseとして追加しない。
- certificate provenance: fine representativeはactual `mkQ_surjective`、primitiveと
  coarse representativeはreview済みCycle 21 existential outputから取得する。
  coarse preimage classと`-primitive` witnessはproof内で構成し、supplied H1 preimage、
  inverse、surjectivity certificateを受けない。
- structure-field escape: none-found。新規 public Prop / structure / certificate surfaceはない。
- route integrity: pass。canonical generated comparison `h1Map`とG-102 actual quotientを
  直接使い、cycles map自体の全射性やdimension equalityへ置換しない。
- anti-weakening: 各exact source-generated blockのactual canonical map全体の全射性を
  主張する。あるmap、ある部分空間、あるrepresentativeだけの存在へ弱めない。一方で
  単射性との統合やglobal同型はまだ主張しない。
- loop、parallel edge、repeated face position、退化成分はCycle 18–21のactual
  representative routeで保持される。quotient段階でedgeやfaceを集合化せず、追加の
  distinctness premiseを要求しない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。actual quotientの
  representative構成、C2–C5のproof-use、`-primitive`の符号、canonical `h1Map` route、
  certificate provenanceとedge casesを独立承認した。
- next obligation: Cycle 16 `generatedBlockComparisonH1Map_injective`とCycle 22の全射性を、
  fixed Condition Cの該当成分から統合し、各labelのcanonical mapのbijectivityを証明する。
  その後Cycle 13 naturalityでglobal mapへ輸送する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 22
decision: approve
result_type: proof-obligation-discharged
proof_obligation: send the Cycle 21 coarse kernel representative to the actual quotient and prove surjectivity of the canonical per-label comparison H1 map
proof_obligation_delta: the negative Cycle 21 primitive supplies the actual d0-image witness for the quotient relation
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonSurjectivity.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_surjective
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - every fine block H1 class has an actual fine kernel representative
    - Cycle 21 constructs an actual coarse kernel representative whose pullback differs by an actual d0 image
    - the canonical generated block comparison H1 map is surjective
  remaining:
    - per-label bijectivity and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - fine representatives come from the actual quotient map
    - coarse representatives and primitives come from the Cycle 21 existential theorem
    - the quotient witness is the proof-local negative primitive
  unresolved:
    - per-label bijectivity integration and global block transport
proof_use_audit:
  used_material_premises:
    - C2, C3, C4, and C5 through the actual Cycle 21 theorem
    - actual generatedBlockComparisonHom, generatedBlockComparisonH1Map, and h1Map_mk
    - actual generatedBlockPullback1 equality and boundaryToCycles quotient relation
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: surjectivity is not reported as bijectivity or invariance
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: combine Cycle 16 injectivity and Cycle 22 surjectivity into per-label bijectivity for the canonical map
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 21 — coarse cocycle descent

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 21
decision: approve
result type: proof-obligation-discharged
proof obligation: C4のexact face liftとactual comm1によりCycle 20 descended cochainをcoarse block cocycleへ昇格する
proof obligation delta: degree-two pullback injectivityがfine cocycle性をactual coarse d1 kernelへ反射する
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonCocycleDescent.lean`
- declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockPullback2_injective_of_conditionC4At`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockD1_eq_zero_of_generatedBlockPullback1_eq_cocycle`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberCocycleDescent`
- `generatedBlockPullback2_injective_of_conditionC4At` は各coarse block faceにC4を適用し、
  exact fine face witnessをproof内だけで取り出す。両cochainのpullback equalityをその
  fine faceで評価し、`faceBlockCoordinateMapOption = some coarseFace` を代入して元座標を回収する。
  `[Fintype Source]`、C5、cocycle premiseを持たない。
- `lawValueBlockD1_eq_zero_of_generatedBlockPullback1_eq_cocycle` はC4から得たdegree-two
  injectivityと既存のactual `generatedBlockPullback_comm1`を使い、fine側`d1 = 0`を
  coarse側`lawValueBlockD1 = 0`へ反射する。ordered incidenceとhereditary退化宣言は
  Cycle 12の`comm1` theorem内で既に放電済みであり、新規premiseに戻さない。
- principal theoremはCycle 20
  `lawValueBlockCycle_exists_coordinateFiberDescent`を直接呼び、primitive、coarseOne、
  actual degree-one pullback equalityを取得する。fine residualがcocycleであることを
  `map_sub`、入力cycleのactual kernel proof、`lawValueBlock_d1_comp_d0`から構成し、
  C4 reflection theoremで`coarseOne`をactual coarse block kernel subtypeへ昇格する。
- focused manifest check: pass。
- targeted module build: pass、3710 jobs。新規 module の linter warningなし。
- namespace axiom audit: 4 declarations、standard axioms only。

### Audit

- premise classification: law family、adequacy、supported nerves、reviewed morphism、label、
  finite Source、actual fine block cocycleは`ambient-boundary`。C2 / C3 / C4 / C5は
  `direction-hypothesis`。
- proof use: C2 / C3 / C5はCycle 20のactual descentを通じて実使用し、C4はdegree-two
  pullback injectivityとactual coarse cocycle reflectionに実使用する。
- C0 / C1 / C6はこのnodeに不要でpremiseに含めない。C5をC4 helperで再使用せず、
  Cycle 20のmapped edge descentだけに限定する。
- certificate provenance: C4 fine-face witnessはinjectivity proof内だけで消去する。
  primitiveとcoarse one-cochainはCycle 20 existential output、kernel membershipはC4と
  actual `comm1`から構成する。face section、lift family、cocycle certificate structureを
  追加しない。
- structure-field escape: none-found。新規 public Prop / structure / certificate surfaceはない。
- route integrity: pass。supplied degree-two injectivityやsupplied coarse kernel proofを
  theorem inputにせず、C4とactual comparison mapから導く。
- anti-weakening: actual coarse block `ker d1`とactual degree-one pullback equalityだけを主張し、
  quotient class、block H1全射性、global invarianceへ読み替えない。
- repeated boundary edgeは既存`comm1`のposition付き交代和により保持され、parallel coarse
  faceはC4のface座標ごとの存在だけで処理する。face-lift uniquenessは要求しない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。C4 exact
  face liftの座標別実使用、actual `comm1`によるkernel reflection、Cycle 20とactual
  `d1d0`からのhelper premise放電、repeated edge / parallel face / self-loop、report scopeを
  独立承認した。
- next obligation: Cycle 21のkernel representativeをactual quotientへ送り、residualとの差が
  actual `d0 primitive`であることからlabel別`generatedBlockComparisonH1Map`の全射性を証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 21
decision: approve
result_type: proof-obligation-discharged
proof_obligation: upgrade the Cycle 20 descended cochain to an actual coarse block cocycle using exact C4 face lifts and the actual comm1 law
proof_obligation_delta: degree-two pullback injectivity reflects fine cocyclehood into the actual coarse d1 kernel
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonCocycleDescent.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockPullback2_injective_of_conditionC4At
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockD1_eq_zero_of_generatedBlockPullback1_eq_cocycle
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberCocycleDescent
build_status: pass
axiom_audit_status: pass
placeholder_scan_status: pass
statement_not_weakened: pass
hidden_material_premise: none-found
premise_delta:
  discharged:
    - C4 exact face lifts make the actual generated degree-two block pullback injective
    - actual comm1 reflects fine cocyclehood to the descended coarse one-cochain
    - Cycle 20 descent is upgraded to an actual coarse block kernel representative
  remaining:
    - per-label H1 surjectivity, bijectivity, and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - C4 face lifts are eliminated only inside the injectivity proof
    - coarse kernel membership is derived from actual comm1 rather than supplied as data
  unresolved:
    - quotient-level H1 preimage construction
proof_use_audit:
  used_material_premises:
    - C2, C3, and C5 through the actual Cycle 20 descent theorem
    - C4 exact face lift existence
    - actual generatedBlockPullback2 and generatedBlockPullback_comm1
    - actual fine cocycle and lawValueBlock_d1_comp_d0
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: coarse cocycle descent is not reported as H1 surjectivity
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove per-label generatedBlockComparisonH1Map surjectivity from the Cycle 21 kernel representative
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 20 — normalized residual descent

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 20
decision: approve
result type: proof-obligation-discharged
proof obligation: C2/C5によりCycle 19 normalized residualをcoarse one-cochainのactual generated block pullbackとして表す
proof obligation delta: proof-local exact edge liftsとblock uniquenessがactual degree-one descentを与える
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberDescent.lean`
- declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.exists_coarse_one_cochain_of_zero_on_degenerate_edges`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberDescent`
- generic theoremはC2から各coarse block edgeのfine liftをproof内で選び、
  `coarseOne coarseEdge := fineOne (fineLift coarseEdge)` と定める。`[Fintype Source]`、C3、
  C4をpremiseに持たない。
- actual `edgeBlockCoordinateMapOption` を直接case splitする。`none` branchは入力の
  degenerate-edge zeroを使い、`some coarseEdge` branchはC5のreview済み
  `conditionC5_block_unique` bridgeでselected liftと現在のfine edgeを同一化する。
- principal theoremはCycle 19
  `lawValueBlockCycle_exists_coordinateFiberNormalization`を直接呼び、primitiveと全
  `CoordinateFiberEdge` 上のresidual zeroを得る。generic theoremのzero premiseを外部入力として
  残さない。
- Option `none` からunderlying whole-edge `none` を得る箇所はproof内で`edgeMap`をcase splitする。
  `some` branchはcanonical `edgeBlockCoordinateMapOption_eq_some` と矛盾し、`none` branchでは
  `chartBlockCoordinateMap_edgeLeft_eq_right_of_none`により左endpoint像のcoordinate fiberを
  構成してCycle 19 zeroを適用する。
- focused manifest check: pass。
- targeted module build: pass、3709 jobs。新規 module の linter warningなし。
- namespace axiom audit: 2 declarations、standard axioms only。

### Audit

- premise classification: generic theoremのlaw family、adequacy、supported nerves、reviewed morphism、
  label、fine cochainは`ambient-boundary` / domain input、C2とC5は`direction-hypothesis`。
  principal theoremはfinite Sourceとactual block cocycleを加え、C3をCycle 19経由で実使用する。
- proof use: C2はselected lift family、C5はmapped branchのexact block uniqueness、C3はCycle 19
  actual normalization、退化geometryはOption none branchのfiber-zero放電に実使用する。
- C0 / C1 / C4 / C6はこのnodeに不要でpremiseに含めない。mapped self-loopでもC5が同じ
  coarse edgeのliftを一意化するためC6を要しない。
- certificate provenance: fine lift familyはC2 existentialからproof内でのみ`Classical.choose`し、
  coarse one-cochainはexistential theorem output。lift section、normalized certificate、coarse
  cocycle certificateをstructure fieldへ移さない。
- structure-field escape: none-found。新規 public Prop / structure / certificate surfaceはない。
- route integrity: pass。generic supplied zeroで止めず、principal theoremがCycle 19 actual residualを
  直接descendする。
- anti-weakening: actual pullback equalityだけを主張し、coarse one-cochainのcocycle性、block H1
  全射性、global invarianceへ読み替えない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。C2 selected
  lift、C5 some-branch uniqueness、Cycle 19 / C3からのnone-branch zero放電、actual
  pullback route、self-loop / parallel edge、C4未完のscope限定を独立承認した。
- next obligation: C4のexact fine face liftを評価し、descended `coarseOne` がactual coarse block
  `lawValueBlockD1` のkernelに入ることを証明する。その後label別H1全射性へ進む。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 20
decision: approve
result_type: proof-obligation-discharged
proof_obligation: descend the Cycle 19 normalized residual through the actual generated degree-one block pullback using C2 and C5
proof_obligation_delta: proof-local exact edge lifts and block uniqueness produce an actual coarse one-cochain preimage
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberDescent.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.exists_coarse_one_cochain_of_zero_on_degenerate_edges
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberDescent
premise_delta:
  ambient_boundary:
    - finite law family, adequate readings, supported nerves, reviewed morphism, label, and actual block cocycle
  discharged:
    - C2 proof-local selection of one exact fine lift for every coarse block edge
    - C5 identification of every mapped fine edge with the selected exact lift
    - Cycle 19 normalized residual vanishing on the degenerate Option branch
    - actual generatedBlockPullback1 equality for the normalized residual
  remaining:
    - C4 proof that the descended coarse one-cochain is an actual cocycle
    - per-label H1 surjectivity, bijectivity, and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - exact edge lifts are selected only from C2 inside the generic proof
    - the degenerate-edge zero premise is discharged from the actual Cycle 19 theorem
  unresolved:
    - actual coarse cocycle and H1 preimage construction
proof_use_audit:
  used_material_premises:
    - C2 exact Option lift existence
    - C5 whole-to-block lift uniqueness
    - C3 through the actual Cycle 19 normalization theorem
    - actual edgeBlockCoordinateMapOption and generatedBlockPullback1 branches
    - endpoint-fiber equality for the degenerate branch
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: degree-one descent is not reported as cocycle descent or H1 surjectivity
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: use C4 to prove that the descended coarse one-cochain lies in the actual coarse block d1 kernel
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 19 — coordinate-fiber residual normalization

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 19
decision: approve
result type: proof-obligation-discharged
proof obligation: chart-fiber primitivesを一つのfine zero-cochainへ組み立て、actual residualを全coordinate-fiber edge上で零化する
proof obligation delta: Cycle 18のlocal primitivesをcanonical chart block mapに沿ってproof-localにassemblyした
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberNormalization.lean`
- principal declaration:
  `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberNormalization`
- 各coarse block chartにCycle 18
  `lawValueBlockCycle_exists_coordinateFiberPrimitive`を直接適用し、そのexistential outputを
  theorem proof内だけで選ぶ。
- assembled primitiveはfine chartを、そのcanonical
  `chartBlockCoordinateMap` imageに対応するlocal primitiveで評価する。coarse chartの
  representative、path、section、spanning tree、basisを選ばない。
- `CoordinateFiberEdge` の二つのendpoint equalityを実使用することで、edgeの左右endpointが
  同じlocal primitiveを参照する。Cycle 18のactual `lawValueBlockD0` equalityを代入し、
  `cycle fineEdge - lawValueBlockD0 primitive fineEdge = 0` を得る。
- C0 / C1はpremiseに含めない。fine chartからcoarse chartへのmapはtotalであり、codomain
  全射性はassemblyに不要。Cycle 18は非連結fiberの全edge上ですでにprimitive equalityを
  与えるためconnectivityも不要。
- focused manifest check: pass。
- targeted module build: pass、3708 jobs。新規 module の linter warning なし。
- namespace axiom audit: 2 declarations、standard axioms only。

### Audit

- premise classification: finite Source、adequacy、supported nerves、reviewed morphismは
  `ambient-boundary`。label別C3だけが`direction-hypothesis`。C0 / C1 / C2 / C4 / C5 /
  C6はこのtheoremのpremiseではない。
- proof use: C3はCycle 18のactual local primitive theoremを各coarse chartについて呼ぶことで
  実使用する。assembled cochainと結論はactual `chartBlockCoordinateMap`、
  `CoordinateFiberEdge`、`lawValueBlockD0`を直接使う。
- certificate provenance: local primitive familyはCycle 18 theorem outputsからproof内でのみ
  `Classical.choose`する。primitive family、normalized residual、fiber exactnessをcondition、
  morphism、certificate fieldへ移さない。
- structure-field escape: none-found。新規 public Prop / structure / certificate surfaceはない。
- route integrity: pass。`∀ coarseChart, ∃ localPrimitive` を無根拠に量化交換せず、各fine chartの
  canonical map imageとfiber edgeの両endpoint equalityで単一primitiveを明示構成する。
- anti-weakening: residualのfiber-edge消滅だけを主張し、actual kernel cycle、coarse descent、
  block H1全射性、global invarianceへ読み替えない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。量化assembly、
  `CoordinateFiberEdge` の左右endpoint equalityの実使用、actual `lawValueBlockD0`
  residual、C0 / C1不要性、proof-local choice provenance、空fiberでのscope限定を
  独立承認した。
- next obligation: C2で各coarse block edgeのliftをproof内で選び、C5で一意化してnormalized
  residualをcoarse one-cochainからのactual generated block pullbackとして表す。退化branchは
  fiber-edge消滅を使い、その次にC4でcoarse cocycle equationを証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 19
decision: approve
result_type: proof-obligation-discharged
proof_obligation: assemble the Cycle 18 chart-fiber primitives and normalize the actual fine block cocycle on every coordinate-fiber edge
proof_obligation_delta: a single proof-local fine zero-cochain now removes the actual cocycle on every coordinate fiber
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberNormalization.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberNormalization
premise_delta:
  ambient_boundary:
    - finite Source, finite law family, adequate readings, supported nerves, and reviewed morphism
  discharged:
    - proof-local assembly of every Cycle 18 chart-fiber primitive
    - actual residual vanishing on every endpoint-defined coordinate-fiber edge
  remaining:
    - C2 and C5 descent of the normalized residual to a coarse one-cochain
    - C4 proof that the descended coarse one-cochain is an actual cocycle
    - per-label H1 surjectivity, bijectivity, and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - local primitives are selected only from Cycle 18 theorem outputs inside this proof
    - each fine chart is assigned by its canonical chart block map image
  unresolved:
    - proof-local edge lift selection and canonical H1 preimage construction
proof_use_audit:
  used_material_premises:
    - C3 through the actual Cycle 18 local primitive theorem
    - both endpoint equalities in CoordinateFiberEdge
    - the actual chartBlockCoordinateMap and lawValueBlockD0 formula
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: fiber normalization is not reported as H1 surjectivity
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: use C2 and C5 to express the normalized residual as an actual generated block pullback from a coarse one-cochain
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 18 — finite graph duality and coordinate-fiber primitive

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 18
decision: approve
result type: proof-obligation-discharged
proof obligation: 全supported cycleのperiod消滅からvertex potentialを導き、actual exact-block fiber上のd0 primitiveへ接続する
proof obligation delta: finite dual annihilator theoremとCycle 17を通じてC3をactual local primitive existenceまで進めた
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberPrimitive.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.FiniteDirectedMultigraph.exists_potential_on_of_annihilates_supported_cycles`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberPrimitive`
- generic theorem は有限 vertex / edge型、左右 endpoint、任意の supported edge predicateを
  量化する。incidence pairing と value pairingはfiber外edgeを零にmaskし、simple graph、
  loop-free、parallel-edge-free、connected の仮定を置かない。
- incidence kernelのchainを各 `Pi.single` vertexで評価し、masked chainのincoming / outgoing
  equalityを得る。period仮定をこのchainへ適用してvalue pairingがkernelをannihilateする
  ことを示す。
- `LinearMap.dualAnnihilator_ker_eq_range_flip` によりvalue pairingをflipped incidence mapの
  rangeへ入れ、そのrange witnessをvertex potentialとして取得する。各 `Pi.single` edgeで
  equalityを評価してsupported edgeごとの right-minus-left 公式を得る。
- specialization はsupported predicateをactual `CoordinateFiberEdge` とし、generic theoremの
  period仮定をCycle 17
  `lawValueBlockCycle_annihilates_coordinateFiberCycle` で直接放電する。出力はactual
  `fine.lawValueBlockD0` 公式である。
- exact block chart / edge の module-local `Fintype` instances はCycle 14のcanonical
  coordinate subnerveから定義的に導出する。
- focused manifest check: pass。
- targeted module build: pass、3707 jobs。新規 module の linter warning なし。
- namespace axiom audit: 4 declarations、standard axioms only。

### Audit

- premise classification: generic theoremの有限型・endpoint・support predicate・period仮定は
  `domain-interface`。specializationのfinite Source、adequacy、supported nerves、reviewed
  morphismは`ambient-boundary`、label別C3だけが`direction-hypothesis`。
- proof use: generic `hperiod` はdual-annihilator membershipに実使用し、specializationは
  Cycle 17 actual period theoremを直接呼ぶ。C3、actual block cocycle、fiber cycle predicate、
  actual `lawValueBlockD0` へrouteが連続する。
- C1はこのnodeに不要。非連結成分ごとにpotentialの加法定数が独立でもexistenceは成立する。
  C1を装飾premiseとして追加せず、Cycle 16での既存proof-useと区別する。
- loopでは単一edge circulationが値を零に強制し、parallel edgeでは二edge差のcirculationが
  値の一致を強制する。generic theoremはedgeをquotientせず多重性を保持する。
- certificate provenance: potentialはdual-annihilator range witnessからexistential outputとして
  取得する。selected path、spanning tree、basis、section、primitive field、range-membership
  premiseを入力に持たない。potentialのcanonicalityや一意性を主張しない。
- structure-field escape: none-found。新規 public Prop / structure / certificate surfaceはない。
- route integrity: pass。dimension equalityだけで結論を出さず、incidence pairing、kernel
  annihilation、flipped range、actual d0をLean termで接続する。
- anti-weakening: fiber-local primitiveだけを主張し、全fine zero-cochainへのassembly、residual
  descent、block H1全射性、global invarianceへ読み替えない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。supported mask、
  dual-annihilator / flip の向き、right-minus-left の符号、loop / parallel / 非連結
  graphでの成立、Cycle 17からactual `lawValueBlockD0` へのproof-useを独立承認した。
- next obligation: coarse block chartごとのprimitiveをproof内で選び、chart block mapに沿って
  一つのfine zero-cochainへ組み立て、元cocycleからそのd0を引いたresidualが全fiber edge上で
  零になることを証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 18
decision: approve
result_type: proof-obligation-discharged
proof_obligation: derive a vertex potential from supported-cycle period vanishing and specialize it to the actual exact-block coordinate fiber
proof_obligation_delta: finite dual annihilator theory and Cycle 17 produce an actual local d0 primitive from C3
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberPrimitive.lean
    declarations:
      - AAT.AG.ResolutionInvariance.FiniteDirectedMultigraph.exists_potential_on_of_annihilates_supported_cycles
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_exists_coordinateFiberPrimitive
premise_delta:
  ambient_boundary:
    - finite Source, finite law family, adequate readings, supported nerves, and reviewed morphism
  discharged:
    - finite directed multigraph duality from supported period vanishing to a vertex potential
    - proof-local coordinate-fiber primitive for every actual exact-block cocycle under C3
  remaining:
    - assembly of chart-fiber primitives and normalization of the fine cocycle
    - C2-C5 residual descent and per-label H1 surjectivity
    - per-label bijectivity and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - the potential is an existential flipped-range witness derived from kernel annihilation
    - exact-block finiteness is derived from the reviewed canonical coordinate subnerve
  unresolved:
    - proof-local assembly and canonical H1 preimage construction
proof_use_audit:
  used_material_premises:
    - the generic period hypothesis in dual-annihilator membership
    - the actual Cycle 17 C3 period theorem in the exact-block specialization
    - the actual coordinate-fiber predicate and lawValueBlockD0 formula
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: local primitive existence is not reported as H1 surjectivity
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: assemble proof-local fiber primitives into one fine zero-cochain and prove residual vanishing on every coordinate-fiber edge
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 17 — exact block cocycle fiber-period vanishing

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 17
decision: approve
result type: proof-obligation-discharged
proof obligation: C3 の局所 rational filling を actual exact-block cocycle の fiber-period 消滅へ接続する
proof obligation delta: discrete Stokes と C3 existential elimination により全 coordinate-fiber period を零にした
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberPeriods.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockCycle_annihilates_coordinateFaceBoundary`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_annihilates_coordinateFiberCycle`
- 最初の theorem は任意の exact block face chainについて、`e₀ - e₁ + e₂` の各
  incidence sum を edge-first から face-first へ交換する。各 face の summand は actual
  `lawValueBlockD1` cocycle equation で零になるため、face chain の oriented incidence
  image と cocycle の pairing は零になる。
- 次の theorem は `ConditionC3At` を指定 coarse block chart と coordinate-fiber cycle に
  適用し、face chain と pointwise equalityを proof 内でだけ取得する。その equalityを
  pairingへ代入し、最初の theoremを適用する。
- exact block edge / face の module-local `Fintype` instance は Cycle 14 の canonical
  coordinate subnerve instanceから定義的に導出する。有限性を新たな theorem premiseや
  data field として受け取らない。
- focused manifest check: pass。
- targeted module build: pass、3706 jobs。新規 module の linter warning なし。
- namespace axiom audit: 5 declarations、standard axioms only。

### Audit

- premise classification: finite Source、finite law family、adequate pair、supported nerves、
  reviewed morphism は `ambient-boundary`。label 別 C3 はこの node 唯一の
  `direction-hypothesis`。C1 / C2 / C4 / C5 は theorem argumentに入れない。
- proof use: actual block cocycle equation、3位置すべての face-edge incidence、C3 の
  existential face chain、pointwise chain equalityを実使用する。C3 output の
  internal-face support conjunct は scalar period の結論には論理的に不要で未使用である。
  C3 package全体の独立必要性や support conjunct の proof-useはこの cycle では主張しない。
- certificate provenance: face chain は C3 Propから proof-localに取得するだけで、selected
  filling、primitive、basis、section、path、inverseを structureへ保存しない。
- structure-field escape: none-found。新規 public Prop / structure / certificate surfaceはない。
- route integrity: actual `lawValueBlockComplex.d1`、exact block coordinates、固定 C3 の
  `coordinateFaceBoundary` を直接使う。dimension count、`H^1 = 0`、supplied inverse、
  conclusion-equivalent exactness premiseを使わない。
- anti-weakening: fiber period vanishingだけを主張し、fiber primitive、block map の
  surjectivity / bijectivity、global invarianceへ読み替えない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。C3 output の
  internal-face support conjunct は exact filling witnessへの制約として維持されるが、
  Stokes pairing は pointwise equalityだけで成立するため、projection後にその proofを
  再使用しないことは hidden premise や overclaim ではないと判定された。
- next obligation: finite rational graph dualityにより、全 fiber cycleを annihilate する
  edge cochainから proof-local fiber primitiveを構成する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 17
decision: approve
result_type: proof-obligation-discharged
proof_obligation: connect C3 local rational filling to vanishing of every actual exact-block cocycle fiber period
proof_obligation_delta: discrete Stokes and proof-local C3 elimination remove every coordinate-fiber period obstruction
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonFiberPeriods.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockCycle_annihilates_coordinateFaceBoundary
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.lawValueBlockCycle_annihilates_coordinateFiberCycle
premise_delta:
  ambient_boundary:
    - finite Source, finite law family, adequate readings, supported nerves, and reviewed morphism
  discharged:
    - discrete Stokes for every actual exact-block cocycle and rational face chain
    - vanishing of the period on every coordinate-fiber cycle under C3
  remaining:
    - finite graph duality and proof-local fiber primitive construction
    - C2-C5 normalization and per-label H1 surjectivity
    - per-label bijectivity and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - C3 face coefficients are eliminated proof-locally and never stored
    - edge and face finiteness is derived from the reviewed canonical coordinate subnerve
  unresolved:
    - proof-local fiber primitive and canonical H1 preimage construction
proof_use_audit:
  used_material_premises:
    - actual block d1 cocycle equation
    - all three oriented face-edge incidence positions
    - C3 face-chain existence and exact pointwise equality
  unused_material_premises:
    - the internal-face support conjunct returned by C3 is not needed for this scalar consequence
    - C1, C2, C4, and C5 are intentionally deferred
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: fiber-period vanishing is not reported as primitive existence or surjectivity
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove finite rational graph duality from cycle-annihilation to a proof-local fiber primitive
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 16 — exact block comparison H1 injectivity

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 16
decision: approve
result type: proof-obligation-discharged
proof obligation: exact law-value block 上の generated comparison H1 map の injectivity を証明する
proof obligation delta: C0 / C1 / C2 / C6 を actual quotient H1 の coarse coboundary reflection に接続した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonInjectivity.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.conditionC0_chartBlockCoordinateMap_surjective`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.fineZero_eq_of_coordinateFiberAdjacent`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.fineZero_eq_of_same_coordinateFiber`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.exists_coarse_zero_cochain_of_generatedBlockPullback1_eq_d0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_injective`
- C0 bridge は coarse K0 coordinate の actual occurrence witness を取り出し、C0 の
  support equality と `lawDescend_comparisonFactor` から同一 law-value を持つ fine
  occurrence を生成する。従って block chart map の全射性を selected section なしで
  theorem として導く。
- fiber adjacency 上の primitive constancy は canonical edge Option map を分岐する。
  `none` branch は generated degree-one pullback の零規則、`some` branch は exact
  endpoint bridge と C6 の block endpoint reflection を使う。C1 の
  `Relation.ReflTransGen` path induction で fiber 全体へ拡張する。
- C0 の existential から選ぶ chart representative は coarse primitive proof の局所
  `let` に限る。C2 の各 exact edge lift で fine `d0` equality を評価し、coarse
  `lawValueBlockD0` primitive を得る。
- actual `generatedBlockComparisonH1Map` の kernel class を G-102 quotient の cycle
  representative へ持ち上げ、`Submodule.Quotient.mk_eq_zero` で fine primitive を取得する。
  上記 reflection theorem から coarse primitive を生成して元 class を零と示す。
- focused manifest check: pass。
- targeted module build: pass、3706 jobs。新規 module の linter warning なし。
- namespace axiom audit: 7 declarations、standard axioms only。

### Audit

- premise classification: finite Source、finite law family、adequate pair、supported nerves、
  reviewed morphism は `ambient-boundary`。C0 / C1 / C2 / C6 はこの単射性方向の
  `direction-hypothesis`。C3 / C4 / C5 は theorem argument に入れず、次の全射性
  obligation へ送る。
- proof use: C0 は K0 occurrence と descend compatibility を持つ block chart lift、C1 は
  fiber connectivity、C2 は actual Option edge lift、C6 は mapped coarse self-loop の
  fine self-loop reflection に実使用する。C0 が chart nonemptiness を与えるため、C1 の
  nonempty conjunct と論理的に重なるが、C1 は path conjunct に実使用する。
- certificate provenance: representatives は C0 existential、paths は C1 Prop、primitive は
  existing quotient membership から proof 内でのみ選ぶ。新規 structure、section、inverse、
  primitive certificate はない。
- structure-field escape: none-found。result は actual generated block map の injectivity
  theorem であり、同型 premise、dimension equality、片側 `H^1 = 0` を受けない。
- route integrity: actual exact block coordinates、`lawValueBlockD0`、generated block Hom / H1
  map、G-102 quotient API を直接使用する。
- anti-weakening: label 別 injectivity だけを主張し、surjectivity、bijectivity、global
  invariance、claim (ii) completion を主張しない。
- blocking findings: none。
- fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: C1 / C2 / C3 / C4 / C5 を使う label 別 surjectivity を
  証明し、bijectivity と Cycle 13 naturality から global invariance へ輸送する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 16
decision: approve
result_type: proof-obligation-discharged
proof_obligation: prove injectivity of the generated comparison H1 map on every exact law-value block
proof_obligation_delta: connected C0, C1, C2, and C6 to actual quotient-level coarse coboundary reflection
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonInjectivity.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.conditionC0_chartBlockCoordinateMap_surjective
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.fineZero_eq_of_coordinateFiberAdjacent
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.fineZero_eq_of_same_coordinateFiber
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.exists_coarse_zero_cochain_of_generatedBlockPullback1_eq_d0
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_injective
premise_delta:
  ambient_boundary:
    - finite Source, finite law family, adequate pair, supported nerves, and reviewed morphism
  discharged:
    - C0-derived surjectivity of the canonical exact-block chart map
    - constancy of a fine primitive along C1 fiber paths using the zero branch and C6
    - coarse primitive reconstruction through C2 exact edge lifts
    - injectivity of the actual generated block comparison H1 map
  remaining:
    - per-label surjectivity using C1-C5
    - per-label bijectivity and global invariance through Cycle 13 naturality
    - corollary, inadequate diagnostics, three counterexamples, and nondegenerate firing witness
certificate_provenance:
  discharged:
    - block chart lifts are generated from C0 support witnesses and canonical law descent
    - representatives, paths, and primitives remain proof-local existential eliminations
  unresolved:
    - surjectivity normalization and the final canonical H1 isomorphism
proof_use_audit:
  used_material_premises:
    - C0 for provenance-bearing block chart lifts
    - C1 for fiber path induction
    - C2 for exact coarse-edge lifts
    - C6 for mapped self-loop endpoint reflection
  unused_material_premises:
    - C3, C4, and C5 are intentionally deferred to surjectivity
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: injectivity is explicitly recorded as one half only
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove per-label surjectivity using C1-C5 and combine it with injectivity
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 15 — incidence / support-only C0–C6 package

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 15
decision: approve
result type: proof-obligation-discharged
proof obligation: fixed GOAL の whole-nerve / coordinate-relative C0–C6 を incidence / support data だけで定義する
proof obligation delta: 不変性 theorem の全 material direction hypotheses と exact block bridge を固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean`
- Lean instance file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditionInstances.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC1`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC2`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC3`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC4`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC5`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC6`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.conditionC5_block_unique`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.conditionC6_block_endpoint_reflection`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.missing_not_conditionC`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC0`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC1`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC2`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC3`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC4`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC5`
  - `AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC6`
- C0 は各 coarse chart support と、その chart fiber に属する fine chart support の
  canonical `comparisonFactor` image の合併を pointwise iff で同定する。
- C1 は各 exact coarse block chart の fiber を非空とし、両 endpoint coordinate が
  その chart へ写る全 fine block edge による undirected graph で連結とする。
- C2 / C4 は canonical `edgeBlockCoordinateMapOption` /
  `faceBlockCoordinateMapOption` が exact same-label coarse block cell を返す lift を
  要求する。
- C3 は全 fine block edge 上の有限 `ℚ` chain を量化する。fiber 外で零、fiber 内の
  全 chart で incoming = outgoing を満たす chain を、3本すべてが fiber edge である
  fine block face の `e₀ - e₁ + e₂` oriented boundary の線形結合として表す。
  `edgeMap = none` / `faceMap = none`、global complex、`H^1`、comparison map を
  定義に参照しない。
- C5 / C6 は whole nerve 上で量化し、C6 は C5 と独立に全 mapped edge へ課す。
  exact block の lift 一意性と self-loop endpoint reflection は、Cycle 14 の cell
  projection 単射性と canonical Option map から theorem として導出する。
- `ConditionC` は7個の命題 fieldだけを束ねる。lift、path、filling chain、inverse、
  cohomology certificate は data field にしない。
- instance fixture は C0–C6 と aggregate C の正例に加え、C0 / C1 / C2 / C4 の
  image 欠落、C5 / C6 の重複 self-loop lift、C3 の内部 face 欠落による反例を持つ。
  `CoordinateFiberEdge`、`CoordinateFiberAdjacent`、`ConditionC1At`、
  `ConditionC2At`、`CoordinateFiberCycle`、`CoordinateInternalFace`、
  `ConditionC3At`、`ConditionC4At` にもそれぞれ正負 witness を置き、定義が空・恒真・
  恒偽へ退化していないことを Lean で固定した。
- positive fixture は proper な reading refinement、2 chart を持つ coarse-chart fiber、
  ordinary / self-loop / reverse edge、triangle / repeated-edge face、宣言済み退化 edge を
  同時に含む。一方、law は constant で各 coordinate subnerve は whole nerve なので、
  claim (v) の nondegenerate 発火 witness と区別する。
- focused manifest check: pass。
- targeted module build: Conditions は pass、3705 jobs。ConditionInstances は pass、
  3706 jobs。新規 modules の linter warning なし。
- namespace axiom audit: Conditions は33 declarations、ConditionInstances は
  129 declarations、いずれも standard axioms only。
- ConditionInstances の named declaration 127件はすべて declaration-level
  `/--` docstring を持ち、fixture / API / instance-pair 内の position と premise 出自を
  記録する。`@[simp]` theorem は normal-form direction も明記する。
- placeholder、hidden / bidirectional Unicode、local-path、禁止語、reverse-import scan: clean。

### Audit

- premise classification: 有限 Source、finite law family、adequate pair、supported nerves、
  reviewed morphism は `ambient-boundary`。C0–C6 は固定 theorem の
  `direction-hypothesis` である。有限 instance pair は条件 API の nonvacuity と
  識別能力を固定する品質証拠であり、不変性や claim (v) の発火 witness には数えない。
- certificate provenance: C0 は canonical factor、C1–C4 は reviewed K0 / K1 の
  exact block coordinates、C2 / C4 は generated partial block transportを使う。
  C3 に cycle basis、filling certificate、global complex、cohomology datumを
  導入しない。
- proof use: C5 bridge は C5、両 Option-map hypotheses、whole-edge extraction、
  edge-cell injectivityを実使用する。C6 bridge は C6、Option-map hypothesis、
  coarse self-loop equality、chart-cell injectivityを実使用し、C5を使わない。
  `Fintype Source` は全 block edge / face 上の有限和に使用する。
- structure-field escape: none-found。C3 は許可された局所 fiber acyclicityそのもの。
  global exactness、comparison equivalence、`H^1` vanishing、selected path / fillingを
  fieldにしない。
- route integrity: pass。relative clauses は canonical coordinate subnerveとexact
  block transportに追跡でき、whole-nerve clausesを label 相対へ弱めていない。
- cheat route: `edgeMap = none`限定C3、global cohomologyへの置換、空 / singleton
  特例、target-fitting certificate、結論相当fieldは none-found。
- initial fixed-head review finding: 最初の snapshot は新規 public Prop 条件の
  positive / negative instance pair を欠き、Lean quality standard §1.4 / §6 に反したため
  major finding を受けた。受理前に同一 Cycle 内で finite pair file を追加し、aggregate、
  principal C0–C6、全補助条件を正負両側から検査した。修正後 snapshot は fresh T3 と
  4 lane fixed-head review の対象とする。
- second fixed-head review finding: instance-pair 修正 snapshot は追加 file の
  declaration docstring が127件中2件だけで、Lean quality standard §3.2 / §6 に反したため
  4 lane すべてで major finding を受けた。受理前に同 file の残る125件へ declaration-level
  docstring を追加し、public abbrev / def / theorem と named local instance を127/127で収載した。
  この修正は signature / proof term / statement を変えず、再 focused elaboration、targeted
  build、129-declaration standard-axiom audit を通した。この修正 snapshot の fresh T3 は
  approve であり、最終受理には4 lane fixed-head reviewを改めて要求する。
- blocking findings: none。
- final docstring repair 後 fresh independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: C1–C6から各 label の定数係数 block comparison `H^1` map が
  同型であることを、C3の局所 fiber contractionとC5 / C6 bridgeを実使用して証明し、
  Cycle 13 の naturalityでglobal generated comparison mapへ輸送する。C0の最終
  proof-useを明示的に追跡する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 15
decision: approve
result_type: proof-obligation-discharged
proof_obligation: define the fixed whole-nerve and coordinate-relative incidence/support-only C0-C6 package
proof_obligation_delta: fixed every material direction hypothesis and its exact block bridge before the invariance proof
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC0
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC1
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC2
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC3
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC4
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC5
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC6
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.ConditionC
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.conditionC5_block_unique
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.conditionC6_block_endpoint_reflection
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditionInstances.lean
    declarations:
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.missing_not_conditionC
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC0
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC1
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC2
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC3
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC4
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC5
      - AAT.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances.positive_conditionC6
premise_delta:
  ambient_boundary:
    - finite Source, finite law family, adequate pair, supported nerves, and reviewed morphism
  discharged:
    - exact whole-nerve C0, C5, and C6 predicates
    - exact coordinate-relative C1-C4 predicates for every source-generated label
    - local rational C3 on all endpoint-defined fiber edges with oriented internal-face boundaries
    - proposition-only aggregate ConditionC package
    - whole-nerve C5 and C6 consequences on exact block coordinates
    - finite positive and negative instance pairs for aggregate ConditionC, every principal C0-C6 predicate, and every public helper predicate
  remaining:
    - blockwise and global invariance
    - nondegenerate ConditionC realization, corollary, inadequate diagnostics, counterexamples, and firing witness
certificate_provenance:
  discharged:
    - support comparison and block transports are canonical reviewed constructions
    - C3 stores no selected basis or filling data
    - quality instances separate image omission, duplicate lifts, endpoint failure, and missing internal faces
  unresolved:
    - nondegenerate claim-v realization and canonical H1 isomorphism
proof_use_audit:
  used_material_premises:
    - C5, exact Option maps, whole-edge extraction, and edge-cell injectivity in the uniqueness bridge
    - C6, exact Option map, coarse loop equality, and chart-cell injectivity in the endpoint bridge
    - finite Source for complete rational edge and face sums
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found for the condition API; the constant-law fixture is explicitly not accepted as claim-v firing evidence
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove per-label block H1 invariance and transport it globally while tracking C0 proof-use
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 14 — canonical law-value coordinate subnerve

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 14
decision: approve
result type: proof-obligation-discharged
proof obligation: K0 / K1 exact block coordinate から各 source-generated label の canonical 座標 subnerve を構成する
proof obligation delta: C1–C4 の相対化対象を任意 selection なしで3次数すべて固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueCoordinateSubnerve.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.CellCoordinate.block_cell_injective`
  - `AAT.AG.ResolutionInvariance.CellCoordinate.exists_block_coordinate_cell_iff`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerve`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerveChartCell_injective`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerveEdgeCell_injective`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerveFaceCell_injective`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.chart_occurs_in_lawValueCoordinateSubnerve_iff`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.edge_occurs_in_lawValueCoordinateSubnerve_iff`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.face_occurs_in_lawValueCoordinateSubnerve_iff`
- subnerve の cell 型は Cycle 10–13 が使う `ChartBlockCoordinate` /
  `EdgeBlockCoordinate` / `FaceBlockCoordinate` そのものであり、同型な複製型や
  caller-supplied predicate を使わない。
- endpoint と face incidence は既存 block incidence map、overlap predicate と
  holds proof は underlying nerve component から定義として継承する。
- general `CellCoordinate` theorem により、固定 label 内では cell projection が
  単射であり、target occurrence witness や source generator の proof data が
  coordinate multiplicity を作らないことを固定した。
- chart / edge / face occurrence theorem は、各 cell の support 上で
  `lawDescend ... label.law = label.value` となる target の存在と subnerve cell の
  存在を双方向で同定する。edge / face 側の support は K1 の導出台である。
- focused manifest check: pass。
- targeted module build: pass、3704 jobs。新規 module の linter warning なし。
- namespace axiom audit: 22 declarations、standard axioms only。
- placeholder、hidden / bidirectional Unicode、local-path、禁止語、reverse-import scan: clean。

### Audit

- premise classification: finite Source、finite law family、adequate reading、
  `TargetSupportedNerve`、source-generated label は `ambient-boundary`。subnerve、
  projection 単射性、exact occurrence characterization は Cycle 14 の出力である。
- certificate provenance: cell selection は K0 `CellCoordinate.Block` の fixed-label
  fiber そのものである。chart は declared support、edge / face は K1 intersection
  support 上の actual `lawDescend` occurrence に追跡できる。
- proof use: dependent law / value equalityは `Sigma laws.Value` の equality から
  law equality と `HEq` value を回収して projection 単射性に実使用する。
  occurrence iff の forward / reverse 両方向、既存 block incidence、underlying
  overlap component、Source と ambient cell の有限性を実使用する。
- structure-field escape: none-found。arbitrary cell membership、closure certificate、
  C 条件、comparison isomorphism、cohomology vanishing を入力 field にしない。
- route integrity: pass。全 `LawValueLabel` を一様に扱い、coarse / fine の双方で
  同じ construction を instantiate する。global `H^1` や C の真偽を membership に
  参照しない。
- cheat route: whole-nerve alias、空 / singleton subnerve、opaque selection、
  occurrence multiplicity、law-name-only annotation、target-fitting membership は
  none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: canonical 座標 subnerve を用い、C1–C4 を各 label 相対、
  C0 / C5 / C6 を whole nerve 上で定式化する incidence / support-only の
  condition package を構成する。global `H^1`、comparison isomorphism、
  cohomology vanishing を field に入れない。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 14
decision: approve
result_type: proof-obligation-discharged
proof_obligation: construct the canonical K0/K1 coordinate subnerve for every source-generated label
proof_obligation_delta: fixed the exact three-degree relative nerve used by C1-C4 without supplied selection
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueCoordinateSubnerve.lean
    declarations:
      - AAT.AG.ResolutionInvariance.CellCoordinate.block_cell_injective
      - AAT.AG.ResolutionInvariance.CellCoordinate.exists_block_coordinate_cell_iff
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerve
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerveChartCell_injective
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerveEdgeCell_injective
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueCoordinateSubnerveFaceCell_injective
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.chart_occurs_in_lawValueCoordinateSubnerve_iff
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.edge_occurs_in_lawValueCoordinateSubnerve_iff
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.face_occurs_in_lawValueCoordinateSubnerve_iff
premise_delta:
  ambient_boundary:
    - finite Source, finite law family, adequate reading, supported nerve, and source-generated label
  discharged:
    - canonical exact-label CoverNerve in all three degrees
    - inherited block incidence and underlying overlap components
    - injective underlying-cell projections
    - exact support-occurrence characterization in all three degrees
    - finite coordinate-subnerve cell instances
  remaining:
    - global C0/C5/C6 and coordinate-relative C1-C4
    - invariance, corollary, diagnostics, counterexamples, and firing witness
certificate_provenance:
  discharged:
    - cell selection is the reviewed K0 fixed-label block itself
    - membership is equivalent to actual lawDescend occurrence on K1-derived support
  unresolved:
    - C0-C6 hypotheses and invariance proof
proof_use_audit:
  used_material_premises:
    - exact CellCoordinate and LawValueLabel fields
    - declared chart support and K1-derived edge and face supports
    - existing block endpoint and face-incidence maps
    - underlying overlap components and finite cell instances
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: define the incidence/support-only global and coordinate-relative C0-C6 package
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 13 — quotient-level block comparison naturality

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 13
decision: approve
result type: proof-obligation-discharged
proof obligation: label 別 block h1Map の finite DirectSum と global comparison H1 map の quotient-level naturality を証明する
proof obligation delta: law-value block decomposition と generated comparison map の quotient-level 接続を放電した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonNaturality.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_component`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonCyclesMap_block_component`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map_mk_block_component`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map_block_naturality`
- direct-sum map は各 label の `generatedBlockComparisonH1Map` による product map を
  `DirectSum.linearEquivFunOnFintype` で直和へ戻して生成する。global map を
  coarse / fine block equivalence で共役して定義する循環経路は使わない。
- `generatedComparisonCyclesMap_block_component` は Cycle 12 の
  `generatedPullback1_block_component` を実使用し、global cycle map と block
  cycle map の同一 label 成分を同定する。
- representative 公式は global 側と block 側の
  `ThreeCochainComplex.Hom.h1Map_mk`、coarse / fine の
  `lawGeneratedH1BlockEquiv_mk_component`、cycle component 公式を合成する。
- 最終 square は quotient の representative extensionality と finite DirectSum の成分外延性で証明し、
  naturality や quotient equality を premise / field として受けない。
- focused manifest check: pass。
- targeted module build: pass、3703 jobs。新規 module の linter warning なし。
- namespace axiom audit: 5 declarations、standard axioms only。
- placeholder、hidden / bidirectional Unicode、local-path、禁止語、reverse-import scan: clean。

### Audit

- premise classification: finite Source / law family、adequate pair、coarseness、supported-nerve
  morphism は `ambient-boundary`。direct-sum map、cycle bridge、representative 公式、
  quotient naturality は Cycle 13 の出力である。
- certificate provenance: direct-sum map は Cycle 12 の actual block `h1Map`、cycle bridge は
  actual degree-one component theorem、quotient transport は reviewed G-102 `h1Map_mk` と
  Cycle 11 の canonical quotient decomposition に追跡できる。
- proof use: Cycle 12 の block Hom / `h1Map` と degree-one component theorem、
  Cycle 11 の coarse / fine cycle equivalence・representative 成分公式、G-102 の
  global / block 両側 `h1Map_mk` を実使用する。Cycle 12 の degree-zero /
  degree-two component theorem は本 node の直接 proof-use に数えない。
- structure-field escape: none-found。naturality、quotient equality、map family を入力しない。
- route integrity: pass。coarse `H^1` → fine `H^1` の向きと source-generated
  common label を保つ。
- cheat route: global map の共役による direct-sum map 定義、arbitrary family、
  supplied certificate、basis / finrank / dimension route、abstract equivalence は none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: K0 / K1 から座標 subnerve を生成し、C0 / C5 / C6 を global、
  C1–C4 を各座標 subnerve 相対で定式化する。C3 は fiber 内の有理1-cycle /
  face-boundary span に限定し、global `H^1` や comparison 同型相当を混入させない。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 13
decision: approve
result_type: proof-obligation-discharged
proof_obligation: prove quotient-level naturality of the finite DirectSum of actual block h1Maps
proof_obligation_delta: connected the law-value H1 decomposition to the generated comparison map
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonNaturality.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_component
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonCyclesMap_block_component
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map_mk_block_component
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map_block_naturality
premise_delta:
  ambient_boundary:
    - finite Source and law family, adequate pair, coarseness, and supported-nerve morphism
  discharged:
    - finite DirectSum of actual block h1Maps
    - global-to-block cycle-map component equality
    - quotient representative component formula
    - full quotient-level block naturality square
  remaining:
    - coordinate subnerves, C0-C6, invariance, corollary, diagnostics, counterexamples, and firing witness
certificate_provenance:
  discharged:
    - direct-sum map generated componentwise from actual block h1Maps
    - cycle bridge generated from the actual degree-one component theorem
    - quotient formula generated from reviewed h1Map_mk and canonical H1 decomposition
  unresolved: []
proof_use_audit:
  used_material_premises:
    - Cycle 12 block Hom, block h1Map, and degree-one component theorem
    - Cycle 11 cycle equivalences and representative component theorem
    - G-102 global and block h1Map_mk
  unused_material_premises:
    - Cycle 12 degree-zero component theorem
    - Cycle 12 degree-two component theorem
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: define coordinate subnerves and the global/relative C0-C6 condition package
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 12 — generated comparison on exact blocks

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 12
decision: approve
result type: proof-obligation-discharged
proof obligation: common label ごとの actual block Hom / h1Map と global pullback の3次数 block 成分一致を生成する
proof obligation delta: partial coordinate transport の mapped / degenerate 全 branch を exact coordinate fiber 上で放電した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparison.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.chartBlockCoordinateMap`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.edgeBlockCoordinateMapOption`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.faceBlockCoordinateMapOption`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockPullback0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockPullback1`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockPullback2`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonHom`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback0_block_component`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback1_block_component`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback2_block_component`
- chart / mapped edge / mapped face の subtype membership は Cycle 10 の3本の
  `*_lawValueLabel` theorem と input coordinate の block membership を合成して生成する。
  reading 間 label bijection や occurrence index は追加しない。
- degree 1 / 2 の block coordinate transport は Cycle 9 と同じ `Option` で、mapped
  branch のみ coarse block coordinate を返し、宣言された退化 branch は `none`
  のまま保つ。block pullback は `Option.elim 0` により零を生成する。
- block `comm0` の mapped branch は `edge_some_left/right`、退化 branch は
  `edge_none_fiber` を使う。block `comm1` は mapped branch の
  `face_some_edge0/1/2` と degenerate branch の `face_none_edge0/1/2` を全て使う。
- `generatedBlockComparisonHom` の source は coarse block complex、target は fine block
  complex。`generatedBlockComparisonH1Map` はこの Hom の reviewed G-102 `h1Map` である。
- global pullback の3本の component theorem は Cycle 10 の canonical coordinate-fiber
  decomposition を使い、degree 1 / 2 で `none` / `some` を再度全分岐する。
- focused manifest check: pass。
- targeted module build: pass、3702 jobs。新規 module の linter warning なし。
- namespace axiom audit: 30 declarations、standard axioms only。
- placeholder、hidden / bidirectional Unicode、local-path、禁止語、reverse-import scan: clean。

### Audit

- premise classification: finite Source / law family、adequate pair、coarseness、supported-nerve
  morphism は `ambient-boundary`。label 保存で生成した subtype map、block pullback、
  commutation、Hom、`h1Map`、component equality は Cycle 12 の出力である。
- certificate provenance: coarse coordinate は canonical `comparisonFactor`、K1-derived
  support transport、`lawDescend_comparisonFactor` に追跡でき、block membership は
  common source-generated label の不変性に追跡できる。
- proof use: label 保存3補題、mapped incidence、fiber 内 edge の endpoint 一致、
  hereditary face 退化の3補題、finite block decomposition を全て実使用する。
- structure-field escape: none-found。block map / commutation / `h1Map` / component theorem を
  input structure に追加せず、actual `ThreeCochainComplex.Hom` の出力として生成する。
- route integrity: pass。coarse → fine の反変 pullback と common label を保ち、
  global Hom の単なる wrapper や mapped-only route を使わない。
- cheat route: arbitrary map / equivalence、basis / finrank、label bijection、vacuity、
  conclusion-equivalent field、quotient naturality の先取りは none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: Cycle 11 の coarse / fine `lawGeneratedH1BlockEquiv` の下で、global
  `generatedComparisonH1Map` と label 別 `generatedBlockComparisonH1Map` の finite
  DirectSum map が一致する quotient-level naturality square と representative 成分公式を証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 12
decision: approve
result_type: proof-obligation-discharged
proof_obligation: generate each exact block Hom and all three global pullback component formulas
proof_obligation_delta: discharged mapped and degenerate branches on the exact common label fibers
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparison.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonHom
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedBlockComparisonH1Map
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback0_block_component
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback1_block_component
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback2_block_component
premise_delta:
  ambient_boundary:
    - finite Source and law family, adequate pair, coarseness, and supported-nerve morphism
  discharged:
    - exact same-label coordinate transport in all three degrees
    - zero-on-degenerate block pullbacks
    - actual block Hom and G-102 h1Map
    - three global-to-block pullback component theorems
  remaining:
    - quotient-level global H1 direct-sum naturality
    - coordinate subnerves, C0-C6, invariance, corollary, diagnostics, counterexamples, and firing witness
certificate_provenance:
  discharged:
    - block coordinate maps generated from canonical Cycle 9 transport and Cycle 10 label preservation
    - component formulas generated from the canonical coordinate-fiber decomposition
  unresolved:
    - quotient-level H1 naturality
proof_use_audit:
  used_material_premises:
    - all three coordinate label-preservation theorems
    - mapped edge and face incidence compatibility
    - degenerate edge endpoint equality and hereditary face declarations
    - finite coordinate-fiber block decomposition
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove quotient-level global H1 finite-DirectSum naturality
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 11 — quotient-level block cohomology

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 11
decision: approve
result type: proof-obligation-discharged
proof obligation: aggregate block complex を構成し、actual G-102 H1 を label 別 block H1 の finite DirectSum に canonical に分解する
proof obligation delta: cochain-level block decomposition を cycle / boundary / quotient の各段階で放電した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockCohomology.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockDirectSumComplex`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedAggregateCyclesEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedBoundaryRange_map_aggregate`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockCyclesEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockBoundaryRange_map_cyclesEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedBlockCyclesEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedBoundaryRange_map_blocks`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedH1BlockEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedH1BlockEquiv_mk_component`
- aggregate 複体の complex law は全 label での Cycle 10 `lawValueBlock_d1_comp_d0`
  から生成した。complex law や differential 対応を入力 field として追加しない。
- global cycle と aggregate cycle の同型は degree-one block equivalence と
  `lawGeneratedD1_block_intertwining`、boundary range の等式は degree-zero block
  equivalence と `lawGeneratedD0_block_intertwining` から導いた。
- finite label 上の aggregate cycle は label 別 cycle の product と canonical に同型で、
  aggregate boundary range は label 別 boundary range の `Submodule.pi Set.univ`
  に正確に写る。この2つの submodule 等式を quotient で実使用した。
- 最終同型は `Submodule.Quotient.equiv` → `Submodule.quotientPi` →
  `DirectSum.linearEquivFunOnFintype.symm` の合成である。basis、finrank、補空間、
  任意の quotient equivalence は使わない。
- `lawGeneratedH1BlockEquiv_mk_component` は global cycle の quotient class の各
  label 成分が、canonical に transport された block cycle の quotient class であることを固定する。
- focused manifest check: pass。
- targeted module build: pass、3701 jobs。新規 module の linter warning なし。
- namespace axiom audit: 12 declarations、standard axioms only。
- placeholder、hidden / bidirectional Unicode、local-path、禁止語、reverse-import scan: clean。

### Audit

- premise classification: finite Source / law family、adequate reading、finite supported nerve は
  `ambient-boundary`。cycle / boundary の対応、aggregate complex、quotient equivalence は
  Cycle 11 の出力である。
- certificate provenance: cycle は actual `d1` kernel、boundary は actual
  `boundaryToCycles` range、quotient は G-102 の actual `H1` に追跡できる。
  finite label は Cycle 10 の source evaluation image をそのまま使う。
- proof use: componentwise complex law、D1 intertwining、D0 intertwining、cycle / boundary
  submodule 等式、G-102 quotient API をすべて最終同型の構成に実使用する。
- structure-field escape: none-found。cycle decomposition、boundary decomposition、H1 iso の
  certificate を新規 structure field で受けない。
- route integrity: pass。common source-generated label と exact coordinate fiber から離れず、
  reading 別 label、occurrence index、dimension-counting route を使わない。
- cheat route: target-fitting construction、vacuity、one-way map の equivalence 扱い、
  supplied quotient equivalence、GOAL / report の読み替えは none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: Cycle 9 `generatedComparisonHom` / `generatedComparisonH1Map` を
  common label の block ごとに分解し、global と block の naturality square を証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 11
decision: approve
result_type: proof-obligation-discharged
proof_obligation: derive the canonical finite-DirectSum decomposition of actual G-102 H1
proof_obligation_delta: discharged cycle, boundary, and quotient decomposition from the Cycle 10 cochain blocks
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockCohomology.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockDirectSumComplex
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedBlockCyclesEquiv
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedBoundaryRange_map_blocks
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedH1BlockEquiv
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedH1BlockEquiv_mk_component
premise_delta:
  ambient_boundary:
    - finite Source and law family, adequate reading, and finite supported nerve
  discharged:
    - aggregate finite-DirectSum block complex
    - exact global-to-block cycle equivalence
    - exact global-to-product boundary-range equality
    - canonical quotient-level H1 finite-DirectSum equivalence and representative formula
  remaining:
    - blockwise generated comparison Hom and H1 naturality
    - coordinate subnerves, C0-C6, invariance, corollary, diagnostics, counterexamples, and firing witness
certificate_provenance:
  discharged:
    - cycle correspondence generated from the actual D1 intertwining theorem
    - boundary correspondence generated from the actual D0 intertwining theorem
    - H1 equivalence generated by quotient equivalence and finite quotientPi
  unresolved:
    - generated-comparison block naturality
proof_use_audit:
  used_material_premises:
    - per-label complex laws for the aggregate complex law
    - D1 intertwining for cycle transport
    - D0 intertwining for boundary-range transport
    - actual G-102 boundaryToCycles and H1 quotient
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove blockwise generated-comparison Hom and H1 naturality
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 10 — finite law-value block complexes

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 10
decision: approve
result type: proof-obligation-discharged
proof obligation: source-generated finite label、label fiber、block 複体、次数別 finite DirectSum と differential intertwining を生成する
proof obligation delta: H1 quotient に先立つ canonical law-value block complex decomposition を一般有限入力上で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockDecomposition.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.LawValueLabel`
  - `AAT.AG.ResolutionInvariance.LawValueLabel.instFintype`
  - `AAT.AG.ResolutionInvariance.CellCoordinate.lawValueLabel`
  - `AAT.AG.ResolutionInvariance.CellCoordinate.cochainBlockEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockComplex`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.chartCochainBlockEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.edgeCochainBlockEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.faceCochainBlockEquiv`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD0_block_intertwining`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD1_block_intertwining`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.chartCoordinateMap_lawValueLabel`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.edgeCoordinateMap_lawValueLabel`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.faceCoordinateMap_lawValueLabel`
- `LawValueLabel` は `∃ source, laws.eval law source = value` を持つ evaluation image で、
  `Σ law, Source` からの全射により有限性を生成する。ambient な
  `FiniteLawFamily.Value law` には `Fintype` を要求しない。
- K0 coordinate の label occurrence は `CellCoordinate.generated`、reading の全射性、
  `lawDescend_commutes` から生成する。同一値の異なる source / target occurrence は
  proof data であり、`LawValueLabel.ext` により label を複製しない。
- endpoint と face の5本の coordinate restriction が label を保つことを証明し、
  各 label fiber 上の `d₀` / `d₁` と `d₁ ∘ d₀ = 0` を incidence から導いた。
- 3次数の cochain space は `Equiv.sigmaFiberEquiv`、`LinearEquiv.piCurry`、
  `DirectSum.linearEquivFunOnFintype` により、各 label block の有限直和へ canonical に
  同型となる。componentwise direct-sum differential は block formula 自体から定義し、
  global `lawGeneratedD0` / `D1` との intertwining を theorem として証明した。
- focused manifest check: pass。
- targeted module build: pass、3699 jobs。新規 module の linter warning なし。
- namespace axiom audit: 54 declarations、standard axioms only。
- placeholder、hidden / bidirectional Unicode、local-path、reverse-import scan: clean。

### Audit

- premise classification: finite Source / law family、adequate reading、finite supported nerve は
  `ambient-boundary`。label image、fiber、block differential、complex、DirectSum equivalence、
  intertwining は Cycle 10 の出力である。
- certificate provenance: label の値は actual `FiniteLawFamily.eval` の像、coordinate の
  label は actual K0 occurrence と law descent に追跡できる。任意の値一覧、partition、
  basis、reading ごとの label bijection、decomposition certificate は受けない。
- proof use: Source と law index の有限性を label の有限性に、adequacy / descent 可換性を
  coordinate label に、K1-derived incidence を block restriction に、face endpoint coherence を
  block の `d₁ ∘ d₀ = 0` に実使用する。Cycle 9 coordinate transport の law / dependent value
  保存も3種類すべて theorem として固定した。
- structure-field escape: none-found。`LawValueLabel.generated` は source occurrence のみを持ち、
  decomposition / comparison / isomorphism certificate を持たない。block complex の complex law は
  proved theorem で埋める。
- route integrity: pass。ambient value 型の偽の有限化、source occurrence を index に含める経路、
  coordinate ごとの自明 block、任意 basis による抽象同型は使わない。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、GOAL / report の
  読み替えは none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: componentwise direct-sum differential を aggregate
  `ThreeCochainComplex` にまとめ、global `H^1` と block `H^1` の有限直和同型、および Cycle 9
  comparison Hom / `H^1` map の blockwise naturality を証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 10
decision: approve
result_type: proof-obligation-discharged
proof_obligation: generate the finite source-law-value block complexes and degreewise DirectSum decomposition
proof_obligation_delta: fixed the canonical complex-level block decomposition before quotient-level H1
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: fixed
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockDecomposition.lean
    declarations:
      - AAT.AG.ResolutionInvariance.LawValueLabel
      - AAT.AG.ResolutionInvariance.CellCoordinate.cochainBlockEquiv
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawValueBlockComplex
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD0_block_intertwining
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD1_block_intertwining
premise_delta:
  ambient_boundary:
    - finite Source and law family, adequate reading, and finite supported nerve
  discharged:
    - finite common source-generated law-value label type
    - exact coordinate fibers and per-label complexes
    - three canonical finite-DirectSum degree equivalences
    - both global-to-block differential intertwining theorems
    - Cycle 9 coordinate-transport label preservation
  remaining:
    - aggregate direct-sum complex and quotient-level H1 decomposition
    - blockwise generated comparison Hom and H1 map
    - coordinate subnerves, C0-C6, invariance, corollary, diagnostics, counterexamples, and firing witness
certificate_provenance:
  discharged:
    - label image generated from actual law evaluation on finite Source
    - coordinate labels generated from K0 occurrence, reading surjectivity, and law descent
    - finite DirectSum equivalences generated without basis or partition input
  unresolved:
    - H1 quotient and comparison naturality
proof_use_audit:
  used_material_premises:
    - finite Source and law index for label finiteness
    - adequacy and lawDescend_commutes for coordinate labels
    - K1 incidence and face endpoint coherence for block complexes
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: package the aggregate block complex and prove H1 and generated-comparison block decomposition
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 9 — generated comparison cochain map

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 9
decision: approve
result type: proof-obligation-discharged
proof obligation: actual lawGeneratedComplex 上で canonical coordinate pullback、comm0 / comm1、Hom、H1 map を生成する
proof obligation delta: claim (i) の coarse-to-fine comparison map を一般有限入力上で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.chartCoordinateMap`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.edgeCoordinateMap`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.faceCoordinateMap`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback1`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback2`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback_comm0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback_comm1`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonHom`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map`
- chart / mapped edge / mapped face coordinate は、fine coordinate の occurrence を
  canonical `comparisonFactor` で送り、`lawDescend_comparisonFactor` と K1-derived
  support transport で同じ law と値を持つ coarse coordinate として生成する。
- degree-one / degree-two pullback は `Option` incidence から生成する。`some` cell
  では transported coordinate を評価し、`none` cell では零とする。
- `comm0` の mapped branch は endpoint incidence、degenerate branch は
  `edge_none_fiber` を使う。`comm1` の mapped branch は ordered
  `face_some_edge0/1/2`、degenerate branch は `face_none_edge0/1/2` をすべて使う。
- `generatedComparisonHom` の source は coarse actual `lawGeneratedComplex`、
  target は fine actual `lawGeneratedComplex`。`generatedComparisonH1Map` は
  review 済み `ThreeCochainComplex.Hom.h1Map` で coarse `H^1 →` fine `H^1` を誘導する。
- focused manifest check: pass。
- targeted module build: pass、3697 jobs。新規 module の linter warning なし。
- namespace axiom audit: 27 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、reverse-import scan: clean。

### Audit

- premise classification: 有限 Source / law family、adequate readings と粗さ順序、
  coarse / fine supported nerve と Cycle 8 morphism は `ambient-boundary`。coordinate
  map、linear map、commutation、Hom、`H^1` map は入力でなく Cycle 9 の出力である。
- certificate provenance: `π` は `CoarserThan` 由来の canonical
  `comparisonFactor`、値の一致は `lawDescend_comparisonFactor`、cell 上の occurrence
  は chart 台包含と K1-derived edge / face transport に追跡できる。任意の coordinate
  correspondence、linear map、Hom certificate を受けない。
- proof use: mapped `comm0` は `edge_some_left/right`、degenerate `comm0` は
  `edge_none_fiber` を実使用する。mapped `comm1` は `face_some_edge0/1/2`、
  degenerate `comm1` は `face_none_edge0/1/2` を実使用し、Cycle 8 で残った
  claim-(i)-specific field の proof-use gap はない。
- structure-field escape: none-found。`TargetSupportedNerveMorphism` は Cycle 8 の
  input geometry のままで、degreewise maps、`comm0` / `comm1`、Hom、`H^1` map は
  新 module が構成・証明する。
- route integrity: pass。singleton fixture、free coefficient proxy、full-support 仮定、
  historical obstruction namespace に依存しない一般 theorem package である。
- cheat route: target-fitting construction、vacuity、mapped branch だけの可換性、
  任意 Hom の supplied certificate、one-way theorem の同値扱いは none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: finite `(law, 値)` block への `lawGeneratedComplex`、`H^1`、
  `generatedComparisonH1Map` の直和分解を証明し、座標 subnerve と C0–C6 の
  不変性 proof への橋を固定する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 9
decision: approve
result_type: proof-obligation-discharged
proof_obligation: generate the canonical comparison Hom and induced H1 map on the actual law-generated complexes
proof_obligation_delta: fixed claim (i) for general finite input data with all degenerate branches proved
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: revised
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback0
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback1
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback2
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback_comm0
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedPullback_comm1
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonHom
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.generatedComparisonH1Map
premise_delta:
  ambient_boundary:
    - finite Source and law family, adequate coarse-fine readings, and CoarserThan
    - coarse-fine TargetSupportedNerve values and TargetSupportedNerveMorphism input geometry
  discharged:
    - canonical law-value coordinate transport and Option-generated degreewise pullbacks
    - comm0 and comm1 on mapped and degenerate components
    - ThreeCochainComplex.Hom and the induced coarse-to-fine H1 map
    - fixed target claim (i)
  remaining:
    - H1 law-value block decomposition
    - coordinate subnerves and C0-C6
    - invariance theorem and no-overresolution corollary
    - canonical inadequate diagnostic, three counterexamples, and firing witness
certificate_provenance:
  discharged:
    - comparisonFactor generated from CoarserThan
    - coordinate values generated through lawDescend_comparisonFactor and K1 support transport
    - commutation generated from incidence and hereditary degeneracy
    - H1 map generated by the reviewed ThreeCochainComplex Hom API
  unresolved:
    - block-decomposition, invariance, and witness provenance
proof_use_audit:
  used_material_premises:
    - edge_some_left-right and edge_none_fiber in comm0
    - face_some_edge0-face_some_edge2 and face_none_edge0-face_none_edge2 in comm1
    - chart support compatibility and K1 support transport in coordinate construction
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: prove the finite law-value block decomposition of the complexes, H1, and generated comparison H1 map
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 8 — hereditary supported-nerve comparison geometry

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 8
decision: approve
result type: proof-obligation-discharged
proof obligation: hereditary な退化宣言を持つ一般の supported-nerve morphism を定義し、mapped edge / face の台両立性を K1 から導出する
proof obligation delta: canonical comparison factor に沿う chart 台包含だけから mapped cell の導出台輸送までを一般入力上で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.edgeSupport_compatible`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.faceSupport_compatible`
- morphism の input fields は chart map、partial edge / face map、mapped cell の
  endpoint / boundary 可換、`edgeMap = none` の chart-fiber 条件、
  `faceMap = none` なら boundary triple の各 edge も `edgeMap = none` となる
  hereditary 条件、canonical `comparisonFactor` に沿う chart 台包含に限る。
- `edgeSupport_compatible` は mapped edge の endpoint incidence、chart 台包含、
  K1 edge 台の endpoint 交わりを使用して導出する。
- `faceSupport_compatible` は mapped face の boundary incidence と、すでに導出した
  3本の edge 台輸送、K1 face 台の boundary-edge 交わりを使用して導出する。
- focused manifest check: pass。
- targeted module build: pass、3695 jobs。新規 module の linter warning なし。
- namespace axiom audit: 27 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、reverse-import scan: clean。

### Audit

- premise classification: partial incidence、hereditary な退化宣言、chart 台包含は
  GOAL が許可する `ambient-boundary` の入力幾何であり、生成・放電した premise
  ではない。Cycle 8 で放電したのは、mapped edge / face の台包含をこの入力と
  K1 生成 def から導く obligation である。
- certificate provenance: `π` 自体は `CoarserThan` から生成する review 済み
  `comparisonFactor`。chart 台包含は supplied input であり、`CoarserThan` から
  生成した certificate ではない。mapped edge / face 台の輸送は Cycle 5 の K1
  定義へ追跡でき、独立な edge / face 台対応や coordinate correspondence は
  受けない。
- proof use: `edge_some_left` / `edge_some_right` と chart 台包含は
  `edgeSupport_compatible` に、`face_some_edge0/1/2` と edge 台輸送は
  `faceSupport_compatible` に実使用される。`edge_none_fiber` と
  `face_none_edge0/1/2` はこの support theorem では未使用であり、次 cycle の
  zero-on-degenerate `comm0` / `comm1` で実使用するまで G-104 全体の完了根拠に
  数えない。
- structure-field escape: none-found。structure は `ThreeCochainComplex.Hom`、
  commutation、`H^1` map、同型、条件 C、座標対応 certificate を持たない。
- route integrity: pass。一般の入力幾何と canonical factor、K1 生成 def からの
  theorem であり、歴史的 obstruction fixture や full-support 選択に依存しない。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、
  GOAL / report の読み替えはすべて none-found。
- blocking findings: none。
- independent T3 verdict:
  `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: この morphism と `lawDescend_comparisonFactor` から degreewise
  comparison map と `ThreeCochainComplex.Hom` を生成し、退化 edge / face fields を
  実使用して `comm0` / `comm1` を証明する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 8
decision: approve
result_type: proof-obligation-discharged
proof_obligation: define the hereditary supported-nerve morphism and derive mapped K1 support transport
proof_obligation_delta: partial comparison geometry and mapped edge-face support transport are now fixed over general finite input data
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 3f43ffd4c68f5b79abe90d0255e5419ec3697f3f
  blob: 3bb623aeaa1181b6626a90141ea47e1717f2a7c6
  status: revised
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.edgeSupport_compatible
      - AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.faceSupport_compatible
premise_delta:
  ambient_boundary:
    - partial chart-edge-face incidence and hereditary degenerate declarations
    - canonical comparison-factor compatibility on chart supports as supplied input geometry
  discharged:
    - mapped edge and face support transport derived from K1 intersections
  remaining:
    - generated comparison cochain map and comm0-comm1
    - H1 law-value block decomposition
    - coordinate subnerves and C0-C6
    - invariance theorem and no-overresolution corollary
    - canonical inadequate diagnostic, three counterexamples, and firing witness
certificate_provenance:
  ambient_boundary:
    - chart-support compatibility is supplied input geometry, not generated from CoarserThan
  discharged:
    - comparisonFactor itself is generated from CoarserThan by the reviewed predecessor
    - edge and face support transport from K1 definitions and mapped incidence
  unresolved:
    - generated coordinate transport and cochain-map provenance
    - proof-use of degenerate edge and hereditary degenerate face declarations in comm0-comm1
    - H1 block-decomposition, invariance, and witness provenance
proof_use_audit:
  used_material_premises:
    - mapped-edge endpoint incidence and canonical chart-support compatibility
    - mapped-face boundary incidence and K1 edge-support transport
  unused_material_premises:
    - edge_none_fiber and face_none_edge0-face_none_edge2 await comm0-comm1 proof-use
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: construct the generated comparison cochain map and prove comm0-comm1 using the degenerate-cell fields
completion_candidate: false
tracking_issue_closed: false
```

## Historical Cycle 7 — literal degenerate-face comm1 obstruction

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 7
decision: approve
result type: blocker-fixed
proof obligation: 固定 GOAL の literal degenerate-face comparison data が generated K0/K1 cochain map を許すか有限 witness で判定する
proof obligation delta: endpoint-defined fiber-internal boundary と zero-on-degenerate face が comm1 を破ることを実 law-generated complex 上で固定した
phase proof state: target-refuted
completion candidate: yes (target-refuted terminal; not target-theorem-proved)
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/DegenerateFaceComm1Obstruction.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.EndpointDegenerateNerveMorphism`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.nerveMorphism`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.chartCoordinateMap`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.edgeCoordinateMap`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.generatedPullback1`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.generatedPullback2`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.selectedFineFaceCoordinate`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.generated_pullback_comm1_fails`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.no_generated_comparison_hom`
  - `AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.fixed_claim_i_refuted`
- witness geometry:
  - coarse nerve = 1 chart、1 self-loop edge `E`、face なし。
  - fine nerve = 1 chart、1 self-loop edge `e`、boundary `(e,e,e)` の1 face `f`。
  - `edgeMap e = some E`、`faceMap f = none`。`e` の両端 chart 像は一致するため、
    boundary triple の3位置の edge は当時の固定 GOAL の意味で
    fiber-internal である。
- witness input は `FaceLiftObstruction` で固定済みの proper adequate reading pair、
  非単射 canonical `comparisonFactor`、非定数 law を再利用する。
- coarse / fine complex は Cycle 5 の actual `lawGeneratedComplex`。edge / face 台は
  K1 の交わりから導出し、selected coordinate は actual derived support 上の
  `CellCoordinate.ofSupportedTarget`、cochain は実 coarse edge coordinate 上の
  `coordinateVector` である。
- `chartCoordinateMap` / `edgeCoordinateMap` は canonical `comparisonFactor` と
  `lawDescend_comparisonFactor` から同じ `(law, 値)` を輸送する。任意の
  coefficient correspondence は受け取らない。
- selected basis cochain `y` について、fine 側 boundary triple の
  3位置の pullback 値はすべて1。
  よって `fine.d₁ (f₁ y) f = 1 - 1 + 1 = 1`。一方、退化 face 上の
  generated `f₂` は零なので `f₂ (coarse.d₁ y) f = 0`。したがって prescribed
  `f₀/f₁/f₂` を component に持つ `ThreeCochainComplex.Hom` は存在しない。
- focused check: pass。
- targeted module build: pass、3697 jobs。新規 module の linter warning なし。
- namespace axiom audit: 62 declarations、standard axioms only。
- principal `#print axioms`: structure は公理依存なし、他は `propext`、
  `Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、reverse-import、diff scan:
  clean。

### Audit

- premise delta: literal comparison geometry、proper adequate pair、nonconstant law、
  canonical factor / descend、actual K0 / K1 coefficient generationを同一 witness に
  接続し、claim (i) の必要仮定不足を固定した。
- certificate provenance: reading / law input は reviewed predecessor へ、cell 台・
  coordinate・differential は Cycle 5 generator へ、coarse coordinate transport は
  canonical factor / descend theorem へ追跡できる。旧 free-coefficient proxy、
  law annotation、selected commutation certificate は使わない。
- proof use: adequacy、`CoarserThan`、K1 support membership、3本の同一 boundary
  coordinate、`Hom.comm1` を実使用する。full support の membership proof が
  `chartSupport_compatible` の proof termで不要なのは両台が `Set.univ` だからで、
  hidden premise ではない。`f₀` equality を矛盾に使わないのは `f₁/f₂` だけで
  既に `comm1` が破れるためである。
- structure-field escape: none-found。nerve morphism は incidence と endpoint-fiber
  条件だけを持ち、Hom、commutation、cohomology、isomorphism field を持たない。
- route integrity: pass。target-fitting coefficient や型不一致による反例ではない。
- dullness: 単一 chart / coarse-face-free は条件 C の発火正例なら除外対象だが、
  claim (i) は条件 C より前に一般の有限 comparison data へ量化される。fine face
  coordinate と非零 `d₁` は実在するため、この dullness filter は普遍 claim (i) の
  反例を除外しない。
- cheat route: target-fitting construction、vacuity、one-way-as-equivalence、
  GOAL / report reinterpretation はすべて none-found。
- blocking findings: none。
- independent T3 verdict: `approve / blocker-fixed / completion_candidate: yes`。
- stop condition: `target-refuted`。`target-theorem-proved` ではない。
- GOAL 改訂候補:
  1. 直接案: `faceMap f = none` なら3本の boundary edge も宣言上退化
     (`edgeMap = none`)であることを要求する。
  2. より弱い案: 退化 face の mapped boundary が各 coarse edge について
     符号付き multiplicity 零になる incidence 条件を要求する。
  どちらの一般的十分性も未証明であり、固定 GOAL は本 cycle で編集しない。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 7
decision: approve
result_type: blocker-fixed
proof_state: target-refuted
proof_obligation: formalize the literal degenerate-face comm1 countermodel on the K0/K1 law-generated complex
proof_obligation_delta: the prescribed generated comparison components fail comm1 on an endpoint-degenerate face whose boundary edge maps to a coarse self-loop
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 2ede7da2d150eda52599f219942e9d9477edd552
  blob: 69edc22678de7ea4c1a219b9540d1408a3b0bea3
  status: immutable-refuted
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/DegenerateFaceComm1Obstruction.lean
    declarations:
      - AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.EndpointDegenerateNerveMorphism
      - AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.generated_pullback_comm1_fails
      - AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.no_generated_comparison_hom
      - AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction.fixed_claim_i_refuted
premise_delta:
  discharged:
    - literal endpoint-defined degenerate-face comparison geometry
    - proper adequate nonidentity reading pair and nonconstant law
    - canonical comparison-factor and law-descend coordinate transport
    - actual K0/K1 law-generated coefficient spaces and differentials
    - explicit comm1 failure and nonexistence of the prescribed comparison Hom
  remaining: []
certificate_provenance:
  discharged:
    - reading and law data from the reviewed finite predecessor witness
    - coordinates from actual law-descend images on K1-derived supports
    - coordinate transport from comparisonFactor and lawDescend_comparisonFactor
    - obstruction cochain from coordinateVector on an actual coarse edge coordinate
  unresolved: []
proof_use_audit:
  used_material_premises:
    - both adequacy proofs
    - CoarserThan and the canonical comparison factor
    - K1-derived support membership
    - all three boundary-coordinate equalities
    - ThreeCochainComplex.Hom.comm1
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: human GOAL revision; preserve this counterexample as the fixed-statement lower bound
completion_candidate: true
target_theorem_proved: false
tracking_issue_closed: false
```

## Cycle 6 — rejected general comparison-map attempt

Cycle 6 では、一般の generated comparison `ThreeCochainComplex.Hom` を構成する
候補を実装したが、独立T3が固定 GOAL にない material premise を検出したため
`reject / rejected` とした。候補は `faceMap f = none` のとき3本の boundary edge
すべてに `edgeMap = none` を要求していた。固定 GOAL の fiber-internal edge は
端点 chart 像の一致だけで定義され、coarse self-loop へ `some` で写る edge も
含むため、この条件は strict strengthening である。

候補 Lean file と aggregate wiring は棄却後に全撤去し、PRは作成していない。
Cycle 6 の最小反例予告を Cycle 7 が actual K0 / K1 上で形式化した。
なお改訂後カードは退化宣言の hereditary 性(`faceMap = none` なら3本の
boundary edge も退化宣言済み)を nerve 射の well-formedness に含めるため、
同種の構成は改訂後 statement では material premise の追加にならない。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
cycle: 6
decision: reject
result_type: rejected
hidden_material_premise: faceMap_none_requires_all_boundary_edgeMap_none
completion_candidate: false
pr: null
tracking_issue_closed: false
next_obligation: formalize the literal degenerate-face comm1 countermodel in Lean
```

## Cycle 5 — K0 / K1 law-generated base complex

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 5
decision: approve
result type: proof-obligation-discharged
proof obligation: chart 台と face endpoint coherence から K1 台、K0 座標、ℚ 上の differential、d₁d₀ theorem、ThreeCochainComplex を生成する
proof obligation delta: 改訂後 statement の最初の discharge-required node を一般の有限入力について Lean で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.edgeSupport`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.faceSupport`
  - `AAT.AG.ResolutionInvariance.CellCoordinate`
  - `AAT.AG.ResolutionInvariance.CellCoordinate.ofSupportedTarget_eq_of_value_eq`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.chartCoordinate_exists`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD1`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGenerated_d1_comp_d0`
  - `AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedComplex`
- K1 は edge 台を両端 chart 台の交わり、face 台を3本の boundary edge 台の
  交わりとして def で生成する。edge / face 台の独立 field はない。
- K0 coordinate は `(cell, law, 値)` と、その値が当該 cell の導出台上で
  canonical `lawDescend` に実在するという Prop witness だけを持つ。target 上の
  occurrence は coordinate field ではなく、同じ descended 値の複数出現が同一
  coordinate になることを theorem で固定した。
- `d₀` は同一 label の right-minus-left、`d₁` は同一 label の
  `e₀ - e₁ + e₂`。`d₁ ∘ d₀ = 0` は face boundary の3本の endpoint
  equality をすべて使用して証明し、G-102 の `ThreeCochainComplex ℚ` を構成する。
- focused manifest check: pass。
- targeted module build: pass、3694 jobs。新規 module の linter warning なし。
- namespace axiom audit: 70 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、reverse-import、diff scan:
  clean。

### Audit

- premise delta: K1 台、K0 の exact-image / no-multiplicity 座標、`ℚ` 上の
  generated differential、`d₁d₀`、base complex を放電。
- certificate provenance: `lawDescend` は `Adequate` と reading surjectivity へ
  追跡できる。coordinate の occurrence witness は exact-image membership であり、
  追加・複製・省略を選ぶ certificate ではない。有限性 instance は supported
  occurrence から coordinate 全体への全射で構成し、座標を選別しない。
- proof use: adequacy は各 coordinate の `lawDescend` に、chart 台は K1 と
  coordinate image に、chart 台非空は `chartCoordinate_exists` に、3本の face
  endpoint equality は `lawGenerated_d1_comp_d0` に実使用される。
- structure-field escape: none-found。入力 structure は finite nerve、chart 台、
  chart 台非空、face endpoint coherence だけを持ち、edge / face 台、differential、
  `d₁d₀`、comparison、cohomology を field で受けない。
- route integrity: pass。一般の入力dataと reviewed `lawDescend` API からの
  canonical construction であり、旧 full-support fixture や selected coefficient
  complex を再包装していない。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、
  GOAL / report の読み替えはすべて none-found。
- blocking findings: none。
- T3 verdict: `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: endpoint / boundary と可換で退化 edge / face を許す一般の
  coarse / fine `TargetSupportedNerve` morphism と `π`-compatible chart 台を、
  comparison / cohomology / isomorphism field なしに定義する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 5
decision: approve
result_type: proof-obligation-discharged
proof_obligation: generate the K0/K1 law-derived rational base complex
proof_obligation_delta: K1 supports, exact law-value coordinates, generated differentials, d1d0, and the ThreeCochainComplex are now constructed from finite input data
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 2ede7da2d150eda52599f219942e9d9477edd552
  status: revised
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean
    declarations:
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.edgeSupport
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.faceSupport
      - AAT.AG.ResolutionInvariance.CellCoordinate
      - AAT.AG.ResolutionInvariance.CellCoordinate.ofSupportedTarget_eq_of_value_eq
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.chartCoordinate_exists
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD0
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedD1
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGenerated_d1_comp_d0
      - AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedComplex
premise_delta:
  discharged:
    - K1 edge and face supports from chart supports
    - exact law-descend cell coordinates without occurrence multiplicity
    - rational same-label d0 and d1
    - d1 composed with d0 from face endpoint coherence
    - finite ThreeCochainComplex over the generated coordinates
  remaining:
    - supported-nerve morphism and pi-compatible chart supports
    - canonical comparison cochain map
    - H1 law-value block decomposition
    - coordinate subnerves and C0-C6
    - invariance theorem and no-overresolution corollary
    - canonical inadequate diagnostic, three counterexamples, and firing witness
certificate_provenance:
  discharged:
    - law descent from Adequate and reading surjectivity
    - coordinates from exact law-descend images on K1 supports
    - d1d0 from the three face endpoint equalities
  unresolved:
    - comparison coordinate transport and cochain-map provenance
    - H1 block-decomposition provenance
    - invariance and witness provenance
proof_use_audit:
  used_material_premises:
    - Adequate and canonical lawDescend
    - chart supports and chart-support nonemptiness
    - all three face endpoint equalities
    - finite Source and finite nerve cells
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: define the supported-nerve morphism and pi-compatible chart supports without comparison or cohomology fields
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 1 — canonical comparison factor と law descend

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 1
decision: approve
result type: proof-obligation-discharged
proof obligation: CoarserThan から canonical factor を構成し、Adequate から生成した law descend の comparison 可換性を証明する
proof obligation delta: factor・descend・可換性を G-103 の入力から生成し、一意性と provenance を Lean theorem で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean`
- declarations:
  - `AAT.AG.ResolutionInvariance.comparisonFactor`
  - `AAT.AG.ResolutionInvariance.comparisonFactor_commutes`
  - `AAT.AG.ResolutionInvariance.comparisonFactor_unique`
  - `AAT.AG.ResolutionInvariance.comparisonFactor_surjective`
  - `AAT.AG.ResolutionInvariance.lawDescend`
  - `AAT.AG.ResolutionInvariance.lawDescend_commutes`
  - `AAT.AG.ResolutionInvariance.lawDescend_unique`
  - `AAT.AG.ResolutionInvariance.lawDescend_comparisonFactor`
  - `AAT.AG.ResolutionInvariance.lawDescend_comp_comparisonFactor`
- focused check: pass。
- targeted module build: pass、616 jobs。
- namespace axiom audit: 9 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、diff check: clean。

### Audit

- premise delta: comparison factor、law descend、descend compatibility を放電。
- certificate provenance: `comparisonFactor` は
  `factorsThrough_iff_coarserThan`、`lawDescend` は `Adequate` の
  `Factors` witness から構成し、reading の全射性で両者の一意性を証明する。
- proof use: `hcoarser`、両 adequacy proof、coarse / fine reading の全射性は
  factor 構成、law descend 構成、一意性、可換性に実使用される。
- structure-field escape: none-found。新規 structure / certificate はない。
- route integrity: pass。G-103 の reviewed factorization API と入力 law
  evaluation へ追跡できる。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、
  GOAL / report の読み替えはすべて none-found。
- blocking findings: none。
- T3 verdict: `approve / proof-obligation-discharged / completion_candidate: no`。
- next obligation: Target に台を持つ finite nerve、incidence と可換な nerve 射、
  `π`-compatible な chart 台、許容する退化 edge / face を、cohomology や
  同型性を field に含めず定義する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 1
decision: approve
result_type: proof-obligation-discharged
proof_obligation: canonical comparison factor and law-descend compatibility
proof_obligation_delta: CoarserThan and Adequate now generate the unique factor, unique law descents, and their commutation
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: null
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean
    declarations:
      - AAT.AG.ResolutionInvariance.comparisonFactor
      - AAT.AG.ResolutionInvariance.comparisonFactor_commutes
      - AAT.AG.ResolutionInvariance.comparisonFactor_unique
      - AAT.AG.ResolutionInvariance.comparisonFactor_surjective
      - AAT.AG.ResolutionInvariance.lawDescend
      - AAT.AG.ResolutionInvariance.lawDescend_commutes
      - AAT.AG.ResolutionInvariance.lawDescend_unique
      - AAT.AG.ResolutionInvariance.lawDescend_comparisonFactor
      - AAT.AG.ResolutionInvariance.lawDescend_comp_comparisonFactor
premise_delta:
  discharged:
    - canonical comparison factor from CoarserThan
    - law descents from Adequate
    - coarse and fine law-descend compatibility
  remaining:
    - finite supported nerves, nerve morphism, and degenerate components
    - law-derived coefficient complex and comparison cochain map
    - incidence conditions C0-C3 and invariance
    - no-overresolution corollary and canonical inadequate diagnostic
    - three counterexamples and firing witness
certificate_provenance:
  discharged:
    - comparison factor from factorsThrough_iff_coarserThan with uniqueness from fine surjectivity
    - law descents from Adequate with uniqueness from reading surjectivity
  unresolved:
    - coefficient-generation provenance
    - cochain-map, invariance, and witness provenance
proof_use_audit:
  used_material_premises:
    - CoarserThan
    - coarse and fine Adequate proofs
    - coarse and fine reading surjectivity
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: define supported finite nerves, an incidence-compatible nerve morphism, π-compatible supports, and allowed degenerate cells
completion_candidate: false
tracking_issue_closed: false
```

## Historical Cycle 4 — coarse self-loop lift obstruction

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 4
decision: approve
result type: blocker-fixed
proof obligation: law 由来係数と canonical comparison map を構成し、固定 C0–C5 の一般不変性を直接判定する
proof obligation delta: C0–C5 をすべて満たしながら canonical H1 map が非単射となる有限反例を Lean に固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/LoopLiftObstruction.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC0`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC1`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC2`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC3`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC4`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC5`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonCochainMap`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonH1Map`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.coarseLoopClass_ne_zero`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonH1Map_coarseLoopClass_zero`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonH1Map_not_injective`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.fineSurvivingClass_ne_zero`
  - `AAT.AG.ResolutionInvariance.LoopLiftObstruction.fixedConditionC0C5_not_sufficient`
- witness:
  - Cycle 2 / 3 で監査済みの proper adequate reading pair と非定数 law を再利用する。
  - coarse nerve は filled triangle、chart 0 の self-loop、triangle の第一 edge と
    parallel な unfilled edge を持つ。
  - fine nerve は coarse chart 0 の fiber に3 chart を持つ。coarse self-loop の
    唯一 lift は最初の2 chart を結び、`edgeMap = none` の edge が残る chart を
    接続するため、fiber graph は非自明な tree になる。
  - 各 coarse edge の lift はちょうど一つで C2 / C5 が成立する。fine filling face
    は unique coarse face へ写り、actual `d1`、`pullback2`、`comm1` に使われる。
  - law-value basis は canonical law descend の実値 `Fin 3`。全 basis value の
    generation と coarse / fine descend の両立は predecessor theorem へ追跡できる。
  - coarse self-loop の basis cocycle は loop period 1 の非零 `H^1` class を作る。
    canonical pullback は fine fiber tree 上の明示 primitive の coboundary であるため、
    canonical `h1Map` は非単射である。
  - fine 側には unfilled parallel edge の period 1 による別の非零 `H^1` class があり、
    fine cohomology 全体の消滅による反例ではない。
- focused check: pass。
- manifest focused check: pass。
- targeted module build: pass、3697 jobs。
- namespace axiom audit: 58 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、diff check: clean。

### Audit

- premise delta: 改訂 C0–C5 の十分性を反証する finite blocker を固定。
- certificate provenance: readings、adequacy、proper comparison、law descends は review 済み
  predecessor へ追跡できる。nerve、supports、incidence morphism、differentials、
  pullbacks、period、nonzero classes は explicit finite data から構成し、非同型性を
  field や premise で受け取らない。
- proof use: comparison factor の全射性を C0 に使う。fiber path と edge map を
  C1–C3 に使い、5本の mapped lift を C2 / C5 で直接検査する。C4 face は actual
  differential と cochain map に使う。coarse self-loop と distinct-endpoint fine lift
  は explicit primitive に、coarse class の非零性とその零像は非単射性に使う。
- structure-field escape: none-found。
- route integrity: pass。proper refinement、非定数 law、law-descend-generated
  coordinates、nonvacuous C4 face、declared degenerate fiber edge、両側の非零
  `H^1` を持ち、identity、constant-law、face-free C4、fiber-edge-free C5、
  zero-`H^1` vacuity ではない。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、
  GOAL / report の読み替えはすべて none-found。
- blocking finding: C0–C5 は coarse self-loop の唯一 fine lift が、同一 chart fiber
  の異なる fine chart を結ぶことを禁じない。この incidence collapse により coarse
  loop class が fine coboundary へ写る。
- T3 verdict: `approve / blocker-fixed / completion_candidate: no`。
- stop condition: `target-refuted`。

### Incidence-level revision proposal

現 GOAL は編集しない。この witness を除外する直接的な次版候補は、coarse edge の
両端点が一致する場合、その唯一 fine lift の両端点も一致することを要求する
**self-loop endpoint reflection** である。coarse self-loop を nerve data から除外する
案も同じ witness を除外する。どちらも incidence レベルの候補に限り、その一般的な
必要性・十分性は証明していない。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 4
decision: approve
result_type: blocker-fixed
proof_obligation: test fixed C0-C5 by constructing the law-generated canonical comparison
proof_obligation_delta: a finite adequate law-generated witness refutes H1 invariance under C0-C5
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 8832100118ced7141757befd1880a6ae1e0b0a5d
  status: revised
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/LoopLiftObstruction.lean
    declarations:
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.support_compatible
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC0
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC1
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC2
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC3
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC4
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.conditionC5
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonCochainMap
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonH1Map
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.coarseLoopClass_ne_zero
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonH1Map_coarseLoopClass_zero
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.comparisonH1Map_not_injective
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.fineSurvivingClass_ne_zero
      - AAT.AG.ResolutionInvariance.LoopLiftObstruction.fixedConditionC0C5_not_sufficient
premise_delta:
  discharged:
    - fixed C0-C5 insufficiency blocker
    - proper adequate pair and nonconstant law
    - nonvacuous C4 face and declared degenerate fiber edge
    - law-descend-generated coordinates and canonical comparison map
    - nonzero coarse H1 class with zero image and separate nonzero fine H1 class
  remaining:
    - current target claim ii cannot be discharged under C0-C5
    - a revised incidence condition controlling coarse self-loop lifts
certificate_provenance:
  discharged:
    - readings, factor, and law descents from reviewed G-103 and G-104 predecessor theorems
    - coefficient coordinates from actual canonical law-descend values
    - cochain map from explicit nerve, cell maps, and value map
    - nonzero and noninjectivity from direct incidence, primitive, period, and quotient calculations
  unresolved: []
proof_use_audit:
  used_material_premises:
    - both adequacy proofs and CoarserThan
    - support compatibility and C0-C5
    - the nonvacuous fine face in d1, pullback2, and comm1
    - law-value generation and descend compatibility
    - coarse nonzero loop class, explicit fine primitive, and separate fine nonzero class
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings:
  - C0-C5 do not reflect a coarse self-loop to a self-loop fine lift
next_obligation: human revision of the incidence condition, with self-loop endpoint reflection as one candidate
completion_candidate: false
tracking_issue_closed: false
```

## Prior refutation cycles

以下は Cycle 4 が再利用する predecessor evidence と改訂履歴である。

### Cycle 2 — coarse-face lift obstruction

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 2
decision: approve
result type: blocker-fixed
proof obligation: 固定 C0–C3 の十分性を、coarse face lift を持たない有限 incidence witness で検査する
proof obligation delta: 全入力と C0–C3 を満たしながら canonical H1 map が非全射となる反例を Lean で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/FaceLiftObstruction.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarse_adequate`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.fine_adequate`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarse_coarser_fine`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.support_compatible`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.comparisonFactor_not_injective`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.law_nonconstant`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC0`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC1`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC2`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC3`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarse_face_has_no_lift`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarseCoordinate_generated`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.fineCoordinate_generated`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.coordinateMap_descend_compatible`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.comparisonCochainMap`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarseH1Zero`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.fineFiringClass_ne_zero`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.comparisonH1Map_not_surjective`
  - `AAT.AG.ResolutionInvariance.FaceLiftObstruction.fixedConditionC_not_sufficient`
- witness:
  - Source は `Fin 4`、fine reading は恒等、coarse reading は source 0 / 1 を
    同一視する `Fin 3` quotient。
  - sole law は explicit coarse reading そのもので非定数。両 reading は adequate。
  - fine nerve は内部 edge と外周3 edge からなる face-free 4-cycle、coarse nerve
    はその像の3 edge triangle と filling face。
  - full target supports は非空で incidence-compatible。C0–C3 をすべて満たす。
  - law-value basis は `Fin 3` で、各 basis value が両 canonical law descend の
    full-support image に実在することを theorem で証明。
  - coarse `H^1 = 0`、fine に unit-period の非零 `H^1` class があり、canonical
    pullback の `h1Map` は非全射。
- focused check: pass。
- targeted module build: pass、3695 jobs。
- full ResearchLean build: pass、4489 jobs (formal review 前 snapshot)。
- formal review 修正後の focused check / targeted module build: pass。
- manifest focused check: pass。
- namespace axiom audit: 113 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、diff check: clean。

### Audit

- premise delta: C0–C3 の十分性を反証する有限 blocker を固定。
- certificate provenance: reading、factor、law descend、coefficient basis、incidence
  differentials、cochain map、`H^1` はすべて入力 data と reviewed predecessor から
  構成。非零性・消滅・非全射性の certificate field はない。
- proof use: coarse filling face は `coarseH1Zero` に、fine face 不在は cocycle と
  face-lift gap に、degenerate edge は pullback の zero rule に実使用される。
  adequacy と descend compatibility は coordinate generation と final witness package
  に接続される。
- structure-field escape: none-found。
- instance-pair audit: witness 内部の Prop helper は private とし、public theorem は
  C0–C3 の incidence 式を直接 statement に持つ。片側だけの public predicate API はない。
- route integrity: pass。proper refinement、非定数 law、3 chart 以上、fine 非零
  `H^1` を持ち、identity / zero-`H^1` / constant-law / single-chart vacuity ではない。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、
  GOAL / report の読み替えはすべて none-found。
- blocking finding: C0–C3 は chart fiber、coarse edge lift、fiber 内 cycle を制御するが、
  coarse face の fine lift を要求しない。この欠落により filled coarse triangle と
  face-free fine cycle の `H^1` が一致しない。
- T3 verdict: `approve / blocker-fixed / completion_candidate: no`。
- stop condition: `target-refuted`。

### Incidence-level revision proposal

現 GOAL は編集しない。次版の候補として、少なくとも次の C4 を追加してから
十分性を再検査する。

- **C4 (coarse-face lift)**: 各 coarse face は、その3本の boundary edge が対応する
  coarse edge へ写る fine face を少なくとも一つ持つ。

C4 はこの witness を除外する次版候補である。その一般的な必要性・十分性は
いずれも証明していない。改訂後は edge / face fiber の追加 incidence coherence が
必要かを別途検査する。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 2
decision: approve
result_type: blocker-fixed
proof_obligation: test fixed C0-C3 against a missing coarse-face lift
proof_obligation_delta: a finite adequate law-generated witness refutes H1 invariance under the fixed C0-C3
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: null
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/FaceLiftObstruction.lean
    declarations:
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarse_adequate
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.fine_adequate
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarse_coarser_fine
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.support_compatible
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.comparisonFactor_not_injective
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.law_nonconstant
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC0
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC1
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC2
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.conditionC3
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarse_face_has_no_lift
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarseCoordinate_generated
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.fineCoordinate_generated
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.coordinateMap_descend_compatible
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.comparisonCochainMap
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.coarseH1Zero
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.fineFiringClass_ne_zero
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.comparisonH1Map_not_surjective
      - AAT.AG.ResolutionInvariance.FaceLiftObstruction.fixedConditionC_not_sufficient
premise_delta:
  discharged:
    - fixed C0-C3 insufficiency blocker
    - proper adequate pair and nonconstant law
    - law-descend-generated coordinate provenance
    - actual incidence complexes and canonical comparison map
    - coarse H1 vanishing and fine nonzero H1
  remaining:
    - revised incidence condition and its sufficiency proof
certificate_provenance:
  discharged:
    - readings and factor from explicit finite data and G-103 factorization
    - coefficient coordinates from the actual images of canonical law descents
    - comparison map from the nerve morphism and generated-value map
    - H1 results from the reviewed ker/range quotient and direct incidence calculations
  unresolved: []
proof_use_audit:
  used_material_premises:
    - both adequacy proofs and CoarserThan
    - support compatibility and C0-C3
    - missing fine face lift
    - coarse filling face and fine face absence
    - law-descend coordinate generation and compatibility
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings:
  - fixed C0-C3 omit coarse-face lifting and therefore do not imply H1 invariance
next_obligation: propose a new GOAL version with incidence-level coarse-face lifting and re-audit sufficiency
completion_candidate: false
tracking_issue_closed: false
```

### Cycle 3 — parallel edge-lift obstruction

```text
Target theorem cycle result

target theorem: Diagnostic Resolution Invariance Theorem
cycle: 3
decision: approve
result type: blocker-fixed
proof obligation: 改訂 C0–C4 の十分性を、parallel coarse-edge lift を持つ有限 incidence witness で検査する
proof obligation delta: C0–C4 と全入力を満たしながら canonical H1 map が非全射となる反例を Lean で固定した
completion candidate: no
```

### Evidence

- Lean file:
  `research/lean/ResearchLean/AG/ResolutionInvariance/EdgeFiberObstruction.lean`
- principal declarations:
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.support_compatible`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC0`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC1`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC2`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC3`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC4`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.comparisonCochainMap`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.comparisonH1Map`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fine_d1_formula`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fineFiringCochain_cocycle`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fineFiringClass_ne_zero`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.comparisonH1Map_not_surjective`
  - `AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fixedConditionC0C4_not_sufficient`
- witness:
  - Cycle 2 で監査済みの proper adequate reading pair と非定数 law を再利用する。
  - fine nerve は3 chart、4 edge、1 face。fine edge 0 と1は同じ coarse edge 0
    の parallel lift で、fine face は edge 0、2、3を boundary に持つ。
  - fine face は unique coarse face へ写り、C4 を非空虚に満たす。同じ face が
    `fineComplex.d1`、`pullback2`、`comparisonCochainMap.comm1` に使われる。
  - law-value basis は canonical law descend の実値 `Fin 3`。全 basis value の
    generation と coarse / fine descend の両立は predecessor theorem へ追跡できる。
  - coarse `H^1 = 0`。face に含まれない parallel edge 1 の basis cochain は
    cocycle で、parallel-edge period により非零 class と証明される。
  - canonical `h1Map` はこの fine class を像に持たず、非全射である。
- focused check: pass。
- targeted module build: pass、3696 jobs。
- full ResearchLean build: pass、4490 jobs。
- namespace axiom audit: 41 declarations、standard axioms only。
- principal `#print axioms`: `propext`、`Classical.choice`、`Quot.sound` の範囲。
- placeholder、hidden / bidirectional Unicode、local-path、diff check: clean。

### Audit

- premise delta: 改訂 C0–C4 の十分性を反証する finite blocker を固定。
- certificate provenance: readings、adequacy、proper comparison、非定数 law、law
  descends は review 済み predecessor へ追跡できる。nerve、supports、incidence
  morphism、differentials、pullbacks、period、nonzero class は explicit finite data
  から構成し、非同型性を field として受け取らない。
- proof use: comparison factor の全射性を C0 に使う。C4 face は actual `d1` と
  degree-two pullback / `comm1` に使う。parallel edge は fine cocycle に、同じ
  endpoints は coboundary period の消滅に、coarse `H^1` 消滅と fine class 非零性は
  canonical map 非全射の証明に使う。
- structure-field escape: none-found。
- route integrity: pass。proper refinement、非定数 law、law-descend-generated
  coordinates、coarse face、fine nonzero `H^1` を持ち、identity、constant-law、
  face-free C4、型不一致による反例ではない。
- cheat route: target-fitting construction、vacuity、one-way theorem の同値扱い、
  GOAL / report の読み替えはすべて none-found。
- blocking finding: C0–C4 は同じ coarse edge に写る複数 fine edge 間の cycle を
  制御しない。一方の lift を C4 face が使っても、別の parallel lift が追加
  `H^1` class を残す。
- T3 verdict: `approve / blocker-fixed / completion_candidate: no`。
- stop condition: `target-refuted`。

### Incidence-level revision proposal

現 GOAL は編集しない。次版でこの witness を除外する直接的な候補は、各 coarse
edge が nondegenerate fine edge lift をちょうど一つ持つことを要求する
**C5 (unique coarse-edge lift)** である。より弱い face-mediated edge-fiber
coherence が十分かは未証明であり、C5 自体の一般的な十分性も証明していない。

```yaml
ledger_type: target_cycle_result
goal: G-104-aat-resolution-invariance
target_theorem: Diagnostic Resolution Invariance Theorem
cycle: 3
decision: approve
result_type: blocker-fixed
proof_obligation: test revised C0-C4 against parallel lifts of one coarse edge
proof_obligation_delta: a finite adequate law-generated witness refutes H1 invariance under C0-C4
primary_specification:
  source: research/goals/G-104-aat-resolution-invariance.md
  version: 2fbf4e185f9216ae7fdee85b1142bbab84edf7b6
  status: revised
lean_artifacts:
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/EdgeFiberObstruction.lean
    declarations:
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.support_compatible
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC0
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC1
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC2
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC3
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.conditionC4
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.comparisonCochainMap
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.comparisonH1Map
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fine_d1_formula
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fineFiringClass_ne_zero
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.comparisonH1Map_not_surjective
      - AAT.AG.ResolutionInvariance.EdgeFiberObstruction.fixedConditionC0C4_not_sufficient
premise_delta:
  discharged:
    - revised C0-C4 insufficiency blocker
    - proper adequate pair and nonconstant law
    - nonvacuous C4 face in the actual differential and cochain map
    - law-descend-generated coordinates and canonical comparison map
    - coarse H1 vanishing, fine nonzero H1, and comparison-map nonsurjectivity
  remaining:
    - current target claim ii cannot be discharged under C0-C4
    - a revised incidence condition controlling parallel coarse-edge lifts
certificate_provenance:
  discharged:
    - readings, factor, and law descents from reviewed G-103 and G-104 predecessor theorems
    - coefficient coordinates from actual canonical law-descend values
    - cochain map from explicit nerve and value maps
    - nonzero and nonsurjectivity from direct incidence and quotient calculations
  unresolved: []
proof_use_audit:
  used_material_premises:
    - both adequacy proofs and CoarserThan
    - support compatibility and C0-C4
    - the nonvacuous fine face in d1, pullback2, and comm1
    - law-value generation and descend compatibility
    - coarse H1 vanishing and fine nonzero class
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings:
  - C0-C4 do not control cycles among parallel fine lifts of one coarse edge
next_obligation: human revision of the incidence condition, with C5 edge-lift uniqueness as one candidate
completion_candidate: false
tracking_issue_closed: false
```
