# G-107-aat-uniform-invariance-characterization — 一様不変性の defect 意味論と Atlas 定理の位置

- 一次仕様: [`research/goals/G-107-aat-uniform-invariance-characterization.md`](../goals/G-107-aat-uniform-invariance-characterization.md)
- tracking Issue: [#3954](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3954)
- target theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
- proof state: `active`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria の正本は GOAL カードであり、この
report はそれらを再定義しない。target-theorem mode なので SCORE は使わない。

## Proof obligation state

- 完了(Cycle 1): U0 law-value block と A-subnerve の同定。任意の target
  subset `A` に対する coarse 側 A-subnerve、canonical factor の逆像による
  fine 側 A-subnerve、その comparison Hom を構成した。source-generated
  law-value label の値 fiber が非空で canonical 逆像と一致することを示し、
  chart / edge / face、endpoint、face incidence、differential、partial
  comparison map の全てで既存 G-104 block との同定と自然性を証明した。
- 完了(Cycle 2): global generated H¹ comparison の全単射性と全
  source-generated block comparison の全単射性の無条件同値。componentwise
  finite direct-sum map の全単射性 iff 各 component map の全単射性を両方向に
  証明し、G-104 の canonical H¹ block equivalence と actual-map naturality
  square で global map へ輸送した。
- 完了(Cycle 3): 任意の非空 target subset `A` を実現する singleton
  lifted-Boolean indicator law family、coarse / fine 両 reading への adequacy、
  source-generated true label、canonical coarse fiber `= A` と fine fiber
  `= comparisonFactor ⁻¹' A`。外部 decidable-membership・supplied factor・
  補集合非空性を仮定しない。
- 完了(Cycle 4): law family と両 adequacy を内部全量化する一様不変性と、
  全非空 `A` の actual A-subnerve H¹ comparison 全単射性の iff。Cycle 1 の
  cochain equivalence / naturality を actual H¹ quotient へ持ち上げ、Cycle 2 の
  global / blockwise iff と Cycle 3 の indicator family を両方向に接続した。
- 完了(Cycle 5): rational linear map の exact defect
  `(finrank ker, finrank (codomain / range))` と零 defect / 全単射性の有限次元
  iff。actual A-subnerve H¹ map へ特殊化し、Cycle 4 と結合して一様不変性と
  全非空 `A` の `J_A = (0, 0)` の iff、すなわち claim (i) を閉じた。
- 完了(Cycle 6): finite / decidable な raw reading・nerve・support・partial
  morphism table と明示 source enumeration から、実行可能
  `computedFactor`、canonical `comparisonFactor` との一致、actual G-104
  comparison geometry、全 projection / support correspondence を生成する
  `FiniteComparisonPresentation` の route-integrity 基盤。
- 完了(Cycle 7): 任意の有限 rectangular rational matrix の entries から
  column selection と Gram determinant を有限探索して exact rank を計算し、
  `Matrix.rank`、literal range finrank、Cycle 5 の kernel/cokernel defect と
  一致する一般 sound / complete 線形代数 kernel。射影・包含・重複列・恒等・
  零行列で同じ evaluator を発火させた。
- 完了(Cycle 8): raw `FiniteComparisonPresentation` と任意の有限 target subset
  `A` から coarse / fine selected cells、両 `d0` / `d1`、actual partial
  comparison `f1`、H¹ block matrix を生成し、Cycle 7 evaluator による
  `computedASubnerveDefect` を literal `aSubnerveDefect` と一致させた。空 `A`
  も含み、boundary を無視した `f1`-rank shortcut は専用 fixture で排除した。
- 完了(Cycle 9): explicit coarse-target enumeration の全 sublist を実行走査する
  `uniformPresentationCheck` と、full semantic `UniformPresentation` との sound /
  complete iff。Cycle 8 の exact defect bridge と Cycle 5 の semantic defect iffを
  接続し、rank-one の positive / negative raw self-loop presentations で同じ
  checkerを `true / false` 両側に発火させ、claim (ii) を閉じた。
- チェックポイント(Cycle 10): whole-nerve C0/C5/C6 と、全非空 target subset
  `A` および canonical fine preimage 上の actual A-subnerve C1--C4 からなる
  law / H¹ / rank / defect 非参照の幾何述語 `ConditionCAllA` を固定した。
  map・incidence・fiber cycle・C1--C4・集約条件の公開 no-unfold API と、
  新規9 Propすべての actual A-subnerve 正負 instance pairも固定した。これは
  direction hypothesis の品質付き definition checkpoint であり、checker
  correctness や premise discharge ではないため `proof-checkpoint` のままである。
- 完了(Cycle 11): finite raw presentation の source / target enumeration、raw
  readings、cell / support / incidence / partial-map tablesを読む
  `conditionCAllACheck` を構成し、full semantic
  `ConditionCAllA` との sound / complete iffを証明した。C1 は有限 fiber graphの
  reachability、C3 は rational constraint / internal-face boundary matrixの複体則と
  exact rank criterionで判定する。同じ checkerを C1・C3・aggregate の正負 raw
  presentationsで発火させた。
- 完了(Cycle 12): G-104 の exact firing geometryを変更せず再利用し、全非空
  target subset上の `firing_conditionCAllA` を直接証明した。同じ raw reading・
  support・incidence・partial-map tableの executable presentation `pFire` を構成し、
  raw C1--C4 の直接証明から generic checkerを `true` に発火させた。proper
  canonical factor、nonconstant law、original geometry、checker truth、coarse / fine
  両側の既存非零 H¹ classを1本の closed bundleへ接続した。
- 完了(Cycle 13): `ConditionCAllA` の全非空 A-subnerve C1--C4 を、任意の
  source-generated law-value label の非空 fiber と canonical fine preimage 上の
  G-104 block 条項へ直接 transport し、任意の law family と両 adequacy witnessに
  対する law-indexed `ConditionC` を導く bridge theoremを証明した。
- 完了(Cycle 14): Cycle 13 bridgeを任意の law familyへ適用し、G-104の受理済み
  `generatedComparisonH1Map_bijective` と直接合成して
  `ConditionCAllA M → M.UniformInvariance` を証明した。これにより claim (iii) の
  Atlas包含方向を閉じた。
- 完了(Cycle 15): R1 `C3_not_necessary` raw presentationをfieldwise転写し、全
  target subsetでactual H¹ comparisonが全単射であることをcochain equivalenceから
  証明した。同じ `A={0}` でactual C3の直接failureとcoarse / fine両側の非零H¹を
  固定し、nonconstant indicator lawのlaw-indexed C3 failureへ逆transportした。
  これによりC3の非必要性とAtlas包含の真性を閉じた。初回PR査読で指摘された
  selected-cell API境界も同Cycle内で補修し、computed preimage、raw support、
  coarse / fine selected cells、partial edge mapの公開characterizationを追加して、
  UniformInvariance subtreeの既存fixture clientすべてでこれらselected-cell系
  generic definitionの展開を公開API利用へ移した。
- 品質チェックポイント(Cycle 16): finite presentationのcoarse / fine `d0`・`d1` linear mapと
  matrix、edge pullback、H¹ block linear mapとmatrixに、raw incidence / partial-map
  tableからのpublic application / entry APIを定義ownerへ13本追加した。Cycle 15
  witnessと既存uniformity instance clientを同APIへ移し、対象定義の直接展開を
  owner内部に限定した。同時にCycle 15の全新規・body変更宣言を再列挙し、各
  docstringへ固定GOAL / fixture上のpositionとmaterial-premise provenanceを記録した。
- 完了(Cycle 17): exact R1 `C0_not_necessary` raw presentationをfieldwise転写した。
  全target subsetでactual H¹ comparisonの全単射性を、共通selected edgeの
  degree-one linear equivalence、fine側零boundary、coarse側零cocycle constraintから
  literal quotient上で直接証明した。coarse chart 1・target 0のsupport差によりraw /
  semantic C0と`ConditionCAllA`を直接反証し、nonconstant indicator law上のfull
  `ConditionC` failureへ接続した。同じfailed targetを含む`A={0}`でexplicit
  self-loop quotient classとactual map injectivityからcoarse / fine両H¹非零も固定した。
- 完了(Cycle 18): exact R1 `C1_not_necessary` のfactor・target counts・nerve・
  support・cell mapをfieldwise転写し、source / readingsはfactorのcanonical
  realizationとして構成した。登録failure scopeのうち、C1 failureと両側
  H¹非零が同じsubsetで成立するfull target `A={0,1}`を選び、coarse chart 1の
  fiberにあるdistinct fine charts 1,2がsole self-loop at chart 0では到達不能で
  あることをraw finite graphから直接証明した。全target subsetのactual H¹ map
  全単射、semantic uniformity、actual C1 / `ConditionCAllA` failure、generated
  indicator label上のlaw-indexed C1 / full `ConditionC` failure、同じfull blockの
  coarse / fine両H¹非零を接続した。law-block C1からlabel-fiber A-subnerve C1への
  reverse transportとselected-cell / fiber-graph evaluation APIもdefinition ownerに
  追加した。
- 完了(Cycle 19): exact R1 `C2_not_necessary` のraw reading・nerve・support・
  partial edge mapをfieldwise転写した。全target subsetでraw degree-one pullbackの
  右逆を構成し、そのkernelに残るcoarse interval係数をexplicit chart primitiveの
  `d0`として吸収することで、actual quotient-H¹ mapの全単射性を直接証明した。
  同じfull subset `A={0,1}`でextra coarse intervalにfine liftがないことからraw /
  semantic C2、`ConditionCAllA`、checker、generated indicator label上のlaw-indexed
  C2 / full `ConditionC`を反証し、同じblockのcoarse / fine両H¹非零も固定した。
  law-block C2からlabel-fiber A-subnerve C2へのreverse transportと、selected coarse
  endpointのdefinition-owner evaluation APIも追加した。
- 完了(Cycle 20): exact R1 `C4_not_necessary` のfactor・target counts・nerve・
  support・partial face mapをfieldwise転写し、source / readingsはfactorのcanonical
  realizationとして構成した。両nerveは同じ2本のself-loopを持ち、
  coarse側だけがboundary `(1,1,1)` のrepeated faceを2枚、fine側が1枚持つ。
  repeated-face cocycle条件の一致とselected edge cochain equivalenceから、全target
  subsetのactual quotient-H¹ map全単射性を直接証明した。同じfull subset
  `A={0,1}`でcoarse face 1にfine liftがないことからraw / semantic C4、
  `ConditionCAllA`、checker、generated indicator label上のlaw-indexed C4 / full
  `ConditionC`を反証し、同じblockのcoarse / fine両H¹非零も固定した。law-block
  C4からlabel-fiber A-subnerve C4へのreverse transportと、block face map equality
  からwhole face map equalityを取り出すdefinition-owner APIも追加した。
- 完了(Cycle 21): exact R1 `C5_not_necessary` のfactor・target counts・nerve・
  support・partial edge mapをfieldwise転写し、source / readingsはfactorのcanonical
  realizationとして構成した。coarse側のchart-one self-loop 1本へ、fine側のdistinctな
  chart-one self-loop 2本が写るためwhole-nerve lift uniqueness C5は破れる。一方、
  coarse側のrepeated face equationとfine側2本のrepeated face equationを実使用して、
  全target subsetのactual quotient-H¹ mapのinjectivity / surjectivityを直接証明した。
  C5、`ConditionCAllA`、aggregate checker、generated indicator law上のfull
  `ConditionC`を直接反証し、同じfull subset `A={0,1}`がduplicate pairの共通supportと
  交わること、およびcoarse / fine両actual H¹の非零性を接続した。
- 完了(Cycle 22): exact R1 `C6_not_necessary` のfactor・target counts・nerve・
  support・partial edge mapをfieldwise転写し、source / readingsはfactorのcanonical
  realizationとして構成した。fine interval edge `(1,2)`がcoarse chart-one
  self-loopへ写るためwhole-nerve endpoint reflection C6は破れる。一方、coarse
  repeated face equationがmapped loop係数を消し、fine interval cochainはexplicit
  chart primitiveのboundaryになることを実使用して、全target subsetのactual
  quotient-H¹ mapのinjectivity / surjectivityを直接証明した。C6、
  `ConditionCAllA`、aggregate checker、generated indicator law上のfull
  `ConditionC`を直接反証し、同じfull subset `A={0,1}`がfailed edge supportと
  交わること、およびcoarse / fine両actual H¹の非零性を接続した。
- 完了(Cycle 23): permanent `G_local-v1` contractの16 componentと出力型、
  full v5の4 packet family、strict decrease、structural reachability、memoized exact
  closure、terminal completeness、all-reachable-state packet union、C0--C6評価を
  finite raw presentationから生成するdefinition-level kernelを固定した。
  side-local radius-one rooted balls、clipped histograms、全非空target subset record、
  internally generated factor-preserving target relabelのstructured minimumから
  executable `obsG` を構成した。permanent source SHAはprovenance定数に限定し、
  observationのinput / field / premiseには使用しない。
- blocker解消(Cycle 24): preregistered `TERNARY-CYCLE-3` / `TERNARY-CYCLE-6`
  のraw finite presentationsを構成し、permanent v5 kernelのv4 coarse・v4
  fine-only・coordinate・doubled-cycleの4 packet familyをraw retained
  incidence / support / map factsから消去するdefinition-owner APIを固定した。
  その結果、T3 / T6それぞれの3非空target scopeすべてでinitial packet setが
  空であることを、巨大なhigher-order assignment列挙やexpected terminal / Obs / label
  を入力せず証明した。
- 完了(Cycle 25): T3 / T6それぞれについて、3非空target scopeの全retained
  cellをroot labelとneighbor histogramへ分解し、permanent clip-two kernelで
  rooted-ball histogramを独立正規化した。全condition coordinates、all-path
  packet-kind union、factor-preserving target relabel orbit、whole / A-scope recordを
  fieldwiseに組み立て、両`obsG`がpresentation非依存の同じclosed structural
  normal formへ評価されることから`obsG T3 = obsG T6`を証明し、claim (v)(a)を
  閉じた。common valueはpresentation field・premise・checker bit・labelではない。
- 完了(Cycle 26): 登録T3について3非空target scopeのactual quotient-H¹次元、
  induced-map rank、computed defectをそれぞれ`1→1 / rank 1 / (0,0)`、
  `0→0 / rank 0 / (0,0)`、`1→1 / rank 1 / (0,0)`とexactに証明し、既存の
  sound-complete checkerから`UniformPresentation t3Presentation`を得た。登録T6は
  target-zero scopeでcoarse / fine actual H¹次元をexactに`3 / 1`と証明し、actual
  H¹ map非全単射、computed defect非零、checker false、
  `¬ UniformPresentation t6Presentation`へ接続した。観測等値module・外部label・
  結論相当field/certificateは使わない。
- 未完了: Cycle 25の同一`obsG`とCycle 26の異なるsemantic labelを用いた、
  quantified observation predicate nonfactorization theorem (v)(d)。

## Cycle 1 — law-value block and A-subnerve identification

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean`](../lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean)
- primary declarations:
  - `TargetSupportedNerve.targetSubsetComplex`
  - `labelValueFiber_nonempty`
  - `labelValueFiber_eq_preimage`
  - `CellCoordinate.targetSubsetEquivBlock`
  - `TargetSupportedNerve.lawValueBlockTargetSubsetComplexEquiv`
  - `TargetSupportedNerveMorphism.aSubnerveComparisonHom`
  - `TargetSupportedNerveMorphism.labelFiberComparisonHom`
  - `TargetSupportedNerveMorphism.labelFiberComparison_naturality`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.ASubnerveReduction` の targeted module
    build: pass
  - namespace axiom audit: 97 declarations、standard axioms only
  - 主要 5 declaration の `#print axioms`: `propext`、`Classical.choice`、
    `Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: 任意 `A` の A-subnerve と canonical preimage comparison Hom、
  source-generated label の値 fiber の非空性と exact preimage、law-value
  block との全 degree 複体同定、comparison naturality。
- remaining: indicator law family と adequacy、global H¹ bijectivity の
  blockwise 還元、有限 defect bridge、decider、`ConditionCAllA` checker と
  bridge、発火正例、G-104 接続、7 witness、`Obs_G` と T3 / T6 分離。

### Provenance / proof-use / escape audit

- certificate provenance: A-subnerve の cell witness は K1 support と `A` の
  実際の交点から生成される。label fiber は source-generated
  `LawValueLabel.generated` と canonical `lawDescend` から生成され、選択済み
  comparison certificate を入力しない。
- proof-use: adequacy は label value と K1 support の同定に、canonical
  factor の可換性は fine fiber と coarse fiber の逆像一致に、hereditary
  nerve morphism は partial comparison map と cochain naturality に実使用される。
- structure-field escape: none found。複体同値、comparison Hom、自然性を
  structure field として受け取らず、cell map と incidence から構成した。
- route integrity: pass。任意 `A` を先に取り、coarse 側 `A` と fine 側の
  canonical preimage から双方の subnerve を構成する。label block はその後に
  source-generated fiber として同定される。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 1
decision: approve
result_type: proof-obligation-discharged
proof_obligation: U0 law-value block and A-subnerve identification
proof_obligation_delta: arbitrary A-subnerves and canonical comparison are now identified with every source-generated law-value block in all degrees
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: c4a94b1ae27e615605fa88ff4e6a9acad86d94e2
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean
    declarations:
      - TargetSupportedNerve.targetSubsetComplex
      - labelValueFiber_nonempty
      - labelValueFiber_eq_preimage
      - CellCoordinate.targetSubsetEquivBlock
      - TargetSupportedNerve.lawValueBlockTargetSubsetComplexEquiv
      - TargetSupportedNerveMorphism.aSubnerveComparisonHom
      - TargetSupportedNerveMorphism.labelFiberComparisonHom
      - TargetSupportedNerveMorphism.labelFiberComparison_naturality
premise_delta:
  discharged:
    - arbitrary A-subnerve construction and canonical preimage comparison Hom
    - nonempty source-generated label fiber and exact canonical preimage
    - law-value block complex identification and comparison naturality in all degrees
  remaining:
    - indicator law family and adequacy
    - global H1 bijectivity iff blockwise bijectivity
    - finite defect bridge and sound-complete decider
    - ConditionCAllA checker, bridge, firing instance, and G-104 connection
    - seven non-necessity witnesses
    - Obs_G fidelity and T3-T6 nonfactorization
certificate_provenance:
  discharged:
    - subnerve cells are generated from actual K1-support intersections with A
    - label fibers are generated from LawValueLabel.generated and canonical lawDescend
  unresolved:
    - indicator-family adequacy and all later witness provenance obligations
proof_use_audit:
  used_material_premises:
    - adequacy identifies label values with K1 support
    - canonical factor commutation identifies the fine fiber with the coarse preimage
    - hereditary nerve morphism constructs partial comparison maps and naturality
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
next_obligation: prove global generated H1 comparison bijective iff every source-generated block comparison is bijective
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 26 — exact T3/T6 semantic labels through the finite checker

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- proof obligation: fixed GOAL claims (v)(b)–(c)として、登録T3の3非空blockの
  actual quotient-H¹ profileをexactに求めてsemantic uniformityを証明し、登録T6の
  target-zero blockでexact `3→1` dimension mismatchを証明してsemantic
  nonuniformityを導く。Cycle 25の`Obs_G`評価や外部登録labelは証拠に使わない。
- Lean files:
  - [`ExecutableRationalRank.lean`](../lean/ResearchLean/AG/UniformInvariance/ExecutableRationalRank.lean)
  - [`PresentationASubnerveDefect.lean`](../lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean)
  - [`GLocalV1T3T6Uniformity.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Uniformity.lean)
  - [`ResearchLean/AG.lean`](../lean/ResearchLean/AG.lean)
  - [`research-modules.txt`](../lean/research-modules.txt)

### Exact profiles and semantic endpoints

T3では、registered raw supportからselected coarse / fine edge数を3非空scopeごとに
`(4,1)`、`(3,3)`、`(4,4)`と求めた。全raw edgeがself-loopなので両`d0` matrixは
零である。`d1` rankはtarget-zeroで`3 / 0`、target-oneとfullで`3 / 3`である。
H¹ block matrix rankはそれぞれ`4 / 3 / 4`である。したがってactual quotient-H¹
とcomputed evaluatorは次の同じprofileを返す。

| T3 scope | coarse H¹ | fine H¹ | induced rank | computed defect |
| --- | ---: | ---: | ---: | --- |
| `targetZero = {0}` | 1 | 1 | 1 | `(0,0)` |
| `targetOne = {1}` | 0 | 0 | 0 | `(0,0)` |
| `targetFull = {0,1}` | 1 | 1 | 1 | `(0,0)` |

`Fin 2`の全非空subsetをこの3 caseへ分類し、
`uniformPresentationCheck_eq_true_iff_allNonemptyDefects`でcheckerをtrueにした後、
sound-complete semantic bridgeから`UniformPresentation t3Presentation`を得る。

T6のtarget-zeroではselected edge数がcoarse / fineで`7 / 1`、両`d0` rankは零、
`d1` rankは`4 / 0`である。従ってactual quotient-H¹次元はexactに`3 / 1`である。
有限次元線形同値ならfinrankが一致するためactual H¹ mapは全単射でありえない。
この反証をgeneric defect correctnessとzero-defect iff bijectiveへ渡してcomputed defect
非零を得て、all-nonempty-defects checker iffからchecker false、さらにsemantic iffから
`¬ UniformPresentation t6Presentation`を導く。T6の期待defect値やchecker bitを
直接評価・入力する経路は使わない。

primary declarations:

- definition-owner rank / dimension API:
  - `rank_eq_of_selectedColumns_basis`
  - `coarseFaceEdge0In_coe` / `coarseFaceEdge1In_coe` /
    `coarseFaceEdge2In_coe`
  - `fineFaceEdge0In_coe` / `fineFaceEdge1In_coe` /
    `fineFaceEdge2In_coe`
  - `computedASubnerveH1Rank_eq_rankFormula`
  - `computedASubnerveDefect_eq_rankFormula`
  - `coarseH1Finrank_eq_card_sub_rationalMatrixRanks`
  - `fineH1Finrank_eq_card_sub_rationalMatrixRanks`
- registered profile / endpoint declarations:
  - `t3_targetZero_profile`
  - `t3_targetOne_profile`
  - `t3_targetFull_profile`
  - `t3_uniformPresentationCheck`
  - `t3_uniformPresentation`
  - `t6_targetZero_h1_profile`
  - `t6_targetZero_h1Map_not_bijective`
  - `t6_targetZero_defect_ne_zero`
  - `t6_uniformPresentationCheck`
  - `t6_not_uniformPresentation`

### Rank proof route and provenance

generic `rank_eq_of_selectedColumns_basis`は、指定列のGram determinant非零による
rank下界と、全列が指定列spanに入ることによる上界からmatrix rankをexactに決める。
fixture clientは期待rankをpresentation fieldや外部certificateとして受け取らず、
raw matrixから列選択、determinant、span relationをその場で構成する。

- T3の各`d1`とH¹ block rankは、raw face incidenceから選んだ全rank列のGram
  determinant非零と、anchor / fine-chart零列を含む残余列のspan membershipで閉じる。
- T6 target-zero coarse `d1`はneutral列1--4のGram determinant非零に加え、anchor
  列を零、残るneutral列5,6をそれぞれ
  `c5 = c1 + c2 - c4`、`c6 = -c1 + c3 + c4`として明示的にspanへ入れる。
- actual H¹ dimensionはgeneric three-cochain-complex rank formulaを、selected edge
  equivalenceとexecutable matrix-rank correctnessへ輸送するdefinition-owner APIから
  得る。computed induced rank / defectは公開rank formula APIから得る。

登録T3 / T6 presentationはCycle 24から不変で、raw reading、enumeration、nerve、
support、incidence、partial maps、well-formedness proofだけを保持する。新moduleは
`GLocalV1T3T6Observation`をimportせず、Cycle 25のcommon observation/equality、
Round-15 / Stop-B label、rank / defect / checker resultをfield・premise・typeclass・
external certificateのいずれとしても使用しない。

### Verification and quality audit

- focused `GLocalV1T3T6Uniformity`: pass、namespace auditは33 declarations、
  standard axioms only、warningなし。
- targeted `GLocalV1T3T6Uniformity` build: pass、3720 jobs。
- targeted `PresentationASubnerveDefect` build: pass、3715 jobs、namespace auditは
  143 declarations、standard axioms only。
- 新規theorem 40件とproof変更theorem 1件の全41 declarationsを個別にdirect
  `#print axioms`した。selected-face projection 6件は
  `[propext, Quot.sound]`のみ、残る35件は
  `[propext, Classical.choice, Quot.sound]`のみ。
- 新moduleは43 top-level declarations
  (29 public theorem、4 public abbreviation、10 documented private typed def)。
  43件すべてにdeclaration docstring、fixed GOAL position、raw premise / provenanceを
  記録した。owner側の新規11 theoremもdefinition直後またはrank ownerに配置し、
  同じprovenance境界を記録した。
- clientはgeneric selected-cell、matrix-rank、computed defect definitionを直接展開せず、
  definition-owner projection / formula APIを使用する。fixture-local raw incidence tableと
  explicit rational finite matrixだけを正規化する。
- `git diff --check`、Research import direction(228 modules)、package direction、
  separation fixtures: pass。
- placeholder / forbidden primitive / hidden-BiDi / privacy / Formal→Research reverse
  import scan: no finding。
- Research full build: ユーザー指示により未実行。
- independent T3: `approve / proof-obligation-discharged`、blocking findingなし。
  T3 reviewerはLean/lake/buildを実行せず、固定sourceと直接依存からrank、dimension、
  defect、checker、semantic labelの全経路を独立再構成した。

fixed source SHA-256:

- `ExecutableRationalRank.lean`:
  `79835a78a693cfbb758708780e54704d27caae9f443d4a53a01d810490b87f09`
- `PresentationASubnerveDefect.lean`:
  `ad41fb92ae2b1558733104f48e7d69a39dd305df6e28a3b14dad95d9a88fd140`
- `GLocalV1T3T6Uniformity.lean`:
  `02c23047480f2ee3df7e63ea872f3e25a24111c12f14cebe0ff5209f54be648c`
- `AG.lean`:
  `426c063c2bc41eba919f377968c42271e3f588d2992601520111e76dcd2e4e9f`
- `research-modules.txt`:
  `6d3a879a6fd43acabd5b49f684035207b0613a6babc9d728a13996a2610cc2a5`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 26
decision: approve
result_type: proof-obligation-discharged
proof_obligation: prove exact T3 uniform and T6 nonuniform semantic labels through the existing sound-complete finite checker
proof_obligation_delta: fixed GOAL claims (v)(b) and (v)(c) are independently audited Lean theorems over the preregistered raw presentations
primary_specification:
  source:
    goal: research/goals/G-107-aat-uniform-invariance-characterization.md
    registered_presentations: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Witnesses.lean
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ExecutableRationalRank.lean
    declarations:
      - rank_eq_of_selectedColumns_basis
  - file: research/lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean
    declarations:
      - coarseH1Finrank_eq_card_sub_rationalMatrixRanks
      - fineH1Finrank_eq_card_sub_rationalMatrixRanks
      - computedASubnerveH1Rank_eq_rankFormula
      - computedASubnerveDefect_eq_rankFormula
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Uniformity.lean
    declarations:
      - t3_targetZero_profile
      - t3_targetOne_profile
      - t3_targetFull_profile
      - t3_uniformPresentationCheck
      - t3_uniformPresentation
      - t6_targetZero_h1_profile
      - t6_targetZero_h1Map_not_bijective
      - t6_targetZero_defect_ne_zero
      - t6_uniformPresentationCheck
      - t6_not_uniformPresentation
premise_delta:
  discharged:
    - exact T3 actual H1 dimensions 1/0/1 on the three nonempty target scopes
    - exact T3 induced-map ranks 1/0/1 and zero computed defects on all three scopes
    - sound-complete checker truth and UniformPresentation for T3
    - exact T6 target-zero coarse/fine actual H1 dimensions 3 and 1
    - T6 target-zero actual H1-map nonbijectivity and nonzero computed defect
    - sound-complete checker falsity and not UniformPresentation for T6
  remaining:
    - quantified observation predicate-factorization refutation from equal obsG and distinct semantic labels
certificate_provenance:
  discharged:
    - registered raw selected-cell counts, self-loop endpoints, face-incidence matrices, and canonical factor
    - explicit selected columns, rational Gram determinants, and spanning relations
    - generic literal quotient-H1 dimension and computed-defect correctness bridges
  unresolved:
    - final quantified nonfactorization theorem
proof_use_audit:
  used_material_premises:
    - all three nonempty T3 target scopes and their complete selected raw incidence tables
    - exact T3 differential and H1-block ranks
    - T6 target-zero selected edge counts, exact differential ranks, and the two residual-column relations
    - generic rank formula, defect correctness, zero-defect iff bijective, and checker semantic iff
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
next_obligation: prove the quantified observation predicate-factorization refutation from Cycle 25 obsG equality and Cycle 26 semantic label separation
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 25 — registered T3/T6 full `Obs_G` evaluation and equality

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- proof obligation: fixed GOAL claim (v)(a)として、登録T3 / T6 presentationの
  permanent `obsG`を互いに独立に全成分評価し、同じclosed structural normal
  formへ到達することから`obsG T3 = obsG T6`を証明する。
- Lean files:
  - [`GLocalV1ObservationValue.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1ObservationValue.lean)
  - [`GLocalV1V5Reduction.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean)
  - [`GLocalV1Observation.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1Observation.lean)
  - [`GLocalV1T3T6Witnesses.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Witnesses.lean)
  - [`GLocalV1T3T6Observation.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Observation.lean)
  - [`ResearchLean/AG.lean`](../lean/ResearchLean/AG.lean)
  - [`research-modules.txt`](../lean/research-modules.txt)

### Closed observation and independent evaluation route

`commonObservation`はpermanent observation型のconstructorとliteral rowだけから
作るclosed dataであり、T3 / T6 presentation、`obsG`、H¹ / rank / defect、
uniformity checker、semantic label、fixture hashをdependency coneに持たない。
その成分は次のとおりである。

- aggregate condition vector:
  `(C0,C1,C2,C3,C4,C5,C6) = (false,false,false,true,false,true,true)`。
- whole record: `(C0,C5,C6) = (false,true,true)`、packet-kind unionは空、
  full-scope rooted-ball histogramは`commonFullBalls`。
- target-zero record: `(C1,C2,C3,C4) = (false,false,true,false)`、packet-kind
  unionは空、histogramは`commonA0Balls`。
- target-one / full records: `(true,true,true,true)`、packet-kind unionは空、
  histogramはそれぞれ`commonA1Balls` / `commonFullBalls`。
- A-scope record familyは上記3 rowのpermanent histogramであり、scope IDやraw
  cell IDをobservation valueへ追加しない。

T3 / T6は同じidentity-split familyとして、factor-preserving relabelがidentityと
fine-target swap `[1,0,2]`の2種類だけであることを、complete coarse / fine
permutation tableとfactor commutationから証明した。両relabelについて全cell labelが
不変であることをraw supportとcanonical code imageから示し、minimum comparatorを
展開せず、生成された全candidateが`commonObservation`であるというowner APIから
それぞれの`obsG`評価を閉じた。

primary declarations:

- owner histogram / lawful-order API:
  - `gLocalV1Histogram_eq_of_perm`
  - `gLocalV1Histogram_replicate_add_two_eq_two`
  - `gLocalV1Histogram_cons_three_eq_cons_two`
  - `gLocalV1Histogram_cons_six_eq_cons_two`
  - `gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd`
  - `gLocalV1RootedBallHistogram_append_replicate_add_two_eq_two`
- owner reducer / observation no-unfold API:
  - `mem_gLocalV1ReachabilityClosure_self`
  - `gLocalV1PathWithoutEdge_eq_true_of_selfLoop`
  - `mem_gLocalV1CoarseCriticalEdges_of_mem_of_selfLoop`
  - `mem_gLocalV1FineCriticalEdges_of_mem_of_selfLoop`
  - `mem_gLocalV1CoarseCriticalVertices_of_criticalEdge_endpoint`
  - `mem_gLocalV1FineCriticalVertices_of_criticalEdge_endpoint`
  - `mem_gLocalV1ActiveFineVertices_of_mapped_criticalEdge_endpoint`
  - `not_mem_gLocalV1CoarseBridges_of_selfLoop`
  - `not_mem_gLocalV1FineBridges_of_selfLoop`
  - `mem_gLocalV1GuardedCoarseEdges_of_mem_critical`
  - `gLocalV1CellList_apply`
  - `gLocalV1CellLabel_apply`
  - `gLocalV1OutwardStubHistogram_eq_of_cellList_eq`
  - `gLocalV1NeighborDescriptors_eq_of_cellList_eq`
  - `gLocalV1RootedBall_apply`
  - `gLocalV1InitialBallHistogram_eq_of_occurrences_eq`
  - `gLocalV1InitialBallHistogram_eq_of_cellLabel_eq`
  - `gLocalV1Minimum_eq_of_forall_mem_eq`
  - `obsG_eq_of_forall_mem_targetRelabels_candidate_eq`
- registered evaluation endpoints:
  - `c25T3MemTargetRelabels_iff` / `c25T6MemTargetRelabels_iff`
  - `t3ConditionVector` / `t6ConditionVector`
  - `t3A0RootedBallOccurrences` / `t3A1RootedBallOccurrences` /
    `t3FullRootedBallOccurrences`
  - `t6A0RootedBallOccurrences` / `t6A1RootedBallOccurrences` /
    `t6FullRootedBallOccurrences`
  - `c25T3CandidateIdentity` / `c25T3CandidateSwap`
  - `c25T6CandidateIdentity` / `c25T6CandidateSwap`
  - `t3_obsG_eq_commonObservation`
  - `t6_obsG_eq_commonObservation`
  - `t3_obsG_eq_t6_obsG`

### Fieldwise rooted-ball normalization and route integrity

各`(presentation, A)` in
`{T3,T6} × {targetZero,targetOne,targetFull}`について、complete retained cell
listをowner APIから評価した。各retained rootは次の3段階で処理する。

1. raw support / factor-image code、map status、self-loop critical / guarded /
   nonbridge flags、FaceTwin injectivityからroot labelを求める。
2. complete cell listとraw incidenceからneighbor descriptor occurrenceを列挙し、
   outward-stub histogramとneighbor histogramを各層で独立に正規化する。
3. `gLocalV1RootedBall_apply`でlabelとneighbor histogramを合成し、cell-list
   map全体をcomplete raw occurrence listへ移す。

T3のneutral edge / face multiplicity 3とT6のmultiplicity 6は、permanent
clip-two quotientの定義owner theoremにより同じmultiplicity 2へ正規化する。
raw occurrence list equalityを要求したり、T6の巨大なstate / Gram / relabel探索を
直接評価したりしない。各histogram層ではpermutation invarianceとrepeat-block
saturationだけを使う。Cycle 24のsix initial-packet-empty factsからreachable terminal
stateがinitial stateだけであることを導き、all-path packet unionも空に固定する。

presentation fieldsはCycle 24から不変で、raw reading、enumeration、nerve、support、
incidence、partial maps、well-formedness proofsだけを保持する。`commonObservation`は
theorem RHSのclosed normal formであってpresentation field / premise / certificateでは
ない。T3 / T6の両評価は別々のcell-list・incidence・support theoremを消費し、最終
equalityはその2本の評価定理だけを合成する。

### Verification and quality audit

- focused new observation module: pass、namespace auditは225 declarations、standard
  axioms only、warningなし。
- targeted `GLocalV1T3T6Observation` build: pass、3719 jobs。依存して変更した
  `GLocalV1ObservationValue` / `GLocalV1V5Reduction` /
  `GLocalV1T3T6Witnesses` / `GLocalV1Observation`も同runで再構築され、namespace
  auditsは562 / 296 / 34 / 192 declarations、standard axioms only。
- primary 3 theoremのdirect `#print axioms`はすべて
  `[propext, Classical.choice, Quot.sound]`のみ。
- new observation moduleは245 top-level declarations
  (193 public theorem、32 public data def、20 documented private typed def)。全宣言に
  declaration docstring、fixed GOAL position、raw premise / provenanceを記録した。
- clientはgeneric observation / reducer definitionを直接展開せず、definition-owner
  `*_apply` / membership / composition APIを使用する。fixture-local presentationとraw
  support / incidence tableだけを有限正規化する。
- 未使用`hand*` wrapper、raw type alias、transport wrapperを削除し、最終主定理を
  除く新規fixture declarationは受理spineまたはowner APIへ接続した。
- `git diff --check`、Research import direction(228 modules)、package direction、
  separation fixtures: pass。
- placeholder / forbidden primitive / hidden-BiDi / privacy / Formal→Research reverse
  import scan: no finding。
- Research full build: ユーザー指示により未実行。

fixed source SHA-256:

- `GLocalV1ObservationValue.lean`:
  `4f7112f545fc54ec248e51bf3e7db290519ec049643eafc4efe89007be0cda5d`
- `GLocalV1V5Reduction.lean`:
  `5b0a8781f5f15005900a629236935d812c4330c96badc5c58fe0c5defe8b6dc8`
- `GLocalV1Observation.lean`:
  `00e0a04cc907ea9325cc5c98d5c0d226515deb2c30a8280842f6790236f930cc`
- `GLocalV1T3T6Witnesses.lean`:
  `42b7720c39de656e97ebee5f87a98281127e5a5ac03222bb63f3d41f44ae5e39`
- `GLocalV1T3T6Observation.lean`:
  `4e4edc8a1b71479dc8619a3a5cbbafc6ddf05b5e650d33df06f80a7aa69f2138`
- `AG.lean`:
  `2a67b9e3d951c910f8f8deb214eded95d5a33b2c58ffe5d637db58b644f98dd9`
- `research-modules.txt`:
  `4e7e34736a4d3e02392e0992fff94d49de692bed8d23ec350164f1d97c40bede`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 25
decision: approve
result_type: proof-obligation-discharged
proof_obligation: independently evaluate full permanent obsG for registered T3 and T6 to one closed structural normal form and prove obsG T3 = obsG T6
proof_obligation_delta: fixed GOAL claim (v)(a) is now a Lean theorem over the preregistered computable presentations
primary_specification:
  source:
    goal: research/goals/G-107-aat-uniform-invariance-characterization.md
    observation: research/experiments/g104-necessity-map/g_local_v1.py
    reducer: research/experiments/g104-necessity-map/r2_hunt.py
    contract_manifest: research/experiments/g104-necessity-map/g_local_v1_stop_b.py
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4 / 5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1ObservationValue.lean
    declarations:
      - gLocalV1Histogram_eq_of_perm
      - gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean
    declarations:
      - mem_gLocalV1ReachabilityClosure_self
      - gLocalV1PathWithoutEdge_eq_true_of_selfLoop
      - gLocalV1MemoizedTerminalStates_eq_singleton_of_initial_packet_empty
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1Observation.lean
    declarations:
      - gLocalV1CellList_apply
      - gLocalV1CellLabel_apply
      - gLocalV1NeighborDescriptors_eq_of_cellList_eq
      - gLocalV1RootedBall_apply
      - gLocalV1InitialBallHistogram_eq_of_occurrences_eq
      - obsG_eq_of_forall_mem_targetRelabels_candidate_eq
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Observation.lean
    declarations:
      - commonObservation
      - t3_obsG_eq_commonObservation
      - t6_obsG_eq_commonObservation
      - t3_obsG_eq_t6_obsG
premise_delta:
  discharged:
    - complete T3/T6 nonempty target-scope enumeration
    - complete factor-preserving target-relabel orbit enumeration
    - all seven condition coordinates for both presentations
    - all-path packet-kind union for all six nonempty scopes
    - every retained-cell label and radius-one neighbor histogram at all six scopes
    - T3 threefold and T6 sixfold occurrence saturation through the same permanent clip-two quotient
    - independent full candidate evaluation for identity and swap relabels on each presentation
    - independent T3 and T6 obsG evaluations and their equality
  remaining:
    - T3 UniformPresentation through the existing sound-complete finite checker
    - T6 not UniformPresentation through the existing sound-complete finite checker
    - quantified observation predicate-factorization refutation
certificate_provenance:
  discharged:
    - registered raw target, factor, nerve, support, incidence, and identity cell-map tables
    - complete generated target relabels and factor commutation
    - complete retained-cell and radius-one incidence occurrence lists
    - Cycle 24 raw initial-packet emptiness and its terminal/all-path consequences
    - presentation-independent closed common observation built from permanent constructors only
  unresolved:
    - semantic uniformity labels and final factorization contradiction
proof_use_audit:
  used_material_premises:
    - all six nonempty scope cell lists and raw support/incidence/map tables
    - self-loop endpoint equalities, critical/guarded/nonbridge consequences, and FaceTwin key injectivity
    - complete outward-stub and neighbor occurrence lists at each retained root
    - permanent clip-two histogram quotient at every nested histogram layer
    - identity and fine-swap relabel validity, completeness, and cell-label invariance
    - Cycle 24 packet emptiness for terminal and all-path packet rows
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
next_obligation: derive T3 UniformPresentation and T6 not UniformPresentation through the existing sound-complete finite checker, without using the registered external labels
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 2 — global H¹ bijectivity iff blockwise bijectivity

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/GlobalBlockBijectivity.lean`](../lean/ResearchLean/AG/UniformInvariance/GlobalBlockBijectivity.lean)
- primary declarations:
  - `TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_bijective_iff`
  - `TargetSupportedNerveMorphism.generatedComparisonH1Map_bijective_iff_blocks`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.GlobalBlockBijectivity` の targeted module
    build: pass
  - namespace axiom audit: 2 declarations、standard axioms only
  - 主要 2 theorem の `#print axioms`: `propext`、`Classical.choice`、
    `Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: actual finite direct-sum H¹ map の全単射性と全 actual block H¹
  map の全単射性の iff、actual global H¹ map の全単射性と全 actual block
  H¹ map の全単射性の iff。
- remaining: indicator law family と両 reading への adequacy、defect profile と
  Cycle 1・2 を結ぶ最終 reduction、finite defect bridge、decider、
  `ConditionCAllA` checker / bridge / firing、7 witness、`Obs_G` と T3 / T6
  分離。

### Provenance / proof-use / escape audit

- certificate provenance: direct-sum map は既存の actual block H¹ map から
  componentwise に構成された G-104 artifact であり、global map の共役として
  新設していない。component 抽出は finite direct sum/function equivalence と
  `Pi.single` から構成する。全射の前像は各方向の `Function.Surjective` から
  proof-local に選び、inverse field を入力しない。
- proof-use: direct-sum から component への方向は全体 map の単射性・全射性を
  それぞれ使用し、逆方向は全 component の単射性・全射性をそれぞれ使用する。
  global iff の両方向は `lawGeneratedH1BlockEquiv` と
  `generatedComparisonH1Map_block_naturality` を実使用する。
- structure-field escape: none found。`ConditionC`、inverse、rank / dimension
  equality、全単射 certificate、新規 result structure を入力しない。
- route integrity: pass。actual block map → 既存 componentwise direct sum →
  reviewed canonical block decomposition / actual-map naturality → actual global
  map の順で証明する。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。empty label 型も有限直和
  一般論の一ケースとして同じ証明が覆う。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 2
decision: approve
result_type: proof-obligation-discharged
proof_obligation: actual global H1 bijectivity iff every source-generated block H1 map is bijective
proof_obligation_delta: unconditional componentwise and global bijectivity equivalences are proved for the actual G-104 maps
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: eca9d0306b4581aa522926f3e7b3f4cea217befe
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/GlobalBlockBijectivity.lean
    declarations:
      - TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_bijective_iff
      - TargetSupportedNerveMorphism.generatedComparisonH1Map_bijective_iff_blocks
premise_delta:
  discharged:
    - direct-sum H1 map bijective iff every actual block H1 map is bijective
    - actual global H1 map bijective iff every actual block H1 map is bijective
  remaining:
    - indicator law family and adequacy on both readings
    - defect profile and final reduction theorem
    - finite defect bridge and sound-complete decider
    - ConditionCAllA checker, bridge, firing instance, and G-104 connection
    - seven non-necessity witnesses
    - Obs_G fidelity and T3-T6 nonfactorization
certificate_provenance:
  discharged:
    - direct-sum map is the existing componentwise map built from actual block H1 maps
    - component extraction is constructed with the finite direct-sum equivalence and Pi.single
    - global transport uses the reviewed canonical H1 block equivalences and actual-map naturality
  unresolved:
    - indicator-family adequacy and all later witness provenance obligations
proof_use_audit:
  used_material_premises:
    - direct-sum injectivity and surjectivity are both used to extract each component
    - all component injectivity and surjectivity hypotheses are used in the reverse direction
    - canonical H1 block equivalences and naturality are used in both global directions
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
next_obligation: construct the indicator law family for every nonempty A and prove adequacy on both readings
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 3 — arbitrary nonempty subset indicator family

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/IndicatorLawFamily.lean`](../lean/ResearchLean/AG/UniformInvariance/IndicatorLawFamily.lean)
- primary declarations:
  - `indicatorLawFamily`
  - `indicatorLawFamily_adequate`
  - `indicatorLawFamily_adequate_of_coarserThan`
  - `indicatorLawFamily_lawDescend_eq`
  - `indicatorLawFamilyTrueLabel`
  - `indicatorLawFamily_trueFiber_eq`
  - `indicatorLawFamily_trueFineFiber_eq_preimage`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.IndicatorLawFamily` の targeted module
    build: pass
  - namespace axiom audit: 12 declarations、standard axioms only
  - 主要 6 declaration の `#print axioms`: `propext`、`Classical.choice`、
    `Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: 任意非空 `A` からの indicator family、coarse / fine adequacy、
  source-generated true label、canonical coarse / fine fiber の exact equality。
- remaining: Cycle 1–3 を actual H¹ map 上で接続する一様不変性 iff 全非空
  A-subnerve comparison 全単射の統合 theorem、`J_A` と finite defect bridge、
  decider、`ConditionCAllA` checker / bridge / firing、7 witness、`Obs_G` と
  T3 / T6 分離。

### Provenance / proof-use / escape audit

- certificate provenance: family は `(coarseReading, A)` だけから
  `Law := PUnit`、`Value := ULift Bool`、`eval := 1_A ∘ read` として構成する。
  `ULift` は universe を合わせるだけで、`ULift.down` により false / true の
  分離を証明する。true label の source witness は `hA` の target witness を
  `Reading.surjective` で持ち上げて生成する。
- proof-use: coarse adequacy は明示 indicator descent、fine adequacy は同 descent
  と canonical `comparisonFactor` の合成で構成する。canonical coarse descend
  との一致には `lawDescend_unique`、fine fiber には Cycle 1 の
  `labelValueFiber_eq_preimage` を実使用する。
- structure-field escape: none found。adequacy、label、fiber equalityを family
  fieldに保持せず、supplied factor / supplied label / external `DecidablePred`
  を受け取らない。
- route integrity: pass。`A = univ` を含む全非空 `A` を扱い、proper-subset・
  補集合非空・false-label generation を要求しない。classical membership は
  semantic indicator 内部だけで、後続 U1 executable decider の代用ではない。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 3
decision: approve
result_type: proof-obligation-discharged
proof_obligation: realize every nonempty target subset by a canonical adequate indicator law family
proof_obligation_delta: every nonempty A is now an exact source-generated true-label fiber on the coarse reading and its canonical preimage on every finer reading
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 26f6fc5a3f0864b6f7cb2115f94879ba455d7060
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/IndicatorLawFamily.lean
    declarations:
      - indicatorLawFamily
      - indicatorLawFamily_adequate
      - indicatorLawFamily_adequate_of_coarserThan
      - indicatorLawFamily_lawDescend_eq
      - indicatorLawFamilyTrueLabel
      - indicatorLawFamily_trueFiber_eq
      - indicatorLawFamily_trueFineFiber_eq_preimage
premise_delta:
  discharged:
    - canonical singleton lifted-Boolean indicator family for arbitrary A
    - coarse and fine adequacy generated from the reading order
    - source-generated true label for every nonempty A
    - exact coarse fiber A and exact fine canonical preimage fiber
  remaining:
    - H1-level assembly of the uniformity iff all nonempty A-subnerve bijectivity reduction
    - defect profile and finite-dimensional zero-defect bridge
    - sound-complete decider
    - ConditionCAllA checker, bridge, firing instance, and G-104 connection
    - seven non-necessity witnesses
    - Obs_G fidelity and T3-T6 nonfactorization
certificate_provenance:
  discharged:
    - family is constructed from the coarse reading and A only
    - true-label source is generated from nonempty A and reading surjectivity
    - coarse descent equality follows from lawDescend_unique
    - fine fiber equality follows through the canonical comparison factor
  unresolved:
    - H1-level assembly and all later witness provenance obligations
proof_use_audit:
  used_material_premises:
    - A nonemptiness generates the true label
    - reading surjectivity generates its source witness
    - coarse order generates fine adequacy through comparisonFactor_commutes
    - lawDescend_unique and exact-preimage naturality identify both canonical fibers
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
next_obligation: assemble Cycles 1-3 into uniformity iff every nonempty A-subnerve H1 comparison is bijective
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 4 — uniformity iff all nonempty A-subnerve H¹ maps are bijective

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean`](../lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean)
  and
  [`research/lean/ResearchLean/AG/UniformInvariance/UniformityInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/UniformityInstancePairs.lean)
- primary declarations:
  - `ThreeCochainComplex.CochainEquiv.h1Equiv`
  - `ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply`
  - `TargetSupportedNerveMorphism.labelFiberComparison_h1_naturality`
  - `TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_bijective_iff_labelFiber`
  - `TargetSupportedNerveMorphism.UniformInvariance`
  - `TargetSupportedNerveMorphism.AllNonemptyASubnerveH1Bijective`
  - `TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective`
  - `TargetSupportedNerveMorphism.identityMorphism_uniformInvariance`
  - `UniformInvarianceInstancePairs.positive_generatedComparisonH1Map_nonzero`
  - `UniformInvarianceInstancePairs.negative_not_uniformInvariance`
  - `UniformInvarianceInstancePairs.negative_exists_nonbijective_aSubnerveH1Map`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.UniformityReduction` の targeted module
    build: pass
  - namespace axiom audit: 14 declarations、standard axioms only
  - 主要 7 declaration の `#print axioms`: `propext`、`Classical.choice`、
    `Quot.sound` のみ
  - instance-pair module の targeted module build / focused check: pass
  - instance-pair namespace axiom audit: 23 declarations、standard axioms only
  - instance-pair 主要 6 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: Cycle 1 の cochain equivalence を actual H¹ equivalence へ持ち上げ、
  actual block / label-fiber maps の自然性と全単射性 iff を証明した。任意の
  law family と両 adequacy を内部量化した一様不変性と、任意非空 `A` の
  actual A-subnerve H¹ map の全単射性を両方向に接続した。
- remaining: `J_A` の定義と finite-dimensional zero-defect bridge、sound /
  complete decider、`ConditionCAllA` checker / bridge / firing、7 witness、
  `Obs_G` と T3 / T6 分離。

### Provenance / proof-use / escape audit

- certificate provenance: H¹ equivalence は Cycle 1 の degreewise linear
  equivalence と differential compatibility から forward / inverse cochain Hom
  を生成し、actual quotient map が互いに逆であることから構成する。H¹
  naturality には Cycle 1 の degree-one naturality を渡し、外部 certificate
  を受け取らない。
- proof-use: forward direction は任意非空 `A` から Cycle 3 indicator family を
  構成し、Cycle 2 global→blocks、actual block→fiber、exact fiber equality を
  全て使う。reverse direction は任意 laws / adequacy / label について
  `labelValueFiber_nonempty`、canonical exact preimage、fiber→block、Cycle 2
  blocks→global を使う。
- structure-field escape: none found。`Function.Bijective`、H¹ equivalence、
  naturality、subset equality を comparison structure field として保持しない。
  subset transport の equality と compatibility proof は主 theorem 内で Cycle 1 / 3
  から生成され、全単射性や map equalityを供給しない。
- route integrity: pass。actual `generatedComparisonH1Map` → actual block map →
  actual `targetSubsetComparisonHom.h1Map` の順で両方向を接続する。固定 family、
  rank equality、zero-H¹、`ConditionC` へ弱めない。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。
- instance pair: 正例は G-104 firing supported nerve の hereditary identity
  comparison。任意 A の actual selected-subset Hom が cochain / H¹ 上で恒等と
  なることを incidence と canonical self-factor から構成し、既存の非零
  `coarseFiringClass` の actual image も非零と証明した。反例は adequate な
  G-104 failure の actual nonbijective global mapを内部量化へ特殊化し、同値定理
  から nonempty A 上の actual nonbijective map の存在まで導出した。反例は
  coarse H¹=0 と fine の既証明非零 class で非全射を示すため、両側零 H¹ の
  vacuity ではない。inadequacy・stored result bit による instance でもない。
- review finding resolution: 初回 4-lane review の P1（新規 Prop 2述語の
  §1.4 instance pair 欠落）を受け、正負 instance と非空虚性 theorem を追加した。
  statement / proof / GOAL scope は不変。宣言と import の追加を含むため
  direct-response 資格は用いず、修正後 fixed head を正式 4-lane で再査読する。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 4
decision: approve
result_type: proof-obligation-discharged
proof_obligation: uniform invariance iff every nonempty actual A-subnerve H1 comparison map is bijective
proof_obligation_delta: Cycles 1-3 are assembled on actual H1 quotients into the unconditional bijectivity-level reduction
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 0360bdd76b9e366686a7d7bb767b2eac0cd3b158
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean
    declarations:
      - ThreeCochainComplex.CochainEquiv.h1Equiv
      - ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
      - TargetSupportedNerveMorphism.labelFiberComparison_h1_naturality
      - TargetSupportedNerveMorphism.generatedBlockComparisonH1Map_bijective_iff_labelFiber
      - TargetSupportedNerveMorphism.UniformInvariance
      - TargetSupportedNerveMorphism.AllNonemptyASubnerveH1Bijective
      - TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective
  - file: research/lean/ResearchLean/AG/UniformInvariance/UniformityInstancePairs.lean
    declarations:
      - TargetSupportedNerveMorphism.identityMorphism_uniformInvariance
      - UniformInvarianceInstancePairs.positive_uniformInvariance
      - UniformInvarianceInstancePairs.positive_generatedComparisonH1Map_nonzero
      - UniformInvarianceInstancePairs.negative_not_uniformInvariance
      - UniformInvarianceInstancePairs.negative_not_allNonemptyASubnerveH1Bijective
      - UniformInvarianceInstancePairs.negative_exists_nonbijective_aSubnerveH1Map
premise_delta:
  discharged:
    - actual H1 equivalence and naturality generated from Cycle 1 cochain data
    - actual block H1 bijectivity iff actual label-fiber A-subnerve H1 bijectivity
    - uniform invariance iff all nonempty actual A-subnerve H1 maps are bijective
    - nonzero-H1 positive identity instance and adequate actual-map negative instance
  remaining:
    - J_A and the finite-dimensional zero-defect bridge
    - sound-complete executable decider
    - ConditionCAllA checker, bridge, firing instance, and G-104 connection
    - seven non-necessity witnesses
    - Obs_G fidelity and T3-T6 nonfactorization
certificate_provenance:
  discharged:
    - H1 equivalence is generated from degreewise equivalences and differential compatibility
    - H1 naturality is generated from the reviewed degree-one naturality theorem
    - all subset equalities used for dependent transport are generated inside the main theorem
    - positive and negative instances are derived from actual comparison geometry and maps
  unresolved:
    - defect, decider, ConditionCAllA, witness, and nonfactorization provenance
proof_use_audit:
  used_material_premises:
    - arbitrary law families and both adequacy proofs in UniformInvariance
    - nonempty A and the generated indicator family in the forward direction
    - nonempty canonical label fibers in the reverse direction
    - canonical comparison factor and exact-preimage equalities in both directions
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
next_obligation: define J_A on the actual A-subnerve H1 map and prove J_A equals zero iff that map is bijective
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 5 — exact defect semantics and completion of claim (i)

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean`](../lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean)
- primary declarations:
  - `blockDefect`
  - `blockDefect_eq_zero_iff_bijective`
  - `TargetSupportedNerveMorphism.aSubnerveDefect`
  - `TargetSupportedNerveMorphism.aSubnerveDefect_eq_zero_iff_bijective`
  - `TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.DefectSemantics` の targeted module
    build: pass
  - namespace axiom audit: 5 declarations、standard axioms only
  - 主要 3 theorem の `#print axioms`: `propext`、`Classical.choice`、
    `Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: generic finite-dimensional rational linear map について、kernel と
  literal cokernel quotient の finrank がともに零であることと全単射性の iff。
  actual `aSubnerveComparisonHom A` の H¹ map へ特殊化し、Cycle 4 の iff と
  各非空 `A` で接続して claim (i) の defect 還元を完成した。
- remaining: `FiniteComparisonPresentation`、executable sound / complete defect
  decider、`ConditionCAllA` checker / bridge / firing、7 witness、`Obs_G` と
  T3 / T6 分離。

### Provenance / proof-use / escape audit

- certificate provenance: `blockDefect` は actual linear map の kernel、range、
  codomain quotient から直接生成する。inverse、rank equality、defect value、
  bijectivity certificate を argument / field として受け取らない。actual
  specialization の finite-dimensional instance は有限 A-subnerve complex の
  H¹ quotient から既存 instance として得る。
- proof-use: forward direction は第1成分から `ker = ⊥` と injectivity、第2
  成分と quotient finrank formula から `range = ⊤` と surjectivity を導く。
  reverse direction も injectivity と surjectivity を別々に各成分へ使う。
  最終 iff は Cycle 4 の uniform / all-nonempty-A iff と pointwise defect
  bridge を両方向・任意非空 `A` で実使用する。
- structure-field escape: none found。defect は `M` と `A` から actual H¹ map
  を経て計算され、comparison structure に新 field を加えない。
- route integrity: pass。`M → aSubnerveComparisonHom A → actual h1Map →
  ker / range / quotient → finrank pair` の経路であり、fine subset は既存の
  canonical `comparisonFactor ⁻¹' A` のまま保持される。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。
- instance nonvacuity: 新設した `blockDefect` / `aSubnerveDefect` はデータ定義で
  新しい Prop wrapper ではない。Cycle 4 の非零 H¹ 正例と actual nonbijective
  負例が、同値を通して零 defect locus の両側を既に発火させる。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 5
decision: approve
result_type: proof-obligation-discharged
proof_obligation: finite kernel-cokernel defect bridge and completion of claim (i)
proof_obligation_delta: exact actual-map defect semantics now characterizes uniform invariance on every nonempty A
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 74a992bc571fc3a71fa46f44cff2f7b1100974b1
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean
    declarations:
      - blockDefect
      - blockDefect_eq_zero_iff_bijective
      - TargetSupportedNerveMorphism.aSubnerveDefect
      - TargetSupportedNerveMorphism.aSubnerveDefect_eq_zero_iff_bijective
      - TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero
premise_delta:
  discharged:
    - finite-dimensional zero defect iff actual linear map bijective
    - actual A-subnerve zero defect iff actual H1 map bijective
    - uniform invariance iff zero defect for every nonempty A
    - fixed GOAL claim (i)
  remaining:
    - FiniteComparisonPresentation and executable sound-complete decider
    - ConditionCAllA checker, bridge, firing instance, and G-104 connection
    - seven non-necessity witnesses
    - Obs_G fidelity and T3-T6 nonfactorization
certificate_provenance:
  discharged:
    - defect is generated directly from the actual H1 map kernel, range, and quotient
    - actual finite-dimensional instances are inherited from finite cochain complexes
  unresolved:
    - presentation, decider, ConditionCAllA, witness, and nonfactorization provenance
proof_use_audit:
  used_material_premises:
    - both zero-defect coordinates and both directions of bijectivity
    - finite-dimensionality of the generic domain and codomain
    - Cycle 4 uniformity reduction and the pointwise defect bridge for every nonempty A
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
next_obligation: construct FiniteComparisonPresentation and the executable sound-complete zero-defect decider required by claim (ii)
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 6 — finite comparison presentation and canonical route integrity

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean`](../lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean)
- primary declarations:
  - `FiniteComparisonPresentation`
  - `FiniteComparisonPresentation.coarseReading`
  - `FiniteComparisonPresentation.fineReading`
  - `FiniteComparisonPresentation.computedRepresentative`
  - `FiniteComparisonPresentation.fineRead_computedRepresentative`
  - `FiniteComparisonPresentation.computedFactor`
  - `FiniteComparisonPresentation.computedFactor_commutes`
  - `FiniteComparisonPresentation.computedFactor_eq_comparisonFactor`
  - `FiniteComparisonPresentation.coarseSupportedNerve`
  - `FiniteComparisonPresentation.fineSupportedNerve`
  - `FiniteComparisonPresentation.toGeometry`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.FiniteComparisonPresentation` の
    targeted module build: pass
  - namespace axiom audit: 110 declarations、standard axioms only
  - 主要 10 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: finite / decidable target と cell、`Finset` support、reading
  table、incidence table、hereditary partial comparison table、明示的 source
  enumeration からの executable factor 生成、canonical factor との一致、
  actual comparison geometry と raw / semantic correspondence。
- remaining: `UniformPresentation`、presentation 上の `J_A` 有限計算、
  sound / complete zero-defect checker、checker を true / false 両側で発火させる
  nonvacuous positive / negative raw presentation、claim (iii)–(v)。

### Provenance / proof-use / escape audit

- certificate provenance: factor は `sourceEntries` 上の Boolean search で fine
  target の source representative を選び、raw coarse reading を適用して生成する。
  search correctness は enumeration coverage と fine-reading surjectivity から得る。
  canonical equality は raw kernel inclusion による commutation と G-104
  `comparisonFactor_unique` から導出する。
- proof-use: source enumeration coverage、両 reading の surjectivity、raw kernel
  inclusion、support compatibility、endpoint / face incidence coherence、hereditary
  degeneracy の各 premise は search proof、factor commutation、supported nerve / morphism
  構成に実使用される。
- structure-field escape: none found。assembled geometry、supplied factor、factor
  equality、H¹、rank、defect、uniformity、checker result の field はない。
- route integrity: pass。raw table → executable factor → canonical equality →
  generated supported nerves / morphism の順を保ち、projection API で reading、
  support、chart / edge / face map、両 nerve の全 incidence が raw table に戻る。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。
- cycle boundary: `UniformPresentation` は導入時に §1.4 の positive /
  negative instance pair が必要なため、checker と同じ次 cycle で導入する。
  本 cycle での defer は固定 target の削除ではなく proof DAG の導入順である。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 6
decision: approve
result_type: proof-obligation-discharged
proof_obligation: finite comparison presentation and canonical route-integrity foundation
proof_obligation_delta: raw finite tables now generate the executable factor, canonical comparison geometry, and all raw-semantic projection correspondences
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 7ab6fe33ce4942ffa25235557618cfbcd4146083
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean
    declarations:
      - FiniteComparisonPresentation
      - FiniteComparisonPresentation.computedRepresentative
      - FiniteComparisonPresentation.computedFactor
      - FiniteComparisonPresentation.computedFactor_commutes
      - FiniteComparisonPresentation.computedFactor_eq_comparisonFactor
      - FiniteComparisonPresentation.coarseSupportedNerve
      - FiniteComparisonPresentation.fineSupportedNerve
      - FiniteComparisonPresentation.toGeometry
premise_delta:
  discharged:
    - executable source enumeration and representative search
    - computed factor commutation and equality with the canonical comparison factor
    - raw-data-generated supported nerves and actual comparison morphism
    - reading, support, map, endpoint, and face-incidence projection correspondence
  remaining:
    - UniformPresentation and executable zero-defect checker
    - soundness and completeness against actual uniform invariance
    - nonvacuous positive and negative raw presentations
    - ConditionCAllA positioning, seven witnesses, and observation nonfactorization
certificate_provenance:
  discharged:
    - factor and geometry are generated from raw finite tables and their well-formedness proofs
  unresolved:
    - checker, ConditionCAllA, witness, and nonfactorization provenance
proof_use_audit:
  used_material_premises:
    - source enumeration coverage and reading surjectivity
    - raw coarse-kernel inclusion
    - support compatibility and all incidence and hereditary-degeneracy laws
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
next_obligation: define UniformPresentation and prove an executable sound-complete zero-defect checker with nonvacuous positive and negative raw presentations
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 7 — executable rational rank and literal defect correctness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/ExecutableRationalRank.lean`](../lean/ResearchLean/AG/UniformInvariance/ExecutableRationalRank.lean)
- primary declarations:
  - `ExecutableRationalLinearAlgebra.selectedColumns`
  - `ExecutableRationalLinearAlgebra.columnGram`
  - `ExecutableRationalLinearAlgebra.columnGram_det_ne_zero_iff`
  - `ExecutableRationalLinearAlgebra.hasNonzeroGramMinor`
  - `ExecutableRationalLinearAlgebra.hasNonzeroGramMinor_eq_true_iff`
  - `ExecutableRationalLinearAlgebra.rationalMatrixRank`
  - `ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_rank`
  - `ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range`
  - `ExecutableRationalLinearAlgebra.rationalMatrixDefect`
  - `ExecutableRationalLinearAlgebra.rationalMatrixDefect_eq_blockDefect`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - `ResearchLean.AG.UniformInvariance.ExecutableRationalRank` の targeted
    module build: pass (3713 jobs)
  - namespace axiom audit: 26 declarations、standard axioms only
  - 主要 10 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - generic evaluator の `#eval`: projection / inclusion / duplicated-column /
    identity / zero の rank は順に `1 / 1 / 1 / 2 / 0`、rectangular defect は
    `(1, 0) / (0, 1)`
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: 一般有限 rectangular rational matrix の executable exact rank、
  Gram selection 判定の sound / complete、計算した domain-minus-rank /
  codomain-minus-rank pair と literal
  `(finrank ker, finrank (codomain ⧸ range))` の一致。
- remaining: `FiniteComparisonPresentation` の各非空 `A` から actual
  A-subnerve cochain / H¹ comparison matrix を生成し、この evaluator による
  defect と `toGeometry.aSubnerveDefect A` を一致させること。全 `A` の零 defect
  checker と `UniformPresentation` sound / completeness、claims (iii)–(v)。

### Provenance / proof-use / escape audit

- certificate provenance: executable definitions は matrix entries、有限
  `Fin k → n` selection、rational arithmetic、Gram determinant の有限判定だけを
  読む。`Matrix.rank`、basis、kernel、range、quotient、supplied rank / defect、
  `Classical.dec` は evaluator body にない。有限 row / column index の
  `Fintype` だけで探索でき、別の `DecidableEq` premise は要求しない。
  column-span basis と古典選択は completeness proof 内だけで使う。
- proof-use: forward は非零 Gram determinant から selected-column independence、
  selected span の単調性を通して `k ≤ rank` を導く。reverse は column span の
  finrank-size independent familyを `Fin.castLE` で制限し、実列 index の selection
  を構成する。exact defect bridge は range finrank、rank-nullity、literal quotient
  finrank の3経路を実使用する。
- structure-field escape: none found。新 structure、supplied basis / rank / defect、
  checker result field はない。Cycle 6 presentation に field を追加していない。
- route integrity: pass。entries → column selection → Gram determinant →
  executable rank → exact linear defect の順を保ち、semantic rank / defect は
  theorem の右辺にだけ現れる。
- cheat-route audit: fixture lookup / square-only determinant / one-way soundness /
  noncomputable rank wrapper / result certificate injection / GOAL reinterpretation は
  いずれも `none-found`。
- cycle boundary: 本 cycle は新しい uniformity Prop / certificate structureを
  導入しないため §1.4 instance pair を発火させない。具体例は一般 evaluator の
  rank感度と kernel/coker 座標順を検査するもので、後続の positive / negative
  `UniformPresentation` pair の代用ではない。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 7
decision: approve
result_type: proof-obligation-discharged
proof_obligation: executable rational matrix rank evaluator and kernel-cokernel defect correctness
proof_obligation_delta: finite Gram search now computes exact rank for every finite rectangular rational matrix and equals the literal linear defect
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 55d25af1c039cb8c0360e30fa1d65f7f9fc2e61f
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ExecutableRationalRank.lean
    declarations:
      - ExecutableRationalLinearAlgebra.columnGram_det_ne_zero_iff
      - ExecutableRationalLinearAlgebra.hasNonzeroGramMinor_eq_true_iff
      - ExecutableRationalLinearAlgebra.rationalMatrixRank
      - ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_rank
      - ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range
      - ExecutableRationalLinearAlgebra.rationalMatrixDefect
      - ExecutableRationalLinearAlgebra.rationalMatrixDefect_eq_blockDefect
premise_delta:
  discharged:
    - executable exact rank for arbitrary finite rectangular rational matrices
    - sound and complete Gram-selection criterion
    - equality with literal kernel and quotient-cokernel finranks
  remaining:
    - presentation-level actual A-subnerve H1 matrix and defect correspondence
    - all-nonempty-A zero-defect checker and UniformPresentation sound-completeness
    - ConditionCAllA positioning, seven witnesses, and observation nonfactorization
certificate_provenance:
  discharged:
    - evaluator output is generated only from matrix entries, finite selections, rational arithmetic, and determinants
  unresolved:
    - actual A-subnerve matrix extraction and uniform checker integration
proof_use_audit:
  used_material_premises:
    - finite row and column index types; no separate DecidableEq premise
    - both directions of Gram determinant versus selected-column independence
    - selected-column span monotonicity and a full column-span independent family
    - matrix rank width bound
    - rank-nullity and literal range-quotient finrank formula
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
next_obligation: derive each actual A-subnerve H1 comparison defect from the finite presentation and connect it to this evaluator before defining the all-A checker
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 8 — presentation A-subnerve matrices and actual defect correspondence

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean`](../lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean)
- primary declarations:
  - `ThreeCochainComplex.Hom.range_h1Map`
  - `ThreeCochainComplex.Hom.h1RankBlockLinearMap`
  - `ThreeCochainComplex.Hom.finrank_range_h1Map_eq_h1RankBlock`
  - `ThreeCochainComplex.finrank_h1_eq_c1_sub_d1_sub_d0`
  - `blockDefect_eq_finrank_sub_range`
  - `FiniteComparisonPresentation.h1RankBlockMatrix`
  - `FiniteComparisonPresentation.computedASubnerveH1Rank`
  - `FiniteComparisonPresentation.computedASubnerveDefect`
  - `FiniteComparisonPresentation.computedASubnerveDefect_eq_aSubnerveDefect`
  - `BoundaryShortcutCounterexample.f1_rank_ne_h1Map_rank`
- verification:
  - `CohomologyComparison`、`DefectSemantics`、manifest 登録済み Cycle 8
    file の focused check: pass
  - `CohomologyComparison` / `DefectSemantics` の targeted module build: pass
  - `ResearchLean.AG.UniformInvariance.PresentationASubnerveDefect` の targeted
    module build: pass (3715 jobs)
  - `AAT.AG.TwoPhase` namespace axiom audit: 15 declarations、standard axioms only
  - `DefectSemantics` の `AAT.AG.ResolutionInvariance` namespace axiom audit:
    6 declarations、standard axioms only
  - `AAT.AG.TwoPhase.ThreeCochainComplex` namespace axiom audit:
    4 declarations、standard axioms only
  - `AAT.AG.ResolutionInvariance` namespace axiom audit:
    97 declarations、standard axioms only
  - 主要 6 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - placeholder、hidden / bidirectional Unicode、privacy、
    Formal→Research 逆 import、`git diff --check`: clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - 初回の generic `Hom` namespace audit 収載漏れを1行の永続 audit 追加で
    解消し、focused check と targeted build を再実行した。
  - 初回 PR 査読の API 品質 finding に対し、`h1Map` range と `blockDefect`
    finrank 形を各定義側の公開 API に移し、Cycle 8 下流の直接 unfold を除去した。
    complex 単体の H¹ 次元定理も `ThreeCochainComplex` 直下へ移動し、修正後
    snapshot の独立 T3 を正式再実行して approve を得た。

### Premise delta

- discharged: raw finite support / incidence tables と任意の `Finset A` からの
  coarse / fine selected cells、computed-factor preimage、両 `d0` / `d1`、
  actual partial `f1`、H¹ block matrix、computed defect の生成。raw / semantic
  cell・incidence・map correspondence、block-rank exact sequence、Cycle 7 rank
  correctnessを通して、空 `A` を含む
  `computedASubnerveDefect_eq_aSubnerveDefect` を証明した。
- remaining: `UniformPresentation`、全 subset 零 defect checker と sound /
  complete theorem、nonvacuous positive / negative raw presentations、
  `ConditionCAllA` checker / bridge / Atlas positioning / firing 正例、7 witness、
  `Obs_G` / T3 / T6 / nonfactorization theorem。

### Provenance / proof-use / escape audit

- certificate provenance: selected cells は raw `Finset` support と `A` の
  実交差から生成し、fine subset は executable `computedFactor` の有限 preimage
  から生成する。matrix は raw incidence / partial edge table で構成した linear
  map の標準 `LinearMap.toMatrix'`、rank は Cycle 7 の exact rational evaluator
  から生成する。semantic 側は correctness theorem の中だけで canonical factor
  equality と cell reindexingを用いて接続する。
- proof-use: chart-support compatibility は mapped selected cell の構成に、endpoint /
  face incidence は raw differential と semantic differential の可換性に、partial
  edge table と hereditary law は actual `f1` との `none` / `some` 両分岐の一致に
  実使用される。block theorem は mapped cycles + target boundaries と block range
  の2本の exact sequence、rank-nullity、literal quotient finrankを使用する。
- structure-field escape: none found。presentation に matrix、basis、rank、H¹、
  defect、uniformity、checker result の field を追加せず、新 structure / Prop も
  導入していない。
- route integrity: pass。raw support → selected cells / incidence → raw linear maps →
  generated matrices → Cycle 7 exact rank → computed defect → canonical cell
  reindexing → actual literal defect の順を保つ。
- boundary sensitivity: source H¹ finrank `1`、target H¹ finrank `0`、underlying
  `f1` range finrank `1`、induced H¹-map range finrank `0` の regression fixture に
  より、`H¹(f)` rank を `f1` rank で置換する shortcut を排除した。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  supplied certificate / `Classical.dec` / GOAL-report reinterpretation はいずれも
  `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 8
decision: approve
result_type: proof-obligation-discharged
proof_obligation: derive every actual A-subnerve H1 comparison defect from the finite presentation
proof_obligation_delta: raw finite tables now generate the H1 block matrix and exact defect for every finite A, equal to the literal actual A-subnerve defect
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: fdc1b13987110d1c7a31a7a08513edd44376b477
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean
    declarations:
      - ThreeCochainComplex.Hom.h1RankBlockLinearMap
      - ThreeCochainComplex.Hom.finrank_range_h1Map_eq_h1RankBlock
      - ThreeCochainComplex.finrank_h1_eq_c1_sub_d1_sub_d0
      - FiniteComparisonPresentation.h1RankBlockMatrix
      - FiniteComparisonPresentation.computedASubnerveH1Rank
      - FiniteComparisonPresentation.computedASubnerveDefect
      - FiniteComparisonPresentation.computedASubnerveDefect_eq_aSubnerveDefect
      - BoundaryShortcutCounterexample.f1_rank_ne_h1Map_rank
  - file: research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean
    declarations:
      - ThreeCochainComplex.Hom.range_h1Map
  - file: research/lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean
    declarations:
      - blockDefect_eq_finrank_sub_range
premise_delta:
  discharged:
    - raw selected cells and computed-factor preimage for every finite A
    - raw and semantic incidence, differential, and actual partial-f1 correspondence
    - exact block-rank recovery of literal quotient-H1 rank
    - executable presentation defect equality with actual A-subnerve defect, including empty A
    - boundary-sensitive rejection of the underlying-f1 rank shortcut
  remaining:
    - UniformPresentation and executable all-subset zero-defect checker
    - checker soundness and completeness
    - nonvacuous positive and negative raw presentation firing
    - ConditionCAllA checker, bridge, Atlas positioning, and firing positive example
    - seven non-necessity witnesses
    - Obs_G, T3/T6 labels, and nonfactorization
certificate_provenance:
  discharged:
    - cells, incidence, matrices, ranks, and defects are generated from raw finite tables and Cycle 7 exact rank
  unresolved: []
proof_use_audit:
  used_material_premises:
    - finite decidable target and cell data
    - raw support, incidence, partial-map, and compatibility laws
    - computed-factor equality with the canonical comparison factor
    - Cycle 7 rational rank correctness
    - finite-dimensional exact-sequence, rank-nullity, and quotient-finrank formulas
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
next_obligation: define UniformPresentation and an executable all-subset zero-defect checker, prove soundness and completeness, and fire nonvacuous positive and negative raw presentations
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 9 — executable all-subset uniform-presentation decider

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`research/lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean`](../lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean`](../lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean)
- primary declarations:
  - `UniformPresentation`
  - `FiniteComparisonPresentation.exists_sublists_toFinset_eq`
  - `FiniteComparisonPresentation.uniformPresentationCheck`
  - `FiniteComparisonPresentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects`
  - `FiniteComparisonPresentation.allNonemptyComputedASubnerveDefect_eq_zero_iff`
  - `FiniteComparisonPresentation.uniformPresentationCheck_eq_true_iff`
  - `UniformPresentationInstancePairs.positivePresentation`
  - `UniformPresentationInstancePairs.negativePresentation`
  - `UniformPresentationInstancePairs.positive_fullTarget_firing`
  - `UniformPresentationInstancePairs.negative_fullTarget_firing`
  - `UniformPresentationInstancePairs.positive_uniformPresentationCheck`
  - `UniformPresentationInstancePairs.negative_uniformPresentationCheck`
  - `UniformPresentationInstancePairs.positive_uniformPresentation`
  - `UniformPresentationInstancePairs.negative_not_uniformPresentation`
- verification:
  - `FiniteComparisonPresentation`、`UniformPresentationDecider`、
    `UniformPresentationInstancePairs` の focused check: pass
  - `ResearchLean.AG.UniformInvariance.UniformPresentationInstancePairs` の
    targeted module build: pass (3717 jobs)
  - namespace axiom audit: `112 / 6 / 10` declarations、standard axioms only
  - 主要 8 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - direct executable evaluation:
    positive rank / defect / checker = `1 / (0, 0) / true`、
    negative rank / defect / checker = `1 / (0, 1) / false`
  - placeholder、hidden / bidirectional Unicode、privacy、
    Formal→Research 逆 import、tracked / untracked `git diff --check`: clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - explicit target List coverage、全 Finset / 全 Set bridge、checker body、
    Cycle 8 / Cycle 5 theorem の proof-use、raw instance pair、rank-one
    nonvacuity、field-content、private helper、no-unfoldを独立監査し、
    blocking finding なし。

### Premise delta

- discharged: explicit coarse-target List の coverage から任意の `Finset` を
  `List.sublists` 内の sublist の `toFinset` として生成し、`List.all` で全非空
  subset の exact zero defect を判定する。有限 target 上の任意の `Set` を
  `Set.Finite.toFinset` でこの量化へ移し、Cycle 8 の
  `computedASubnerveDefect_eq_aSubnerveDefect` と Cycle 5 の
  `uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero` を通して
  `uniformPresentationCheck = true ↔ UniformPresentation` を両方向に証明した。
  同じ checkerを nonvacuous positive / negative raw presentationで発火させた。
- remaining: `ConditionCAllA` の law / H¹ / rank 非参照の幾何定義、
  presentation-level checker と sound / complete theorem、bridge / Atlas
  positioning / firing 正例、7 non-necessity witnesses、`Obs_G` の全成分転写、
  T3 / T6 labels・観測等値・分離 theorem。

### Provenance / proof-use / escape audit

- certificate provenance: checker は explicit raw target List、raw support /
  incidence / partial-map tables、Cycle 8 exact defect evaluatorだけを読む。
  `FiniteComparisonPresentation` への追加 field は target List と全要素 coverage
  proof のみ。positive / negative は同じ raw self-loop constructorを
  `FineEdge = PUnit / Bool` で発火し、matrix、rank、defect、uniformity、expected
  Booleanを保存しない。
- proof-use: `coarseTarget_mem_coarseTargetEntries` は任意 Finset の coverageに、
  `computedASubnerveDefect_eq_aSubnerveDefect` は raw / actual defect 接続に、
  `uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero` は full semantic iffに
  実使用される。positive / negative checker verdictは一般 sound / complete
  theoremを通り、rank-one proof は checker / semantic truthを仮定せず raw block
  matrixの outer-product rankから独立に導く。
- structure-field escape: none found。新 field は raw enumeration と coverageのみで、
  rank、defect、uniformity、checker result、all-subset zero certificate はない。
- route integrity: pass。explicit target List → all sublists → `toFinset` →
  raw matrices / exact rational rank → computed defect → actual defect →
  full semantic `UniformInvariance` の順を保つ。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  semantic checker embedding / `Classical.dec` / supplied result bit / fixture lookup /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 9
decision: approve
result_type: proof-obligation-discharged
proof_obligation: complete claim ii with an executable all-subset uniform-presentation decider
proof_obligation_delta: explicit target enumeration now drives a sound-complete checker connected to full semantic uniformity and fired on rank-one positive and negative raw presentations
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: bd630a2a7371c973d6644b19902ec2fb1e220566
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean
    declarations:
      - FiniteComparisonPresentation.coarseTargetEntries
      - FiniteComparisonPresentation.coarseTarget_mem_coarseTargetEntries
  - file: research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean
    declarations:
      - UniformPresentation
      - FiniteComparisonPresentation.exists_sublists_toFinset_eq
      - FiniteComparisonPresentation.uniformPresentationCheck
      - FiniteComparisonPresentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects
      - FiniteComparisonPresentation.allNonemptyComputedASubnerveDefect_eq_zero_iff
      - FiniteComparisonPresentation.uniformPresentationCheck_eq_true_iff
  - file: research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean
    declarations:
      - UniformPresentationInstancePairs.positivePresentation
      - UniformPresentationInstancePairs.negativePresentation
      - UniformPresentationInstancePairs.positive_fullTarget_firing
      - UniformPresentationInstancePairs.negative_fullTarget_firing
      - UniformPresentationInstancePairs.positive_uniformPresentationCheck
      - UniformPresentationInstancePairs.negative_uniformPresentationCheck
      - UniformPresentationInstancePairs.positive_uniformPresentation
      - UniformPresentationInstancePairs.negative_not_uniformPresentation
premise_delta:
  discharged:
    - every finite coarse-target subset is generated from the explicit target List
    - executable all-nonempty-subset zero-defect checking
    - raw computed defect to arbitrary semantic Set defect correspondence
    - checker truth iff full semantic UniformPresentation
    - rank-one positive and negative raw presentation firing through the same checker
  remaining:
    - ConditionCAllA definition, checker, bridge, Atlas positioning, and positive firing
    - seven non-necessity witnesses
    - Obs_G component transcription, T3/T6 labels, observational equality, and separation
certificate_provenance:
  discharged:
    - target subsets, matrices, ranks, defects, and checker results are generated from raw finite tables
  unresolved: []
proof_use_audit:
  used_material_premises:
    - explicit target-list coverage
    - Cycle 8 presentation defect correctness
    - Cycle 5 semantic defect characterization
    - raw incidence and partial-map data in both instance firings
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
next_obligation: define law-H1-rank-free ConditionCAllA from C0/C5/C6 and all-nonempty-A C1-C4 A-subnerve clauses before constructing its executable checker
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 10 — all-subset geometric Condition C semantics

- decision: `approve`
- result type: `proof-checkpoint`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllA.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllA.lean)
  [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllAInstancePairs.lean)
- primary declarations:
  - `TargetSupportedNerveMorphism.aSubnerveChartMap`
  - `TargetSupportedNerveMorphism.aSubnerveEdgeMapOption`
  - `TargetSupportedNerveMorphism.aSubnerveFaceMapOption`
  - `TargetSupportedNerveMorphism.TargetSubsetFiberEdge`
  - `TargetSupportedNerveMorphism.TargetSubsetFiberAdjacent`
  - `TargetSupportedNerveMorphism.targetSubsetFiberIncoming`
  - `TargetSupportedNerveMorphism.targetSubsetFiberIncoming_apply`
  - `TargetSupportedNerveMorphism.targetSubsetFiberOutgoing`
  - `TargetSupportedNerveMorphism.targetSubsetFiberOutgoing_apply`
  - `TargetSupportedNerveMorphism.TargetSubsetFiberCycle`
  - `TargetSupportedNerveMorphism.TargetSubsetInternalFace`
  - `TargetSupportedNerveMorphism.targetSubsetFaceBoundary`
  - `TargetSupportedNerveMorphism.targetSubsetFaceBoundary_apply`
  - `TargetSupportedNerveMorphism.ConditionC1AtTargetSubset`
  - `TargetSupportedNerveMorphism.ConditionC2AtTargetSubset`
  - `TargetSupportedNerveMorphism.ConditionC3AtTargetSubset`
  - `TargetSupportedNerveMorphism.ConditionC4AtTargetSubset`
  - `TargetSupportedNerveMorphism.ConditionCAllA`
  - `TargetSupportedNerveMorphism.aSubnerveEdgeMapOption_eq_some_iff`
  - `TargetSupportedNerveMorphism.aSubnerveFaceMapOption_eq_some_iff`
  - `TargetSupportedNerveMorphism.targetSubsetFiberEdge_iff_endpoint_cells`
  - `TargetSupportedNerveMorphism.targetSubsetFiberAdjacent_iff`
  - `TargetSupportedNerveMorphism.targetSubsetFiberCycle_mk`
  - `TargetSupportedNerveMorphism.conditionCAllA_intro`
  - `ConditionCAllAInstancePairs.positive_targetSubsetFiberEdge`
  - `ConditionCAllAInstancePairs.not_targetSubsetFiberEdge`
  - `ConditionCAllAInstancePairs.positive_targetSubsetFiberAdjacent`
  - `ConditionCAllAInstancePairs.not_targetSubsetFiberAdjacent`
  - `ConditionCAllAInstancePairs.positive_targetSubsetFiberCycle`
  - `ConditionCAllAInstancePairs.not_targetSubsetFiberCycle`
  - `ConditionCAllAInstancePairs.positive_targetSubsetInternalFace`
  - `ConditionCAllAInstancePairs.not_targetSubsetInternalFace`
  - `ConditionCAllAInstancePairs.positive_conditionC1AtTargetSubset`
  - `ConditionCAllAInstancePairs.missing_not_conditionC1AtTargetSubset`
  - `ConditionCAllAInstancePairs.positive_conditionC2AtTargetSubset`
  - `ConditionCAllAInstancePairs.missing_not_conditionC2AtTargetSubset`
  - `ConditionCAllAInstancePairs.positive_conditionC3AtTargetSubset`
  - `ConditionCAllAInstancePairs.acyclicityFailure_not_conditionC3AtTargetSubset`
  - `ConditionCAllAInstancePairs.positive_conditionC4AtTargetSubset`
  - `ConditionCAllAInstancePairs.missing_not_conditionC4AtTargetSubset`
  - `ConditionCAllAInstancePairs.positive_conditionCAllA`
  - `ConditionCAllAInstancePairs.missing_not_conditionCAllA`
- verification:
  - `ConditionCAllA.lean` と `ConditionCAllAInstancePairs.lean` の focused
    check: pass
  - `ResearchLean.AG.UniformInvariance.ConditionCAllAInstancePairs` targeted
    module build: pass (3709 jobs)
  - namespace axiom audit: API module 59 declarations、instance module 56
    declarations、いずれも standard axioms only
  - 主要 7 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - placeholder、`Classical.dec`、`native_decide`、hidden / bidirectional
    Unicode、privacy、Formal→Research 逆 import、tracked / untracked
    `git diff --check`: clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-checkpoint`
  - C0/C5/C6 の whole-nerve scope、C1 の endpoint-defined fiber、C2/C4 の
    canonical partial map、C3 の有限 rational cycle / internal-face boundary、
    全非空 `Set A` と canonical preimage を独立監査し、定義 snapshot には
    blocking finding なし。
  - 初回修正 snapshot は incoming / outgoing / face-boundary の3有限和定義を
    instance proof が直接 `unfold` していたため、§2.4 API gap として一度 reject。
    generic `[simp]` evaluation lemma 3本を追加し、下流4箇所を API 経由へ置換した
    直接対応再監査で finding 解消を確認した。
  - 9組の正負例は predicate の品質 gate を閉じるが固定 GOAL の
    discharge-required firing / checker / bridge を代替しないため、
    `proof-obligation-discharged` への昇格は不可。

### Initial PR review finding and repair

- initial fixed head の4本査読では、Math A lane が Lean品質基準 §1.4 の
  正負 instance pairと §2.4 の same-unit no-unfold API 欠落を Major と判定した。
  他3 lane は definition checkpoint として承認または minor扱いだったが、
  共有 review protocol に従い Major を採用して実装へ戻した。
- 修正後は map Option の raw characterization、endpoint / face incidence、
  fiber edge / adjacency / cycle / internal face、C1--C4、`ConditionCAllA` の
  constructor / eliminator、incoming / outgoing / face-boundary の有限和評価を
  公開 API として追加した。
- 既査読 G-104 fixture の raw reading・supported nerve・partial morphismだけを
  actual `A = univ` subnerveへ読み直し、9 Propすべてで正負を発火させた。
  central 正例では二 chart fiber、非零 self-loop cycle、internal face filling、
  exact edge / face liftを実使用する。central 負例は missing-image C0、C3 負例は
  face-free nonzero cycleを直接使う。result bitや filling certificate fieldはない。
- この品質 instance は constant-law G-104 fixtureであり、固定 GOAL が別途要求する
  `ResolutionInvarianceFiringData` の nonconstant-law・両側非零 H¹ firingを
  代替しない。
- 修正 head の正式査読中間監査で、face-boundary 負例の `simp` listに定義名が
  1箇所残ることと adjacency の named eliminator欠落を検出した。前者を
  `targetSubsetFaceBoundary_apply` 利用へ置換し、後者に
  `targetSubsetFiberAdjacent_iff` を追加して正負例を同API経由へ統一した。

### Premise delta

- discharged: なし。`ConditionCAllA` は固定 GOAL の direction hypothesis の
  意味論を曖昧性なく固定したが、discharge-required premise を証明していない。
- fixed at checkpoint: existing whole-nerve `ConditionC0` / `ConditionC5` /
  `ConditionC6` を一度だけ要求し、全非空 `A : Set coarseReading.Target` と
  `comparisonFactor ⁻¹' A` 上で actual A-subnerve C1--C4 を要求する幾何 predicate。
- remaining: `conditionCAllACheck` と sound / complete iff、G-107指定の firing
  正例、`labelValueFiber` transport による bridge、Atlas positioning、7
  non-necessity witnesses、`Obs_G`、T3 / T6、observation nonfactorization。

### Provenance / proof-use / escape audit

- certificate provenance: A-subnerve は実際の K1 support intersectionから、fine
  subset は canonical `comparisonFactor` の逆像から定義される。新しい
  certificate、supplied factor、checker verdict は入力に追加しない。
- proof-use: C0/C5/C6 は既存 whole-nerve 条項として実使用される。C1 は
  endpoint-defined fiber graphだけを読み、誤って partial `edgeMap` を条件へ
  加えない。C2/C4 は canonical partial subset mapを、C3 は有限 rational
  cycle と internal-face boundaryを実使用する。
- instance proof-use: 正例は raw incidenceから二 chart fiberの連結、非零
  self-loop cycleの保存則、internal face boundary、edge / face liftを導出する。
  負例は missing raw map または face-free nonzero cycleを直接発火させる。
- structure-field escape: none found。全新規条件は `Prop` であり、path、lift、
  face chain は存在量化内にだけ現れる。law family、adequacy、H¹、rank、defect、
  uniformity、checker truth の field はない。
- route integrity: pass。任意の非空 `A` を先に取り、coarse `A` と canonical fine
  preimage 上の actual cell / incidence / partial mapsから各 clauseを定める。
- cheat-route audit: target-fitting construction / vacuity / degeneracy /
  one-way-as-equivalence / GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 10
decision: approve
result_type: proof-checkpoint
proof_obligation: fix law-H1-rank-free ConditionCAllA semantics before constructing its executable checker
proof_obligation_delta: the whole-nerve and every-nonempty-A geometric hypothesis, public no-unfold API including all finite-sum evaluation lemmas, and all nine positive-negative quality pairs are now fixed without discharging executable or transport obligations
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 5c90c38ca3609e2e8852b75a140651be7b625d0f
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllA.lean
    declarations:
      - TargetSupportedNerveMorphism.aSubnerveChartMap
      - TargetSupportedNerveMorphism.aSubnerveEdgeMapOption
      - TargetSupportedNerveMorphism.aSubnerveFaceMapOption
      - TargetSupportedNerveMorphism.TargetSubsetFiberEdge
      - TargetSupportedNerveMorphism.TargetSubsetFiberAdjacent
      - TargetSupportedNerveMorphism.targetSubsetFiberIncoming
      - TargetSupportedNerveMorphism.targetSubsetFiberIncoming_apply
      - TargetSupportedNerveMorphism.targetSubsetFiberOutgoing
      - TargetSupportedNerveMorphism.targetSubsetFiberOutgoing_apply
      - TargetSupportedNerveMorphism.TargetSubsetFiberCycle
      - TargetSupportedNerveMorphism.TargetSubsetInternalFace
      - TargetSupportedNerveMorphism.targetSubsetFaceBoundary
      - TargetSupportedNerveMorphism.targetSubsetFaceBoundary_apply
      - TargetSupportedNerveMorphism.ConditionC1AtTargetSubset
      - TargetSupportedNerveMorphism.ConditionC2AtTargetSubset
      - TargetSupportedNerveMorphism.ConditionC3AtTargetSubset
      - TargetSupportedNerveMorphism.ConditionC4AtTargetSubset
      - TargetSupportedNerveMorphism.ConditionCAllA
      - TargetSupportedNerveMorphism.aSubnerveEdgeMapOption_eq_some_iff
      - TargetSupportedNerveMorphism.aSubnerveFaceMapOption_eq_some_iff
      - TargetSupportedNerveMorphism.targetSubsetFiberEdge_iff_endpoint_cells
      - TargetSupportedNerveMorphism.targetSubsetFiberAdjacent_iff
      - TargetSupportedNerveMorphism.targetSubsetFiberCycle_mk
      - TargetSupportedNerveMorphism.conditionCAllA_intro
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAInstancePairs.lean
    declarations:
      - ConditionCAllAInstancePairs.positive_targetSubsetFiberEdge
      - ConditionCAllAInstancePairs.not_targetSubsetFiberEdge
      - ConditionCAllAInstancePairs.positive_targetSubsetFiberAdjacent
      - ConditionCAllAInstancePairs.not_targetSubsetFiberAdjacent
      - ConditionCAllAInstancePairs.positive_targetSubsetFiberCycle
      - ConditionCAllAInstancePairs.not_targetSubsetFiberCycle
      - ConditionCAllAInstancePairs.positive_targetSubsetInternalFace
      - ConditionCAllAInstancePairs.not_targetSubsetInternalFace
      - ConditionCAllAInstancePairs.positive_conditionC1AtTargetSubset
      - ConditionCAllAInstancePairs.missing_not_conditionC1AtTargetSubset
      - ConditionCAllAInstancePairs.positive_conditionC2AtTargetSubset
      - ConditionCAllAInstancePairs.missing_not_conditionC2AtTargetSubset
      - ConditionCAllAInstancePairs.positive_conditionC3AtTargetSubset
      - ConditionCAllAInstancePairs.acyclicityFailure_not_conditionC3AtTargetSubset
      - ConditionCAllAInstancePairs.positive_conditionC4AtTargetSubset
      - ConditionCAllAInstancePairs.missing_not_conditionC4AtTargetSubset
      - ConditionCAllAInstancePairs.positive_conditionCAllA
      - ConditionCAllAInstancePairs.missing_not_conditionCAllA
premise_delta:
  discharged: []
  fixed_at_checkpoint:
    - whole-nerve C0, C5, and C6 together with every-nonempty-A C1-C4 semantics
  remaining:
    - conditionCAllACheck and its sound-complete iff
    - nonconstant-law firing example with both H1 sides nonzero
    - labelValueFiber transport bridge
    - Atlas positioning theorem
    - seven non-necessity witnesses
    - Obs_G, T3/T6 labels, observational equality, and separation
certificate_provenance:
  discharged: []
  unresolved:
    - checker correctness and firing provenance
    - bridge transport
    - negative witness provenance
proof_use_audit:
  used_material_premises:
    - existing whole-nerve ConditionC0, ConditionC5, and ConditionC6
    - actual A-subnerve support and incidence
    - canonical comparisonFactor and partial subset maps
    - reviewed raw G-104 positive, missing-image, and face-free fixtures
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
next_obligation: construct conditionCAllACheck on FiniteComparisonPresentation and prove conditionCAllACheck_eq_true_iff, including sound-complete handling of finite C1 reachability and rational C3 solvability
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 11 — executable all-subset Condition C checker

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAChecker.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllAChecker.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllACheckerInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllACheckerInstancePairs.lean)
- primary declarations:
  - `ExecutableRationalLinearAlgebra.ker_le_range_iff_finrank_range_add_eq_card`
  - `FiniteComparisonPresentation.exists_conditionC_sublists_toFinset_eq`
  - `FiniteComparisonPresentation.fiberGraph`
  - `FiniteComparisonPresentation.fiberGraph_reachable_iff_targetSubsetFiberAdjacent_reflTransGen`
  - `FiniteComparisonPresentation.conditionC1AtTargetSubsetCheck_eq_true_iff`
  - `FiniteComparisonPresentation.fiberCycleConstraintMatrix`
  - `FiniteComparisonPresentation.internalFaceBoundaryMatrix`
  - `FiniteComparisonPresentation.fiberCycleConstraint_comp_internalFaceBoundary`
  - `FiniteComparisonPresentation.conditionC3FiberCheck_eq_true_iff`
  - `FiniteComparisonPresentation.rawConditionC3At_iff_conditionC3AtTargetSubset`
  - `FiniteComparisonPresentation.conditionC3AtTargetSubsetCheck_eq_true_iff`
  - `FiniteComparisonPresentation.conditionCAllACheck`
  - `FiniteComparisonPresentation.conditionCAllACheck_eq_true_iff`
  - `ConditionCAllACheckerInstancePairs.positive_conditionC1AtTargetSubsetCheck`
  - `ConditionCAllACheckerInstancePairs.disconnected_conditionC1AtTargetSubsetCheck`
  - `ConditionCAllACheckerInstancePairs.positive_conditionC3AtTargetSubsetCheck`
  - `ConditionCAllACheckerInstancePairs.faceFree_conditionC3AtTargetSubsetCheck`
  - `ConditionCAllACheckerInstancePairs.positive_conditionCAllACheck`
  - `ConditionCAllACheckerInstancePairs.faceFree_conditionCAllACheck`
- verification:
  - `ConditionCAllAChecker.lean` focused check: pass
  - `ResearchLean.AG.UniformInvariance.ConditionCAllACheckerInstancePairs`
    targeted module build: pass (3739 jobs)
  - namespace axiom audit: checker module 86 declarations、instance module 31
    declarations、いずれも standard axioms only
  - 主要 7 declaration の `#print axioms`: `propext`、
    `Classical.choice`、`Quot.sound` のみ
  - direct executable evaluation: positive / disconnected C1 = `true / false`、
    positive / face-free C3 = `true / false`、positive / face-free aggregate =
    `true / false`
  - placeholder、`unsafe`、`native_decide`、hidden / bidirectional Unicode、
    privacy、Formal→Research 逆 import、tracked / untracked `git diff --check`:
    clean
  - Research 全体の full build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - checker source hash `cca79dd846d26f6cc8fc0ba86e79c9c06f5f3c032e88b5c520960c3317b13236`、
    instance source hash `c90c045ffe0d5e4623261737231fc5593e30c148f9a315802d4f0256130975fb`
    の固定 snapshotを独立監査した。
  - C0--C6 raw定義、C1 finite reachability、C3 raw complex / exact rank、
    raw / semantic transport、全 subset coverage、main iff、正負6 firingに
    blocking findingなし。
  - checker obligationは閉じたが、品質 fixtureは固定 GOAL が要求する
    nonconstant-law・両側非零 H¹ の `Pfire` ではなく、bridge / Atlas / witness /
    observation系も未完なので completion candidate ではない。

### Premise delta

- discharged: finite raw presentationだけを入力とする `conditionCAllACheck` と
  `conditionCAllACheck P = true ↔ P.toGeometry.ConditionCAllA`。C1 の endpoint
  fiber graph上の有限 reachabilityと semantic `Relation.ReflTransGen` の同値、
  C3 の fiber-support / conservation constraint、internal-face boundary、複体則、
  exact rational rank criterion、raw / semantic chain・face・boundaryの双方向輸送、
  explicit target Listから全非空 `Set`への subset coverageを閉じた。同じ generic
  checkerを C1・C3・aggregate の正負側で発火させた。
- remaining: G-104 firing fixtureを raw presentation `Pfire` として接続し、
  `firing_conditionCAllA`、`conditionCAllACheck Pfire = true`、両側非零 H¹ を同時に
  証明すること。続いて `ConditionCAllA` から law-indexed `ConditionC` への bridge、
  Atlas positioning、C0--C6 の非必要性 witness 7種、`Obs_G`、T3 / T6、
  observation nonfactorization。

### Provenance / proof-use / escape audit

- certificate provenance: checkerは finite source / target enumeration、raw
  readings、cell / support / incidence / partial mapsを読む。result bit、path、
  filling chain、matrix、rank、exactness certificateの fieldはなく、
  `computedFactor` は同じ raw reading dataから計算し canonical `comparisonFactor`
  との既存一致 theoremへ接続する。
- proof-use: C1 は endpoint-defined adjacencyと有限 graph reachabilityを実使用する。
  C3 は face-incidence identitiesから boundary が constraint kernelへ入る複体則を
  証明し、Cycle 7 rational rank correctnessを kernel / range exactnessへ接続する。
  最終 iffでは C0、全非空 A の C1--C4、C5、C6を全て使用する。
- structure-field escape: none found。`FiniteComparisonPresentation` への field追加は
  なく、instance fixturesも raw geometryと well-formednessだけを保持する。
- route integrity: pass。raw tables → canonical factor / selected cells → fiber graph /
  rational matrices → Bool checker → actual A-subnerve clauses → `ConditionCAllA` の順を
  保つ。`UniformPresentationDecider` の semantic checkerを importして結果を迂回しない。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  `Classical.dec` / supplied result・path・filling・rank certificate /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 11
decision: approve
result_type: proof-obligation-discharged
proof_obligation: construct an executable finite raw ConditionCAllA checker with sound-complete C1 reachability and rational C3 solvability
proof_obligation_delta: conditionCAllACheck now decides the full law-H1-rank-free ConditionCAllA predicate from raw finite geometry and fires on positive and negative C1, C3, and aggregate presentations
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 2633fc64af2b85e608648de4ca006791c550eaa1
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAChecker.lean
    declarations:
      - ExecutableRationalLinearAlgebra.ker_le_range_iff_finrank_range_add_eq_card
      - FiniteComparisonPresentation.exists_conditionC_sublists_toFinset_eq
      - FiniteComparisonPresentation.fiberGraph_reachable_iff_targetSubsetFiberAdjacent_reflTransGen
      - FiniteComparisonPresentation.conditionC1AtTargetSubsetCheck_eq_true_iff
      - FiniteComparisonPresentation.fiberCycleConstraint_comp_internalFaceBoundary
      - FiniteComparisonPresentation.conditionC3FiberCheck_eq_true_iff
      - FiniteComparisonPresentation.rawConditionC3At_iff_conditionC3AtTargetSubset
      - FiniteComparisonPresentation.conditionC3AtTargetSubsetCheck_eq_true_iff
      - FiniteComparisonPresentation.conditionCAllACheck
      - FiniteComparisonPresentation.conditionCAllACheck_eq_true_iff
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllACheckerInstancePairs.lean
    declarations:
      - ConditionCAllACheckerInstancePairs.positive_conditionC1AtTargetSubsetCheck
      - ConditionCAllACheckerInstancePairs.disconnected_conditionC1AtTargetSubsetCheck
      - ConditionCAllACheckerInstancePairs.positive_conditionC3AtTargetSubsetCheck
      - ConditionCAllACheckerInstancePairs.faceFree_conditionC3AtTargetSubsetCheck
      - ConditionCAllACheckerInstancePairs.positive_conditionCAllACheck
      - ConditionCAllACheckerInstancePairs.faceFree_conditionCAllACheck
premise_delta:
  discharged:
    - executable conditionCAllACheck from finite raw presentation data only
    - checker truth iff full semantic ConditionCAllA
    - finite C1 reachability iff semantic fiber connectivity
    - rational C3 complex law and exact rank criterion
    - raw-semantic C3 chain and boundary transport
    - all explicit target subsets iff every nonempty semantic Set
    - positive-negative C1, C3, and aggregate checker firing
  remaining:
    - nonconstant-law Pfire with checker true and both H1 sides nonzero
    - ConditionCAllA to law-indexed ConditionC bridge
    - Atlas positioning theorem
    - seven non-necessity witnesses
    - Obs_G, T3/T6 labels, observational equality, and separation
certificate_provenance:
  discharged:
    - checker result, reachability, exactness, and ranks are derived from raw finite tables
    - computedFactor is derived from raw readings and identified with the canonical factor
  unresolved: []
proof_use_audit:
  used_material_premises:
    - finite enumeration completeness and explicit target-list coverage
    - raw incidence and support compatibility
    - canonical-factor correspondence and selected-cell equivalences
    - Cycle 7 exact rational rank correctness
    - all C0-C6 components of ConditionCAllA
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
next_obligation: construct the fixed-GOAL nonconstant-law Pfire presentation and prove firing_conditionCAllA, conditionCAllACheck Pfire = true, and both-side nonzero H1 firing together
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 12 — nonconstant-law ConditionCAllA firing

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean)
- primary declarations:
  - `ResolutionInvarianceFiringWitness.firingCoarseChartSupportFinset`
  - `ResolutionInvarianceFiringWitness.firingFineChartSupportFinset`
  - `ResolutionInvarianceFiringWitness.pFire`
  - `ResolutionInvarianceFiringWitness.pFire_computedFactor_eq_coarseRead`
  - `ResolutionInvarianceFiringWitness.pFire_conditionCAllA`
  - `ResolutionInvarianceFiringWitness.pFire_conditionCAllACheck`
  - `ResolutionInvarianceFiringWitness.firing_conditionCAllA`
  - `ResolutionInvarianceFiringWitness.fixed_conditionCAllA_firing`
- verification:
  - `ConditionCAllAFiring.lean` focused check: pass
  - `ResearchLean.AG.UniformInvariance.ConditionCAllAFiring` targeted module
    build: pass (3749 jobs)
  - namespace axiom audit: 25 declarations、standard axioms only
  - 主要5 declarationの `#print axioms`: `propext`、`Classical.choice`、
    `Quot.sound` のみ
  - placeholder、`unsafe`、`native_decide`、`Classical.dec`、hidden /
    bidirectional Unicode、privacy、Formal→Research逆import、aggregate / manifest、
    tracked / untracked whitespace scan: clean
  - Research全体のfull build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - source SHA-256
    `28e54c152314cefc5d9eab394b0f543240c90e9a5cff04b9f565683c13390460`
    の固定 snapshotを独立監査した。
  - original geometryとraw presentationを別々に有限セルから再構成し、global
    structure equality / `HEq` や checker result fieldで接続していない。
  - C1の非自明connector、C3のsupport / conservation / internal-face filling、
    singleton repeated-face branch、proper factor、nonconstant law、両側非零 H¹の
    proof-useにblocking findingなし。

### Premise delta

- discharged: 固定GOALの `ConditionCAllA` 正例 instance。G-104 firing fixtureの
  original `nerveMorphism` に対し、任意の非空 `A : Set (Fin 2)` を `0 ∈ A` と
  `A = {1}` に分け、C1--C4を直接証明した。前者では三 fine chart、五 fine edge、
  二 fine faceを保持し、connectorによるfiber connectivity、fiber外edgeの零、
  conservationからのconnector係数零、二internal faceによるcycle fillingを使用する。
  後者では唯一のcoarse/fine chart・self-loop edge・repeated faceを使用する。
  whole-nerve C0/C5/C6と集約して `firing_conditionCAllA` を得た。
- discharged: 同じ raw tablesだけから `pFire` を構成した。明示target subsetの
  C1/C2/C4は有限決定、C3はraw cycle constraintとinternal-face boundaryを直接
  解き、全非空subsetの `pFire_conditionCAllA` を証明したうえで、Cycle 11のgeneric
  iffから `pFire.conditionCAllACheck = true` を得た。
- discharged: `fixed_conditionCAllA_firing` により、`pFire` と元readingの一致、
  computed / canonical factor一致、factorの非単射性、lawの非定常性、original
  `ConditionCAllA`、checker truth、coarse / fine両側の非零H¹ class、canonical
  imageの一致を一つのclosed theoremに固定した。
- remaining: `ConditionCAllA M → ∀ laws hcoarse hfine,
  M.ConditionC laws hcoarse hfine` の条項別transport bridge。続いてAtlas
  positioning、C0--C6非必要性witness 7種、`Obs_G` / T3 / T6 / observation
  nonfactorization。

### Provenance / proof-use / escape audit

- certificate provenance: `pFire` は G-104 fixtureと同じ source / target型、raw
  readings、cell incidence、chart / partial edge / partial face mapをfieldへ直接置く。
  supportだけを既存 `Set` supportと点ごとに同値な `Finset` tableへ移し、source /
  targetの実行用enumerationを加える。condition bit、path、face chain、matrix、rank、
  H¹ class、checker result fieldは持たない。
- proof-use: `pFire_computedFactor_eq_coarseRead` はraw source searchからの
  `computedFactor_eq_comparisonFactor` とG-104 canonical uniqueness theoremを使用する。
  raw C3はfiber外edge row、fiber chart conservation row、internal-face boundaryを
  直接使用する。original C3はactual A-subnerveのincoming / outgoing / face-boundary
  APIを通し、非零self-loop係数をinternal faceで充填する。
- structure-field escape: none found。original geometry側の結論をraw presentationの
  fieldに保持せず、両側をそれぞれtable / supportから証明する。
- route integrity: pass。G-104 raw data → executable support / enumeration → canonical
  factor → raw all-subset clauses → generic checker truth、およびG-104 original geometry
  → actual all-subset clauses、の二経路をclosed bundleで合流させる。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  global structure `HEq` / supplied result・path・filling・rank certificate /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 12
decision: approve
result_type: proof-obligation-discharged
proof_obligation: reuse the exact G-104 nonconstant-law firing fixture and connect original ConditionCAllA, the executable raw checker, and both nonzero H1 classes
proof_obligation_delta: the exact G-104 firing geometry now satisfies ConditionCAllA on every nonempty target subset, its fieldwise raw finite presentation fires the generic checker, and one closed theorem joins the proper comparison, nonconstant law, checker truth, and both nonzero H1 classes
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 2c837d1ab6718e4fda0045731914b492ea9510f4
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean
    declarations:
      - ResolutionInvarianceFiringWitness.firingCoarseChartSupportFinset
      - ResolutionInvarianceFiringWitness.firingFineChartSupportFinset
      - ResolutionInvarianceFiringWitness.pFire
      - ResolutionInvarianceFiringWitness.pFire_computedFactor_eq_coarseRead
      - ResolutionInvarianceFiringWitness.pFire_conditionCAllA
      - ResolutionInvarianceFiringWitness.pFire_conditionCAllACheck
      - ResolutionInvarianceFiringWitness.firing_conditionCAllA
      - ResolutionInvarianceFiringWitness.fixed_conditionCAllA_firing
premise_delta:
  discharged:
    - original G-104 firing geometry satisfies ConditionCAllA for every nonempty target subset
    - fieldwise raw presentation computes the same canonical comparison factor
    - raw C1-C4 proofs cover every explicit nonempty target subset
    - generic conditionCAllACheck fires true on the same presentation
    - one closed theorem joins proper comparison, nonconstant law, original condition, checker truth, and both nonzero H1 classes
  remaining:
    - ConditionCAllA to all-adequate-law ConditionC bridge
    - Atlas positioning theorem
    - seven non-necessity witnesses
    - Obs_G, T3/T6 labels, observational equality, and separation
certificate_provenance:
  discharged:
    - presentation fields are the reviewed G-104 raw tables plus explicit finite enumerations and pointwise-equivalent Finset supports
    - checker truth is proved from raw clauses through the generic sound-complete theorem
    - both H1 nonzero facts and the canonical image are reused from the reviewed G-104 firing witness
  unresolved: []
proof_use_audit:
  used_material_premises:
    - canonical comparisonFactor and its noninjectivity
    - nonconstant firing law and both adequacy witnesses
    - actual A-subnerve endpoint, incidence, partial-map, and finite-sum APIs
    - raw selected-cell, cycle-constraint, internal-face boundary, and checker correctness APIs
    - existing coarse and fine nonzero H1 firing classes
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
next_obligation: prove ConditionCAllA M -> forall laws hcoarse hfine, M.ConditionC laws hcoarse hfine by transporting C1-C4 along the existing label-value-fiber/A-subnerve identifications
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 13 — ConditionCAllA から全 adequate law の ConditionC への bridge

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean)
  - [`research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean`](../lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean)
- primary declarations:
  - `TargetSupportedNerveMorphism.conditionC1At_of_conditionC1AtTargetSubset_labelValueFiber`
  - `TargetSupportedNerveMorphism.conditionC2At_of_conditionC2AtTargetSubset_labelValueFiber`
  - `TargetSupportedNerveMorphism.conditionC3At_of_conditionC3AtTargetSubset_labelValueFiber`
  - `TargetSupportedNerveMorphism.conditionC4At_of_conditionC4AtTargetSubset_labelValueFiber`
  - `TargetSupportedNerveMorphism.targetSubsetFiberCycle_iff_coordinateFiberCycle_labelValueFiber`
  - `TargetSupportedNerveMorphism.conditionC_of_conditionCAllA`
- verification:
  - `ResolutionInvarianceConditions.lean` focused check: pass
  - `ConditionCAllABridge.lean` focused check: pass
  - `ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditions`
    targeted module build: pass (3705 jobs)
  - `ResearchLean.AG.UniformInvariance.ConditionCAllABridge` targeted module
    build: pass (3708 jobs)
  - bridge namespace axiom audit: 33 declarations、standard axioms only
  - C1 / C2 / C3 / C4 transportと最終bridgeの `#print axioms`:
    `propext`、`Classical.choice`、`Quot.sound` のみ
  - placeholder、`unsafe`、`native_decide`、`Classical.dec`、hidden /
    bidirectional Unicode、privacy、Formal→Research逆import、aggregate / manifest、
    tracked / untracked whitespace scan: clean
  - Research全体のfull build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - bridge source SHA-256
    `85c0e157ff99539e96016ddbc1ce5f17603bee4c6f82de1094abb2c6c524d0da`
    の固定snapshotを独立監査した。
  - final theoremがlaw familyと両 adequacy witnessを結論内で全量化し、
    `ConditionCAllA`以外の幾何premiseを加えないことを確認した。
  - C3の block cycle ↔ A-subnerve cycle、internal faceの3 slot、
    incoming / outgoing、`+ - +` face boundaryの有限和再添字化を両方向で
    再構成し、blocking findingはなかった。
  - G-104側の13追加APIは既存definition / theorem bodyを変更せず、
    constructor / projection / iff / normalizationの no-unfold APIだけを追加する。

### Premise delta

- discharged: `ConditionCAllA M → ∀ laws hcoarse hfine,
  M.ConditionC laws hcoarse hfine`。各 `LawValueLabel`に対し
  `labelValueFiber_nonempty`でcoarse fiberの非空性を得て、全非空 `A`
  の C1--C4 projectionを適用した。
- discharged: `labelValueFiber_eq_preimage`由来の dependent-cell
  equivalenceでfine側canonical preimageをlabel-value blockへ移し、chart /
  edge / face、endpoint、face incidence、partial edge / face mapを条項ごとに
  transportした。subset equalityは equivalence構成中で生成・消費し、
  最終theoremの仮定に残さない。
- discharged: C3は block chainをactual A-subnerve chainへpull backし、fiber
  support / conservation、internal-face support、3つのface incidenceと有限和を使って
  filling chainをblock側へ戻した。cochain / H¹ equivalenceだけによる
  代用はしていない。
- remaining: bridgeをG-104の `generatedComparisonH1Map_bijective`に全lawごとに
  適用する Atlas positioning theorem。続いて C0--C6非必要性witness 7種、
  `Obs_G` / T3 / T6 / observation nonfactorization。

### Provenance / proof-use / escape audit

- certificate provenance: coarse fiberはsource-generated law labelのactual value fiber、
  fine fiberはcanonical `comparisonFactor`によるその逆像である。cell
  equivalenceは既存support intersectionと `labelValueFiber_eq_preimage`から構成し、
  supplied transport certificateを受け取らない。
- proof-use: C0 / C5 / C6は `ConditionCAllA` projectionを直接使い、C1--C4は
  任意labelに対する非空fiberのsubset clauseを使う。C1はadjacency path、
  C2 / C4はexact partial-map image、C3はcycleの双方向transport、internal
  faces、incoming / outgoing、face-boundaryを実使用する。
- structure-field escape: none found。`ConditionC`は結論側の Prop structureとして
  C0--C6をproof body内で構成し、field / instanceとして前提化しない。
- route integrity: pass。`ConditionCAllA` → 非空coarse label fiber → canonical
  fine preimage → actual cell / incidence / partial-map transport → law-indexed
  `ConditionC`の順を保つ。
- cheat-route audit: fixture-only検証 / `ConditionCForAllAdequate` 型premise /
  supplied equality・certificate / cochain-equivalence-only代用 / one-way-as-equivalence /
  target fitting / GOAL-report reinterpretationはいずれも `none-found`。

### Carried quality obligations from Cycle 12

Cycle 13 bridgeの中心claim・依存・公理に影響しないため本cycleに混ぜず、
G-107最終完了前の narrow quality-remediationとして次の2件を保持する。

1. `PresentationASubnerveDefect.lean`のselected-cell membershipに対する
   private characterization APIを公開no-unfold APIにし、
   `ConditionCAllAFiring.lean`の該当直接definition展開をそのAPI利用へ移す。
2. Cycle 12で追加されたprivate helper宣言に個別docstringを付与し、
   Lean品質基準 §3.2 の機械coverageを閉じる。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 13
decision: approve
result_type: proof-obligation-discharged
proof_obligation: prove ConditionCAllA M -> forall laws hcoarse hfine, M.ConditionC laws hcoarse hfine by direct label-fiber/A-subnerve transport of C1-C4
proof_obligation_delta: the law-free all-subset Atlas condition now implies the original G-104 ConditionC for every adequate finite law family, with cell incidence, partial maps, local cycles, internal faces, and finite boundaries transported explicitly
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: df635a06c82ac2ef23abd51aa3f58110b1897615
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean
    declarations:
      - TargetSupportedNerveMorphism.conditionC1At_of_conditionC1AtTargetSubset_labelValueFiber
      - TargetSupportedNerveMorphism.conditionC2At_of_conditionC2AtTargetSubset_labelValueFiber
      - TargetSupportedNerveMorphism.conditionC3At_of_conditionC3AtTargetSubset_labelValueFiber
      - TargetSupportedNerveMorphism.conditionC4At_of_conditionC4AtTargetSubset_labelValueFiber
      - TargetSupportedNerveMorphism.targetSubsetFiberCycle_iff_coordinateFiberCycle_labelValueFiber
      - TargetSupportedNerveMorphism.conditionC_of_conditionCAllA
  - file: research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean
    declarations:
      - thirteen public no-unfold constructor, projection, iff, and finite-sum normalization APIs
premise_delta:
  discharged:
    - ConditionCAllA implies ConditionC for every finite law family adequate for both readings
    - every source-generated label has a nonempty coarse value fiber
    - the fine value fiber equals the canonical inverse image of the coarse fiber
    - chart, edge, face, endpoint, face-incidence, and partial-map transport
    - bidirectional local-cycle and internal-face transport with exact finite boundaries
  remaining:
    - Atlas positioning theorem
    - seven non-necessity witnesses
    - Obs_G, T3/T6 labels, observational equality, and separation
    - two noncentral Cycle 12 quality-remediation items
certificate_provenance:
  discharged:
    - all cell equivalences are generated from actual support intersections and canonical label fibers
    - subset equality is generated by law descent and canonical comparisonFactor commutation
  unresolved: []
proof_use_audit:
  used_material_premises:
    - all C0-C6 components of ConditionCAllA
    - arbitrary laws and both adequacy witnesses quantified inside the conclusion
    - labelValueFiber_nonempty and canonical preimage equality
    - endpoint and face incidence, partial maps, and all C3 finite sums
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
next_obligation: prove the Atlas positioning theorem by applying conditionC_of_conditionCAllA and the accepted G-104 generatedComparisonH1Map_bijective theorem to every adequate law family
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 14 — Atlas positioning inclusion

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/UniformInvariance/AtlasPositioning.lean`](../lean/ResearchLean/AG/UniformInvariance/AtlasPositioning.lean)
- primary declaration:
  - `TargetSupportedNerveMorphism.uniformInvariance_of_conditionCAllA`
- verification:
  - focused check: pass
  - `ResearchLean.AG.UniformInvariance.AtlasPositioning` targeted module build:
    pass (3720 jobs)
  - namespace axiom audit: 1 declaration、standard axioms only
  - primary theorem の `#print axioms`:
    `propext`、`Classical.choice`、`Quot.sound` のみ
  - `git diff --check`、untracked whitespace、placeholder、`unsafe`、
    `native_decide`、`Classical.dec`、hidden / bidirectional Unicode、privacy、
    Formal→Research逆import、aggregate / manifest scan: clean
  - Research全体のfull build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - source SHA-256:
    `e54de5a3d3e4d4bdc63ce62175f89542d6a179471d4f5650fc654de4d2067fad`
  - `UniformInvariance` が law family と両 adequacy witnessを内部全量化すること、
    bridgeが同じ引数に対する `ConditionC` を構成すること、G-104 theoremがactual
    global generated H¹ comparison mapの全単射性を返すことを独立に追跡した。
  - blocking findingなし。

### Premise delta

- discharged: `ConditionCAllA M → M.UniformInvariance`。任意の `laws`、
  `hcoarse`、`hfine` を `UniformInvariance` の内部量化から導入し、Cycle 13
  bridgeで `ConditionC` を構成して、G-104の
  `generatedComparisonH1Map_bijective` へ渡した。
- remaining: C0--C6非必要性 witness 7種と包含真性、`Obs_G`忠実転写、T3 / T6
  labels、観測等値、observation nonfactorization、Cycle 12品質負債2件。

### Provenance / proof-use / escape audit

- certificate provenance: law-indexed `ConditionC` は外部certificateでなく
  `conditionC_of_conditionCAllA` がproof内で生成する。全単射性はsupplied inverse、
  defect equality、rank equalityでなくG-104 theoremがactual mapについて導く。
- proof-use: `hAllA` はbridgeに、`laws` / `hcoarse` / `hfine` はbridgeとG-104
  theoremの双方に実使用される。
- structure-field escape: none found。`ConditionC` や全単射性resultをcomparison
  geometryのfield / instanceとして受け取らない。
- route integrity: pass。固定GOALが指定した bridge → G-104 pointwise theoremの
  直接合成である。
- cheat-route audit: fixed law wrapper、fixture-only発火、zero-defect premise、
  supplied inverse / certificate、`ConditionCForAllAdequate` premiseはいずれも
  `none-found`。

### Carried quality obligations from Cycle 12

Atlas theoremのimport closure・statement・proofには影響しないため、本Cycleでも
次の2件を最終completion前のnarrow remediationとして保持する。

1. selected-cell / fiber / internal-face membership characterizationの公開
   no-unfold API化と、`ConditionCAllAFiring.lean`の直接definition展開の置換。
2. Cycle 12 private helper群の個別docstring補完。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 14
decision: approve
result_type: proof-obligation-discharged
proof_obligation: prove ConditionCAllA M -> M.UniformInvariance by composing the all-laws bridge with the accepted G-104 generatedComparisonH1Map_bijective theorem
proof_obligation_delta: the geometric all-subset ConditionC locus is now proved to lie inside the semantic uniform-invariance locus for arbitrary finite Source
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 02e1fcc3e458634062db9c9f5ce6744ffcda76e9
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/AtlasPositioning.lean
    declarations:
      - TargetSupportedNerveMorphism.uniformInvariance_of_conditionCAllA
premise_delta:
  discharged:
    - ConditionCAllA implies semantic UniformInvariance with every law family and both adequacy witnesses internally quantified
  remaining:
    - seven non-necessity witnesses and strictness of the Condition-C inclusion
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
    - two noncentral Cycle 12 quality-remediation items
certificate_provenance:
  discharged:
    - law-indexed ConditionC is generated by the Cycle 13 bridge
    - actual H1 bijectivity is generated by the reviewed G-104 theorem
  unresolved: []
proof_use_audit:
  used_material_premises:
    - ConditionCAllA direction hypothesis
    - arbitrary laws and both adequacy witnesses introduced from UniformInvariance
    - Cycle 13 bridge and G-104 actual-map bijectivity theorem
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
next_obligation: construct and verify the seven C0-C6 non-necessity witnesses, each with the required nondegenerate A-subnerve H1 block and direct ConditionCAllA component failure
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 15 — exact C3 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditionInstances.lean`](../lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditionInstances.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean`](../lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllACheckerInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllACheckerInstancePairs.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean)
  - [`research/lean/ResearchLean/AG/UniformInvariance/ConditionC3NonnecessityWitness.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionC3NonnecessityWitness.lean)
- primary declarations:
  - `TargetSupportedNerveMorphism.conditionC3AtTargetSubset_of_conditionC3At_labelValueFiber`
  - `R1ConditionC3Witness.presentation`
  - `R1ConditionC3Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC3Witness.uniformPresentationCheck_true`
  - `R1ConditionC3Witness.uniformPresentation`
  - `R1ConditionC3Witness.conditionC3AtTargetSubsetCheck_false`
  - `R1ConditionC3Witness.not_conditionC3AtTargetSubset`
  - `R1ConditionC3Witness.conditionCAllACheck_false`
  - `R1ConditionC3Witness.not_conditionCAllA`
  - `R1ConditionC3Witness.targetZero_both_h1_pos`
  - `R1ConditionC3Witness.indicatorLaw_nonconstant`
  - `R1ConditionC3Witness.indicator_not_conditionC3`
  - `R1ConditionC3Witness.c3_not_necessary`
- verification:
  - `PresentationASubnerveDefect`、`ConditionCAllAFiring`、
    `ConditionCAllACheckerInstancePairs`、`UniformPresentationInstancePairs`、
    `ResolutionInvarianceConditionInstances`、witnessのfocused check: pass、警告なし
  - `ResearchLean.AG.UniformInvariance.PresentationASubnerveDefect`
    targeted module build: pass (3715 jobs)
  - `ResearchLean.AG.UniformInvariance.ConditionCAllAFiring`
    targeted module build: pass (3749 jobs)
  - `ResearchLean.AG.UniformInvariance.ConditionCAllACheckerInstancePairs`
    targeted module build: pass (3739 jobs)。このcold pathで
    `ResolutionInvarianceConditionInstances`も再buildされpass
  - `ResearchLean.AG.UniformInvariance.UniformPresentationInstancePairs`
    targeted module build: pass (3717 jobs)
  - witness focused check: pass、警告なし
  - `ResearchLean.AG.UniformInvariance.ConditionC3NonnecessityWitness`
    targeted module build: pass (3740 jobs)
  - namespace axiom audit: `PresentationASubnerveDefect` 115 declarations、
    firing 25 declarations、checker pairs 31 declarations、uniform pairs 10
    declarations、G-104 condition instances 129 declarations、witness 82
    declarations、standard axioms only
  - 公開remediation API、G-104 condition instance、checker/uniform pairs、
    firing、bridge、witnessを含む主要10 declarationの
    型確認と `#print axioms`:
    `propext`、`Classical.choice`、`Quot.sound` のみ
  - canonical R1 report SHA-256とname-free semantic SHA-256を既存canonical
    generatorから再現し、raw tableをfieldwise照合
  - `git diff --check`、placeholder、`unsafe`、`native_decide`、
    `Classical.dec`、hidden / bidirectional Unicode、privacy、
    Formal→Research逆import、aggregate / manifest scan: clean
  - Research全体のfull build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - source SHA-256:
    - `ResolutionInvarianceConditionInstances.lean`:
      `595a3701f892ccb84e31491b0d84b2655fa76f0fa5622577d533a15694b0d196`
    - `PresentationASubnerveDefect.lean`:
      `b8267d009fa721fd5f4180aadffa028f11aa743ae15cdd6ebac6647f67fe891d`
    - `ConditionCAllAFiring.lean`:
      `0a7024322e9943573037444e68e7ecdb5de5b80ea0a3d2566aa045c0454a68b0`
    - `ConditionCAllACheckerInstancePairs.lean`:
      `c0538b99b1429fe85242e9acec9d80e0c7d2207a4f52966b9373d5308a3d9bb9`
    - `UniformPresentationInstancePairs.lean`:
      `60f59652bbcd7913238fee15936821d1e0942a2fe9407be93b932b33a7e3ce8d`
    - `ConditionCAllABridge.lean`:
      `2389d0e417bc7be28c4fb0576262428deb5c4cf6f046c322c8b31536446bc4d3`
    - `ConditionC3NonnecessityWitness.lean`:
      `d75934b019e6a1b1c512dc69ba4e88338c5274ebac4ddf88cf74041ec9623b7f`
  - all-subset actual cochain / H¹ equivalence、target-zero C3 failure、同じ
    canonical-preimage comparison上の両側非零H¹、indicator true-fiber逆transport、
    raw field内容を独立に追跡し、blocking findingなし。

### Premise delta

- discharged: exact R1 `C3_not_necessary` presentationの全非空 `A` に対する
  `UniformPresentation`、`A={0}` におけるactual
  `ConditionC3AtTargetSubset` failureと同じcomparisonの両側非零H¹、
  nonconstant indicator lawによるlaw-indexed `ConditionC3` failure、
  `ConditionCAllA`の直接failure、C3 witnessによるAtlas包含の真性。
- remaining: C0 / C1 / C2 / C4 / C5 / C6の個別non-necessity witness、
  `Obs_G`忠実転写、T3 / T6 labels、観測等値、observation
  nonfactorization、finite cochain / block-map evaluationの公開no-unfold API、
  新規・変更宣言docstringのposition / premise provenance監査。

### Provenance / proof-use / escape audit

- certificate provenance: canonical R1 report SHA-256
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
  とname-free semantic SHA-256
  `9bbb58959ac5840b3a50befbf3132fcf0b2e7dbaf41f91695c406a8c15ec5cc0`
  を独立再現した。factor `[0,0,1]`、両nerve、support、identity cell mapを
  fieldwise照合した。実験結果は転写照合先でありLean proof premiseではない。
- proof-use: raw support / preimage / incidenceから全 `A` のselected cell
  equivalenceとactual cochain equivalenceを構成し、actual comparison `f1`との
  equalityからactual quotient-H¹ mapの全単射性を得た。target-zeroのisolated
  self-loop、flow conservation、face不在からraw / semantic C3 failureを得た。
  coarse quotient-H¹ classのunit periodとactual mapのinjectivityから同じ `A` の
  fine H¹非零を得た。indicator adequacy、true-fiber equality、新しい逆transport
  theoremはlaw-indexed C3反証に実使用される。
- structure-field escape: none found。presentationはraw reading、enumeration、
  incidence、support、partial cell map、well-formednessのみを持つ。factor、matrix、
  rank、H¹、defect、condition / checker result、certificate fieldを持たない。
- route integrity: pass。個別rank profileを保存する代わりに、全 `Finset A` のactual
  comparisonをcochain equivalenceで直接全単射にする、より強いrouteを用いた。
- cheat-route audit: opaque decision bit、fixed-indicator-only uniformity、
  conclusion-equivalent field、supplied factor、零H¹によるvacuity、
  one-way-as-equivalenceはいずれも `none-found`。
- localized elaboration: `selectedFaceEquiv`だけに置いた
  `set_option maxHeartbeats 400000 in` はcompile上限であり、数学premiseや
  certificateではない。

### Cycle 15 review remediation and remaining quality obligation

初回fixed headのLean査読は、新witnessの中心経路がgeneric selected-cell / partial-map
定義を直接展開し、Cycle 12から保持していたAPI負債を拡大していると判定した。
同Cycle内で次を補修し、新headでfocused / targeted / axiom検証を再実行した。

- `finePreimageFinset`、raw edge / face support、coarse / fine chart / edge / face
  selection、`edgeMapOptionIn = some`の公開evaluation APIを追加した。
- 既存6本のraw-selected-cell / actual-subnerve membership characterizationを
  privateから公開APIへ昇格した。
- `ConditionCAllAFiring.lean`、本witness、Cycle 9 / 11 instance pairsを含む
  UniformInvariance subtreeの全fixture clientから、これらgeneric定義の直接展開を
  除去した。
- 公開API追加後のcold targeted rebuildで露出したG-104 condition instanceの
  brittle `simp` 1箇所を、既存incoming / outgoing formula APIの明示 `rw` と同じ
  finite normalizationへ置換した。statement、fixture、chain、結論は不変である。
- 強いall-subset theoremに置換され参照されない `targetOne` / `targetFull` と、
  それらに付随して不要になったpreimage補助APIを削除した。

これによりCycle 12品質負債のうちselected-cell / support / preimage / partial-map
characterization APIは閉じた。修正後fixed-head査読では、generic D0 / D1、edge
pullback、H¹ block map / matrixのapplication・entry APIがまだ不足し、新witnessと
既存instance-pair clientに `change` / definition展開が残ると指摘された。また、
このPRでbodyを変更したprivate helper 5件には同Cycle内で個別docstringを追加したが、
新規・変更宣言全体について一次仕様との対応、主定理/API補題としてのposition、premise
provenanceを§3.2に照らして精査・補完する品質義務は残る。いずれもCycle 15の数学
statement、premise discharge、certificate provenanceを落とさない非中心findingであり、
最終completion前にnarrow remediationとして閉じる。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 15
decision: approve
result_type: proof-obligation-discharged
proof_obligation: formalize the exact R1 C3_not_necessary raw presentation with all-subset uniformity, direct C3 failure, and nonzero H1 on both sides of the same failing subset
proof_obligation_delta: C3 is now proved non-necessary, and one uniform presentation outside ConditionCAllA establishes strictness of the Atlas inclusion
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 98cb58f76e65d7d8c54224b34a423a994f844064
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean
    declarations:
      - TargetSupportedNerveMorphism.conditionC3AtTargetSubset_of_conditionC3At_labelValueFiber
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionC3NonnecessityWitness.lean
    declarations:
      - R1ConditionC3Witness.presentation
      - R1ConditionC3Witness.uniformPresentation
      - R1ConditionC3Witness.not_conditionC3AtTargetSubset
      - R1ConditionC3Witness.targetZero_both_h1_pos
      - R1ConditionC3Witness.indicator_not_conditionC3
      - R1ConditionC3Witness.c3_not_necessary
premise_delta:
  discharged:
    - exact R1 C3_not_necessary raw presentation is semantically uniform on every nonempty target subset
    - actual C3 and ConditionCAllA fail directly on target zero
    - coarse and fine H1 are both nonzero on that same target-zero comparison
    - a nonconstant indicator law realizes the same law-indexed C3 failure
    - the Condition-C locus is a strict subset of the uniform-invariance locus
  remaining:
    - C0 C1 C2 C4 C5 C6 non-necessity witnesses
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
    - finite cochain and block-map no-unfold evaluation APIs
    - new and changed declaration docstring position and premise-provenance audit
certificate_provenance:
  discharged:
    - canonical R1 report and name-free semantic hashes independently reproduced
    - raw factor, nerves, supports, and cell maps matched field by field
    - actual factor and H1 results generated in Lean rather than stored in the presentation
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw finite reading support incidence and partial cell-map tables
    - all-subset actual cochain equivalence and actual H1 comparison
    - target-zero loop conservation, face absence, and quotient-period witness
    - indicator adequacy, true-fiber equality, and reverse C3 transport
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
nonblocking_quality_findings:
  - generic D0 D1 edge-pullback and H1 block-map or matrix clients still unfold their definitions
  - new and changed declaration docstrings require a full position and premise-provenance audit
next_obligation: close the finite cochain and block-map no-unfold APIs and the changed-declaration docstring audit before resuming the exact R1 C0_not_necessary witness
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 16 — finite cochain API and declaration provenance remediation

- decision: `approve`
- result type: `proof-checkpoint`
- completion candidate: `no`
- T1-selected obligation: finite coarse/fine `d0`・`d1` linear map / matrix、
  edge pullback、H¹ block linear map / matrixのdefinition-owner evaluation APIを
  公開し、Cycle 15 clientをdirect unfoldingから移行する。同じbounded cycleで
  Cycle 15全新規・body変更宣言のdocstring position / material-premise provenance
  を監査・補完する。

### Lean delta

`FiniteComparisonPresentation`の既存data field・definition signature・計算bodyを
変えず、次の13 theoremを`PresentationASubnerveDefect.lean`の定義直後に追加した。

- linear-map application API:
  - `coarseD0LinearMap_apply`
  - `coarseD1LinearMap_apply`
  - `fineD0LinearMap_apply`
  - `fineD1LinearMap_apply`
  - `edgePullback1LinearMap_apply`
  - `h1RankBlockLinearMap_apply_inl`
  - `h1RankBlockLinearMap_apply_inr`
- matrix-entry API:
  - `coarseD0Matrix_apply`
  - `coarseD1Matrix_apply`
  - `fineD0Matrix_apply`
  - `fineD1Matrix_apply`
  - `edgePullback1Matrix_apply`
  - `h1RankBlockMatrix_apply`

各APIは既存raw incidence / selected partial-map tableまたは
`LinearMap.toMatrix'`のstandard basis評価を返すだけで、新しい仮定、fixture固有値、
matrix、rank、defect、H¹ class、checker resultをfieldまたは引数に追加しない。

client移行:

- `ConditionC3NonnecessityWitness.rawCochainEquiv_comm0`はcoarse/fine `d0`
  application APIを使用。
- `rawCochainEquiv_comm1`はcoarse/fine `d1` application APIを使用。
- `edgePullback1_eq_rawEdgeCochainEquiv`はedge-pullback application APIを使用。
- `UniformPresentationInstancePairs`のpositive/negative block entry、coarse/fine
  zero `d0` matrix、full block-matrix formulaはlinear-map / matrix entry APIを使用。
- repository-wide scanでは対象12 definitionの`unfold` / downstream
  `simp [definition]` / `rw [definition]`はdefinition owner内部だけに残り、client
  subtreeには残らない。

### Cycle 15 declaration docstring audit

固定base `98cb58f76e65d7d8c54224b34a423a994f844064`からCycle 15 merge
`09eb070e195ea61a59580d877a69ac702805ed95`までの新規・body変更宣言を再列挙した。

- exact R1 witness: raw table datum、selected-cell / cochain API、actual comparison、
  target-zero C3 obstruction、literal quotient-H¹ nonvacuity、indicator bridge、main
  theoremの各positionと、raw table / preceding theorem由来のpremiseを全docstringに記録。
- presentation owner: Cycle 15で追加・公開化したpreimage / support / selection /
  partial-map APIとCycle 16評価APIに、owner APIとしてのpositionとraw-data provenance
  を記録。
- existing fixture clients: G-104 cycle theorem、checker selected cells、firing private
  helpers、uniformity rank fixtureのbody変更宣言に、元cycle/instance上のpositionと
  support・incidence・partial-map由来を記録。
- reverse C3 bridge: G-104 law-block clauseが唯一のmaterial premiseであり、finite
  sourceはboundary reindexのambient inputであることを宣言docstringへ記録。

### Verification

- focused elaboration: 対象7 Lean fileすべてpass、変更由来warningなし。
- targeted module build:
  - `PresentationASubnerveDefect`: pass (3715 jobs)
  - `UniformPresentationInstancePairs`: pass (3717 jobs)
  - `ConditionC3NonnecessityWitness`: pass (3740 jobs)
- namespace axiom audit:
  - `PresentationASubnerveDefect`: 128 declarations、standard axioms only
  - `ConditionCAllABridge`: 34 declarations、standard axioms only
  - checker pairs / firing / uniform pairs / G-104 instances / R1 witness:
    `31 / 25 / 10 / 129 / 82` declarations、standard axioms only
- 新規13 APIと主要client theorem 4件の`#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound`のみ。
- Research full build: ユーザー指定により未実行。

source SHA-256:

- `ResolutionInvarianceConditionInstances.lean`:
  `36187cf0dc402b060643415acd462f552a376f6d10bec3ef43e8a0bed02e4080`
- `PresentationASubnerveDefect.lean`:
  `611852da7b857b95512f89af438e347c1c65ff1498c85a8ed29d267b8da43968`
- `ConditionCAllAFiring.lean`:
  `20cdbcc175459d3f7ffd2442942e6b5399fffedd85643a4cec616338d137ed0b`
- `ConditionCAllACheckerInstancePairs.lean`:
  `56c33441bd17b6e2feb34ea25241e3336c243d8b44e76f97a32e92580269b0ce`
- `UniformPresentationInstancePairs.lean`:
  `e2b6b834cdba4e93915dcabb621a6183b2a8e5be248ccdedf7c265e3f1c5db92`
- `ConditionCAllABridge.lean`:
  `f618349ce92f41cea6afbfa19f8cfe59860b8d83d1376c7e870ee0a6f30cb953`
- `ConditionC3NonnecessityWitness.lean`:
  `9e8a303998506768ecd47849aa590f8824aa1e142361e8211909b9d51679cee0`

Independent T3はこのfixed snapshotを、API owner / client use、全Cycle 15
declaration docstring、premise、field-content、route integrity、static scanの観点で
独立監査し、blocking findingなしでAPI / docstring品質gateの実体を承認した。
PR査読では、これは固定GOALの`discharge-required` premiseを閉じるcycleではないため、
result typeを`proof-checkpoint`に較正した。13 APIはいずれも既存raw dataから導く
owner theoremであり、対象12 definitionの
direct expansionはowner内部にだけ残る。Cycle 15全新規・body変更宣言のdocstringも
proof bodyと照合し、position / material-premise provenanceが記録されたことを確認した。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 16
decision: approve
result_type: proof-checkpoint
proof_obligation: close the finite cochain and block-map no-unfold APIs and the Cycle 15 changed-declaration docstring audit
proof_obligation_delta: the Cycle 15 quality gate is discharged without changing the fixed target, mathematical definitions, presentation fields, or premise ledger
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: 98cb58f76e65d7d8c54224b34a423a994f844064
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean
    declarations:
      - FiniteComparisonPresentation.coarseD0LinearMap_apply
      - FiniteComparisonPresentation.coarseD1LinearMap_apply
      - FiniteComparisonPresentation.fineD0LinearMap_apply
      - FiniteComparisonPresentation.fineD1LinearMap_apply
      - FiniteComparisonPresentation.edgePullback1LinearMap_apply
      - FiniteComparisonPresentation.h1RankBlockLinearMap_apply_inl
      - FiniteComparisonPresentation.h1RankBlockLinearMap_apply_inr
      - FiniteComparisonPresentation.coarseD0Matrix_apply
      - FiniteComparisonPresentation.coarseD1Matrix_apply
      - FiniteComparisonPresentation.fineD0Matrix_apply
      - FiniteComparisonPresentation.fineD1Matrix_apply
      - FiniteComparisonPresentation.edgePullback1Matrix_apply
      - FiniteComparisonPresentation.h1RankBlockMatrix_apply
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionC3NonnecessityWitness.lean
    declarations:
      - R1ConditionC3Witness.rawCochainEquiv_comm0
      - R1ConditionC3Witness.rawCochainEquiv_comm1
      - R1ConditionC3Witness.edgePullback1_eq_rawEdgeCochainEquiv
  - file: research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean
    declarations:
      - UniformPresentationInstancePairs.positive_fullTarget_h1Rank
      - UniformPresentationInstancePairs.negative_fullTarget_h1Rank
premise_delta:
  discharged: []
  remaining:
    - C0 C1 C2 C4 C5 C6 non-necessity witnesses
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
quality_remediation:
  closed:
    - public definition-owner evaluation APIs for coarse and fine d0 and d1 maps and matrices
    - public definition-owner evaluation API for selected-edge pullback
    - public row APIs for the H1 block map and entry API for its matrix
    - governed client migration away from direct generic definition expansion
    - declaration-by-declaration Cycle 15 docstring position and premise-provenance audit
certificate_provenance:
  discharged:
    - all evaluation theorems are derived from raw incidence, selected partial-map tables, or standard-basis evaluation
    - no matrix, rank, defect, H1 class, result bit, or certificate field was added
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw endpoint and face-incidence tables
    - selected partial edge map
    - public owner APIs in all governed downstream clients
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
next_obligation: construct and verify the exact R1 C0_not_necessary witness with semantic uniformity, direct law-indexed and ConditionCAllA C0 failure, and a nonzero H1 block meeting the failed support datum
completion_candidate: false
tracking_issue_closed: false
```
## Cycle 17 — exact R1 C0 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- T1-selected obligation: exact R1 `C0_not_necessary` raw presentationを固定し、
  full semantic uniformity、direct raw / semantic C0 failure、direct
  `ConditionCAllA` failure、nonconstant indicator law上のfull `ConditionC`
  failure、failed support targetを含む同じ非空blockでのcoarse / fine両H¹非零を
  closed theorem packageへ接続する。

### Exact raw presentation and provenance

`ConditionC0NonnecessityWitness.lean`の`R1ConditionC0Witness.presentation`は、
次のraw tableだけをfieldに持つ。

- Source / FineTargetは`Fin 3`、CoarseTargetは`Fin 2`、coarse readingは
  `[0,0,1]`、fine readingはidentity。
- coarse / fine nerveはいずれもchart `Fin 2`、chart 0のself-loop edge
  `Fin 1`、empty face `Fin 0`。
- coarse chart supportは`[{0},{0,1}]`、fine chart supportは
  `[{0,1},{2}]`。
- chart mapはidentity、edge mapは`some`、face mapはempty。

canonical R1 parent payload SHA-256は
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`。
canonical generatorをread-onlyで再実行し、name-free semantic SHA-256
`9222cd14e8e9ff2685b346f9e27ec239ccb86c91a53870811b3a3b4f8da07348`
を独立再現した。factor、両nerve、support、cell mapをLean tableとfieldwise照合した。
実験artifactは転写provenanceでありLean theoremのpremiseではない。
`computedFactor_eq_coarseRead`と`comparisonFactor_eq_coarseRead`は、明示source
enumerationとcanonical uniquenessからproper factor `[0,0,1]`を生成する。

### Semantic uniformity and direct C0 failure

`A : Finset (Fin 2)`を任意に固定する。coarse / fine selected edgeは同じraw
self-loopに一致するため`selectedEdgeEquiv A`とactual
`semanticEdgeCochainEquiv A`を構成した。actual canonical comparisonの`f1`がこの
linear equivalenceに一致することをpublic partial-map APIから証明する。fine側の
`d0`はself-loop incidenceにより零、coarse側の`d1`はface typeがemptyなので零である。
したがってliteral quotient-H¹上で次を直接得る。

- injectivity: fine quotientで等しい二classの差はfine boundaryだが、そのboundaryは
  零。degree-one equivalenceのinjectivityでcoarse cycleが一致する。
- surjectivity: 任意fine cycleをdegree-one equivalenceの逆でcoarse cochainへ戻す。
  coarse `d1=0`によりcoarse cycleとなり、そのactual H¹ imageが元のclassに一致する。

この`aSubnerveComparisonHom_h1Map_bijective A`をgeneric raw-to-actual defect theoremへ
接続し、全`A`で`computedASubnerveDefect A = (0,0)`、checker true、full
`UniformPresentation presentation`を得た。checker実行値も空subsetを含む4 subsetで
`[(0,0),(0,0),(0,0),(0,0)]`、`uniformPresentationCheck=true`と独立確認した。

C0 failureはcoarse chart 1・coarse target 0に固定する。coarse supportには0が入るが、
chart fiberの唯一のfine chart 1はfine target 2だけをsupportし、そのcanonical imageは1
である。`failedSupportDatum`から`not_rawConditionC0`、`conditionC0Check=false`、
`not_conditionC0`を得る。`ConditionCAllA`のwhole-nerve C0 projectionで
`not_conditionCAllA`を直接証明し、aggregate checkerもfalseへ接続した。

target-zero indicator familyはsource 0と2を実際に区別するnonconstant law familyで、
coarse / fine adequacyはgeneric indicator theoremから得る。このfamily上で仮定したfull
law-indexed `ConditionC`の`c0` fieldを`not_conditionC0`へ適用し、
`indicator_not_conditionC`を閉じた。C0はlaw-independentだが、main theoremでは
proved-nonconstant familyと両adequacyを実際にinstantiateしている。

### Same-datum H¹ nonvacuity

failed target 0を含む`targetZero={0}`は両nerveのself-loopを選ぶ。coarse actual loopの
evaluation periodを構成し、全coboundaryのperiodが零、constant-one cocycleのperiodが1
であることからliteral quotient class `coarseTargetZeroClass`が非零と示した。fine classは
actual target-zero H¹ mapのimageとして構成し、上記all-subset theoremのinjectivityで
非零を保つ。これにより同じblockで両側finrankが正となる。

### Public no-unfold API delta

本witnessがgeneric actual-complex定義を下流で展開しないよう、既存定義の計算則だけを
各definition ownerの対応定義直後へ次のpublic theoremとして追加した。

- `TargetSupportedNerve.targetSubsetComplex_d0_apply`
- `TargetSupportedNerve.targetSubsetComplex_d1_apply`
- `ThreeCochainComplex.boundaryToCycles_apply`
- `ThreeCochainComplex.Hom.cyclesMap_apply`
- `ThreeCochainComplex.Hom.cyclesMap_sub_apply`

前2本は`ASubnerveReduction.lean`、後3本は係数体一般の
`TwoPhase/CohomologyComparison.lean`に置いた。いずれもendpoint / face incidence、
既存`d0`、既存`f1`のdefinition-owner evaluationを返す`rfl` theoremで、新premise・
field・matrix・rank・H¹・resultを追加しない。

### Lean artifacts and verification

- Lean files:
  - `research/lean/ResearchLean/AG/UniformInvariance/ConditionC0NonnecessityWitness.lean`
  - `research/lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean`
  - `research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean`
  - `research/lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean`
  - `research/lean/ResearchLean/AG.lean`
  - `research/lean/research-modules.txt`
- primary declarations:
  - `R1ConditionC0Witness.presentation`
  - `R1ConditionC0Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC0Witness.uniformPresentation`
  - `R1ConditionC0Witness.not_conditionC0`
  - `R1ConditionC0Witness.not_conditionCAllA`
  - `R1ConditionC0Witness.indicator_not_conditionC`
  - `R1ConditionC0Witness.targetZero_both_h1_pos`
  - `R1ConditionC0Witness.c0_not_necessary`
- focused elaboration:
  - `CohomologyComparison.lean`: pass、18 declarations standard axioms only
  - `ASubnerveReduction.lean`: pass、99 declarations standard axioms only
  - `PresentationASubnerveDefect.lean`: pass、TwoPhase 4 / ResolutionInvariance 128 declarations standard axioms only
  - `ConditionC0NonnecessityWitness.lean`: pass、57 declarations standard axioms only
- targeted module build:
  - `CohomologyComparison`: pass (3692 jobs)
  - `PresentationASubnerveDefect`: pass (3715 jobs)
  - `ConditionC0NonnecessityWitness`: pass (3739 jobs)
- direct execution:
  - `conditionC0Check=false`
  - `conditionCAllACheck=false`
  - `uniformPresentationCheck=true`
  - computed defects on `∅,{0},{1},{0,1}` are all `(0,0)`
- major 9 declarations / new API `#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / changed-public-artifact / research-package / separation gates: pass
- `git diff --check`: pass
- Research full build: ユーザー指定により未実行

source SHA-256:

- `ConditionC0NonnecessityWitness.lean`:
  `d9ab09fd400cd4a130defc5a8dd8eeebeecfe79d3c50338f7ac11f213ff3ec0e`
- `ASubnerveReduction.lean`:
  `af3f89ed9c5ff83d74885d0dc29dd0948cf9453cef0fc83346d587db5dd82218`
- `CohomologyComparison.lean`:
  `fd16285ce4434559138fa7c170d34de694679bd5d8d04dd82174a075e6bb4ae3`
- `PresentationASubnerveDefect.lean`:
  `611852da7b857b95512f89af438e347c1c65ff1498c85a8ed29d267b8da43968`
- `AG.lean`:
  `8233125c8fc75d2ce3f7273fa5e31799f81e36a35ff09e834d94c4decacd6fa6`
- `research-modules.txt`:
  `151e122679aae5c93005c1c480f46a60968cd58eb2beb4d8db14a53e49480e26`

Independent T3は上記fixed snapshotを、canonical R1 provenance、literal quotient-H¹、
C0 failure scope、law-indexed failure、same-datum nonvacuity、premise / field-content、
route integrity、public API境界の観点で独立監査した。canonical generatorから
name-free semantic SHA-256を再現し、Lean tableとのfieldwise一致も独立確認した。
blocking findingはなく、exact C0 non-necessity witnessという固定GOALの
`discharge-required`義務1件を放電した。残る5 witnessと観測非分解性義務があるため、
completion candidateではない。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 17
decision: approve
result_type: proof-obligation-discharged
proof_obligation: construct and verify the exact R1 C0_not_necessary witness with semantic uniformity, direct law-indexed and ConditionCAllA C0 failure, and a nonzero H1 block meeting the failed support datum
proof_obligation_delta: the exact R1 C0 non-necessity witness is discharged without changing the fixed target, presentation field boundary, or remaining witness and observation obligations
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: ba375202480ab9025dfe694529e9f4bf14325aaa
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/ConditionC0NonnecessityWitness.lean
    declarations:
      - R1ConditionC0Witness.presentation
      - R1ConditionC0Witness.aSubnerveComparisonHom_h1Map_bijective
      - R1ConditionC0Witness.uniformPresentation
      - R1ConditionC0Witness.not_rawConditionC0
      - R1ConditionC0Witness.not_conditionC0
      - R1ConditionC0Witness.not_conditionCAllA
      - R1ConditionC0Witness.indicator_not_conditionC
      - R1ConditionC0Witness.targetZero_both_h1_pos
      - R1ConditionC0Witness.c0_not_necessary
  - file: research/lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean
    declarations:
      - TargetSupportedNerve.targetSubsetComplex_d0_apply
      - TargetSupportedNerve.targetSubsetComplex_d1_apply
  - file: research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean
    declarations:
      - ThreeCochainComplex.boundaryToCycles_apply
      - ThreeCochainComplex.Hom.cyclesMap_apply
      - ThreeCochainComplex.Hom.cyclesMap_sub_apply
premise_delta:
  discharged:
    - exact R1 C0_not_necessary raw fixture and fieldwise canonical provenance
    - actual quotient-H1 comparison bijectivity for every target subset
    - direct raw C0, semantic C0, ConditionCAllA, and checker failure
    - law-indexed ConditionC failure for a proved-nonconstant indicator family
    - coarse and fine actual H1 nonvanishing on A={0}, which contains the failed target
  remaining:
    - C1 C2 C4 C5 C6 non-necessity witnesses
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
certificate_provenance:
  discharged:
    - presentation fields contain only raw readings, incidence, support, partial cell maps, and well-formedness proofs
    - canonical factor is generated from source enumeration and uniqueness
    - actual H1 bijectivity is proved on literal quotients rather than supplied by a checker result
    - the R1 experiment is transfer provenance only and is not a Lean premise
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw readings and source enumeration
    - self-loop endpoint incidence and empty face incidence
    - selected partial edge map
    - coarse and fine chart-support tables
    - target-zero indicator semantics and generated adequacy
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
next_obligation: construct and verify the exact R1 C1_not_necessary witness with the C1 failure and coarse and fine actual H1 nonvanishing connected on the same target subset
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 18 — exact R1 C1 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`ConditionC1NonnecessityWitness.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionC1NonnecessityWitness.lean)
  - [`ConditionCAllABridge.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean)
  - [`ConditionCAllAChecker.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllAChecker.lean)
  - [`PresentationASubnerveDefect.lean`](../lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean)
- canonical R1 parent SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- canonical name-free semantic SHA-256:
  `59e02ca26270c672ee5b96791f48742f3e7171f165d5c236f8c796626ed1310a`
- canonical payloadが直接固定するfactor・target counts・nerve・support・cell mapを
  Lean tableへfieldwise転写し、`Source`・source enumeration・coarse/fine readingsは
  そのfactorのcanonical realizationとして構成した。
- primary declarations:
  - `R1ConditionC1Witness.presentation`
  - `R1ConditionC1Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC1Witness.uniformPresentation`
  - `R1ConditionC1Witness.not_rawConditionC1At`
  - `R1ConditionC1Witness.not_conditionC1AtTargetSubset`
  - `R1ConditionC1Witness.not_conditionCAllA`
  - `R1ConditionC1Witness.indicator_not_conditionC1`
  - `R1ConditionC1Witness.indicator_not_conditionC`
  - `R1ConditionC1Witness.targetFull_both_h1_pos`
  - `R1ConditionC1Witness.c1_not_necessary`
- new owner APIs:
  - `TargetSupportedNerveMorphism.conditionC1AtTargetSubset_of_conditionC1At_labelValueFiber`
  - `FiniteComparisonPresentation.fineEdgeLeftIn_coe`
  - `FiniteComparisonPresentation.fineEdgeRightIn_coe`
  - `FiniteComparisonPresentation.chartMapIn_coe`
  - `FiniteComparisonPresentation.fiberGraph_adj_iff`

### Fixed same-A scope and proof route

canonical fixtureではC1が`A={1}`と`A={0,1}`で破れるが、前者は両側H¹が
`0→0`である。固定GOALの相対条項scopeは**同じ非空A**で条項破れと両側
H¹非零を要求するため、登録failure scopeに含まれ、H¹ profileが`1→1`
rank 1である`targetFull={0,1}`を選んだ。full-subset indicatorはconstant true
だが、固定GOALはC1 witnessにnonconstant lawを要求しない。proper factor、
source-generated nonempty label、distinct fine charts 1,2の実在、raw fiber graphの
非連結、および同じblockの両側非零H¹がnonvacuityを担う。

raw tableはSource / FineTarget `Fin 3`、CoarseTarget `Fin 2`、coarse reading
`[0,0,1]`、fine reading `id`、coarse charts `Fin 2`、fine charts `Fin 3`、
両側のsole chart-zero self-loop、empty faces、coarse supports `[{0},{1}]`、
fine supports `[{0,1},{2},{2}]`、chart map `[0,1,1]`、edge map `[some 0]`
だけから成る。factor、path、rank、H¹、defect、condition / checker bit、uniformity
certificateはfieldにない。canonical factorはsource enumerationから生成する。

全finite `A`についてselected degree-one cochain equivalence、fine `d0=0`、
coarse `d1=0`からliteral quotient H¹ mapのinjectivity / surjectivityを別々に
証明し、全defect零とfull semantic `UniformPresentation`へ接続した。
full subsetではfine charts 1,2がcoarse chart 1へ写る一方、sole fine edgeは
chart 0 self-loopなのでfiber adjacencyは空である。これをraw finite graph上で
証明し、raw / actual C1、`ConditionCAllA`、checkerを直接反証した。

law-indexed failureには、law-block C1からlabel-fiber A-subnerve C1へのgeneric
reverse transportを追加した。既存chart equivalenceとadjacency iffを逆向きに使い、
`ReflTransGen` path全体を輸送する。generated true label fiber `= targetFull`と
組み合わせ、law-indexed `ConditionC1`およびfull `ConditionC`を反証した。
same-A H¹非零はactual coarse self-loop quotient classのperiod argumentと、actual
H¹ mapのinjectivityによるfine imageの非零性から得た。

### Verification

- focused elaboration:
  - `PresentationASubnerveDefect.lean`: pass、TwoPhase 4 / ResolutionInvariance 131 declarations standard-only
  - `ConditionCAllAChecker.lean`: pass、87 declarations standard-only
  - `ConditionCAllABridge.lean`: pass、35 declarations standard-only
  - `ConditionC1NonnecessityWitness.lean`: pass、64 declarations standard-only
- targeted builds: 3715 / 3737 / 3708 / 3740 jobs、すべてpass
- direct execution: C1 check `false`、aggregate check `false`、uniform check
  `true`、`∅,{0},{1},{0,1}`のcomputed defectは全て`(0,0)`
- reverse bridge、4 owner APIs、主要witness declarationsの`#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / research-package / separation gates: pass
- placeholder / hidden-BiDi / privacy / `git diff --check`: clean
- independent T3: `approve / proof-obligation-discharged`、blocking findingなし
- Research full build: ユーザー指定により未実行

source SHA-256:

- `ConditionC1NonnecessityWitness.lean`:
  `9450c73ad19a7c6fb3117c37207842b6234f5f8e944a88139f8da2cc5467d9f5`
- `ConditionCAllABridge.lean`:
  `bb23fd0ae23195f140c4470dff2b9b246e24bbe8f9f102a17b40a177ac2d02e2`
- `ConditionCAllAChecker.lean`:
  `5ab5ae97a5471eb6179a60bf85f9490c9eb888fb2c94c0c73a352ba953eb8aed`
- `PresentationASubnerveDefect.lean`:
  `7392c3d1afc1e91186a1a98af20d98a2fd51c1c5a9c23dcf31e08202005c72c6`
- `AG.lean`:
  `54740dc4fc5928ef8f801bca21dd48c569a0417331d6096f1d0a43218adef5f5`
- `research-modules.txt`:
  `c9f5a0bd99d5c9a30129095bcb533d23a4beeebb8fbe260fa21ed5b98ab334f1`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 18
decision: approve
result_type: proof-obligation-discharged
proof_obligation: exact R1 C1_not_necessary witness with law-indexed and direct A-subnerve C1 failure and coarse and fine actual H1 nonvanishing on the same A={0,1}
proof_obligation_delta: exact C1 witness is discharged without changing the fixed target or presentation field boundary
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4
  status: recorded
premise_delta:
  discharged:
    - exact R1 raw fixture and canonical provenance
    - all-target-subset actual quotient-H1 bijectivity
    - direct raw and semantic C1 failure on A={0,1}
    - direct ConditionCAllA and checker failure
    - law-indexed ConditionC1 and full ConditionC failure on the generated label
    - coarse and fine actual H1 nonvanishing on the same A={0,1}
  remaining:
    - C2 C4 C5 C6 non-necessity witnesses
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
certificate_provenance:
  status: raw-table-generated
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw readings and source enumeration
    - self-loop incidence, chart supports, chart map, and partial edge map
    - generated indicator label and exact fiber equality
    - reverse path transport through canonical chart equivalences
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
next_obligation: exact R1 C2_not_necessary witness with same-A clause failure and coarse/fine actual H1 nonvanishing
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 19 — exact R1 C2 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`ConditionC2NonnecessityWitness.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionC2NonnecessityWitness.lean)
  - [`ConditionCAllABridge.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean)
  - [`PresentationASubnerveDefect.lean`](../lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean)
- canonical R1 parent SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- canonical name-free semantic SHA-256:
  `b0ff8026708b3a5466568682efc72b2758469ca3f526e75756eabcee24355cc9`
- fixed `results-summary.json` SHA-256:
  `556c7279626a4395bc2446bc2f2a1f9af725c24e3ce6aacddfe59cc8ab11ee3e`
- primary declarations:
  - `R1ConditionC2Witness.presentation`
  - `R1ConditionC2Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC2Witness.uniformPresentation`
  - `R1ConditionC2Witness.not_rawConditionC2At`
  - `R1ConditionC2Witness.not_conditionC2AtTargetSubset`
  - `R1ConditionC2Witness.not_conditionCAllA`
  - `R1ConditionC2Witness.indicator_not_conditionC2`
  - `R1ConditionC2Witness.indicator_not_conditionC`
  - `R1ConditionC2Witness.targetFull_both_h1_pos`
  - `R1ConditionC2Witness.c2_not_necessary`
- new owner APIs:
  - `TargetSupportedNerveMorphism.conditionC2AtTargetSubset_of_conditionC2At_labelValueFiber`
  - `FiniteComparisonPresentation.coarseEdgeLeftIn_coe`
  - `FiniteComparisonPresentation.coarseEdgeRightIn_coe`

### Fixed same-A scope and proof route

canonical fixtureではC2が`A={1}`と`A={0,1}`で破れるが、前者の両側H¹は
`0→0`である。固定GOALの相対条項scopeは**同じ非空A**で条項破れと両側
H¹非零を要求するため、登録failure scopeに含まれ、H¹ profileが`1→1`
rank 1である`targetFull={0,1}`を採用した。full-subset indicatorはconstant true
だが、固定GOALはC2 witnessにnonconstant lawを要求しない。proper factor、
実在するunmapped coarse interval、同じfull blockの両側非零H¹がnonvacuityを担う。

raw tableはSource / FineTarget `Fin 3`、CoarseTarget `Fin 2`、coarse reading
`[0,0,1]`、fine reading `id`、coarse chart supports `[{0},{1},{1}]`、coarse edges
`(0,0)`と`(1,2)`、fine chart supports `[{0,1},{2},{2}]`、fine sole edge
`(0,0)`、chart map `id`、edge map `0 ↦ some 0`、両側empty facesだけから成る。
factor、lift、matrix、rank、H¹、defect、condition / checker bit、uniformity certificateは
presentation fieldにない。canonical factorはsource enumerationから生成する。

任意のfinite `A`について、raw edge pullbackのright inverseをexplicitに構成した。
pullback kernelではcoarse self-loop係数が零になり、残るinterval `(1,2)` の係数を
chart 2に置くraw primitiveのcoarse `d0`が元cochainに一致する。raw / actual
cochain equivalenceとnaturalityを使い、このkernel=image `d0`とright inverseを
literal quotient H¹へ持ち上げ、injectivity / surjectivityを別々に証明した。これを
全defect零、generic all-subset checker、full semantic `UniformPresentation`へ接続した。

full subsetではcoarse interval edge 1がselectedされる一方、sole fine edgeはcoarse
self-loop 0へしか写らない。これをraw tableから直接示し、raw / semantic C2、
`ConditionCAllA`、aggregate checkerを反証した。law-indexed failureには、law-block
C2のfine liftをcanonical edge equivalenceでactual label-fiber A-subnerveへ戻すgeneric
reverse transportを追加した。generated true label fiber `= targetFull`と組み合わせ、
law-indexed C2およびfull `ConditionC`を反証した。same-A H¹非零はactual coarse
self-loop quotient classのperiod argumentと、actual H¹ map injectivityによるfine像の
非零性から得た。

### Verification

- focused elaboration:
  - `PresentationASubnerveDefect.lean`: pass、TwoPhase 4 / ResolutionInvariance 133 declarations standard-only
  - `ConditionCAllABridge.lean`: pass、36 declarations standard-only
  - `ConditionC2NonnecessityWitness.lean`: pass、61 declarations standard-only
- targeted builds: 3715 / 3708 / 3740 jobs、すべてpass
- direct execution: C2 check `false`、aggregate check `false`、uniform check
  `true`、`∅,{0},{1},{0,1}`のcomputed defectは全て`(0,0)`
- reverse bridge、2 owner APIs、主要witness declarationsの`#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / research-package / separation gates: pass
- placeholder / hidden-BiDi / privacy / `git diff --check`: clean
- independent T3: `approve / proof-obligation-discharged`、blocking findingなし
- Research full build: ユーザー指定により未実行

source SHA-256:

- `ConditionC2NonnecessityWitness.lean`:
  `51fe9887a702b4afecb5a39246609b02b545583c4bde1d7d45df5bb7c2728a40`
- `ConditionCAllABridge.lean`:
  `b4d05fcc2d4a69d0c236237365e1107bd0bec88c6f0002b17d5cc6637ac6f65f`
- `PresentationASubnerveDefect.lean`:
  `e53a8d959cd51493fbe988d743c1b2bbd01214a2b87b0b273636d637ff27fa00`
- `AG.lean`:
  `4e41d26ece24a30b9ab8b722e896776402e74ec7af914d7c61cb587fa31326ab`
- `research-modules.txt`:
  `fb12b3f56d31a882dba0f6a91fbd5c388eac9c8f709f8a723c03ae432864605f`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 19
decision: approve
result_type: proof-obligation-discharged
proof_obligation: exact R1 C2_not_necessary witness with law-indexed and direct A-subnerve C2 failure and coarse and fine actual H1 nonvanishing on the same A={0,1}
proof_obligation_delta: exact C2 witness is discharged without changing the fixed target or presentation field boundary
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4
  status: recorded
premise_delta:
  discharged:
    - exact canonical R1 raw fixture and fieldwise provenance
    - all-target-subset actual quotient-H1 bijectivity
    - direct raw and semantic C2 failure on A={0,1}
    - direct ConditionCAllA and checker failure
    - law-indexed ConditionC2 and full ConditionC failure on the generated label
    - coarse and fine actual H1 nonvanishing on the same A={0,1}
  remaining:
    - C4 C5 C6 non-necessity witnesses
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
certificate_provenance:
  status: raw-table-generated
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw readings and source enumeration
    - loop and interval incidence, chart supports, chart map, and partial edge map
    - empty coarse and fine face tables
    - generated indicator label and exact fiber equality
    - reverse C2 transport through canonical edge equivalences
    - actual H1 map injectivity on the same full subset
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
next_obligation: exact R1 C4_not_necessary witness with same-A clause failure and coarse/fine actual H1 nonvanishing
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 20 — exact R1 C4 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean files:
  - [`ConditionC4NonnecessityWitness.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionC4NonnecessityWitness.lean)
  - [`ConditionCAllABridge.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean)
  - [`LawValueBlockComparison.lean`](../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparison.lean)
- canonical R1 parent SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- canonical name-free semantic SHA-256:
  `5e6e1cb8fdaf2e0015007e80f029528455c587d56a40a47299d075323e366a74`
- fixed `results-summary.json` SHA-256:
  `556c7279626a4395bc2446bc2f2a1f9af725c24e3ce6aacddfe59cc8ab11ee3e`
- primary declarations:
  - `R1ConditionC4Witness.presentation`
  - `R1ConditionC4Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC4Witness.uniformPresentation`
  - `R1ConditionC4Witness.not_rawConditionC4At`
  - `R1ConditionC4Witness.not_conditionC4AtTargetSubset`
  - `R1ConditionC4Witness.not_conditionCAllA`
  - `R1ConditionC4Witness.indicator_not_conditionC4`
  - `R1ConditionC4Witness.indicator_not_conditionC`
  - `R1ConditionC4Witness.targetFull_both_h1_pos`
  - `R1ConditionC4Witness.c4_not_necessary`
- new owner APIs:
  - `TargetSupportedNerveMorphism.faceMap_eq_some_of_faceBlockCoordinateMapOption_eq_some`
  - `TargetSupportedNerveMorphism.conditionC4AtTargetSubset_of_conditionC4At_labelValueFiber`

### Fixed same-A scope and proof route

canonical fixtureではC4が`A={1}`と`A={0,1}`で破れるが、前者の両側H¹は
`0→0`である。固定GOALが要求するsame-A clause failureと両側H¹非零を満たす
ため、登録failure scopeに含まれ、H¹ profileが`1→1` rank 1である
`targetFull={0,1}`を採用した。full-subset indicatorはconstant trueだが、固定GOALは
C4 witnessにnonconstant lawを要求しない。proper factor、実在するmissing coarse
face lift、同じfull blockの両側非零H¹がnonvacuityを担う。

canonical R1 payloadが直接固定するfactor・target counts・両nerve・support・cell mapを
Lean tableへfieldwise転写し、Source / FineTarget `Fin 3`、CoarseTarget `Fin 2`、
coarse reading `[0,0,1]`、fine reading `id`はそのfactorのcanonical realizationとして
構成した。両nerveのcharts / self-loop edgesは`Fin 2`、coarse facesは`Fin 2`、
fine faceは`Fin 1`である。全face boundaryはedge 1の
`(1,1,1)`であり、sole fine faceはcoarse face 0へ写る。coarse chart supportsは
`[{0},{1}]`、fine chart supportsは`[{0,1},{2}]`、chart / edge mapはidentityである。
factor、face lift、matrix、rank、H¹、defect、condition / checker bit、uniformity
certificateはpresentation fieldにない。canonical factorはsource enumerationから生成する。

任意のfinite `A`について、coarse / fine selected edge tableをraw supportから同定し、
degree-one cochain equivalenceを構成した。fine `d0`はself-loop incidenceにより零である。
fine cocycleをedge equivalenceでcoarseへ戻す際は、unique fine repeated faceの
`d1=0`がedge-1係数の零性を与え、同じboundaryを持つ2枚のcoarse face双方の
`d1=0`へ輸送される。これによりliteral quotient H¹上のinjectivity / surjectivityを
別々に証明し、全defect零、generic all-subset checker、full semantic
`UniformPresentation`へ接続した。

full subsetではcoarse face 1がselectedされる一方、sole fine faceはcoarse face 0へ
しか写らない。これをraw partial face tableから直接示し、raw / semantic C4、
`ConditionCAllA`、aggregate checkerを反証した。law-indexed failureには、law-block
C4のfine face liftをcanonical face equivalenceでactual label-fiber A-subnerveへ戻す
reverse transportを追加した。そのproofが必要とするblock equalityのelimination APIは、
T3の初回指摘を受けて`faceBlockCoordinateMapOption`のdefinition ownerである
`LawValueBlockComparison.lean`へ配置し、owner外のdefinition展開を除去した。
generated true label fiber `= targetFull`と組み合わせ、law-indexed C4およびfull
`ConditionC`を反証した。same-A H¹非零はactual coarse chart-zero self-loop quotient
classのperiod argumentと、actual H¹ map injectivityによるfine像の非零性から得た。

### Verification

- focused elaboration: `ConditionC4NonnecessityWitness.lean` pass、62 declarations
  standard-only
- targeted builds:
  - `LawValueBlockComparison.lean`: pass、31 declarations standard-only
  - `ResolutionInvarianceConditions.lean`: pass、base同一、46 declarations standard-only
  - `ConditionCAllABridge.lean`: pass、37 declarations standard-only
  - `ConditionC4NonnecessityWitness.lean`: pass、aggregate 3740 jobs
- direct execution: C4 check `false`、aggregate check `false`、uniform check
  `true`、`∅,{0},{1},{0,1}`のcomputed defectは全て`(0,0)`
- owner extraction API、reverse bridge、主要witness declarationsの`#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / research-package / separation gates: pass
- placeholder / hidden-BiDi / privacy / `git diff --check`: clean
- independent T3: `approve / proof-obligation-discharged`、初回owner-placement findingは
  修正後snapshotで解消、blocking findingなし
- Research full build: ユーザー指定により未実行

source SHA-256:

- `ConditionC4NonnecessityWitness.lean`:
  `918eaccf9b0830aaf37f25d5c8298ed9a116f310328b89db539b3f986f5fff5a`
- `ConditionCAllABridge.lean`:
  `b9ad08a7b496d21f85d2278f41dc8e997e418a4ca77a0b8e61e775266ad86c4c`
- `LawValueBlockComparison.lean`:
  `0e48d2f141906b45bd09060abc01aa5dda6aa4a2e7ae739ffbc4e8a6f8b57815`
- `AG.lean`:
  `35aa919c372279e320f556da43c54bf39a9ba0e89ca8310415ed0c9af0afe262`
- `research-modules.txt`:
  `c73729e0973fabd8ed9d0426604124d9bef0b9f0b43c9d1a7e39299d1e3560f2`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 20
decision: approve
result_type: proof-obligation-discharged
proof_obligation: exact R1 C4_not_necessary witness with law-indexed and direct A-subnerve C4 failure and coarse and fine actual H1 nonvanishing on the same A={0,1}
proof_obligation_delta: exact C4 witness is discharged without changing the fixed target or presentation field boundary
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4
  status: recorded
premise_delta:
  discharged:
    - exact canonical R1 factor, targets, nerves, supports, and maps with a canonical source-reading realization
    - all-target-subset actual quotient-H1 bijectivity
    - direct raw and semantic C4 failure on A={0,1}
    - direct ConditionCAllA and checker failure
    - law-indexed ConditionC4 and full ConditionC failure on the generated label
    - coarse and fine actual H1 nonvanishing on the same A={0,1}
  remaining:
    - C5 C6 non-necessity witnesses
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
certificate_provenance:
  status: raw-table-generated
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw readings and source enumeration
    - self-loop and repeated-face incidence, chart supports, and partial face map
    - generated indicator label and exact fiber equality
    - reverse C4 transport through canonical face equivalences
    - actual H1 map injectivity on the same full subset
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
next_obligation: exact R1 C5_not_necessary witness with same-A clause failure and coarse/fine actual H1 nonvanishing
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 21 — exact R1 C5 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`ConditionC5NonnecessityWitness.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionC5NonnecessityWitness.lean)
- canonical R1 parent SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- canonical name-free semantic SHA-256:
  `a1907afb86e6a570e244676e48358f9d21a87077ee868b09308177aef04b7ca4`
- fixed `results-summary.json` SHA-256:
  `556c7279626a4395bc2446bc2f2a1f9af725c24e3ce6aacddfe59cc8ab11ee3e`
- primary declarations:
  - `R1ConditionC5Witness.presentation`
  - `R1ConditionC5Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC5Witness.uniformPresentation`
  - `R1ConditionC5Witness.not_rawConditionC5`
  - `R1ConditionC5Witness.not_conditionC5`
  - `R1ConditionC5Witness.not_conditionCAllA`
  - `R1ConditionC5Witness.indicator_not_conditionC`
  - `R1ConditionC5Witness.failedLiftPair_support_meets_targetFull`
  - `R1ConditionC5Witness.targetFull_both_h1_pos`
  - `R1ConditionC5Witness.c5_not_necessary`

### Fixed same-A scope and proof route

canonical R1 payloadが直接固定するfactor・target counts・両nerve・support・cell mapを
Lean tableへfieldwise転写し、Source / FineTarget `Fin 3`、CoarseTarget `Fin 2`、
coarse reading `[0,0,1]`、fine reading `id`はfactorのcanonical realizationとして
構成した。coarse nerveは2本のself-loopとchart-one loop上の1枚のrepeated face、
fine nerveは同じchart-zero loop、2本のdistinctなchart-one loop、それぞれに1枚の
repeated faceを持つ。fine chart-one loops 1, 2はともにcoarse loop 1へ写る。
factor、duplicate-lift certificate、matrix、rank、H¹、defect、condition / checker bit、
uniformity certificateはpresentation fieldにない。

任意のfinite target subset `A`について、selected coarse edgeからcanonical fine liftを
raw partial edge tableで構成し、fine edgeからcoarse imageへの射影がその左逆であることを
証明した。fine cocycleでは2枚のrepeated face equationがduplicate edge 1, 2の係数を
個別に零にし、coarse projectionがcoarse repeated-face equationを満たす。これにより
actual degree-one pullbackのinjectivityとfine cycle上のsurjectivityを得て、literal
quotient H¹上のinjectivity / surjectivityを別々に証明した。全subsetのdefect零、generic
all-subset checker、full semantic `UniformPresentation`はこのactual-map theoremから導いた。

whole nerveではdistinctなfine edges 1, 2が同じcoarse edge 1へ写るため、raw C5を直接
反証し、generic raw / semantic iffでsemantic C5へ接続した。`ConditionCAllA`はその
`conditionC5` projection、law-indexed `ConditionC`はgenerated full-indicator family上の
`c5` fieldを使って直接反証した。full subset `targetFull={0,1}`はduplicate pairの共通
fine support target 2をcanonical factorで受け取る。同じfull subset上でcoarse
chart-zero self-loopのliteral quotient classがperiod argumentにより非零であり、actual
H¹ mapのinjectivityからfine像も非零となる。C5 failureはtarget-one component、明示
H¹ classはtarget-zero componentにあるので、固定GOALが要求するsame-A intersectionと
両側非零H¹を主張し、それより強いsame-component因果性は主張しない。

### Verification

- focused elaboration: `ConditionC5NonnecessityWitness.lean` pass、71 declarations
  standard-only
- targeted module build:
  `ResearchLean.AG.UniformInvariance.ConditionC5NonnecessityWitness` pass、3739 jobs
- direct execution: C5 check `false`、aggregate check `false`、uniform check `true`、
  `∅,{0},{1},{0,1}`のcomputed defectは全て`(0,0)`
- primary 10 declarationsの`#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / research-package / separation gates: pass
- placeholder / hidden-BiDi / privacy / `git diff --check`: clean
- independent T3: `approve / proof-obligation-discharged`、blocking findingなし。
  T3後に未使用fixture helperを削除し、両側H¹結合 theoremをmain proofで実使用する
  狭い品質修正を行い、focused / targeted / direct execution / axiom auditを再実行した
- 初回formal reviewで冗長な`ConditionCAllABridge` direct importと、edge indexを
  coefficientの非零性とも読めるdocstringを指摘された。direct importを削除し、
  docstringをnonzero edge indexへ限定して、同じ検証packetを修正後snapshotで再実行した
- 修正後fixed snapshotのindependent T3も
  `approve / proof-obligation-discharged`、blocking findingなし
- Research full build: ユーザー指定により未実行

source SHA-256:

- `ConditionC5NonnecessityWitness.lean`:
  `b2a853bf6349c07d50f36e5fd8b849c04e408e2c684bf25fbb57671d16583de5`
- `AG.lean`:
  `0779f19205eb8a8ad7bba54fc10e170d0dee9b2b045dd79d8dc0f4bbec9ffeb7`
- `research-modules.txt`:
  `39c5d570d5bdb37dc0b07588b3815ff5ceee4c150e3d1078b461a3f2d577c83b`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 21
decision: approve
result_type: proof-obligation-discharged
proof_obligation: exact R1 C5_not_necessary witness with direct C5 and ConditionCAllA failure, common-support same-A intersection, and coarse and fine actual H1 nonvanishing
proof_obligation_delta: exact C5 witness is discharged without changing the fixed target or presentation field boundary
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4
  status: recorded
premise_delta:
  discharged:
    - exact canonical R1 factor, targets, nerves, supports, and maps with a canonical source-reading realization
    - all-target-subset actual quotient-H1 bijectivity
    - direct raw and semantic whole-nerve C5 failure
    - direct ConditionCAllA and checker failure through the C5 projection
    - law-indexed full ConditionC failure through its C5 field
    - duplicate-pair common support meeting A={0,1}
    - coarse and fine actual H1 nonvanishing on the same A={0,1}
  remaining:
    - C6 non-necessity witness
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
certificate_provenance:
  status: raw-table-generated
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw readings and source enumeration
    - self-loop incidence, chart supports, and duplicate partial edge map
    - one coarse and two fine repeated-face equations
    - generated indicator law and the ConditionC c5 field
    - actual H1 map injectivity on the same full subset
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
next_obligation: exact R1 C6_not_necessary witness with direct whole-nerve C6 and ConditionCAllA failure, common-support same-A intersection, and coarse/fine actual H1 nonvanishing
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 22 — exact R1 C6 non-necessity witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`ConditionC6NonnecessityWitness.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionC6NonnecessityWitness.lean)
- canonical R1 parent SHA-256:
  `ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`
- canonical name-free semantic SHA-256:
  `01839cd41c6418c92315cf1ea4693647c3109f077c32961cf929fefa1f98e91f`
- fixed `results-summary.json` SHA-256:
  `556c7279626a4395bc2446bc2f2a1f9af725c24e3ce6aacddfe59cc8ab11ee3e`
- primary declarations:
  - `R1ConditionC6Witness.presentation`
  - `R1ConditionC6Witness.aSubnerveComparisonHom_h1Map_bijective`
  - `R1ConditionC6Witness.uniformPresentation`
  - `R1ConditionC6Witness.not_rawConditionC6`
  - `R1ConditionC6Witness.not_conditionC6`
  - `R1ConditionC6Witness.not_conditionCAllA`
  - `R1ConditionC6Witness.indicator_not_conditionC`
  - `R1ConditionC6Witness.failedFineEdge_support_meets_targetFull`
  - `R1ConditionC6Witness.targetFull_both_h1_pos`
  - `R1ConditionC6Witness.c6_not_necessary`

### Fixed same-A scope and proof route

canonical R1 payloadが直接固定するfactor・target counts・両nerve・support・cell mapを
Lean tableへfieldwise転写し、Source / FineTarget `Fin 3`、CoarseTarget `Fin 2`、
coarse reading `[0,0,1]`、fine reading `id`はfactorのcanonical realizationとして
構成した。coarse nerveはchart-zeroとchart-oneのself-loop、およびchart-one loop上の
1枚のrepeated faceを持つ。fine nerveはchart-zero self-loopとchart 1から2への
interval edgeを持ち、faceはない。fine loop / intervalはそれぞれcoarse loop 0 / 1へ
写る。factor、endpoint-reflection certificate、matrix、rank、H¹、defect、condition /
checker bit、uniformity certificateはpresentation fieldにない。

任意のfinite target subset `A`についてselected coarse / fine edge tableをraw supportから
同定し、actual degree-one comparisonをedge cochain equivalenceとして固定した。literal
quotient H¹のinjectivityでは、fine boundary差のchart-zero loop係数が零であることと、
coarse repeated-face cocycle equationがchart-one loop係数を零にすることを組み合わせて
coarse cycle差を消した。surjectivityではfine cycleのloop係数をcoarse側へ射影し、残る
fine interval係数をchart 2に置くexplicit raw primitiveの`d0`として吸収した。これにより
actual quotient H¹ mapのinjectivity / surjectivityを別々に証明し、全subsetのdefect零、
generic all-subset checker、full semantic `UniformPresentation`へ接続した。

whole nerveではfine interval edge `(1,2)`がcoarse chart-one self-loopへ写るため、raw C6を
直接反証し、generic raw / semantic iffでsemantic C6へ接続した。`ConditionCAllA`はその
`conditionC6` projection、law-indexed `ConditionC`はgenerated full-indicator family上の
`c6` fieldを使って直接反証した。full subset `targetFull={0,1}`はfailed interval edgeの
fine support target 2をcanonical factorで受け取る。同じfull subset上でcoarse
chart-zero self-loopのliteral quotient classがperiod argumentにより非零であり、actual
H¹ mapのinjectivityからfine像も非零となる。C6 failureはtarget-one component、明示
H¹ classはtarget-zero componentにあるので、固定GOALが要求するsame-A intersectionと
両側非零H¹を主張し、それより強いsame-component因果性は主張しない。

### Verification

- focused elaboration: `ConditionC6NonnecessityWitness.lean` pass、66 declarations
  standard-only
- targeted module build:
  `ResearchLean.AG.UniformInvariance.ConditionC6NonnecessityWitness` pass、3739 jobs
- direct execution: C6 check `false`、aggregate check `false`、uniform check `true`、
  `∅,{0},{1},{0,1}`のcomputed defectは全て`(0,0)`
- primary 10 declarationsの`#print axioms`:
  `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / research-package / separation gates: pass
- placeholder / hidden-BiDi / privacy / `git diff --check`: clean
- independent T3: `approve / proof-obligation-discharged`、blocking findingなし
- Research full build: ユーザー指定により未実行

source SHA-256:

- `ConditionC6NonnecessityWitness.lean`:
  `ad70ec6b8bc345d4d7b8ae305b2a03f8f943e9e72ab34668ca21c873a89ae5df`
- `AG.lean`:
  `c39d2eeacd05247fff90f547e5d1ef2aaa3d63534c5af10031d423ccfb6d28c5`
- `research-modules.txt`:
  `33a376d4aa1be78f70cabbb4786bb0d9e2cfbb584e3edf0474e766015c13346b`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 22
decision: approve
result_type: proof-obligation-discharged
proof_obligation: exact R1 C6_not_necessary witness with direct whole-nerve C6 and ConditionCAllA failure, failed-edge-support same-A intersection, and coarse and fine actual H1 nonvanishing
proof_obligation_delta: exact C6 witness is discharged without changing the fixed target or presentation field boundary
primary_specification:
  source: research/goals/G-107-aat-uniform-invariance-characterization.md
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4
  status: recorded
premise_delta:
  discharged:
    - exact canonical R1 factor, targets, nerves, supports, and maps with a canonical source-reading realization
    - all-target-subset actual quotient-H1 bijectivity
    - direct raw and semantic whole-nerve C6 failure
    - direct ConditionCAllA and checker failure through the C6 projection
    - law-indexed full ConditionC failure through its C6 field
    - failed-edge support meeting A={0,1}
    - coarse and fine actual H1 nonvanishing on the same A={0,1}
  remaining:
    - Obs_G fidelity, T3/T6 labels, observational equality, and nonfactorization
certificate_provenance:
  status: raw-table-generated
  unresolved: []
proof_use_audit:
  used_material_premises:
    - raw readings and source enumeration
    - self-loop and interval incidence, chart supports, and partial edge map
    - coarse repeated-face equation
    - explicit fine interval boundary primitive
    - generated indicator law and the ConditionC c6 field
    - actual H1 map injectivity on the same full subset
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
next_obligation: define the faithful G_local-v1 observation map Obs_G and fix its permanent-contract component correspondence before transferring T3 and T6
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 23 — permanent `G_local-v1` reducer and definition-level `Obs_G`

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- primary specification:
  - fixed GOAL claim (v) and permanent-observation requirements
  - `research/experiments/g104-necessity-map/g_local_v1.py`: permanent
    16-component observation contract, observation constructor, and serializer
  - `research/experiments/g104-necessity-map/r2_hunt.py`: permanent v5
    structural reducer and condition helpers
  - `research/experiments/g104-necessity-map/necessity_map.py`: base restriction
    structures consumed by the reducer
  - `research/experiments/g104-necessity-map/g_local_v1_stop_b.py`: permanent
    contract manifest and canonical source-bundle owner
- permanent contract source-bundle SHA-256:
  `5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8`
- primary Lean files:
  - [`GLocalV1ObservationValue.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1ObservationValue.lean)
  - [`GLocalV1V5Reduction.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean)
  - [`GLocalV1Observation.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1Observation.lean)
  - [`GLocalV1KernelInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1KernelInstancePairs.lean)
- presentation / fixture compatibility files:
  - [`FiniteComparisonPresentation.lean`](../lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean)
  - [`UniformPresentationInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/UniformPresentationInstancePairs.lean)
  - [`ConditionCAllACheckerInstancePairs.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllACheckerInstancePairs.lean)
  - [`ConditionCAllAFiring.lean`](../lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean)
  - `ConditionC0NonnecessityWitness.lean` through
    `ConditionC6NonnecessityWitness.lean`
- aggregate / manifest:
  - [`ResearchLean/AG.lean`](../lean/ResearchLean/AG.lean)
  - [`research-modules.txt`](../lean/research-modules.txt)

### Definition-level fidelity packet

`GLocalV1ObsValue` はpermanent contractが許す次のdataだけを持つ。

- aggregate C0--C6 condition vector
- whole-scope condition recordとside-local radius-one rooted-ball histogram
- 全非空coarse-target subsetのscope record histogram
- multiplicity `0 / 1 / ≥2`のclipped normal form

raw cell ID、raw subset ID、fixture name、semantic hash、exact multiplicity above two、
parity、global cycle length、full graph lookup、H¹、comparison rank、uniformity、
checker / result bit、supplied observation / terminal / labelはfieldに含まない。
`gLocalV1PermanentContractSha256` はprovenanceを固定する独立定数であり、
`obsG`のargument、field、proof premiseには使用しない。

full v5 reducerはraw scoped cells / supports / incidence / partial mapsから次を
実行可能に生成する。

1. inherited v4 coarse packet
2. inherited v4 fine-only packet
3. coordinate-dependency packet
4. closed-doubled-cycle packet

packetはremoved-cell setsだけを持ち、validity / terminal / condition / result
certificateを持たない。`gLocalV1PacketVariants` のcomputed guardが厳密な
retained-cell measure decreaseを課し、`gLocalV1ReachableFrom` はこのdecreaseで
構造再帰する。`gLocalV1MemoizedReachableStates` / `TerminalStates`は
structural reachability / reachable irreducible statesとiffであり、
`gLocalV1PacketKindUnion` はselected traceではなく全reachable stateの全outgoing
packetのkind unionである。

### Permanent 16-component correspondence

| component | Lean owner | correspondence fixed in this cycle |
| --- | --- | --- |
| scope | `gLocalV1WholeRecord`, `gLocalV1NonemptyTargetSubsets`, `gLocalV1ARecord` | full support-active scopeを1回、全非空`A`を重複なく1回ずつ生成 |
| terminal | `gLocalV1MemoizedTerminalStates` | 全reachable irreducible terminalとexact iff |
| conditions | `gLocalV1WholeConditions`, `gLocalV1AConditions`, `gLocalV1ConditionVector` | whole C0/C5/C6と各`A`のC1--C4を全terminal上で評価 |
| packets | `gLocalV1PacketVariants`, `gLocalV1PacketKindUnion` | 4 packet familyと全reachable-state packet union |
| chart-role | `GLocalV1Cell`, `gLocalV1CellList`, `gLocalV1IncidenceRelations` | chart / vertex rootと`chartAt`を区別 |
| ball | `gLocalV1RootedBall`, `gLocalV1TerminalBallHistogram` | side-local root-preserving radius-one typed incidence star |
| relations | `GLocalV1Relation`, `gLocalV1IncidenceRelations` | `chartAt`, endpoints 0/1, boundary 0+/1−/2+ |
| map-status | `GLocalV1MapStatus`, `gLocalV1CellMapStatus` | coarseとfine chart/vertexは`mapped`、fine edge/faceはactual partial map |
| neighbor | `gLocalV1NeighborDescriptors` | actual neighborごとにrelation multisetをgroupしidentityは出力しない |
| stubs | `gLocalV1OutwardStubHistogram` | outside cell typeとcollapsed slotだけを保持 |
| multiplicity | `GLocalV1Multiplicity`, `gLocalV1Histogram` | `0 / 1 / ≥2`にclipし同rowを正規化 |
| flags | `GLocalV1Flags`, `gLocalV1CellFlags` | critical / guard / port / bridge / self-loop / FaceTwinの6 Bool |
| supports | `gLocalV1CellSupportCodes`, `gLocalV1CellPiImageCodes` | scoped supportと`computedFactor`によるπ-image |
| faces | FaceTwin key / class / member declarations | ordered boundary triple + support、actual face root、multiplicity flag |
| targets | target entries/codes, `GLocalV1TargetRelabel`, `obsG` | complete permutation pairsのπ-commutationを内部検査しstructured minimum |
| forbidden | `GLocalV1ObsValue` field inventory | H¹/rank/uniformity/result/certificate/raw IDを含まない |

`obsG` はcomplete explicit target entriesからcoarse / fine code permutationsを生成し、
`computedFactor`とのcommutationを内部検査した全valid relabel candidateの
structured minimumである。このCycleはLean内のdefinition-level fidelityを固定するもので、
Python JSONとのbyte-for-byte serialization equalityは主張しない。

### First T3 rejection and repairs

初回independent T3は次の4件を指摘し、snapshotをrejectした。

1. coordinate coarse assignmentがselected edgesだけでsigned supportを調べ、
   permanent `_v5_beta_support` の全retained coarse edges上の一意性を落としていた。
2. `gLocalV1CertifiedPair` がSLOT / KILL認証の前にlift左右のscoped edge
   support同値を要求していなかった。
3. `SubstateOf`, `Step`, `Reachable`, `Irreducible`, `LocalFineEdge`,
   `LocalFineFaceClass` の新規Prop述語に正負instance pairがなかった。
4. `UniformPresentationInstancePairs` の新規private `SelfLoopEntries`
   2 instanceに個別docstringがなかった。

修正snapshotはcoarse assignmentのuniquenessを`state.coarseEdges`全体上で検査し、
`gLocalV1CertifiedPair` でsupport equalityをcertificate前のguardにした。
`GLocalV1KernelInstancePairs` はreview済みpFire raw fixtureで六述語それぞれの
正負theoremを同じgeneric kernelに発火させた。追加監査で見つかった
`GLocalV1Irreducible` のdownstream定義展開は、definition ownerの公開API
`gLocalV1_not_irreducible_of_step` を追加して除去した。修正後T3は全findingの
実体解消とpermanent sourceへの対応を再構成し、
`approve / proof-obligation-discharged`を返した。

Formal reviewではさらに、`SelfLoopEntries` certificateの非充足側と、
非自明なkernel設計の明示的なImplementation notes、恒久sourceの役割別
provenanceを要求した。`not_nonempty_selfLoopEntries_nat` は有限listで無限型を
被覆できないことからnegative instanceを固定し、4 kernel moduleは棄却した
certificate / serialization / target-fitting routeをmodule docstringに記録した。
上記primary specificationは観測、reducer、base structure、contract manifestの
ownerを分離している。

その修正headのformal review再実行では、private theoremがnamespace-prefixの
AxiomAuditへ収載されないことと、Cycle 23で新規・body変更された宣言の
declaration-level position / material-premise provenanceが不完全であることを
指摘された。negative theoremはpublic audited theoremへ移し、namespace auditを
11 declarationsへ更新した。docstringは4新規module 261件、
`UniformPresentationInstancePairs` 13件、explicit entry-list fieldsを追加した
既存fixture presentation 11件の計285宣言を宣言単位で監査・補完した。
これはvisibility監査と記録品質の修正であり、presentation field、定理statement、
reducer / observation semantics、premise ledgerは変更していない。

### Primary declarations

- codomain / contract:
  - `GLocalV1ObsValue`
  - `GLocalV1Histogram`
  - `gLocalV1Histogram`
  - `GLocalV1ContractComponent`
  - `gLocalV1ContractComponents`
  - `gLocalV1PermanentContractSha256`
- reducer / closure:
  - `GLocalV1V5State`
  - `GLocalV1V5Packet`
  - `gLocalV1PacketVariants`
  - `GLocalV1Step`
  - `GLocalV1Reachable`
  - `GLocalV1Irreducible`
  - `gLocalV1_not_irreducible_of_step`
  - `mem_gLocalV1MemoizedReachableStates_iff`
  - `mem_gLocalV1MemoizedTerminalStates_iff`
  - `gLocalV1MemoizedTerminalStates_eq_terminalStates`
  - `mem_gLocalV1PacketKindUnion_iff_reachable_packet`
  - `gLocalV1ConditionC0` through `gLocalV1ConditionC6`
- observation:
  - `GLocalV1TargetRelabel`
  - `mem_gLocalV1TargetRelabels_iff_valid`
  - `gLocalV1AllStateList_complete`
  - `gLocalV1RootedBall`
  - `gLocalV1TerminalBallHistogram`
  - `gLocalV1ConditionVector`
  - `gLocalV1Candidate`
  - `obsG`
  - `obsG_eq_min_piPreservingRelabels`
- instance-pair gate:
  - `initial_substateOf_self` / `outside_not_substateOf_emptyInitial`
  - `exists_initial_step` / `not_initial_step_self`
  - `initial_reachable` / `outside_not_reachable`
  - `exists_irreducible` / `initial_not_irreducible`
  - `fineEdgeThree_local` / `fineEdgeZero_not_local`
  - `fineFaceOne_local` / `fineFaceZero_not_local`

### Premise, provenance, and proof-use audit

- discharged:
  - permanent 16-component output boundary and forbidden-field inventory
  - full four-family v5 packet generation and computed strict decrease
  - structural reachability, exact memoized closure, terminal completeness
  - all-reachable-state packet-kind union
  - terminal C0--C6 evaluation and target-relabel orbit minimum
  - six new Prop kernels' nonvacuous positive / negative instances
  - finite `SelfLoopEntries` certificateのpositive instanceとinfinite-`Nat`
    negative instance
- remaining:
  - registered T3 / T6 raw structural presentations and fieldwise provenance
  - all `Obs_G` component evaluations and `obsG T3 = obsG T6`
  - T3 uniform / T6 nonuniform semantic labels inside Lean
  - predicate factorization refutation and final nonfactorization theorem
- used material premises:
  - explicit finite target / cell entries and completeness proofs
  - raw readings, supports, incidence, partial chart / edge / face maps
  - canonical `computedFactor`
  - full v4 / coordinate / doubled-cycle recognizers
  - structural reachability and terminal evaluation
  - retained critical cells, ports, bridges, SLOT / KILL witnesses
  - factor-preserving target relabels
- unused material premises: none found
- structure-field escape: none found
- target-fitting / vacuity / one-way-as-equivalence / GOAL reinterpretation:
  none found

### Verification

- focused elaboration:
  - `GLocalV1V5Reduction.lean` pass; namespace audit 234 declarations,
    standard-only
  - `GLocalV1Observation.lean` pass; namespace audit 141 declarations,
    standard-only
  - `GLocalV1KernelInstancePairs.lean` pass; namespace audit 22 declarations,
    standard-only
  - modified presentation / fixture clients pass
  - `UniformPresentationInstancePairs.lean` formal-review remediation pass;
    namespace audit 11 declarations, standard-only
- targeted module build:
  - `ResearchLean.AG.UniformInvariance.GLocalV1V5Reduction` pass, 3716 jobs
  - `ResearchLean.AG.UniformInvariance.GLocalV1KernelInstancePairs` pass,
    3753 jobs; this route also rebuilds `GLocalV1Observation`
  - `ResearchLean.AG.UniformInvariance.UniformPresentationInstancePairs` pass,
    3717 jobs
- direct executable smoke on reviewed pFire input:
  - aggregate condition vector: C0--C6 all `true`
  - whole rooted-ball histogram: 15 rows
  - nonempty-subset record histogram: 3 rows
- primary declaration `#print axioms`:
  - contract length / nodup: axiom-free
  - closure, terminal, observation, no-unfold, and instance-pair declarations:
    `propext` / `Classical.choice` / `Quot.sound` only
- import-direction / research-package / separation gates: pass
- placeholder / forbidden primitive / hidden-BiDi / privacy /
  `git diff --check`: clean
- independent T3: `approve / proof-obligation-discharged`, blocking finding none
- Research full build: ユーザー指定により未実行

source SHA-256:

- `FiniteComparisonPresentation.lean`:
  `ff29a0a815d8252afa5beefea4e49000b26b5a12b4d303d20f7d0ba6e89c5f14`
- `GLocalV1ObservationValue.lean`:
  `da49dd200dc114dda71ecda2e0317e698d506150cb6dea3e1f99c5a8f742536e`
- `GLocalV1V5Reduction.lean`:
  `e38d87f04a399181b93b1d623706cd4d74dc4dcaba77d0eff93d2088ce315e9c`
- `GLocalV1Observation.lean`:
  `b7cdbca7ec1889d2704044083c070b91ebfeab8d3020cdb6ba0750b787531b7a`
- `GLocalV1KernelInstancePairs.lean`:
  `2c25186225fa4fad2ed16e539da9834dc4544d81ef0970d1fcda99095fad79cc`
- `UniformPresentationInstancePairs.lean`:
  `4aa018da7f277e0029a24bca24fa8e5f9437dc5e097703fdab280ae44e05090c`
- `AG.lean`:
  `0e8b62a38f595b223eb1f091e374afd481f314ad6295da7aead3095b8ff1f975`
- `research-modules.txt`:
  `b56056d87147877c04e68d7c3c1fadf64812010eda336525246a795a0f90e70e`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 23
decision: approve
result_type: proof-obligation-discharged
proof_obligation: faithful definition-level permanent G_local-v1 reducer and Obs_G packet
proof_obligation_delta: permanent 16-component codomain, full v5 reduction, all-terminal evaluation, and executable target-relabel minimum are generated from finite raw presentation data
primary_specification:
  source:
    goal: research/goals/G-107-aat-uniform-invariance-characterization.md
    observation: research/experiments/g104-necessity-map/g_local_v1.py
    reducer: research/experiments/g104-necessity-map/r2_hunt.py
    base_restrictions: research/experiments/g104-necessity-map/necessity_map.py
    contract_manifest: research/experiments/g104-necessity-map/g_local_v1_stop_b.py
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4 / 5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8
  status: recorded
premise_delta:
  discharged:
    - permanent G_local-v1 16-component output and forbidden-field boundary
    - full v5 four-family reducer with computed strict decrease
    - structural reachability, exact memoized closure, and terminal completeness
    - all-reachable-state packet-kind union and all-terminal C0-C6 evaluation
    - internally generated factor-preserving target relabel orbit minimum
    - positive and negative instances for six new Prop kernels
    - positive and negative instances for the finite fixture enumeration certificate
  remaining:
    - registered T3 and T6 structural presentation transfer
    - T3 and T6 component evaluation and obsG equality
    - T3 uniform and T6 nonuniform semantic labels inside Lean
    - observation nonfactorization
certificate_provenance:
  status: raw-table-generated
  unresolved:
    - T3 and T6 fieldwise transfer and semantic SHA correspondence
proof_use_audit:
  used_material_premises:
    - complete finite target and cell enumerations
    - raw readings, supports, incidence, partial maps, and computedFactor
    - all four packet recognizers and computed strict-decrease guard
    - structural reachability, terminal completeness, and all-terminal evaluation
    - target relabel permutation and factor-commutation checks
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
next_obligation: transfer registered T3 and T6 structural inputs, evaluate every Obs_G component, prove obsG equality, and derive semantic labels in Lean
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 24 — registered T3/T6 transfer and structural packet-emptiness blocker fix

- decision: `approve`
- result type: `blocker-fixed`
- completion candidate: `no`
- proof obligation: preregistered T3 / T6 raw presentationsに対し、permanent
  v5 reducerのinitial packet emptinessを全6非空scopeで、巨大な直接判定を
  使わずraw structureから証明する。
- Lean files:
  - [`GLocalV1V5Reduction.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean)
  - [`GLocalV1T3T6Witnesses.lean`](../lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Witnesses.lean)
  - [`ResearchLean/AG.lean`](../lean/ResearchLean/AG.lean)
  - [`research-modules.txt`](../lean/research-modules.txt)

### Raw presentation and route integrity

`t3Presentation` / `t6Presentation`は、permanent sourceの
`_identity_split_payload`と登録T3 / T6 inputにあるtarget counts、factor
`[0,0,1]`、nerve、chart support、identity cell mapsをraw finite tablesとして
転写する。Lean側の`Source = FineTarget = Fin 3`、`fineRead = id`、explicit
entry listsはそのcanonical finite realizationである。presentation fieldsは
reading、enumeration、incidence、support、partial maps、well-formedness proofsに
限られ、factor result、reducer state、packet、terminal、observation、rank、defect、
checker truth、uniformity、semantic labelを保持しない。

登録name-free structural SHA-256はT3
`452517a5dd3df09eea96f4de0c0b737f274384c239267aeba2d5ba06fda616a2`、T6
`0e92de476cd0af4dbeb80290afff463354da87c01c4548bab5d7806927d1d180`。
いずれもdocumentation locatorであり、Lean definition / proof premiseではない。

definition ownerへraw support、FaceTwin key / class、initial-state class、occurrence
membershipのconstructor / destructor / projection APIと、v4 coarse、v4 fine-only、
coordinate、doubled-cycleの4 family eliminatorを追加した。aggregate theorem
`gLocalV1PacketVariants_eq_empty_of_face_support`は次のraw factsだけからfull
packet unionを空にする。

- 各nonzero signed boundary occurrenceは別のfaceにも現れる。
- 各FaceTwin classはdistinctな2本のnonzero retained edgeを持つ。
- fine edge mapはtotal identityである。
- 各faceのslot 0とslot 2は異なる。

これにより任意のnonempty `A : Finset (Fin 2)`でT3 / T6 initial packet setが
空となり、`targetZero = {0}`、`targetOne = {1}`、`targetFull = univ`の全6 closed
factsを得た。higher-order assignment spaceへの`decide` / `native_decide`、expected
packet / terminal / observation / labelは用いない。

primary declarations:

- owner no-unfold / incidence API 12本:
  - `mem_gLocalV1CoarseFaceSupport_iff_raw`
  - `mem_gLocalV1CoarseFaces_iff_raw`
  - `coarseFaceEdge0_mem_gLocalV1CoarseEdges`
  - `coarseFaceEdge1_mem_gLocalV1CoarseEdges`
  - `gLocalV1CoarseFaceKey_edge0` / `_edge1` / `_edge2` / `_support`
  - `mem_gLocalV1CoarseFaceClasses_iff`
  - `gLocalV1InitialState_coarseFaceClasses`
  - `mem_gLocalV1InitialState_coarseFaceClasses_iff`
  - `mem_gLocalV1CoarseOccurrenceClasses_iff`
- owner packet eliminators 6本:
  - `gLocalV1V4CoarsePackets_eq_empty_of_no_unit`
  - `gLocalV1V4FineOnlyPackets_eq_empty_of_all_mapped`
  - `gLocalV1CoordinateCoarseAssignments_eq_empty_of_two_nonzero`
  - `gLocalV1CoordinatePackets_eq_empty_of_two_nonzero`
  - `gLocalV1DoubledCyclePackets_eq_empty_of_no_doubled_face`
  - `gLocalV1PacketVariants_eq_empty_of_face_support`
- witness spine:
  - `t3Presentation` / `t6Presentation`
  - `t3_computedFactor_apply` / `t6_computedFactor_apply`
  - `t3_initial_packet_empty_of_nonempty`
  - `t6_initial_packet_empty_of_nonempty`
  - `t3_targetZero_initial_packet_empty`
  - `t3_targetOne_initial_packet_empty`
  - `t3_targetFull_initial_packet_empty`
  - `t6_targetZero_initial_packet_empty`
  - `t6_targetOne_initial_packet_empty`
  - `t6_targetFull_initial_packet_empty`

### Verification and independent T3

- focused owner / witness: pass。namespace auditsは253 / 32 declarations、standard
  axioms only。
- targeted owner / witness builds: pass、3716 / 3717 jobs。
- master eliminator、T3 / T6 generic emptiness、T3 target-zero、T6 target-fullの
  direct `#print axioms`はすべて
  `[propext, Classical.choice, Quot.sound]`のみ。
- `git diff --check`、Research import direction(228 modules)、package direction、
  separation fixtures、changed public artifact scan: pass。
- placeholder / forbidden primitive / hidden-BiDi / privacy / Formal→Research
  reverse-import scan: no finding。
- Research full build: ユーザー指示により未実行。

独立T3の初回監査は、clientがgeneric FaceTwin / initial-state / occurrence filterを
直接利用する§2.4 API gapを検出した。ownerへmembership / projection APIを置きclientを
移行した最終snapshotを再監査し、`approve / blocker-fixed`、blocking findingなしと
判定した。

fixed source SHA-256:

- `GLocalV1V5Reduction.lean`:
  `daa981d533b3d7b4fbf35a794375c374d80329010fec65a3bbcb240abf14041a`
- `GLocalV1T3T6Witnesses.lean`:
  `969d55907c6571bee3f37bf7582eb394e1c520e46b43543c37914876050608df`
- `AG.lean`:
  `1dbe9c76e3500d7c1c0780b454d1835e1fdba6896e893fc1709edfaaab005260`
- `research-modules.txt`:
  `913d0ced0c230255f98a31c115a481b28d0b7aabbe53bcfa680ac532644b2525`

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-107-aat-uniform-invariance-characterization
target_theorem: Uniform Invariance Defect Semantics and Nonfactorization Theorem
cycle: 24
decision: approve
result_type: blocker-fixed
proof_obligation: prove initial packet emptiness for all six preregistered T3/T6 nonempty scopes without higher-order direct decision
proof_obligation_delta: registered raw presentations and definition-owner four-family eliminators remove the concrete Obs_G evaluation-route blocker
primary_specification:
  source:
    goal: research/goals/G-107-aat-uniform-invariance-characterization.md
    observation: research/experiments/g104-necessity-map/g_local_v1.py
    reducer: research/experiments/g104-necessity-map/r2_hunt.py
    contract_manifest: research/experiments/g104-necessity-map/g_local_v1_stop_b.py
  version: dd6fd9ad81d52c1ec32f51e63fbafb986f6322ac1cbf970dc9db5bbae56407d4 / 5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1V5Reduction.lean
    declarations:
      - mem_gLocalV1CoarseOccurrenceClasses_iff
      - gLocalV1PacketVariants_eq_empty_of_face_support
  - file: research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Witnesses.lean
    declarations:
      - t3Presentation
      - t6Presentation
      - t3_initial_packet_empty_of_nonempty
      - t6_initial_packet_empty_of_nonempty
      - t3_targetZero_initial_packet_empty
      - t3_targetOne_initial_packet_empty
      - t3_targetFull_initial_packet_empty
      - t6_targetZero_initial_packet_empty
      - t6_targetOne_initial_packet_empty
      - t6_targetFull_initial_packet_empty
premise_delta:
  discharged:
    - registered T3/T6 raw finite presentation construction
    - pointwise computed factor normalization to [0,0,1]
    - all four initial packet families excluded from raw retained structure
    - initial packet emptiness for every nonempty target subset of both presentations
    - six closed target-zero/target-one/target-full packet-emptiness facts
  remaining:
    - complete observation-component fieldwise normal forms and provenance
    - independent T3 and T6 Obs_G evaluations and their equality
    - T3 uniform and T6 nonuniform semantic labels through the sound-complete checker
    - observation predicate-factorization refutation
certificate_provenance:
  discharged:
    - raw registered target, factor, nerve, support, incidence, and identity cell-map tables
    - packet emptiness generated from raw occurrence, coefficient, support, and map facts
  unresolved:
    - observation-level evaluation and semantic labels
proof_use_audit:
  used_material_premises:
    - nonempty target scopes and complete raw face tables
    - distinct face keys and second occurrences of nonzero boundary coefficients
    - total fine edge maps and two nonzero retained edges per FaceTwin class
    - absence of doubled slot-zero/slot-two faces
    - all four packet-family exclusions in the aggregate eliminator
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
next_obligation: complete fieldwise T3/T6 Obs_G normal forms, prove both evaluations and obsG equality, then derive T3 uniform and T6 nonuniform labels through the existing checker
completion_candidate: false
tracking_issue_closed: false
```
