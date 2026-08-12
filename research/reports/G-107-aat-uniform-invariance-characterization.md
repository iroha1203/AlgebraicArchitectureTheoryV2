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
  これによりC3の非必要性とAtlas包含の真性を閉じた。
- 未完了: C0 / C1 / C2 / C4 / C5 / C6非必要性 witness 6種、`Obs_G` / T3 / T6 /
  observation nonfactorization、Cycle 12由来の非中心品質負債2件。

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
  - witness focused check: pass、警告なし
  - `ResearchLean.AG.UniformInvariance.ConditionC3NonnecessityWitness`
    targeted module build: pass (3740 jobs)
  - witness namespace axiom audit: 87 declarations、standard axioms only
  - bridgeを含む主要6 declarationの型確認と `#print axioms`:
    `propext`、`Classical.choice`、`Quot.sound` のみ
  - canonical R1 report SHA-256とname-free semantic SHA-256を既存canonical
    generatorから再現し、raw tableをfieldwise照合
  - `git diff --check`、placeholder、`unsafe`、`native_decide`、
    `Classical.dec`、hidden / bidirectional Unicode、privacy、
    Formal→Research逆import、aggregate / manifest scan: clean
  - Research全体のfull build: ユーザー指定により未実行
- T3 independent audit: `approve / proof-obligation-discharged`
  - source SHA-256:
    - `ConditionCAllABridge.lean`:
      `2389d0e417bc7be28c4fb0576262428deb5c4cf6f046c322c8b31536446bc4d3`
    - `ConditionC3NonnecessityWitness.lean`:
      `2aea45d2cf173c5b6c77cab3b642967f5d82be68454aed9e404b13c45f515cda`
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
  nonfactorization、Cycle 12品質負債2件。

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

### Carried quality obligations from Cycle 12

本witnessの中心claimには影響しないため、次の2件は最終completion前のnarrow
remediationとして引き続き保持する。

1. selected-cell / fiber / internal-face membership characterizationの公開
   no-unfold API化と、`ConditionCAllAFiring.lean`の直接definition展開の置換。
2. Cycle 12 private helper群の個別docstring補完。

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
    - two noncentral Cycle 12 quality-remediation items
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
next_obligation: formalize the exact R1 C0_not_necessary witness with uniformity, direct C0 and ConditionCAllA failure, and nonzero H1 on both sides of a nonempty block meeting the failure data
completion_candidate: false
tracking_issue_closed: false
```
