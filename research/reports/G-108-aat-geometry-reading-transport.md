# G-108-aat-geometry-reading-transport — geometry reading 輸送の opcartesian lift

- 一次仕様: [`research/goals/G-108-aat-geometry-reading-transport.md`](../goals/G-108-aat-geometry-reading-transport.md)
- tracking Issue: [#4013](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4013)
- target theorem: Geometry Reading Transport Opcartesian Lift Theorem
- proof state: `target-proof-checkpoint`
- completion candidate: `yes (standard PR review / final math-lean-review pending)`

この report は固定 GOAL の証拠索引、proof obligation delta、material premise
監査を記録する。target statement と completion criteria の正本は GOAL カードで
あり、この report はそれらを再定義しない。target-theorem mode のため SCORE は
使わない。

## Completion candidate judgment

- fixed GOAL SHA-256:
  `67a94101084bebb87245f05c0a6c6b42f09ef84ca1d6c35c47d3956b82edad6a`
- implementation base: `d9ad65625ec61569e3562bc0d775dbf2fce58c40`
- fixed review head: `pending`
- implementation PR: `pending`
- standard PR review: `pending`
- formal completion review: `pending (Math A / Math B / Lean A / Lean B)`
- fixed GOAL claims (i)--(v): Lean artifact 接続済み
- remaining known mathematical proof obligations: `[]`
- unchecked completion gates:
  - standard `$review-pr` の固定 head 監査
  - root acceptance recheck
  - final packet に対する独立 `$math-lean-review` 4 lane
  - GitHub CI

したがって、この snapshot は proof package の completion candidate であり、
`target-theorem-proved` 判定そのものではない。最終判定は同一 PR head の review
packet と tracking Issue に置く。

## Fixed target mapping

### (i) geometry 段総圏と射影

- `GeometryPackage` は Formal の `ReadingCore` をそのまま再利用する。site、
  `SelectedGeometryReading`、単一 `CommRing` 係数、
  `RawAmbientRestrictionSystem` を別の Research 型へ複製していない。
- `CoverageTransport` は固定された index map に沿う9個の前進保存則を持つ。
  required equation coordinate は `requiredCoordinateMap`、violation coordinate は
  `equationCoordinateMap`、context index は `contextMap` を実使用する。
- `OverlapTransport` は selected overlap の `Iso` を持つ。
  `OverlapTransport.left_comm`、`right_comm`、`base_comm`、`lift_preserved` が
  両射影・共通 base・普遍性との両立を公開する。
- `GeomReadHom` は coverage、overlap、前進 `RingHom`、raw reindex/base-change
  等式、support / axis / observable comparison family、三つの cross-context
  read-preservation、三つの自然性を固定 contract のまま持つ。
- `GeomReadHom.id` / `GeomReadHom.comp` と `geometryTotalCategory` が identity、
  composition、圏則を証明し、`geometryProjection` が G-101 package 総圏へ
  忘却する。

主な source:

- [`Basic.lean`](../lean/ResearchLean/AG/GeometryTransport/Basic.lean)
- [`Categories.lean`](../lean/ResearchLean/AG/GeometryTransport/Categories.lean)

### (ii) canonical 輸送と strong cocartesian 性

- `pushCoverage`、`pushOverlap`、`rawReindexCore` から
  `geomTransportAlong` を生成する。係数は `RingHom.id` で base change し、raw
  restriction system 全体を inverse context functor で reindex する。
- `geomTransportAlongGeometryHom` の三 realization family は G-101 の
  `transportCoreSupportEquiv`、`transportCoreAxisEquiv`、
  `transportCoreObservableEquiv` から生成する。read-preservation と自然性も
  G-101 transport の構成定理から放電する。
- `geomTransportAlongHom_base` は射影された底射が
  `transportAlongHom G.core sigma` であることを `rfl` で固定する。
- 任意の core tail とその composite 上の geometry hom に対し、
  `geometryTotalFactor` を構成する。`geometryTotalFactor_fac` と
  `geometryTotalFactor_unique` が factorization と一意性を与え、
  `geomTransportAlongHom_factor_existsUnique` および
  `geomTransportAlongHom_isStronglyCocartesian` が選択された exact 底射上の
  partial op-cleavage を確定する。opcartesian 性は structure field として
  受け取らない。

主な source:

- [`Transport.lean`](../lean/ResearchLean/AG/GeometryTransport/Transport.lean)
- [`Opcartesian.lean`](../lean/ResearchLean/AG/GeometryTransport/Opcartesian.lean)
- [`FactorLaws.lean`](../lean/ResearchLean/AG/GeometryTransport/FactorLaws.lean)
- [`Factorization.lean`](../lean/ResearchLean/AG/GeometryTransport/Factorization.lean)

### (iii) lift 一意性と fiber 内同型の全成分

`geomTransportAlong_liftUniqueUpToFiberIso` は canonical lift と任意の strongly
cocartesian lift を core fiber 内の `GeometryFiberInnerIso` で結ぶ。forward / inverse
の factorization は
`geomTransportAlong_liftUniqueUpToFiberIso_hom_fac` と
`geomTransportAlong_liftUniqueUpToFiberIso_inv_fac` で固定する。

categorical `Iso` の両 leg は full `GeomReadHom` contract を持ち、その逆則から
次の可逆成分を導出する。

- coverage: `requiredSupport_iff` から `boundaryVisibleOn_iff` まで固定9 predicate
- overlap: `selectedOverlapIso` と両 leg の `OverlapTransport` projection / lift 定理
- coefficient: `coefficientEquiv : C.Coefficient ≃+* Q.Coefficient`
- raw: `raw_forward_eq` / `raw_inverse_eq`
- display: `coordinatePresentationEquiv` / `relationPresentationEquiv`
- realization carrier: `supportComparisonEquiv` / `axisComparisonEquiv` /
  `observableComparisonEquiv`
- reading compatibility: `supportComparison_reads_iff` /
  `axisComparison_reads_iff` / `observableComparison_reads_iff`

source: [`LiftUniqueness.lean`](../lean/ResearchLean/AG/GeometryTransport/LiftUniqueness.lean)

### (iv) standalone 成分等式、生成位相、Formal finite instantiation

`geomTransportAlong_geometry_eq`、`geomTransportAlong_requirements_eq`、
`geomTransportAlong_overlap_eq`、`geomTransportAlong_coefficient_eq`、
`geomTransportAlong_raw_eq`、`geomTransportAlong_coordinateFamily_eq`、
`geomTransportAlong_relationFamily_eq` が、一本の
canonical transport から site / coefficient / raw の値を standalone に取り出す。

`pushAATCoverageFamily` と `pullAATCoverageFamily` は source / target の admissible
cover generator を相互に運び、presieve の実際の pushforward を計算する。
`geomSourceTopology_le_inducedTarget` と `geomTargetTopology_le_inducedSource` の
両包含から、`geomTransportAlong_coveringSieve_iff` は任意の sieve `S` について
source の生成位相で covering であることと、Mathlib の
`Sieve.functorPushforward` が target の生成位相で covering であることの iff を
証明する。

`FiniteGeometryWitness.package` は Formal の
`RawPresheafFiniteExample.system` を実際の raw 成分として持つ。次を concrete
theorem で放電する。

- `site_nonempty`
- `has_topology_cover`
- `coefficient_nontrivial`
- `raw_relation_nonzero`
- `raw_restriction_fires`

主な source:

- [`Components.lean`](../lean/ResearchLean/AG/GeometryTransport/Components.lean)
- [`FiniteWitnesses.lean`](../lean/ResearchLean/AG/GeometryTransport/FiniteWitnesses.lean)

### (v) realization 障害の必要十分性と正負 witness

- `NonRealizationComponentTransport` と
  `nonRealizationComponents_transportable` は任意の core package hom に沿って
  coverage、overlap、係数、raw が常に輸送できることを証明する。
- `RealizationTransportSupply` / `HGeom` は lift を参照せず、三 comparison
  family、三 read-preservation、三自然性、mapped non-generation だけを持つ。
- `geomReadHomOfHGeom` / `geometryLiftOfHGeom` が十分性を証明する。
- `hGeomOfGeomReadHom` / `hGeom_necessary` が任意の target package と任意の lift
  から必要条件を抽出する。GOAL の exact・非退化 class より強い一般形である。
- `hGeom_iff_nonempty_geomReadHom` は canonical pushed target における iff を
  上の二方向から導出する。
- `canonicalHGeom` / `canonicalHGeom_nonempty` は exact canonical route を source
  data から生成する。

positive witness は `FiniteGeometryWitness.exactSwap` を使う。Atom A/B を入れ替える
非恒等 exact hom であり、`exactSwap_nonidentity`、`positiveHGeom`、
`positiveLift`、`positiveLift_base_nonidentity_atom` が可住性と発火を固定する。
site、cover、係数、raw の非退化性は同じ namespace の concrete theorem 群が示す。

negative witness は `NegativeGeometryWitness.coreHom` を使う。

- `coreHom_base_doctrineHom`: exact lower map が選択した `doctrineHom` に一致
- `core_stage_lift_exists`: core 段の射は可住
- `coreSupportReadProfile`: target package に依存しない共通 realization profile
- `CoreLiftRoute`: target と hom を同じ型へ束ねる exact core lift route
- `coreHom_ne_tautological`: 同じ exact doctrine map の selected / G-101 canonical
  route は上記 profile の実値が異なるため route 自体が不等
- `not_hGeom`: source support が読む componentA の像 componentB を target context
  が読めないことから `¬ Nonempty (HGeom package coreHom)`
- `no_geomReadHom_to_any_target`: 固定 target core 上の任意の geometry / coefficient /
  raw target への hom が存在しない
- `no_geometryLift_to_any_target`: 同じ主張の総圏射版
- `target_candidate_class_nonempty`: target package 候補 class 自体は非空

負例 source についても `cover_mem_topology`、`coefficient_nontrivial`、
`raw_relation_nonzero` が非退化性を構成から証明する。さらに
`source_not_requires_componentB` / `target_requires_componentB` が site requirement
の値変化を、`pairRaw_value_changes` が非恒等 coefficient base change 後の raw
polynomial の実値変化を証明する。

source: [`Supply.lean`](../lean/ResearchLean/AG/GeometryTransport/Supply.lean)、
[`FiniteWitnesses.lean`](../lean/ResearchLean/AG/GeometryTransport/FiniteWitnesses.lean)

## Material premise and proof-use audit

### 入力として残る data

- `U` と一般 source `G`: 全一般 theorem の量化入力。
- G-101 accepted artifact と Formal `ReadingCore` component types: import して
  使用する既存 theorem / type。
- `sigma : ExactDoctrineHom`: canonical direction。`transportAlongHom` の
  `transportCoreReading`、equation exact transport、Atom conjugation、context
  carrier equivalenceを通じて target core と三 realization family の生成に
  実使用する。
- 一般 tail の `GeomReadHom`: opcartesian 全称域の入力。factor construction は
  coverage 9 field、overlap iso、coefficient hom、raw equality、三 comparison
  family、三 read-preservation、三自然性をそれぞれ使用する。

### 放電した premise

- geometry hom contract、identity / composition、総圏圏則、functor 則:
  `Categories.lean` で証明。
- canonical well-definedness と射影可換:
  `Transport.lean` で構成、`geomTransportAlongHom_base` で証明。
- opcartesian factorization と一意性:
  `Factorization.lean` で componentwise に証明。
- fiber 内一意性:
  Mathlib strong-cocartesian uniquenessから `GeometryFiberInnerIso` を構成し、
  全 component API を `LiftUniqueness.lean` で導出。
- non-realization component transport:
  `transportNonRealizationComponents` が任意の core hom から生成。
- canonical realization route:
  `canonicalHGeom` が G-101 carrier transport から生成。
- supplied `HGeom` route:
  `geomReadHomOfHGeom` が低レベル field を contract へ接続。
- necessity:
  `hGeomOfGeomReadHom` が geometry hom の realization fields と、target core の
  derived non-generation theoremだけから抽出。
- positive / negative / target-candidate / site+raw firing:
  `FiniteWitnesses.lean` の closed fixturesから証明。
- component / topology equations:
  `Components.lean` が canonical construction から導出。

### Escape / route checks

- strong cocartesian 性、factorization、一意性、component equations は structure
  fieldとして入力していない。
- `HGeom` は coverage、overlap、coefficient、raw、lift existenceを持たない。
  十分性は `geometryLiftOfHGeom`、必要性は `hGeom_necessary` という別 theorem。
- canonical route、supplied-HGeom route、arbitrary-tail route は別 declaration で
  証拠 provenance を保つ。
- positive route は非恒等 exact Atom action、実 cover、非零係数、非零 relation、
  非恒等 restrictionで発火する。
- negative route は空 target class、空 site、零環、空 raw system、型差だけを
  不存在証明に使わない。
- topology は hom field ではなく `AATSite` の生成位相から導出する。

## Dependency and aggregate wiring

- root facade: [`GeometryTransport.lean`](../lean/ResearchLean/AG/GeometryTransport.lean)
- Research aggregate: [`ResearchLean/AG.lean`](../lean/ResearchLean/AG.lean)
- focused module manifest: [`research-modules.txt`](../lean/research-modules.txt)
- G-101 public transport support API:
  [`AtomFoundation/Transport.lean`](../lean/ResearchLean/AG/AtomFoundation/Transport.lean)

import 方向は `ResearchLean -> Formal` のみで、`Formal/AG` は変更していない。

## Validation evidence

```text
cd research/lean
lake env lean ResearchLean/AG/GeometryTransport/FiniteWitnesses.lean
  -> axiom audit: 85 declarations under AAT.AG.GeometryTransport,
     standard axioms only

lake build ResearchLean.AG.GeometryTransport.Components
  -> Build completed successfully

lake build ResearchLean.AG.GeometryTransport.FiniteWitnesses
  -> Build completed successfully

lake build ResearchLean.AG.GeometryTransport
  -> Build completed successfully
```

各 module 末尾の `#assert_standard_axioms_only AAT.AG.GeometryTransport` と、
G-101 support API owner の `#assert_standard_axioms_only AAT.AG.AtomFoundation` は
standard axioms only で通る。Research package全体 buildは実行していない。

PR 前に次を再実行し、固定 head packetへ出力 hashを載せる。

```text
research/lean/check_research_modules.sh --focused \
  ResearchLean/AG/GeometryTransport.lean
git diff --check
placeholder / hidden-BiDi / privacy / import-direction scans
```

## Cycle ledger

### Cycle 1 — E0 fixed hom contract and total category

- selected obligation: fixed 7-part geometry hom contract、identity / composition、
  `GeomRead_U`、core projection
- delta: `GeometryPackage` / `GeomReadHom` / `GeometryTotalHom` /
  `geometryTotalCategory` / `geometryProjection` を接続
- result: `proof-obligation-discharged`
- principal artifacts: `Basic.lean`, `Categories.lean`

### Cycle 2 — E1/E2 canonical lift and universal property

- selected obligation: exact `sigma` から canonical geometry liftを生成し、任意の
  core tail上で factorization / uniquenessを証明
- delta: `geomTransportAlongHom_isStronglyCocartesian` まで接続
- result: `proof-obligation-discharged`
- principal artifacts: `Transport.lean`, `Opcartesian.lean`, `FactorLaws.lean`,
  `Factorization.lean`

### Cycle 3 — E3 realization supply criterion

- selected obligation: non-realization component transportability、lift非参照 `HGeom`、
  十分性、必要性、canonical route
- delta: `hGeom_iff_nonempty_geomReadHom` と `canonicalHGeom_nonempty` まで接続
- result: `proof-obligation-discharged`
- principal artifact: `Supply.lean`

### Cycle 4 — fiber uniqueness and derived components

- selected obligation: liftの同型を除く一意性、全fiber component、standalone
  component equations、生成位相 iff
- delta: `geomTransportAlong_liftUniqueUpToFiberIso` と
  `geomTransportAlong_coveringSieve_iff` まで接続
- result: `proof-obligation-discharged`
- principal artifacts: `LiftUniqueness.lean`, `Components.lean`

### Cycle 5 — closed positive/negative portfolio and completion candidate

```yaml
ledger_type: target_cycle_result
goal: G-108-aat-geometry-reading-transport
cycle: 5
goal_blob_sha: 67a94101084bebb87245f05c0a6c6b42f09ef84ca1d6c35c47d3956b82edad6a
base_oid: d9ad65625ec61569e3562bc0d775dbf2fce58c40
tracking_issue: 4013
report_path: research/reports/G-108-aat-geometry-reading-transport.md
selection:
  proof_state_ref: fixed GOAL target (iv)-(v), Cycles 1-4 artifacts
  proof_dag_predecessors:
    - GeometryTransport categorical and supply spine
    - Formal FiniteModel and RawPresheafFiniteExample
  proof_obligation: positive/negative/nonvacuity portfolio and final artifact connection
  selection_reason: closes the last discharge-required witness and route-integrity rows
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/GeometryTransport/FiniteWitnesses.lean
    - ResearchLean/AG/GeometryTransport.lean
  risks:
    - negative route could be vacuous
    - non-tautological claim could rely only on target types
    - HGeom could be uninhabited
    - site/raw firing could reduce to index relabeling
  unchecked:
    - fixed-head independent review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: closed Formal instantiation, positive HGeom firing, no-lift witness, and site/raw value change
  completion_candidate: yes
  lean_artifacts:
    - FiniteGeometryWitness package and positiveLift
    - NegativeGeometryWitness coreHom, not_hGeom, no_geometryLift_to_any_target
    - NegativeGeometryWitness coreHom_ne_tautological
    - NegativeGeometryWitness pairRaw_value_changes
  evidence:
    - concrete nondegeneracy theorems
    - target_candidate_class_nonempty
    - standard-axiom audit
  claim_mapping:
    theorem_names:
      - canonicalHGeom_nonempty
      - hGeom_necessary
      - coreHom_ne_tautological
      - not_hGeom
      - no_geometryLift_to_any_target
      - pairRaw_value_changes
    source_labels:
      - target theorem (iv)
      - target theorem (v)(a)-(e)
    conjuncts:
      - Formal finite raw instantiation
      - HGeom positive inhabitation and lift firing
      - non-tautological exact core lift with no geometry lift
      - nonempty target candidate class
      - site and raw actual value change
    undischarged_assumptions: []
    acceptance_point: all fixed target artifacts are connected; formal completion review remains a gate
    port_status: unported
audits:
  premise_delta:
    discharged:
      - witness nondegeneracy
      - HGeom inhabitation
      - negative no-lift
      - target class nonemptiness
      - site/raw firing
    remaining: []
  certificate_provenance:
    discharged:
      - Formal RawPresheafFiniteExample.system
      - Formal FiniteModel exact core change
      - input-generated pushGeometryPackage constructions
    unresolved: []
  proof_use:
    used:
      - exact Atom equivalences
      - cross-context supportReads
      - coefficient baseChange
      - actual raw polynomial evaluation
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused FiniteWitnesses check, 85 declarations, standard axioms only
    - targeted GeometryTransport build success
  blocking_findings: []
  next_obligation: fixed-head standard PR review and final four-lane completion review
```

## Current completion ledger

```yaml
ledger_type: target_theorem_completion_candidate
goal: G-108-aat-geometry-reading-transport
verdict: target-proof-checkpoint
target_theorem: Geometry Reading Transport Opcartesian Lift Theorem
completion_criteria_status: implementation-satisfied-review-pending
math_lean_review_gate: pending
target_proved_gate: fail-closed-pending-review
material_premise_ledger_audit: root-pass-review-pending
certificate_provenance_audit: root-pass-review-pending
proof_use_audit: root-pass-review-pending
structure_field_escape_audit: root-pass-review-pending
route_integrity_audit: root-pass-review-pending
axiom_audit_status: pass
placeholder_scan_status: pending-final-head
dependency_audit_status: pending-final-head
artifact_sync_audit: implementation-and-report-connected-issue-sync-pending
completed_proof_obligations:
  - claim (i) geometry total category and projection
  - claim (ii) canonical transport and strong cocartesian lift
  - claim (iii) fiber-inner uniqueness and reversible components
  - claim (iv) components, topology, Formal finite instantiation
  - claim (v) HGeom criterion and positive/negative portfolio
remaining_proof_obligations: []
unchecked_central_claim:
  - independent fixed-head review pending
research_full_build: not-run-by-hard-rule
completion_candidate: true
proof_state: target-proof-checkpoint
```
