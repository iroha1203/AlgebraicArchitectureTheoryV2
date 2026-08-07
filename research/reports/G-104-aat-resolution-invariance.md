# G-104-aat-resolution-invariance — 診断の解像度不変性

- 一次仕様: [`research/goals/G-104-aat-resolution-invariance.md`](../goals/G-104-aat-resolution-invariance.md)
- tracking Issue: [#3902](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3902)
- target theorem: Diagnostic Resolution Invariance Theorem
- proof state: `target-proof-checkpoint`(カードは退化宣言の hereditary 化で
  statement を再固定済み。Cycle 7 の `target-refuted` は改訂前の退化 face
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
  canonical comparison cochain map と `comm0` / `comm1`、`H^1` の座標
  block 直和分解、座標 subnerve と C0–C6 の定義、不変性 theorem、系、
  inadequate 側診断、反例3種、発火 witness。

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

- premise delta: hereditary な partial incidence morphism、canonical `π` と chart 台の
  両立、mapped edge / face の K1-derived support transport を放電した。
- certificate provenance: `π` は `CoarserThan` から生成する review 済み
  `comparisonFactor`。edge / face 台は Cycle 5 の K1 定義に追跡できる。
  任意 factor、独立な edge / face 台対応、coordinate correspondence は受けない。
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
  discharged:
    - hereditary partial chart-edge-face incidence geometry
    - canonical comparison-factor compatibility on chart supports
    - mapped edge and face support transport derived from K1 intersections
  remaining:
    - generated comparison cochain map and comm0-comm1
    - H1 law-value block decomposition
    - coordinate subnerves and C0-C6
    - invariance theorem and no-overresolution corollary
    - canonical inadequate diagnostic, three counterexamples, and firing witness
certificate_provenance:
  discharged:
    - chart support transport through comparisonFactor generated from CoarserThan
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
