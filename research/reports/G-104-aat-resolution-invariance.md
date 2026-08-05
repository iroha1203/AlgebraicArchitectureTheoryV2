# G-104-aat-resolution-invariance — 診断の解像度不変性

- 一次仕様: [`research/goals/G-104-aat-resolution-invariance.md`](../goals/G-104-aat-resolution-invariance.md)
- tracking Issue: [#3902](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3902)
- target theorem: Diagnostic Resolution Invariance Theorem
- proof state: `target-refuted`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria の正本は GOAL カードであり、この
report はそれらを再定義しない。

## Proof obligation state

- 完了: H0a `CoarserThan` からの canonical comparison factor、その可換性・
  一意性・全射性。
- 完了: H0b `Adequate` から生成した各 law descend、その可換性・一意性、
  comparison factor に沿う coarse / fine descend の可換性。
- 完了: Cycle 2 の C0–C3 十分性 blocker。coarse face lift の欠落を有限反例で
  固定し、条件 C を C0–C4 へ改訂する根拠を得た。
- 完了: Cycle 3 の C0–C4 十分性 blocker。C4 face を actual differential と
  comparison map に使いながら、同一 coarse edge の parallel fine lift が作る
  追加 `H^1` class を Lean で固定した。
- 停止: 改訂 target の (ii)。C0–C4 をすべて満たす canonical comparison map が
  非全射となるため、現 statement の証明は続行しない。
- 未実行: (iii)–(v)。中心 claim (ii) の反例が固定されたため completion artifact
  としては進めない。

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

## Cycle 2 — coarse-face lift obstruction

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

## Cycle 3 — parallel edge-lift obstruction

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

現 GOAL は編集しない。次版でこの witness を除外する最小の候補は、各 coarse
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
