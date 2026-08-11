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
- 未完了: global generated H¹ comparison の全単射性と全 block comparison
  の全単射性の同値、indicator law family と adequacy、有限 defect bridge、
  decider、Atlas positioning、7 witness、observation nonfactorization。

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
