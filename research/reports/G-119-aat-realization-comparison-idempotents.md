# G-119 — Realization comparison categories and idempotent normalization

一次仕様は
[`research/goals/G-119-aat-realization-comparison-idempotents.md`](../goals/G-119-aat-realization-comparison-idempotents.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、前提の出所、
proof-use、検証、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `2d0478fcc0b00bf4f2072a03180fcf6a892e1c45`
- fixed GOAL blob: `83b7efa5a097143b8a12d575955eb5c4a76c54a4`
- common criteria base: `2d0478fcc0b00bf4f2072a03180fcf6a892e1c45`
- tracking Issue: [#4416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4416)
- current proof obligation: A の任意の関手に関する自然性と恒等・合成整合
- pending proof obligations: A の残り、B、C、D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: A の `Kar(Arr(F))` と `Arr(Kar(F))` に関する可換自然同型

## Cycle 1 — Karoubi completion and arrow equivalence

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 1
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 2d0478fcc0b00bf4f2072a03180fcf6a892e1c45
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 initial proof state: A--D unproved"
  proof_dag_predecessors:
    - "Mathlib.CategoryTheory.Comma.Arrow"
    - "Mathlib.CategoryTheory.Idempotents.Karoubi"
  proof_obligation: "A1: construct Kar(Arr(E)) ≃ Arr(Kar(E)), retaining endpoint maps and explicitly fixing both unit and counit directions"
  selection_reason: "This equivalence defines the comparison category used by B--D and is the shortest common predecessor of every remaining target clause."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowEquivalence
  risks:
    - "raw identities versus Karoubi identities"
    - "endpoint component order in the normalized arrow"
    - "square commutativity after endpoint sandwiching"
    - "target-fitting by assuming the raw comparison already lies in the image"
  unchecked:
    - "A functor naturality and identity/composition compatibility"
    - "A maximal subgroupoid statement"
    - "B--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed both functors, their unit and counit natural isomorphisms, and the equivalence.  The forward object is independently normalized as e ≫ c ≫ d; all endpoint maps of the unit and counit are the relevant idempotents."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowToArrowKaroubi
    - AAT.AG.RealizationComparisonIdempotents.arrowKaroubiToKaroubiArrow
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowUnitIso
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowCounitIso
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowEquivalence
    - CategoryTheory.Equivalence.unit_inverse_comp
  claim_mapping:
    theorem_names:
      - karoubiArrowToArrowKaroubiObj_hom_f
      - karoubiArrowToArrowKaroubi
      - arrowKaroubiToKaroubiArrow
      - karoubiArrowUnitIso
      - karoubiArrowCounitIso
      - karoubiArrowEquivalence
    source_labels:
      - "fixed target A: comparison and idempotent completion exchange"
    conjuncts:
      - "left object (c,e,d) -> endpoint Karoubi objects and independently normalized e ≫ c ≫ d"
      - "morphisms -> retained endpoint maps"
      - "inverse -> raw comparison plus endpoint idempotent square"
      - "unit in both directions -> endpoint maps (e,d)"
      - "counit in both directions -> endpoint Karoubi identities, whose raw maps are the endpoint idempotents"
      - "forward triangle -> karoubiArrowEquivalence.functor_unitIso_comp"
      - "inverse triangle -> CategoryTheory.Equivalence.unit_inverse_comp karoubiArrowEquivalence"
    undischarged_assumptions: []
    acceptance_point: "A1 is general in every category E and introduces no added premise or certificate.  It discharges only the equivalence part of A."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "A functor naturality and identity/composition compatibility"
      - "A maximal subgroupoid statement"
      - "all B--D construction obligations"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "Karoubi idempotence in endpoint objects, the normalized comparison, unit/counit inverse laws, and the triangle identity"
      - "Arrow square equations in the forward map, inverse object, and unit squares"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean; exit 0"
    - "module terminal axiom audit: 29 declarations, standard axioms only"
    - "git diff --check; exit 0"
    - "hidden/BiDi scan on all changed and added files; no matches"
    - "axiom/admit/sorry/unsafe scan on the new Lean file; no matches"
    - "privacy/local-path scan on the GOAL, report, and Lean file; no matches"
    - "Formal-to-ResearchLean reverse-import scan; no matches"
  blocking_findings: []
  next_obligation: "A2: construct the commuting natural isomorphism for every F:E→E' and prove identity/composition compatibility"
```

### Cycle 1 acceptance spine

`karoubiArrowToArrowKaroubiObj` は raw comparison をそのまま採用せず、入力の二つの
冪等射から `e ≫ c ≫ d` を構成する。逆関手は Karoubi 内の比較から raw comparison と
両端の冪等正方形を回収する。unit と counit の両方向で端点写像を明示し、
`karoubiArrowEquivalence` の forward triangle fieldを直接証明する。inverse triangleは
mathlibの `CategoryTheory.Equivalence.unit_inverse_comp` から得る。

Cycle 1 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の圏 `[Category E]`、`Karoubi (Arrow E)` のcomponentwise
  idempotenceとArrow-square relation、`Arrow (Karoubi E)` のendpoint idempotenceと
  `Karoubi.Hom.comm`、各圏のmorphism law。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。
- `conclusion-equivalent-risk`: 該当なし。
