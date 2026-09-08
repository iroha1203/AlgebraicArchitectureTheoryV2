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
- current proof obligation: A の最大亜群
- pending proof obligations: A の最大亜群、B、C、D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: A の可逆な表示変更を `M(E)` の最大亜群として固定

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

## Cycle 2 — Functor naturality and coherence

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 2
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: f2954a74f27794ae8a17fc732a9f4ccadf8f8455
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 1 result: A1 discharged; A2 selected next"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowEquivalence
    - CategoryTheory.Functor.mapArrow
    - CategoryTheory.Idempotents.functorExtension₂
  proof_obligation: "A2: for every F:E→E', construct the commuting natural isomorphism, identify all endpoint components, and prove identity/composition coherence"
  selection_reason: "A2 is the remaining functorial part of A and is required before applying A to the three AAT projection functors in B."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIso
  risks:
    - "mistaking F(e ≫ c ≫ d) and F(e) ≫ F(c) ≫ F(d) for definitional equality"
    - "using raw identities instead of Karoubi identities at the endpoints"
    - "recording only component formulas without naturality or pseudofunctor coherence"
  unchecked:
    - "A maximal subgroupoid statement"
    - "B--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the induced Karoubi and arrow functors, the commuting component and natural isomorphism, all hom/inv endpoint evaluations, identity coherence, and composition coherence as an equality of isomorphisms."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean
  evidence:
    - CategoryTheory.Idempotents.functorExtension₂
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowMap
    - AAT.AG.RealizationComparisonIdempotents.arrowKaroubiMap
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIsoApp
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIso
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIsoApp_id
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIsoApp_comp
  claim_mapping:
    theorem_names:
      - karoubiArrowNaturalityLeft_obj_hom_f
      - karoubiArrowNaturalityRight_obj_hom_f
      - karoubiArrowNaturalityIsoApp_hom_left_f
      - karoubiArrowNaturalityIsoApp_hom_right_f
      - karoubiArrowNaturalityIsoApp_inv_left_f
      - karoubiArrowNaturalityIsoApp_inv_right_f
      - karoubiArrowNaturalityIso
      - karoubiArrowNaturalityIsoApp_id
      - karoubiArrowNaturalityIsoApp_comp
    source_labels:
      - "fixed target A: functor naturality and identity/composition compatibility"
    conjuncts:
      - "Kar(Arr(F)) followed by T_E' -> F(e) ≫ F(c) ≫ F(d)"
      - "T_E followed by Arr(Kar(F)) -> F(e ≫ c ≫ d)"
      - "hom and inv endpoint components -> (F(e),F(d))"
      - "naturality -> karoubiArrowNaturalityIso"
      - "identity coherence -> component Iso.refl equality"
      - "composition coherence -> component Iso equality under mapped and composed components"
    undischarged_assumptions: []
    acceptance_point: "A2 is general in F, exposes both comparison formulas, and proves naturality plus identity/composition coherence without adding a preservation premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "A maximal subgroupoid statement"
      - "all B--D construction obligations"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "F.map_comp transports the normalized comparison and the endpoint idempotence equations"
      - "Karoubi morphism commutativity proves component naturality"
      - "mapped endpoint idempotence proves composition coherence"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.KaroubiArrowEquivalence; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean; exit 0"
    - "module terminal axiom audit: 29 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "A3: identify reversible representation changes with the maximal subgroupoid of M(E), retaining noninvertible comparison objects"
```

### Cycle 2 acceptance spine

mathlibの `functorExtension₂` は対象の冪等射と射を `F.map` で送る。これを用いた
`karoubiArrowMap` と `arrowKaroubiMap` はそれぞれ `Kar(Arr(F))` と
`Arr(Kar(F))` を与える。二経路の
比較射は定義的には同じではなく、片方は `F.map (e ≫ c ≫ d)`、他方は
`F.map e ≫ F.map c ≫ F.map d` である。`karoubiArrowNaturalityIsoApp` は両者を
端点のKaroubi恒等成分 `(F(e),F(d))` で結び、homとinvの双方を評価定理で固定する。
`karoubiArrowNaturalityIso` が射に関する自然性を証明し、identity componentは
`Iso.refl`、合成componentはmapped componentと次のcomponentのIso合成に一致する。

Cycle 2 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の圏 `E,E'` と任意の関手 `F:E⥤E'`、入力Karoubi/Arrow
  対象と射が持つ定義上の法則、関手法則。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。比較式は `F.map_comp` から導く。
- `conclusion-equivalent-risk`: 該当なし。
