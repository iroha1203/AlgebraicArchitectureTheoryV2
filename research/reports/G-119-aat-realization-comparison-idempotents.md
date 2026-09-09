# G-119 — Realization comparison categories and idempotent normalization

一次仕様は
[`research/goals/G-119-aat-realization-comparison-idempotents.md`](../goals/G-119-aat-realization-comparison-idempotents.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、前提の出所、
proof-use、検証、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `2d0478fcc0b00bf4f2072a03180fcf6a892e1c45`
- fixed GOAL blob: `83b7efa5a097143b8a12d575955eb5c4a76c54a4`
- active GOAL blob at the completion-audit base: `c4f170b4c28ea40a964bf8c82b4718266b6066b1`
- common criteria base: `2d0478fcc0b00bf4f2072a03180fcf6a892e1c45`
- completion audit schema: PR #4435 で復元した手組み
  `completion-ledger.md` blob `52af37a4f0bdbe839c7839875057c0a53280929c`
  （Issue #4416 comment 5605317972 の人間判断による）
- tracking Issue: [#4416](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4416)
- current proof obligation: 固定target A–D 全体の手組みcompletion audit
- pending mathematical proof obligations: none after Cycle 13 acceptance
- current target state: `target-proof-checkpoint`
- completion candidate: yes。Cycle 13 は PR #4429、merge
  `36d6e8de7541f3bb038ef99c2501367457ccea4e` で受理済み
- next proof obligation: 固定headで手組みのschema-complete completion packetを作り、
  標準PR reviewとは独立したfresh 4-lane最終査読を実施する

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

## Cycle 3 — Maximal subgroupoid of comparison changes

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 3
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 466af9b2a384b254323d9a0fa2549b6b74aee497
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 2 result: A2 discharged; A3 selected next"
  proof_dag_predecessors:
    - CategoryTheory.Core
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowEquivalence
  proof_obligation: "A3: define reversible representation changes as the maximal subgroupoid of M(E), retaining every comparison object"
  selection_reason: "A3 closes clause A and fixes the groupoid read used by the qualified automorphism groups in B and D."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/MaximalSubgroupoid.lean
    - AAT.AG.RealizationComparisonIdempotents.ReversibleRepresentationChanges
  risks:
    - "using a full subcategory on invertible comparison arrows and thereby dropping objects"
    - "characterizing only some invertible changes rather than all isomorphisms"
    - "naming Core without recording its groupoid factorization property"
  unchecked:
    - "B--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Instantiated the comparison category and its Core, proved that inclusion is object-surjective, identified core morphisms with all comparison isomorphisms, and exposed the factorization of every groupoid functor through the inclusion."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/MaximalSubgroupoid.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.RealizationComparisonCategory
    - AAT.AG.RealizationComparisonIdempotents.ReversibleRepresentationChanges
    - AAT.AG.RealizationComparisonIdempotents.reversibleRepresentationInclusion_obj_surjective
    - AAT.AG.RealizationComparisonIdempotents.reversibleRepresentationHomEquiv
    - AAT.AG.RealizationComparisonIdempotents.reversibleRepresentationLift
    - AAT.AG.RealizationComparisonIdempotents.reversibleRepresentationLift_comp_inclusion
  claim_mapping:
    theorem_names:
      - reversibleRepresentationInclusion_obj_surjective
      - reversibleRepresentationHomEquiv
      - reversibleRepresentationLift_comp_inclusion
    source_labels:
      - "fixed target A: reversible representation changes are the maximal subgroupoid of M(E)"
    conjuncts:
      - "objects -> every object of Arrow(Karoubi E), with no invertibility condition on its comparison arrow"
      - "morphisms -> exactly isomorphisms in Arrow(Karoubi E)"
      - "maximality -> every functor from a groupoid factors through Core inclusion"
    undischarged_assumptions: []
    acceptance_point: "A3 uses the canonical Core, retains all comparison objects, and records both the all-isomorphism hom characterization and groupoid factorization."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "all B--D construction obligations"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "Core.of retains every comparison object"
      - "CoreHom.iso identifies every reversible change"
      - "Core.functorToCore supplies groupoid factorization"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.FunctorNaturality; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/MaximalSubgroupoid.lean; exit 0"
    - "module terminal axiom audit: 12 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "B1: instantiate A on the geometry, core, and extraction categories and prove compatibility with the composite projection"
```

### Cycle 3 acceptance spine

`ReversibleRepresentationChanges E` は `Core (Arrow (Karoubi E))` である。
`reversibleRepresentationInclusion_obj_surjective` は任意の比較対象がそのままCoreの対象に
なることを示し、比較射自体の可逆性を対象条件にしない。
`reversibleRepresentationHomEquiv` はCoreの射が元の比較圏の全同型と正確に一致することを示す。
さらに `reversibleRepresentationLift_comp_inclusion` は任意のgroupoidから比較圏への関手が
Core inclusionを経由することを固定する。

Cycle 3 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の圏 `E`、標準的な `Core` とgroupoidの法則。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 4 — Three-stage projection tower

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 4
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 3f13de53cecd57e49324917ffc4123a6acc119aa
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 3 result: clause A discharged; B1 selected next"
  proof_dag_predecessors:
    - AAT.AG.CrossStageCoherence.crossStageProjection
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowEquivalence
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIso
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowNaturalityIsoApp_comp
  proof_obligation: "B1: specialize clause A to the geometry, core-package, and pointed-extraction categories and prove compatibility with the composite projection"
  selection_reason: "B1 fixes the typed projection tower and its concrete evaluation API before imposing the qualified endpoint conditions in B2."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
    - AAT.AG.RealizationComparisonIdempotents.crossStageProjectionKaroubiArrowNaturalityIsoApp_comp
  risks:
    - "reversing the Lean functor-composition direction for pi rho"
    - "merely renaming generic clause-A constructions without exposing their AAT projection fields"
    - "requiring an arbitrary idempotent or comparison itself to project to an identity"
  unchecked:
    - "B2 qualified comparison group"
    - "B3 generated comparison specialization"
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Specialized the Karoubi-arrow equivalence to all three AAT categories, constructed the induced Karoubi and comparison projections for rho, pi, and pi rho, evaluated them through the actual base fields, and specialized A2 composition coherence to the projection tower."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.geometryKaroubiArrowEquivalence
    - AAT.AG.RealizationComparisonIdempotents.packageKaroubiArrowEquivalence
    - AAT.AG.RealizationComparisonIdempotents.extractionKaroubiArrowEquivalence
    - AAT.AG.RealizationComparisonIdempotents.geometryKaroubiProjection
    - AAT.AG.RealizationComparisonIdempotents.packageKaroubiProjection
    - AAT.AG.RealizationComparisonIdempotents.crossStageKaroubiProjection
    - AAT.AG.RealizationComparisonIdempotents.geometryComparisonProjection
    - AAT.AG.RealizationComparisonIdempotents.packageComparisonProjection
    - AAT.AG.RealizationComparisonIdempotents.crossStageComparisonProjection
    - AAT.AG.RealizationComparisonIdempotents.crossStageProjectionKaroubiArrowNaturalityIsoApp_comp
  claim_mapping:
    theorem_names:
      - geometryPackageKaroubiProjection_comp
      - geometryPackageComparisonProjection_comp
      - crossStageProjection_eq_geometry_comp_package
      - crossStageKaroubiProjection_obj_p
      - crossStageComparisonProjection_obj_hom_f
      - crossStageComparisonProjection_map_left_f
      - crossStageComparisonProjection_map_right_f
      - crossStageProjectionKaroubiArrowNaturalityIsoApp_comp
    source_labels:
      - "fixed target B paragraph 1: three AAT categories, rho, pi, and compatibility with pi rho"
      - "fixed target B paragraph 1: arbitrary idempotents land in Kar(B), comparisons land in M(B)"
    conjuncts:
      - "three categories -> clause-A equivalences are specialized at geometry, core-package, and pointed-extraction stages"
      - "Karoubi projection -> arbitrary geometry idempotents land in Kar(ExtractionInstance U) with idempotent P.p.base.base"
      - "comparison projection -> arbitrary geometry comparisons land in M(ExtractionInstance U) with comparison C.hom.f.base.base"
      - "composition -> stagewise Karoubi and comparison projections equal the declared composite actions"
      - "A2 coherence -> the composite naturality component is the mapped rho component followed by the pi component"
    undischarged_assumptions: []
    acceptance_point: "B1 uses the existing crossStageProjection, adds no identity condition on arbitrary objects, and exposes the concrete twice-projected fields."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "B2--B3 and C--D"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "geometryProjection maps actual GeometryTotalHom.base"
      - "packageProjection maps actual PackageTotalHom.base"
      - "crossStageProjection is the existing composite rho followed by pi"
      - "karoubiArrowNaturalityIsoApp_comp supplies projection composition coherence"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.GeometryTransport.Categories; exit 0"
    - "direct predecessor targeted build: ResearchLean.AG.CrossStageCoherence.Basic; exit 0"
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.MaximalSubgroupoid; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean; exit 0"
    - "module terminal axiom audit: 50 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "B2: embed an arbitrary geometry comparison with identity idempotents and identify its base-qualified automorphism group with qualifiedComparisonSubgroup"
```

### Cycle 4 acceptance spine

`geometryKaroubiArrowEquivalence`、`packageKaroubiArrowEquivalence`、
`extractionKaroubiArrowEquivalence` はAの同値を三圏へ適用する。
`geometryKaroubiProjection`、`packageKaroubiProjection`、`crossStageKaroubiProjection` は
一般の冪等対象を各Karoubi圏へ送り、合成先を `Kar(ExtractionInstance U)` に固定する。
対応する三つのcomparison projectionは比較を `M(ExtractionInstance U)` まで送り、
評価APIは幾何射の `.base.base` を実際に読む。
`crossStageProjectionKaroubiArrowNaturalityIsoApp_comp` は合成投影のA2成分を
rho成分をpiで写したものとpi成分の合成として同定する。

Cycle 4 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U : AtomCarrier`、既存の幾何universe、三圏と二投影。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。一般の冪等対象や比較の底像に恒等性を要求しない。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 5 — Qualified automorphisms of an embedded comparison

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 5
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 3d4e83bffcb38f0780f7894d81f1ebef5ea88d9e
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 4 result: B1 discharged; B2 selected next"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.ReversibleRepresentationChanges
    - AAT.AG.CrossStageCoherence.compositeFiberAutSubgroup
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonSubgroup
  proof_obligation: "B2: embed every geometry comparison with identity endpoint idempotents and identify its base-qualified reversible automorphisms with the existing qualified comparison group"
  selection_reason: "B2 provides the group-level bridge needed before specializing it to the generated G-118 comparison in B3."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/QualifiedComparisonGroup.lean
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv
  risks:
    - "requiring the comparison itself, rather than only endpoint automorphisms, to project to an identity"
    - "reversing the Arrow intertwining equation or Aut multiplication order"
    - "defining the new endpoint projections by transport across the final equivalence"
  unchecked:
    - "B3 generated comparison specialization"
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Embedded arbitrary comparisons into the maximal subgroupoid with identity endpoint idempotents, formed the independently qualified automorphism subgroup, and constructed a projection-compatible group equivalence with qualifiedComparisonSubgroup."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/QualifiedComparisonGroup.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.identityIdempotentReversibleComparison
    - AAT.AG.RealizationComparisonIdempotents.baseQualifiedReversibleComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.baseQualifiedReversibleComparisonSourceProjection
    - AAT.AG.RealizationComparisonIdempotents.baseQualifiedReversibleComparisonTargetProjection
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv_source_projection
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv_target_projection
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv_symm_source_projection
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv_symm_target_projection
  claim_mapping:
    theorem_names:
      - identityIdempotentReversibleComparison_left_X
      - identityIdempotentReversibleComparison_left_p
      - identityIdempotentReversibleComparison_right_X
      - identityIdempotentReversibleComparison_right_p
      - identityIdempotentReversibleComparison_hom_f
      - identityIdempotentReversibleComparison_projected_hom
      - mem_baseQualifiedReversibleComparisonSubgroup
      - baseQualifiedReversibleComparison_source_projected_identity
      - baseQualifiedReversibleComparison_target_projected_identity
      - qualifiedComparisonReversibleMulEquiv
      - qualifiedComparisonReversibleMulEquiv_source_projection
      - qualifiedComparisonReversibleMulEquiv_target_projection
      - qualifiedComparisonReversibleMulEquiv_symm_source_projection
      - qualifiedComparisonReversibleMulEquiv_symm_target_projection
      - baseQualifiedReversibleComparisonSourceProjection_hom
      - baseQualifiedReversibleComparisonTargetProjection_hom
    source_labels:
      - "fixed target B paragraph 2: identity-idempotent embedding of every geometry comparison"
      - "fixed target B paragraph 2: base-qualified endpoint automorphisms and qualifiedComparisonSubgroup are isomorphic"
      - "fixed target B paragraph 2: endpoint projections and full geometry maps agree"
    conjuncts:
      - "embedding -> endpoints are G and H with raw identity idempotents, and the comparison map is exactly c"
      - "comparison base -> the projected comparison is c.base.base, with no identity requirement"
      - "qualification -> only the two endpoint automorphisms map to bottom identities"
      - "intertwining -> the Arrow square is the existing source-comp-c equals c-comp-target equation"
      - "group isomorphism -> qualifiedComparisonSubgroup c is MulEquiv to the new qualified reversible automorphism subgroup"
      - "projections -> source and target projections agree in both directions and retain full GeometryTotalHom maps"
    undischarged_assumptions: []
    acceptance_point: "B2 derives the existing subgroup equation from the Arrow square and constructs both endpoint projections before the final equivalence."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "B3 and C--D"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "toKaroubi supplies identity endpoint idempotents"
      - "Core.isoMk realizes each endpoint-pair square as a reversible comparison change"
      - "the Arrow morphism equation supplies comparison preservation"
      - "compositeFiberAutSubgroup supplies the actual endpoint base-identity qualification"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonStabilizer; exit 0"
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.ThreeStageProjection; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/QualifiedComparisonGroup.lean; exit 0"
    - "module terminal axiom audit: 26 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "B3: specialize the embedded comparison object, group equivalence, and endpoint projections to generatedCompatibleUpperGeometryMateAt"
```

### Cycle 5 acceptance spine

`identityIdempotentReversibleComparison c` は任意の完全幾何比較 `c` を、
両端のraw恒等冪等射を持つ `Core (M(E_geom))` の対象へ入れる。
`identityIdempotentReversibleComparison_projected_hom` は比較自身の底像が
`c.base.base` であることだけを述べ、恒等性を要求しない。
`baseQualifiedReversibleComparisonSubgroup c` はその自己同型のうち両端だけが
合成投影で底の恒等射へ送られるものを選ぶ。
`qualifiedComparisonReversibleMulEquiv c` はArrowの可換正方形を用いて、これを既存の
`qualifiedComparisonSubgroup c` と群同型にし、独立に構成した両端射影と完全幾何写像を保つ。

Cycle 5 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `G,H : GeometryPackage U` と任意の `c : GeometryTotalHom G H`。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。資格は自己同型の両端にだけ課す。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 6 — Generated compatible comparison specialization

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 6
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 35275ec7c3f6068f1f10b4997a4673f1c648f6e4
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 5 result: B2 discharged; B3 selected next"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedCompatibleUpperGeometryMateAt
    - AAT.AG.RealizationComparisonIdempotents.identityIdempotentReversibleComparison
    - AAT.AG.RealizationComparisonIdempotents.qualifiedComparisonReversibleMulEquiv
  proof_obligation: "B3: specialize the comparison object and group identification to every generatedCompatibleUpperGeometryMateAt and retain the generated endpoints, comparison, and existing endpoint projections"
  selection_reason: "B3 closes the final fixed target B clause before placing the concrete G-116 Karoubi image required by C."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/GeneratedQualifiedComparison.lean
    - AAT.AG.RealizationComparisonIdempotents.generatedCompatibleQualifiedComparisonReversibleMulEquiv
  risks:
    - "replacing the generated endpoints or mate by definitionally convenient identities"
    - "adding a base-identity premise on the generated comparison itself"
    - "exposing only an alias without named endpoint and projection compatibility evidence"
  unchecked:
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Specialized B2 to every G-118 generated compatible upper-geometry mate, retaining both generated endpoint geometries, identity endpoint idempotents, the actual mate and its base projection, and the existing source and target group projections."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/GeneratedQualifiedComparison.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.generatedCompatibleReversibleComparisonAt
    - AAT.AG.RealizationComparisonIdempotents.generatedCompatibleBaseQualifiedReversibleComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.generatedCompatibleQualifiedComparisonReversibleMulEquiv
    - AAT.AG.RealizationComparisonIdempotents.generatedCompatibleQualifiedComparisonReversibleMulEquiv_source_projection
    - AAT.AG.RealizationComparisonIdempotents.generatedCompatibleQualifiedComparisonReversibleMulEquiv_target_projection
  claim_mapping:
    theorem_names:
      - generatedCompatibleReversibleComparisonAt_left_X
      - generatedCompatibleReversibleComparisonAt_left_p
      - generatedCompatibleReversibleComparisonAt_right_X
      - generatedCompatibleReversibleComparisonAt_right_p
      - generatedCompatibleReversibleComparisonAt_hom_f
      - generatedCompatibleReversibleComparisonAt_projected_hom
      - generatedCompatibleQualifiedComparisonReversibleMulEquiv
      - generatedCompatibleQualifiedComparisonReversibleMulEquiv_source_projection
      - generatedCompatibleQualifiedComparisonReversibleMulEquiv_target_projection
    source_labels:
      - "fixed target B paragraph 3: every generated compatible upper-geometry mate"
      - "fixed target B paragraph 3: generated endpoints and comparison are retained"
      - "fixed target B paragraph 3: group identification agrees with existing endpoint projections"
    conjuncts:
      - "quantification -> arbitrary ctx, P, k, compatible input, and vertex"
      - "object -> generated source and target geometries with raw identity idempotents"
      - "comparison -> the actual generated compatible mate and its actual twice-projected map"
      - "group -> the general B2 MulEquiv specialized to the generated mate"
      - "projections -> the specialized equivalence preserves both existing CompositeFiberAut projections"
    undischarged_assumptions: []
    acceptance_point: "B3 is a premise-free specialization of B2 whose named evaluations retain the G-118 generated data and whose projection equations reuse the general compatibility theorems."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "C--D"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "generatedCompatibleUpperGeometryMateAt supplies the actual generated source, target, and comparison"
      - "the B2 identity-idempotent embedding supplies the comparison object"
      - "the B2 group equivalence and projection theorems supply the specialized group identification"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.QualifiedComparisonGroup; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/GeneratedQualifiedComparison.lean; exit 0"
    - "focused research module check; exit 0"
    - "module terminal axiom audit: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "C: place the G-116 collapse Karoubi isomorphism hom as a comparison object and project it to M(E_core)"
```

### Cycle 6 acceptance spine

`generatedCompatibleReversibleComparisonAt input i` はG-118が生成したsource、target、mateを
そのまま用い、両端だけにraw恒等冪等射を置く。比較自身の合成投影は実際の
`generatedCompatibleUpperGeometryMateAt` の `.base.base` であり、恒等性は要求しない。
`generatedCompatibleQualifiedComparisonReversibleMulEquiv` はB2の群同型を任意の
`ctx, P, k, input, i` へ特殊化し、既存のsource/target射影との一致を名前付き定理で保つ。

Cycle 6 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `ctx`、有限表示 `P`、係数圏 `k`、互換入力 `input`、頂点 `i`。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。生成比較自身の底像に恒等性を要求しない。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 7 — G-116 Karoubi comparison placement

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 7
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: d040b4d2ba2aa944800d350eb7b31912dd6914fc
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 6 result: B discharged; C selected next"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.authoredDiagnosticObjectCollapseKaroubiIso
    - CategoryTheory.Functor.Fiber.fiberInclusion
    - AAT.AG.RealizationComparisonIdempotents.arrowKaroubiMap
  proof_obligation: "C1: place the actual G-116 Karoubi-isomorphism hom in M(CoreFiber NE), map it to M(E_core), retain both existing endpoints and beta, and prove both endpoint projectors become bottom identities"
  selection_reason: "This fixes the concrete comparison and its two qualified endpoint projectors before independently reconstructing it as the T-image of a raw-alpha idempotent square."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiPlacement.lean
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticCoreComparison
  risks:
    - "replacing the existing beta comparison by the raw reversible mate alpha"
    - "requiring beta itself to project to an identity"
    - "turning the fixed endpoint projector into an automorphism qualification"
    - "assuming fiber verticality as a new caller-supplied certificate"
  unchecked:
    - "C2 raw-alpha Karoubi exchange"
    - "D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Placed the existing G-116 Karoubi-isomorphism hom as a northeast-core-fiber comparison, mapped it through the fiber inclusion to M(E_core), retained both endpoint Karoubi objects and beta, exposed the inverse E-comp-alpha-inverse, and derived both base-identity projector equations from fiber verticality."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiPlacement.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticKaroubiComparison
    - AAT.AG.RealizationComparisonIdempotents.coreFiberComparisonInclusion
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticCoreComparison
    - AAT.AG.RealizationComparisonIdempotents.coreFiberEndomorphism_packageProjection_identity
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticCoreComparison_source_projected_identity
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticCoreComparison_target_projected_identity
  claim_mapping:
    theorem_names:
      - authoredDiagnosticKaroubiComparison_left
      - authoredDiagnosticKaroubiComparison_right
      - authoredDiagnosticKaroubiComparison_hom_f
      - authoredDiagnosticObjectCollapseKaroubiIso_inv_f
      - authoredDiagnosticCoreComparison_left_X
      - authoredDiagnosticCoreComparison_left_p
      - authoredDiagnosticCoreComparison_right_X
      - authoredDiagnosticCoreComparison_right_p
      - authoredDiagnosticCoreComparison_hom_f
      - authoredDiagnosticCoreComparison_source_projected_identity
      - authoredDiagnosticCoreComparison_target_projected_identity
    source_labels:
      - "fixed target C paragraph 1: place the existing Karoubi-isomorphism hom in M(CoreFiber NE) and forget it to M(E_core)"
      - "fixed target C paragraph 2: retain the existing endpoints, beta, source projector, target projector, and inverse component"
      - "fixed target C paragraph 3: both endpoint idempotents project to identities"
    conjuncts:
      - "fiber placement -> the actual hom of authoredDiagnosticObjectCollapseKaroubiIso"
      - "endpoints -> the existing authoredDiagnosticImageSourceKaroubi and authoredDiagnosticImageTargetKaroubi"
      - "comparison -> the existing beta component, not the raw alpha mate"
      - "inverse -> the existing E followed by inverse alpha component"
      - "forgetful image -> complete underlying core packages, projectors, and beta morphism"
      - "bottom qualification -> each endpoint projector maps to its endpoint bottom identity"
    undischarged_assumptions: []
    acceptance_point: "C1 derives the two bottom identities from the existing CoreFiber morphism witnesses and imposes no identity condition on beta."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "C2 and D"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "the existing G-116 Karoubi isomorphism supplies its actual hom and inverse"
      - "fiberInclusion supplies the canonical forgetful functor to E_core"
      - "each CoreFiber morphism's IsHomLift witness supplies its packageProjection identity"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeKaroubiImage; exit 0"
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.GeneratedQualifiedComparison; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiPlacement.lean; exit 0"
    - "focused research module check; exit 0"
    - "module terminal axiom audit: 15 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "C2: construct the raw-alpha idempotent square in Kar(Arr(CoreFiber NE)) and identify its T-image with the existing beta Karoubi comparison"
```

### Cycle 7 acceptance spine

`authoredDiagnosticKaroubiComparison` はG-116の既存Karoubi同型のhomをそのまま
`M(CoreFiber NE)` の対象とし、source、target、比較射を既存のKaroubi像と `β` に固定する。
`coreFiberComparisonInclusion` による像 `authoredDiagnosticCoreComparison` は各完全core package、
source projector `β ≫ α⁻¹`、target projector `E`、比較 `β` を保持する。
二つのprojectorの底恒等性はCoreFiber射が既に持つverticalityから導き、比較 `β` 自身には
底恒等性を要求しない。

Cycle 7 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U`、`[DecidableEq U.Atom]`、`input`、`cochain`、`cell`。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。既存のKaroubi同型とCoreFiber verticalityだけを使う。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 8 — G-116 raw-mate Karoubi exchange

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 8
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 8236a6a3ef1a901da7b2fd46e9d0c67b1966aad6
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 7 result: C1 discharged; C2 selected next"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowToArrowKaroubiObj
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticKaroubiComparison
    - AAT.AG.DoctrineFiberProduct.authoredDiagnosticObjectCollapseComparisonAtCochain_app
    - AAT.AG.DoctrineFiberProduct.authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp
  proof_obligation: "C2: independently construct the Kar(Arr(CoreFiber NE)) object with raw alpha and endpoint idempotents, derive the exchange identities, and identify its T-image with the actual beta Karoubi comparison"
  selection_reason: "C2 closes the remaining fixed target C realization claim after C1 fixed the concrete target object and endpoint qualifications."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiExchange.lean
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticRawIdempotentComparison_exchange
  risks:
    - "using beta rather than the reversible mate alpha as the raw comparison"
    - "reversing the conventional and Lean composition orders"
    - "taking the normalized beta equation or Arrow square as a caller premise"
    - "showing only the comparison morphism while losing endpoint object equality"
  unchecked:
    - "D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the raw-alpha idempotent square with endpoint projectors beta-comp-alpha-inverse and E, identified the source projector with the conjugate alpha-comp-E-comp-alpha-inverse, derived the Arrow exchange and normalized beta equations, and proved the entire T-image equals the placed G-116 Karoubi comparison."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiExchange.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticRawIdempotentComparison
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticRawIdempotentComparison_p_left_conjugate
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticRawIdempotentComparison_intertwining
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticRawIdempotentComparison_normalized_hom
    - AAT.AG.RealizationComparisonIdempotents.authoredDiagnosticRawIdempotentComparison_exchange
  claim_mapping:
    theorem_names:
      - authoredDiagnosticRawIdempotentComparison_X_hom
      - authoredDiagnosticRawIdempotentComparison_p_left
      - authoredDiagnosticRawIdempotentComparison_p_left_conjugate
      - authoredDiagnosticRawIdempotentComparison_p_right
      - authoredDiagnosticRawIdempotentComparison_intertwining
      - authoredDiagnosticRawIdempotentComparison_normalized_hom
      - authoredDiagnosticRawIdempotentComparison_exchange
    source_labels:
      - "fixed target C paragraph 3: raw alpha with idempotent pair (alpha-inverse E alpha, E)"
      - "fixed target C paragraph 3: E alpha equals alpha e, e equals alpha-inverse beta, and E alpha e equals beta"
      - "fixed target C paragraph 3: the T-image equals the existing Karoubi-isomorphism hom"
    conjuncts:
      - "raw comparison -> the actual reversible canonical mate alpha"
      - "source idempotent -> beta followed by inverse alpha and equivalently alpha-E-inverse-alpha"
      - "target idempotent -> the actual cell projector E"
      - "exchange -> endpoint idempotents form an Arrow endomorphism of raw alpha"
      - "normalization -> source-idempotent, alpha, target-idempotent compose to beta"
      - "T-image -> full Arrow object equality with the C1 placed comparison, including endpoints"
    undischarged_assumptions: []
    acceptance_point: "C2 derives every exchange equation from beta equals alpha-comp-E, alpha invertibility, and E idempotence, and proves full object equality rather than only hom equality."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "D"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "the existing source and target Karoubi projectors supply the idempotent pair"
      - "the existing beta factorization supplies the Arrow square and source conjugate equation"
      - "the existing E idempotence supplies normalized beta"
      - "A1 karoubiArrowToArrowKaroubiObj supplies the actual T normalization"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.G116KaroubiPlacement; exit 0"
    - "lake env lean ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiExchange.lean; exit 0"
    - "focused research module check; exit 0"
    - "module terminal axiom audit: 8 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D: derive the canonical absorption law and construct the normalization category N_C"
```

### Cycle 8 acceptance spine

`authoredDiagnosticRawIdempotentComparison` はraw比較を既存の可逆mate `α` とし、
source projectorを `β ≫ α⁻¹`、target projectorを `E` とするA左辺の対象である。
source projectorは既存の `β=α ≫ E` から `α ≫ E ≫ α⁻¹` とも同定される。
Arrowの交換式、`E` の冪等性、`α` の可逆性から正規化射が `β` になることを導き、
`authoredDiagnosticRawIdempotentComparison_exchange` はT像をC1の実比較対象と全体で同定する。

Cycle 8 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U`、`[DecidableEq U.Atom]`、`input`、`cochain`、`cell`。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加premiseなし。`β=α ≫ E`、`E²=E`、`α` の可逆性は既存G-116構成から使う。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 9 — canonical package-normalization absorption

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 9
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 99bc00edb82115eec84d55bfd2ce759cd4b16e36
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 8 result: A--C discharged; D selected next"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.canonicalObjectNormalizationTotal
    - AAT.AG.DoctrineFiberProduct.canonicalObjectNormalization_natural_apply
    - AAT.AG.DoctrineFiberProduct.canonicalObjectNormalization_idempotent
    - AAT.AG.DoctrineFiberProduct.equationSystemExactTransport_hext
  proof_obligation: "D1: for every total morphism between admissible core packages, prove e_P ≫ f ≫ e_Q = e_P ≫ f as a complete total-morphism equality, including the dependent operation component"
  selection_reason: "The absorption equation is the direct predecessor of the category N_C, the normalization functor, its fullness, and the natural inclusion required by every remaining D clause."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/CanonicalNormalizationAbsorption.lean
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_absorption
  risks:
    - "adding one-sided absorption or operation coherence as a morphism field or theorem premise"
    - "proving only object-map equality while omitting the dependent operation map"
    - "reversing conventional and Lean composition order"
    - "using the G-117-refuted opposite two-sided naturality equation"
  unchecked:
    - "D2: N_C, K, and N"
    - "D3: ambient inclusion, comparison functors, and pi_N"
    - "D4: i, objectwise p, naturality characterization, and tagged failure"
    - "D5: endpoint automorphism and qualified subgroup homomorphisms"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined the full admissible-package subcategory and its existing canonical endomorphism, then proved the fixed one-sided sandwich equality for every total morphism by complete extensionality.  The operationMap branch uses heterogeneous function extensionality and cast_heq, so its dependent types are part of the theorem rather than an extra certificate."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/CanonicalNormalizationAbsorption.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.CanonicalNormalizationAdmissiblePackage
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization
    - AAT.AG.RealizationComparisonIdempotents.canonicalObjectNormalization_fixed_after_map
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_absorption
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_idem
    - AAT.AG.RealizationComparisonIdempotents.packageProjection_canonicalPackageNormalization
  claim_mapping:
    theorem_names:
      - canonicalObjectNormalization_fixed_after_map
      - canonicalPackageNormalization_absorption
      - canonicalPackageNormalization_idem
      - packageProjection_canonicalPackageNormalization
    source_labels:
      - "fixed target D: admissible core packages and canonical absorption"
    conjuncts:
      - "C -> the ordinary full subcategory cut out by existing CanonicalObjectNormalizationAdmissible"
      - "e_P -> the existing canonicalObjectNormalizationTotal built from P.property"
      - "object component -> naturality followed by target idempotence"
      - "equation transport -> exact heterogeneous extensionality with the same object computation"
      - "dependent operation component -> nested hfunext and cast_heq"
      - "total equality -> e_P ≫ f ≫ e_Q = e_P ≫ f, equivalent to conventional e_Q f e_P = f e_P"
      - "base projection -> pi(e_P) is the identity"
    undischarged_assumptions: []
    acceptance_point: "D1 quantifies over every morphism in the full subcategory and derives absorption solely from existing admissibility and total-morphism laws, with no conclusion-equivalent field or operation-coherence input."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D one-sided absorption is derived for arbitrary total morphisms"
      - "D dependent operation component is included in the total equality"
      - "D base identity pi(e_P)=1"
    remaining:
      - "D2--D5 constructions and characterization theorems"
  certificate_provenance:
    discharged:
      - "e_P is canonicalObjectNormalizationTotal P.obj P.property"
    unresolved: []
  proof_use:
    used:
      - "P.property and Q.property construct the endpoint normalizations and their operation type equalities"
      - "canonicalObjectNormalization_natural_apply uses the arbitrary total morphism's object-formation and configuration laws"
      - "canonicalObjectNormalization_idempotent fixes the transported normalized objects"
      - "PackageTotalHom.ext, SignedExactCoreReadingHom.ext, equationSystemExactTransport_hext, Function.hfunext, and cast_heq cover every total-morphism component"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization; exit 0"
    - "direct predecessor targeted build: ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationNaturality; exit 0"
    - "focused research module check; exit 0"
    - "module terminal axiom audit: 8 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D2: construct N_C, the fully faithful K:N_C→Kar(C), and the full normalization functor N:C→N_C"
```

### Cycle 9 acceptance spine

`CanonicalNormalizationAdmissiblePackage` は既存の
`CanonicalObjectNormalizationAdmissible` を対象条件とする通常の充満部分圏であり、
射に追加の吸収則やoperation coherenceを持たせない。
`canonicalPackageNormalization_absorption` は任意のtotal射に対し、object map、
equation transport、依存型を持つoperation map、残りのexact成分を順に外延して
`e_P ≫ f ≫ e_Q = e_P ≫ f` を証明する。operation mapでは
`Function.hfunext` と `cast_heq` を使い、型の依存性も等式に含める。

Cycle 9 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U`と、既存admissibilityを持つ任意の `P,Q:C`。
- `direction-hypothesis`: なし。対象条件とtotal射の既存法則から固定された片側吸収を導く。
- `discharge-required`: 追加premiseなし。依存operation成分も主定理の証明項で直接放電する。
- `conclusion-equivalent-risk`: 該当なし。吸収式は部分圏や射のfieldに入っていない。

## Cycle 10 — normalized package category and full normalization functor

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 10
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: d4f610eeb3e12d271bb0b67b8a6580feffb220c9
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 9 result: D1 merged and discharged; D2 selected next"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_absorption
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_idem
    - CategoryTheory.Idempotents.Karoubi
  proof_obligation: "D2: construct the labelled sandwich category N_C, a fully faithful K:N_C→Kar(C), and a full normalization functor N:C→N_C with N(f)=e_P≫f"
  selection_reason: "D2 turns the reviewed D1 absorption theorem into the categorical domain required by every remaining D comparison, naturality, and automorphism construction."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean
    - AAT.AG.RealizationComparisonIdempotents.NormalizedPackageObject
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiFunctor
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor
  risks:
    - "replacing all sandwich morphisms by the selected image of N"
    - "adding absorption as a new Hom certificate instead of reusing the Karoubi equation"
    - "using raw identities instead of e_P"
    - "proving fullness only at a selected endpoint pair"
  unchecked:
    - "D3: ambient inclusion, comparison functors, and pi_N"
    - "D4: i, objectwise p, naturality characterization, and tagged failure"
    - "D5: endpoint automorphism and qualified subgroup homomorphisms"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed N_C with explicit package labels and Hom equal to the corresponding mathlib Karoubi Hom, so identities have raw map e_P and composition is raw composition.  Constructed K by identity-on-Hom reuse and proved it full and faithful.  Constructed N with raw map e_P≫f using D1 absorption and proved it full for every sandwich morphism by taking that morphism's raw map as preimage."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.NormalizedPackageObject
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiObject
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageCategory
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageCategory_id_f
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageCategory_comp_f
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageHom_sandwich
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiFunctor
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiFunctor_faithful
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiFunctor_full
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor_map_f
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor_full
  claim_mapping:
    theorem_names:
      - normalizedPackageCategory_id_f
      - normalizedPackageCategory_comp_f
      - normalizedPackageHom_sandwich
      - normalizedPackageKaroubiFunctor_faithful
      - normalizedPackageKaroubiFunctor_full
      - packageNormalizationFunctor_map_f
      - packageNormalizationFunctor_full
    source_labels:
      - "fixed target D paragraph 2: N_C, K, and N"
    conjuncts:
      - "N_C objects -> explicit labels P:C"
      - "N_C homs -> Karoubi morphisms whose comm field is e_P ≫ a ≫ e_Q = a"
      - "N_C identity -> underlying e_P"
      - "N_C composition -> underlying raw composition"
      - "K -> P maps to (P,e_P) and each Hom is retained"
      - "K fully faithful -> identity Hom maps give injectivity and surjectivity"
      - "N objects -> unchanged package labels"
      - "N(f) -> underlying e_P ≫ f, conventional f e_P"
      - "N functoriality -> D1 absorption and e_P idempotence"
      - "N fullness -> every arbitrary sandwich morphism is lifted from its own raw map"
    undischarged_assumptions: []
    acceptance_point: "D2 uses the reviewed canonical idempotents and absorption theorem, reuses mathlib Karoubi Hom for the exact fixed sandwich equation, and quantifies fullness over every endpoint pair and sandwich morphism."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D labelled sandwich category N_C"
      - "D fully faithful comparison K"
      - "D full normalization functor N"
    remaining:
      - "D3--D5 constructions and characterization theorems"
  certificate_provenance:
    discharged:
      - "the Hom sandwich law is the standard Karoubi.Hom comm equation for the independently constructed endpoint idempotents"
      - "N(f) obtains its sandwich law from reviewed D1 absorption rather than caller input"
    unresolved: []
  proof_use:
    used:
      - "canonicalPackageNormalization_idem defines each endpoint Karoubi object and N_C identity"
      - "Karoubi Hom composition provides raw composition and its closure"
      - "canonicalPackageNormalization_absorption proves N(f) is a sandwich morphism and proves N's composition law"
      - "Karoubi.p_comp identifies N applied to an arbitrary sandwich morphism's raw map with that morphism"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.CanonicalNormalizationAbsorption; exit 0"
    - "focused research module check; exit 0"
    - "module terminal namespace audit: 29 current-module declarations, standard axioms only; the 8 D1 declarations were audited independently in Cycle 9"
    - "16 source-level declarations in NormalizationCategory.lean"
  blocking_findings: []
  next_obligation: "D3: construct Kar(V)K, Arr(N_C)→M(E_core), normalized comparison evaluation, pi_N, and pi_N N=pi V"
```

### Cycle 10 acceptance spine

`NormalizedPackageObject` はadmissible packageをlabelとして保ち、そのHomに
`normalizedPackageKaroubiObject P.obj ⟶ normalizedPackageKaroubiObject Q.obj` を使う。
このKaroubi Homの `comm` が固定targetの `e_P ≫ a ≫ e_Q = a` であり、
恒等射と合成のunderlying mapはそれぞれ `e_P` とraw合成になる。
`normalizedPackageKaroubiFunctor` はobjectとHomをそのまま保つため充満忠実である。
`packageNormalizationFunctor` は `f` を `e_P ≫ f` に送り、Cycle 9の吸収式で
sandwich条件と合成則を導く。任意のsandwich射 `a` のraw map自身を逆像に取り、
Karoubiの `p_comp` から充満性を証明する。

Cycle 10 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U`とadmissible package `P,Q`。
- `direction-hypothesis`: なし。
- `discharge-required`: `N_C`、`K`の充満忠実性、`N`の関手性と充満性。Cycle 9の査読済みD1定理とKaroubi構成から放電する。
- `conclusion-equivalent-risk`: 該当なし。`N_C` を `N` の像とせず、任意のsandwich射を直接Homとする。

## Cycle 11 — ambient Karoubi comparison and bottom projection

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 11
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 4edbf8371fc326c1a058290f40ef6e91a2cd6fc1
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 10 result: D2 merged and discharged; D3 selected next"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiFunctor
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor
    - AAT.AG.RealizationComparisonIdempotents.packageProjection_canonicalPackageNormalization
    - AAT.AG.RealizationComparisonIdempotents.arrowKaroubiMap
    - CategoryTheory.Idempotents.functorExtension₂
  proof_obligation: "D3: construct Kar(V)K, the induced Arr(N_C)→M(E_core), the normalized comparison with underlying c e_P, pi_N, and the equality pi_N N=pi V on objects and morphisms"
  selection_reason: "D3 connects the reviewed normalization category to the clause-A comparison surface and fixes the common bottom projection required by the remaining naturality and qualified-group clauses."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationProjection.lean
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageCoreKaroubiFunctor
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageArrowCoreComparison
    - AAT.AG.RealizationComparisonIdempotents.canonicalNormalizedCoreComparison_obj_hom_f
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_normalization_eq
  risks:
    - "constructing a second comparison category instead of using Arrow(Kar(E_core))"
    - "losing the source normalization in the claimed underlying comparison"
    - "assuming pi(e_P)=1 instead of using the reviewed D1 computation"
    - "proving pi_N N=pi V only on objects and omitting morphisms"
  unchecked:
    - "D4: i, objectwise p, naturality characterization, and tagged failure"
    - "D5: endpoint automorphism and qualified subgroup homomorphisms"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed V as the standard full-subcategory inclusion, formed Kar(V)K with mathlib functorExtension₂, and induced the Arrow comparison into M(E_core).  The normalized raw comparison evaluates to e_P≫c, i.e. c e_P in the target notation.  Constructed pi_N from actual base maps and proved pi_N N=pi V as a functor equality with separate object and morphism APIs."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationProjection.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.canonicalNormalizationCoreInclusion
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageCoreKaroubiFunctor
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageArrowCoreComparison
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageArrowCoreComparison_eq
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageArrowCoreComparison_obj_hom_f
    - AAT.AG.RealizationComparisonIdempotents.canonicalNormalizedCoreComparison
    - AAT.AG.RealizationComparisonIdempotents.canonicalNormalizedCoreComparison_obj_hom_f
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_obj
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_map
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_normalization_obj
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_normalization_map
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_normalization_eq
  claim_mapping:
    theorem_names:
      - normalizedPackageArrowCoreComparison_eq
      - normalizedPackageArrowCoreComparison_obj_hom_f
      - canonicalNormalizedCoreComparison_obj_hom_f
      - normalizedPackageProjection_obj
      - normalizedPackageProjection_map
      - normalizedPackageProjection_normalization_obj
      - normalizedPackageProjection_normalization_map
      - normalizedPackageProjection_normalization_eq
    source_labels:
      - "fixed target D paragraph 3: ambient inclusion, comparison, and bottom projection"
    conjuncts:
      - "V:C→E_core -> standard full-subcategory inclusion"
      - "Kar(V)K -> standard functorExtension₂ applied after K"
      - "Arr(N_C)→M(E_core) -> mapArrow followed by arrowKaroubiMap V"
      - "normalized comparison -> underlying e_P≫c, conventional c e_P"
      - "pi_N objects -> packagePoint of the labelled package"
      - "pi_N morphisms -> actual base component of the raw total morphism"
      - "pi_N N=pi V -> equality on both objects and arbitrary morphisms"
    undischarged_assumptions: []
    acceptance_point: "D3 reuses the fixed clause-A Arrow(Kar _) surface and the existing package projection; the morphism equality is discharged by the reviewed pi(e_P)=1 computation rather than a new premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D ambient inclusion and induced Karoubi/Arrow comparison"
      - "D normalized comparison evaluation c e_P"
      - "D bottom projection pi_N and equality pi_N N=pi V"
    remaining:
      - "D4--D5 naturality characterization, tagged failure, and group homomorphisms"
  certificate_provenance:
    discharged:
      - "endpoint idempotents are the reviewed canonicalPackageNormalization values carried through K and Kar(V)"
      - "bottom normalization disappears by the reviewed packageProjection_canonicalPackageNormalization theorem"
    unresolved: []
  proof_use:
    used:
      - "normalizedPackageKaroubiFunctor supplies K before the standard Karoubi action of V"
      - "packageNormalizationFunctor supplies e_P≫c before the Arrow comparison"
      - "the base component of canonicalPackageNormalization reduces to the identity in the morphism proof of pi_N N=pi V"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.NormalizationCategory; exit 0"
    - "focused research module check; exit 0"
    - "module terminal namespace audit: 13 current-module declarations, standard axioms only"
    - "13 source-level declarations in NormalizationProjection.lean"
  blocking_findings: []
  next_obligation: "D4: construct i:KN→J, objectwise p and its splitting, characterize p naturality by the failed two-sided equation and operation coherence, and instantiate the G-117 tagged counterexample"
```

### Cycle 11 acceptance spine

`canonicalNormalizationCoreInclusion` is the standard inclusion of the admissible
full subcategory, and `normalizedPackageCoreKaroubiFunctor` applies mathlib's
Karoubi action after the reviewed fully faithful `K`.  Its Arrow functor is the
required comparison into `M(E_core)`.  Precomposition with `N` exposes the
underlying map as `e_P ≫ c`, exactly `c e_P` in the fixed conventional notation.

`normalizedPackageProjection` reads the existing package point and the actual
base component of every sandwich morphism.  On an arbitrary raw morphism, the
base of `N(f)` is the identity followed by `f.base`; the identity is supplied by
the Cycle 9 theorem `π(e_P)=1`.  Thus the object and morphism computations combine
to the functor equality `π_N N=πV` without a new preservation certificate.

Cycle 11 material premise roles are:

- `ambient-boundary`: arbitrary `U`, admissible packages, and all raw or sandwich morphisms at the displayed endpoints.
- `direction-hypothesis`: none.
- `discharge-required`: the comparison evaluation and the morphism component of `π_N N=πV`; discharged by D2's functor definitions and D1's base computation.
- `conclusion-equivalent-risk`: none; `π_N` is constructed from raw base maps and carries no field asserting the desired functor equality.

## Cycle 12 — one-sided naturality and tagged retraction failure

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 12
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 724a13f0da5421b914aab37453f268599ebf8690
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 11 result: D3 merged and discharged; D4 selected next"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_absorption
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageKaroubiFunctor
    - AAT.AG.DoctrineFiberProduct.canonicalObjectNormalizationTotal_natural_iff_operationCoherent
    - AAT.AG.DoctrineFiberProduct.taggedEndpointFlip_not_natural
  proof_obligation: "D4: construct i:KN→J and objectwise p with p i=1, characterize p naturality by f e_P=e_Q f and CanonicalNormalizationOperationCoherent, and realize its failure on the fixed tagged Bool counterexample"
  selection_reason: "D4 records the exact asymmetry between the universally valid one-sided absorption and the refuted opposite exchange equation before any automorphism-group construction can use normalization."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationNaturalityFailure.lean
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageInclusion
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageInclusion_retraction
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionNaturalAt_iff_operationCoherent
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionNaturalAt_id
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_retraction_not_natural
  risks:
    - "packaging p as a natural transformation and thereby assuming the refuted equation"
    - "reversing the Lean and conventional composition orders"
    - "claiming that i naturality requires the failed operation coherence"
    - "introducing a new counterexample instead of reusing the fixed G-117 tagged witness"
    - "disconnecting the inequality from the existing Bool component evaluations"
  unchecked:
    - "D5: endpoint automorphism and qualified subgroup homomorphisms"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the natural inclusion i from KN to the raw Karoubi embedding J using D1 absorption.  Constructed objectwise reverse maps p and proved their split identity.  Proved p naturality at each raw f iff f≫e_Q=e_P≫f, and iff the exact G-117 operation coherence holds.  Embedded the fixed tagged package and flip in C, retained one-sided absorption and i naturality, refuted p naturality with the existing inequality, and re-exposed the false/true Bool evaluations of the two composites."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationNaturalityFailure.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.rawPackageKaroubiInclusion
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageInclusion
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageInclusion_app_f
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionApp
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionApp_f
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageInclusion_retraction
    - AAT.AG.RealizationComparisonIdempotents.NormalizedPackageRetractionNaturalAt
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionNaturalAt_iff
    - AAT.AG.RealizationComparisonIdempotents.canonicalPackageNormalization_natural_iff_operationCoherent
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionNaturalAt_iff_operationCoherent
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageRetractionNaturalAt_id
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalizationPackage
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalizationFlip
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_absorption
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_inclusion_naturality
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_not_natural
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_retraction_not_natural
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_normalize_then_flip_snd
    - AAT.AG.RealizationComparisonIdempotents.taggedCanonicalNormalization_flip_then_normalize_snd
  claim_mapping:
    theorem_names:
      - normalizedPackageInclusion_app_f
      - normalizedPackageRetractionApp_f
      - normalizedPackageInclusion_retraction
      - normalizedPackageRetractionNaturalAt_iff
      - canonicalPackageNormalization_natural_iff_operationCoherent
      - normalizedPackageRetractionNaturalAt_iff_operationCoherent
      - normalizedPackageRetractionNaturalAt_id
      - taggedCanonicalNormalization_absorption
      - taggedCanonicalNormalization_inclusion_naturality
      - taggedCanonicalNormalization_not_natural
      - taggedCanonicalNormalization_retraction_not_natural
      - taggedCanonicalNormalization_normalize_then_flip_snd
      - taggedCanonicalNormalization_flip_then_normalize_snd
    source_labels:
      - "fixed target D paragraphs 4--5: natural inclusion, objectwise retraction, exact naturality obstruction, and tagged failure"
    conjuncts:
      - "J:C→Kar(C) -> raw identity-idempotent embedding"
      - "i:KN→J -> component raw e_P and universal naturality from one-sided absorption"
      - "p_P:J(P)→KN(P) -> component raw e_P without a false natural-transformation wrapper"
      - "p_P i_P=1_KN(P) -> endpoint idempotence"
      - "p naturality at f -> iff f≫e_Q=e_P≫f"
      - "opposite exchange equation -> iff existing CanonicalNormalizationOperationCoherent"
      - "positive naturality witness -> every identity morphism satisfies the retraction naturality predicate"
      - "tagged package/flip -> actual object and morphism of the same C"
      - "tagged flip -> one-sided absorption and i naturality hold while p naturality fails"
      - "tagged inequality -> the same false/true Bool operation evaluations"
    undischarged_assumptions: []
    acceptance_point: "D4 separates the proved natural inclusion from the merely objectwise reverse maps, proves the exact iff obstruction, and reuses rather than replaces the G-117 counterexample and its computational witness."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D natural inclusion i and objectwise split p"
      - "D exact naturality characterization by exchange and operation coherence"
      - "D fixed tagged counterexample placement, failure, and Bool evaluation connection"
    remaining:
      - "D5 endpoint automorphism and qualified subgroup homomorphisms"
  certificate_provenance:
    discharged:
      - "i naturality is derived from reviewed D1 absorption for arbitrary raw morphisms"
      - "p naturality is tested as an explicit proposition and not stored in the morphism or object interface"
      - "failure is inherited from the fixed G-117 tagged total morphism and its operation-map computation"
    unresolved: []
  proof_use:
    used:
      - "canonicalPackageNormalization_absorption proves the naturality field of i"
      - "canonicalPackageNormalization_idem proves p_P i_P=1 and removes the duplicate source idempotent in the naturality iff"
      - "canonicalObjectNormalizationTotal_natural_iff_operationCoherent transfers the package-level equation to the existing operation condition"
      - "taggedEndpointFlip_not_natural refutes the package-level equation; taggedLeftComposite_snd and taggedRightComposite_snd expose the Bool witness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted builds: NormalizationProjection and LaxDiagnosticProjectorModificationCounterexample; exit 0"
    - "focused research module check; exit 0"
    - "module terminal namespace audit: 19 current-module declarations, standard axioms only"
    - "19 source-level declarations in NormalizationNaturalityFailure.lean"
  blocking_findings: []
  next_obligation: "D5: construct the endpoint automorphism product hom r_N, restrict it to comparison-preserving subgroups, and then to the raw/image bottom-qualified subgroups"
```

### Cycle 12 acceptance spine

`normalizedPackageInclusion` uses `Karoubi.decompId_i` with component `e_P`.
Its naturality square is the D1 sandwich equation and therefore holds for every
raw morphism.  The reverse `Karoubi.decompId_p` maps exist objectwise and split
the inclusion, but are not packaged as a natural transformation.

For each `f`, `NormalizedPackageRetractionNaturalAt f` is proved equivalent to
`f ≫ e_Q = e_P ≫ f`; the extra source projector introduced by `N(f)` is removed
only by endpoint idempotence.  The existing G-117 theorem identifies this exact
equation with `CanonicalNormalizationOperationCoherent`.

The fixed tagged package and endpoint flip are then lifted into the same full
subcategory `C`.  D1 absorption and `i` naturality remain valid, while the
opposite equation and `p` naturality fail.  The two composites retain the
existing `false` and `true` evaluations on `taggedBoolOperation`, so the failure
is connected to the same computational witness rather than a new proposition.

Cycle 12 material premise roles are:

- `ambient-boundary`: arbitrary `U`, arbitrary admissible endpoints and raw morphisms; the final refutation specializes only to the fixed tagged witness required by the target.
- `direction-hypothesis`: none.
- `discharge-required`: naturality of `i`, splitting of `p`, both iff characterizations, and tagged failure; each is discharged by reviewed D1/G-117 declarations.
- `conclusion-equivalent-risk`: none; no naturality field is added to `p`, and operation coherence remains an equivalent tested proposition rather than an input.

## Cycle 13 — normalization on comparison-preserving automorphism groups

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 13
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: 0973ecc6e7e1096c83f4af794d327d8df0614b0a
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 12 result: D4 merged and discharged; D5 is the sole remaining target obligation"
  proof_dag_predecessors:
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor
    - AAT.AG.RealizationComparisonIdempotents.packageNormalizationFunctor_full
    - AAT.AG.RealizationComparisonIdempotents.normalizedPackageProjection_normalization_map
    - CategoryTheory.Functor.mapIso
    - Subgroup.comap
  proof_obligation: "D5: construct r_N on the full product of endpoint automorphism groups, restrict it from raw to normalized comparison-preserving subgroups, and restrict again to the subgroups qualified by endpoint identity under pi V and pi_N"
  selection_reason: "D5 is the last fixed D clause; it must record preservation without claiming the reflection or lift-surjectivity explicitly deferred to S2 and S4."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationComparisonGroup.lean
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphismHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationComparisonSubgroupHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationBaseQualifiedComparisonSubgroupHom
  risks:
    - "defining r_N only on a selected subgroup instead of all endpoint automorphisms"
    - "reversing p c=c b under the Aut multiplication convention"
    - "assuming comparison preservation rather than transporting it by N.map_comp"
    - "using the same bottom functor on both sides instead of pi V and pi_N respectively"
    - "claiming reflection, injectivity, or lift surjectivity assigned to S2/S4"
  unchecked:
    - "fixed-head Cycle 13 four-lane review"
    - "schema-complete final completion review across A--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed r_N by the standard functor action on both full endpoint automorphism groups.  Defined the raw p≫c=c≫b and normalized N(p)≫N(c)=N(c)≫N(b) subgroups and proved functorial preservation, yielding a subgroup homomorphism.  Defined raw endpoint qualification through pi V and normalized qualification through pi_N as kernel comaps, used the D3 morphism equality pi_N N=pi V to preserve both endpoint identities, and restricted the subgroup homomorphism accordingly.  No reflection or lift-surjectivity statement is made."
  completion_candidate: yes
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationComparisonGroup.lean
  evidence:
    - AAT.AG.RealizationComparisonIdempotents.functorAutomorphismHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphismHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphismHom_fst_hom
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphismHom_snd_hom
    - AAT.AG.RealizationComparisonIdempotents.rawNormalizationComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.mem_rawNormalizationComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.normalizedComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.mem_normalizedComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphism_preserves_comparison
    - AAT.AG.RealizationComparisonIdempotents.normalizationComparisonSubgroupHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationComparisonSubgroupHom_val
    - AAT.AG.RealizationComparisonIdempotents.rawNormalizationComparisonSourceHom
    - AAT.AG.RealizationComparisonIdempotents.rawNormalizationComparisonTargetHom
    - AAT.AG.RealizationComparisonIdempotents.normalizedComparisonSourceHom
    - AAT.AG.RealizationComparisonIdempotents.normalizedComparisonTargetHom
    - AAT.AG.RealizationComparisonIdempotents.rawNormalizationBottomAutomorphismHom
    - AAT.AG.RealizationComparisonIdempotents.rawNormalizationBottomAutomorphismHom_hom
    - AAT.AG.RealizationComparisonIdempotents.normalizedBottomAutomorphismHom
    - AAT.AG.RealizationComparisonIdempotents.normalizedBottomAutomorphismHom_hom
    - AAT.AG.RealizationComparisonIdempotents.rawBaseQualifiedNormalizationComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.mem_rawBaseQualifiedNormalizationComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.normalizedBaseQualifiedComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.mem_normalizedBaseQualifiedComparisonSubgroup
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphism_preserves_bottom
    - AAT.AG.RealizationComparisonIdempotents.normalizationBaseQualifiedComparisonSubgroupHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationBaseQualifiedComparisonSubgroupHom_val
  claim_mapping:
    theorem_names:
      - normalizationEndpointAutomorphismHom_fst_hom
      - normalizationEndpointAutomorphismHom_snd_hom
      - mem_rawNormalizationComparisonSubgroup
      - mem_normalizedComparisonSubgroup
      - normalizationEndpointAutomorphism_preserves_comparison
      - normalizationComparisonSubgroupHom
      - mem_rawBaseQualifiedNormalizationComparisonSubgroup
      - mem_normalizedBaseQualifiedComparisonSubgroup
      - normalizationEndpointAutomorphism_preserves_bottom
      - normalizationBaseQualifiedComparisonSubgroupHom
    source_labels:
      - "fixed target D paragraph 6: endpoint automorphism, comparison-preserving, and bottom-qualified subgroup homomorphisms"
    conjuncts:
      - "r_N domain -> all Aut_C(P)×Aut_C(Q), not a selected subset"
      - "r_N codomain -> all normalized endpoint automorphism pairs"
      - "raw comparison subgroup -> p≫c=c≫b"
      - "normalized comparison subgroup -> N(p)≫N(c)=N(c)≫N(b)"
      - "comparison subgroup hom -> preservation follows from N.map_comp"
      - "comparison subgroup hom evaluation -> its underlying endpoint pair is the full r_N value"
      - "raw bottom qualification -> both endpoint homs become identities under pi V"
      - "normalized bottom qualification -> both endpoint homs become identities under pi_N"
      - "qualified restriction -> preservation follows from pi_N N=pi V on each endpoint"
      - "qualified restriction evaluation -> its underlying comparison pair is the first restriction value"
      - "scope limit -> no reflection, injectivity, or lift-surjectivity claim"
    undischarged_assumptions: []
    acceptance_point: "D5 uses the full endpoint automorphism groups and standard subgroup kernels, transports comparison preservation by functoriality and bottom qualification by the reviewed D3 equality, and stops exactly before the S2/S4 reflection and lifting questions."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D full endpoint product hom r_N"
      - "D raw-to-normalized comparison-preserving subgroup hom"
      - "D restriction to the pi V / pi_N bottom-qualified subgroups"
    remaining:
      - "independent fixed-head Cycle 13 review"
      - "schema-complete final completion review"
  certificate_provenance:
    discharged:
      - "endpoint automorphisms are mapped by the existing normalization functor's mapIso, not by a selected witness"
      - "comparison preservation is inherited from the raw subgroup equation through Functor.map_comp"
      - "bottom preservation is inherited from the D3 equality pi_N N=pi V"
    unresolved: []
  proof_use:
    used:
      - "Functor.map_id and map_comp prove the full endpoint automorphism group homomorphisms"
      - "congrArg of packageNormalizationFunctor.map transports p≫c=c≫b to the normalized comparison equation"
      - "normalizedPackageProjection_normalization_map transports each raw bottom-kernel identity to the normalized bottom kernel"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.RealizationComparisonIdempotents.NormalizationNaturalityFailure; exit 0"
    - "focused research module check; exit 0"
    - "module terminal namespace audit: 26 current-module declarations, standard axioms only"
    - "26 source-level declarations in NormalizationComparisonGroup.lean"
  blocking_findings: []
  next_obligation: "after Cycle 13 acceptance, generate and independently review the schema-complete G-119 completion packet across fixed target A--D"
```

### Cycle 13 acceptance spine

`normalizationEndpointAutomorphismHom` is defined on the full product
`Aut_C(P) × Aut_C(Q)` by applying `N.mapIso` at each endpoint.  The raw and
normalized comparison subgroups use the literal equations `p ≫ c = c ≫ b`
and `N(p) ≫ N(c) = N(c) ≫ N(b)`.  Applying `N.map` to the first equation and
using `map_comp` proves that `r_N` restricts to a group homomorphism between
these subgroups.

Raw bottom qualification is the intersection of the two kernel comaps for the
endpoint actions of `πV`; normalized qualification uses the corresponding
actions of `π_N`.  The D3 morphism equality rewrites each `π_N(N(a))` to
`πV(a)`, so the comparison subgroup hom restricts again to the two qualified
subgroups.  These standard subgroup constructions carry only the equations
specified by the target and add no reflection or lifting certificate.

Cycle 13 material premise roles are:

- `ambient-boundary`: arbitrary `U`, arbitrary admissible `P,Q`, arbitrary raw comparison `c`, and all endpoint automorphisms.
- `direction-hypothesis`: none.
- `discharge-required`: comparison preservation and both endpoint bottom identities; discharged respectively by `N.map_comp` and `π_N N=πV`.
- `conclusion-equivalent-risk`: none; comparison and qualification are subgroup membership conditions, and the preservation maps are proved rather than supplied by callers.

## Cycle 14 — fixed-target completion audit

```yaml
ledger_type: target_cycle_result
goal: G-119-aat-realization-comparison-idempotents
cycle: 14
goal_blob_sha: 83b7efa5a097143b8a12d575955eb5c4a76c54a4
base_oid: c1a63e7f67e07e6a3bc1b8d02ff6d627bf192be0
tracking_issue: 4416
report_path: research/reports/G-119-aat-realization-comparison-idempotents.md
selection:
  proof_state_ref: "Issue #4416 Cycle 13 result and completion-audit reset comment 5605317972"
  proof_dag_predecessors:
    - "Cycles 1--13 accepted Lean declarations and review records"
    - ".codex/skills/target-theorem-loop/references/completion-ledger.md blob 52af37a4f0bdbe839c7839875057c0a53280929c restored by PR #4435 and selected by Issue #4416 comment 5605317972"
    - "PR #4435 merge c1a63e7f67e07e6a3bc1b8d02ff6d627bf192be0, restoring the hand-written completion audit"
  proof_obligation: "assemble the fixed-target A--D final packet, run the standard PR review and a separate fresh Math A / Math B / Lean A / Lean B completion review, and issue the formal completion verdict"
  selection_reason: "All mathematical clauses A--D are individually accepted. The remaining obligation is the fail-closed whole-GOAL comparison required before target-theorem-proved."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiExchange.lean
    - research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationComparisonGroup.lean
  risks:
    - "reusing per-cycle review as the required fresh whole-GOAL review"
    - "treating CI or declaration existence as mathematical completion"
    - "omitting a target clause, material premise, proof-use edge, direction, or fixed tagged evaluation"
    - "reviving the withdrawn generated packet or pattern-2 receipt as completion evidence"
  unchecked:
    - "same-head standard PR review"
    - "schema-complete hand-written final packet"
    - "fresh four-lane final math-lean-review"
    - "formal completion ledger, CI, merge, and lifecycle synchronization"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Cycle 13 acceptance and the restored hand-written audit route are synchronized. No new mathematical declaration or premise is introduced."
  completion_candidate: yes
  lean_artifacts: []
  evidence:
    - "Issue #4416 Cycle 13 acceptance comment 5594157652"
    - "Issue #4416 completion-audit reset comment 5605317972"
  claim_mapping:
    theorem_names: []
    source_labels:
      - "fixed target A--D and its completion conditions"
    conjuncts:
      - "This cycle changes audit state only; all mathematical evidence remains in the accepted Cycle 1--13 artifacts."
    undischarged_assumptions: []
    acceptance_point: "The candidate remains target-proof-checkpoint until every completion gate passes on one fixed head."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "whole-GOAL final packet and independent final review"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used: []
    unused:
      - "Cycle 1--13 report entries are indices for the whole-GOAL recheck, not Cycle 14 proof-use evidence."
      - "withdrawn generated completion packets and pattern-2 receipts"
  structure_field_escape: cannot-determine
  route_integrity: cannot-determine
  target_fitting: cannot-determine
  vacuity: cannot-determine
  one_way_as_equivalence: cannot-determine
  goal_or_report_reinterpretation: cannot-determine
  validation_refs:
    - "focused checks, declaration audits, and CI remain to be fixed on the completion PR head"
  blocking_findings: []
  next_obligation: "fix the audit PR head, run standard review, post the hand-written final packet, and run four fresh completion-review lanes"
```
