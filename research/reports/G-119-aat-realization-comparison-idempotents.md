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
- current proof obligation: C のraw mateからのKaroubi交換
- pending proof obligations: C、D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: raw mate α と冪等対からA左辺の対象を構成し、そのT像を既存Karoubi比較へ同定

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
