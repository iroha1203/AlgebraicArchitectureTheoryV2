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
- current proof obligation: B の恒等冪等埋込みとqualified比較群
- pending proof obligations: B、C、D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: B の任意の幾何比較をM(E_geom)へ埋め、qualifiedComparisonSubgroupとの群同型を固定

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
      - crossStageKaroubiProjection_obj_p
      - crossStageComparisonProjection_obj_hom_f
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
    - "module terminal axiom audit: 40 declarations, standard axioms only"
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
