# G-125-aat-obstruction-diagnostic-bridge — 障害類と診断を結ぶ比較

- 一次仕様: [`research/goals/G-125-aat-obstruction-diagnostic-bridge.md`](../goals/G-125-aat-obstruction-diagnostic-bridge.md)
- tracking Issue: [#4791](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4791)
- 固定 GOAL commit: `cc69ecee0e8e04d2f1cb364cbb697bb1112e1793`
- 固定 GOAL blob: `1e8df2624cf35704299c2cf47a879f2dc6565b03`
- 共通基準・既存宣言の解決 commit: `cc69ecee0e8e04d2f1cb364cbb697bb1112e1793`
- proof state: `target-proof-checkpoint`

このreportは固定GOALの証拠索引とproof obligation deltaを記録する。固定targetと
完了条件はGOALカードにあり、このreportでは再定義しない。

## Proof obligation state

- 完了: 紙上設計 §1–2 の生成子関係から `B = π₀(R)` と既存の
  `LawValueLabel` への写像を構成し、構造条件 `R_q` から `B ≃ Λ` を導出する。
- 完了: 紙上設計 §6 の有理0-cochainの辺差が整数なら、座標ごとのfloorから
  同じ辺差を持つ整数0-cochainを構成する。`blockLabel : B → Λ` で診断座標を読む
  block-indexed APIも構成したが、`R_q` の実質使用と実診断零類からの証人生成は未完了。
- 完了: primitive relationが生成する自由アーベル群上の最小加法合同から
  presentation group `M_R` を構成し、`M_R ≃+ ℤ^(B)` を導出する。
- 完了: `M_R ≃+ ℤ^(B)` と `blockLabel : B → Λ` から係数比較
  `ε_R : M_R →+ (Λ → ℚ)` を構成し、`R_q` の下で単射性を導出する。
- 未完了: Aの実障害複体・診断複体と次数0–2の比較写像。
- 未完了: B1・B2、C1・C2、同一入力上の有限例、論文対応、最終検証・査読。
- 次のproof obligation: 係数比較を実障害cochainとlaw-generated診断cochainへ
  cellwiseに持ち上げ、次数0–2のcochain mapを構成する。

## Cycle 1 — 生成子関係成分と Law-value label の比較

```yaml
ledger_type: target_cycle_result
goal: G-125-aat-obstruction-diagnostic-bridge
cycle: 1
goal_blob_sha: 1e8df2624cf35704299c2cf47a879f2dc6565b03
base_oid: 8dd01cbce46be3e6e143e488e8ef7a2d25af9b28
tracking_issue: 4791
report_path: research/reports/G-125-aat-obstruction-diagnostic-bridge.md
selection:
  proof_state_ref: "Issue #4791 initial proof state and paper design sections 1-2"
  proof_dag_predecessors:
    - "ResolutionInvariance.LawValueLabel: introduction commit c25a2b8471abc3d8e79db04098b7d63b631516a5; G-104 Cycle 10; accepted in PR #3943, merge 0fdc9867c5b383f276800ff9ebfe976141aac5c3; unchanged through fixed GOAL commit"
  proof_obligation: "derive the relation-component to law-value-label equivalence from primitive generator relations and R_q"
  selection_reason: "this is the first unproved coefficient provenance step used by the later comparison map and zero-class reflection"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "ResearchLean/AG/ObstructionDiagnosticBridge/GeneratorPresentation.lean"
    - "GeneratorPresentation.blockLabelEquiv"
  risks:
    - "defining components by label equality would fit the target instead of deriving them from primitive relations"
    - "placing injectivity inside the presentation would make R_q conclusion-equivalent"
    - "copying the diagnostic label type would leave the existing generated complex unconnected"
  unchecked:
    - "fixed-head independent review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Primitive law-source generators and their relation closure now generate B; relation preservation descends the existing LawValueLabel to B; R_q derives injectivity and hence B equivalence Lambda. Positive and negative R_q fixtures establish nonvacuity."
  completion_candidate: no
  lean_artifacts:
    - "ObstructionDiagnosticBridge.PrimitiveGenerator"
    - "ObstructionDiagnosticBridge.GeneratorPresentation"
    - "GeneratorPresentation.Related"
    - "GeneratorPresentation.Block"
    - "GeneratorPresentation.blockLabel"
    - "GeneratorPresentation.ReflectionCondition"
    - "GeneratorPresentation.blockLabelEquiv"
    - "ReflectionConditionFixtures.connected_reflectionCondition"
    - "ReflectionConditionFixtures.disconnected_not_reflectionCondition"
  evidence:
    - "blockLabel is a Quotient lift justified by related_preserves_label"
    - "blockLabel_surjective is derived from LawValueLabel.generated"
    - "blockLabel_injective uses only R_q and Quotient.sound"
    - "the positive fixture relates distinct generators; the empty-relation fixture refutes R_q"
  claim_mapping:
    theorem_names:
      - "GeneratorPresentation.blockLabelEquiv"
    source_labels:
      - "GOAL A coefficient generators and relations"
      - "GOAL B structural reflection condition R_q"
      - "Issue #4791 paper design sections 1-2"
    conjuncts:
      - "primitive relations generate B -> GeneratorPresentation.Block"
      - "relations preserve law values -> related_preserves_label and blockLabel"
      - "R_q -> B equivalent to Lambda -> blockLabelEquiv"
    undischarged_assumptions:
      - "relation_preserves_label is an input condition of the general presentation; the selected G-125 input and fixed finite example must construct it from their primitive relations"
      - "ReflectionCondition is a direction hypothesis of the general theorem; the selected input and fixed finite example must prove it from their primitive relations"
    acceptance_point: "R_q is a generator-connectivity condition and the equivalence is derived from it; no cohomology conclusion is stored in data"
    port_status: not-applicable
audits:
  material_premises:
    ambient_boundary:
      - "FiniteLawFamily, Source, and the primitive relation are input data"
      - "LawValueLabel.generated is reviewed predecessor data used to construct label representatives"
    direction_hypothesis:
      - "relation_preserves_label supplies quotient-map well-definedness in the general presentation"
      - "ReflectionCondition supplies injectivity in the general equivalence theorem"
    discharge_required:
      - "the selected G-125 input and fixed finite example must construct relation_preserves_label from their declared graphs"
      - "the selected input and fixed finite example must prove ReflectionCondition from their declared graph"
    conclusion_equivalent_risk:
      - "ReflectionCondition is equivalent to injectivity of the already-surjective blockLabel, but is admitted here because fixed paper design section 2 requires generator connectivity; it contains neither B2 nor Phi_q injectivity"
  premise_delta:
    discharged:
      - "for any presentation satisfying relation_preserves_label, relation closure preserves actual source-generated law-value labels"
      - "for any presentation satisfying ReflectionCondition, R_q derives B equivalent to Lambda"
    remaining:
      - "construct relation_preserves_label and ReflectionCondition for the selected G-125 input and fixed finite example"
      - "integer presentation group and coefficient comparison"
      - "A1, B1, B2, C1, C2 and the fixed finite example"
  certificate_provenance:
    discharged:
      - "Lambda reuses LawValueLabel and its generated source witness"
      - "B is the Quotient of Relation.EqvGen on declared primitive relations"
    unresolved: []
  proof_use:
    used:
      - "relation_preserves_label is used by the quotient lift"
      - "ReflectionCondition is used by blockLabel_injective"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/ObstructionDiagnosticBridge/GeneratorPresentation.lean: pass; 36 namespace declarations, standard axioms only"
    - "reported declarations #print axioms: propext, Classical.choice, Quot.sound only"
    - "git diff --check: pass"
    - "placeholder, hidden/BiDi Unicode, private-path, and Formal-to-Research import scans: clean"
  blocking_findings: []
  next_obligation: "construct the integral coefficient comparison and the rational-to-integral correction lemma used by B2"
```

## Cycle 2 — 有理 coboundary 証人の整数化

```yaml
ledger_type: target_cycle_result
goal: G-125-aat-obstruction-diagnostic-bridge
cycle: 2
goal_blob_sha: 1e8df2624cf35704299c2cf47a879f2dc6565b03
base_oid: dfcc02b073ac1b8cc7d7c76533dcac24827cf24b
tracking_issue: 4791
report_path: research/reports/G-125-aat-obstruction-diagnostic-bridge.md
selection:
  proof_state_ref: "Issue #4791 paper design section 6 and Cycle 1 merge dfcc02b073ac1b8cc7d7c76533dcac24827cf24b"
  proof_dag_predecessors:
    - "GeneratorPresentation.blockLabel: PR #4799, merge dfcc02b073ac1b8cc7d7c76533dcac24827cf24b, fixed-head audit https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4799#issuecomment-5742401350"
    - "Int.floor_add_intCast from the pinned mathlib dependency"
  proof_obligation: "construct an integral zero-cochain from a rational witness whose edge differences are integral, with a block-indexed API through the existing blockLabel map"
  selection_reason: "this is the arithmetic kernel of B2 and the paper design's next recommended module after the generator presentation"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean"
    - "IntegralReflection.exists_integral_correction"
    - "GeneratorPresentation.exists_block_integral_correction"
  risks:
    - "treating floor as an additive homomorphism would assert a false general coefficient retraction"
    - "assuming an integral correction would make zero-class reflection circular"
    - "mistaking forward blockLabel use for material use of the R_q-derived equivalence would overstate the Cycle 1 connection"
  unchecked:
    - "fixed-head independent review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "A rational vertex witness with integral edge differences now constructs an integral vertex correction by floor. The block specialization reads diagnostic coordinates through blockLabel only; material use of R_q and the inverse B equivalent Lambda remains a later obligation. No additive inverse from rationals to integers or H1 injectivity premise is introduced."
  completion_candidate: no
  lean_artifacts:
    - "IntegralReflection.floorCorrection"
    - "IntegralReflection.floorCorrection_edgeDifference"
    - "IntegralReflection.exists_integral_correction"
    - "GeneratorPresentation.blockFloorCorrection"
    - "GeneratorPresentation.blockFloorCorrection_edgeDifference"
    - "GeneratorPresentation.exists_block_integral_correction"
    - "IntegralReflectionFixtures.rationalWitness_edgeDifference"
    - "IntegralReflectionFixtures.source_value_not_integral"
  evidence:
    - "floorCorrection_edgeDifference uses only the supplied rational edge equation and Int.floor_add_intCast"
    - "exists_block_integral_correction indexes b by LawValueLabel through the quotient map blockLabel without requiring R_q"
    - "the fixture uses rational values 1/2 and 3/2, proves the source value is not integral, and recovers the nonzero integer edge difference 1"
  claim_mapping:
    theorem_names:
      - "IntegralReflection.exists_integral_correction"
      - "GeneratorPresentation.exists_block_integral_correction"
    source_labels:
      - "GOAL B2 zero-class reflection"
      - "Issue #4791 paper design section 6 equations (7)-(8)"
    conjuncts:
      - "floor the supplied rational zero-cochain -> IntegralReflection.floorCorrection"
      - "integer rational edge difference is preserved -> floorCorrection_edgeDifference"
      - "blockLabel indexes the diagnostic witness without claiming R_q use -> exists_block_integral_correction"
    undischarged_assumptions:
      - "the later diagnostic comparison must supply the rational edge-difference witness h from diagnostic zero-class data"
      - "full B2 must use R_q materially when deriving the per-block edge equation h from diagnostic label-coordinate data"
    acceptance_point: "the theorem extracts one integral coboundary witness from one rational witness; it does not define an additive rational-to-integer inverse or assume obstruction zero-class reflection"
    port_status: not-applicable
audits:
  material_premises:
    ambient_boundary:
      - "Vertex, Edge, Block, source, target, the integral edge cochain z, and the supplied rational witness b are input data"
      - "the block-indexed API additionally receives laws and GeneratorPresentation P; P.relation_preserves_label is the Cycle 1 predecessor premise making blockLabel well-defined"
    direction_hypothesis:
      - "h states that the supplied rational zero-cochain has the cast integral edge cochain as its edge difference"
    discharge_required:
      - "B1 and the actual diagnostic complex must construct h from a diagnostic zero-class witness"
      - "the later B2 bridge must use R_q to turn diagnostic label-coordinate data into the per-block premise h"
    conclusion_equivalent_risk:
      - "h is diagnostic-side rational coboundary data, not the integral correction concluded by the theorem; the latter is constructed by floor"
  premise_delta:
    discharged:
      - "rational edge differences known to be integral have an explicitly constructed integral correction"
      - "the block-indexed API reads diagnostic coordinates through the Cycle 1 quotient map blockLabel"
    remaining:
      - "construct M_R equivalent to the free integer coefficients on relation components"
      - "construct the actual coefficient and cochain comparison maps"
      - "A1, B1, full B2, C1, C2 and the fixed finite example"
  certificate_provenance:
    discharged:
      - "the integral correction is the coordinatewise floor of the supplied rational witness"
      - "the block coordinate is read by the Cycle 1 quotient map blockLabel, not a new certificate field"
    unresolved:
      - "construct h from actual diagnostic zero-class data"
      - "use the R_q-derived equivalence materially in the full B2 bridge"
  proof_use:
    used:
      - "h is rearranged into b(target) = b(source) + z and consumed by Int.floor_add_intCast"
      - "blockLabel selects the diagnostic coordinate of each obstruction block"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass-for-selected-arithmetic-kernel
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: not-applicable
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean: pass; 16 namespace declarations, standard axioms only"
    - "main declarations #print axioms: propext, Classical.choice, Quot.sound only"
    - "git diff --check and placeholder, hidden/BiDi Unicode, private-path, vocabulary, and Formal-to-Research import scans: pass"
  blocking_findings: []
  next_obligation: "construct the integer presentation group, its relation-component normal form, and the resulting integral-to-rational law-value coefficient comparison"
```

## Cycle 3 — 整数presentation groupの成分標準形

```yaml
ledger_type: target_cycle_result
goal: G-125-aat-obstruction-diagnostic-bridge
cycle: 3
goal_blob_sha: 1e8df2624cf35704299c2cf47a879f2dc6565b03
base_oid: 5dbcd31fb683f4d18c7617c3790376e1f147b79a
tracking_issue: 4791
report_path: research/reports/G-125-aat-obstruction-diagnostic-bridge.md
selection:
  proof_state_ref: "Issue #4791 paper design section 1 and Cycle 2 merge 5dbcd31fb683f4d18c7617c3790376e1f147b79a"
  proof_dag_predecessors:
    - "GeneratorPresentation.Block and Related: PR #4799, merge dfcc02b073ac1b8cc7d7c76533dcac24827cf24b"
    - "GeneratorPresentation primitive relation presentation from the fixed GOAL path"
  proof_obligation: "derive M_R equivalent to the free abelian group on relation components B from the primitive generator relations"
  selection_reason: "this discharges the coefficient provenance step required before constructing the integral-to-rational law-value comparison"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean"
    - "GeneratorPresentation.presentationGroupEquivBlocks"
  risks:
    - "defining M_R directly as the free group on B would bypass the primitive presentation"
    - "accepting the normal-form equivalence as input would make the result certificate-driven"
    - "quotienting by an arbitrary supplied congruence could identify more elements than the declared relations generate"
  unchecked:
    - "fixed-head independent review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The least additive congruence generated by declared primitive generator pairs now defines M_R. Maps in both directions between M_R and the free abelian group on B are constructed and proved inverse, deriving M_R equivalent to the direct-sum group Z^(B) without an equivalence certificate."
  completion_candidate: no
  lean_artifacts:
    - "GeneratorPresentation.presentationRelation"
    - "GeneratorPresentation.presentationCongruence"
    - "GeneratorPresentation.PresentationGroup"
    - "GeneratorPresentation.generatorClass_eq_of_related"
    - "GeneratorPresentation.presentationToBlocks"
    - "GeneratorPresentation.blocksToPresentation"
    - "GeneratorPresentation.presentationGroupEquivBlocks"
    - "PresentationGroupFixtures.connected_distinct_generator_classes_equal"
  evidence:
    - "presentationCongruence is addConGen of the declared primitive-relation basis pairs"
    - "presentationCongruence_le_ker_generatorToBlock is proved by induction over generated additive congruence"
    - "both composite homomorphisms are identities by quotient and free-abelian-group extensionality"
    - "the fixture proves two distinct related primitive generators have equal presentation classes"
  claim_mapping:
    theorem_names:
      - "GeneratorPresentation.presentationGroupEquivBlocks"
    source_labels:
      - "GOAL A coefficient presentation"
      - "Issue #4791 paper design section 1"
    conjuncts:
      - "free group on primitive generators -> FreeAbelianGroup (PrimitiveGenerator laws)"
      - "quotient by declared generator relations -> presentationCongruence and PresentationGroup"
      - "normal form indexed by connected components -> presentationGroupEquivBlocks"
    undischarged_assumptions: []
    acceptance_point: "the quotient congruence is generated from primitive relations and the equivalence to the component basis is derived by explicit inverse homomorphisms"
    port_status: not-applicable
audits:
  material_premises:
    ambient_boundary:
      - "FiniteLawFamily and GeneratorPresentation are input data from Cycle 1"
      - "the component type B is the quotient of Relation.EqvGen generated by P.relation"
    direction_hypothesis: []
    discharge_required: []
    conclusion_equivalent_risk:
      - "no normal-form equivalence or inverse map is stored in presentation data"
  premise_delta:
    discharged:
      - "the integer presentation group generated by primitive relations has component-basis normal form"
    remaining:
      - "construct the integral-to-rational law-value coefficient comparison using B equivalent Lambda"
      - "construct actual obstruction and diagnostic cochain complexes and degree 0-2 comparison maps"
      - "A1, B1, full B2, C1, C2 and the fixed finite example"
  certificate_provenance:
    discharged:
      - "M_R is a generated quotient, not a supplied quotient certificate"
      - "the two inverse homomorphisms are constructed from quotient and free universal properties"
    unresolved: []
  proof_use:
    used:
      - "the primitive relation is consumed by AddConGen.Rel.of"
      - "Relation.EqvGen connectivity makes blockGenerator well-defined"
      - "the generated-congruence induction is used to descend generatorToBlock"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean: pass; 17 namespace declarations, standard axioms only"
    - "main declarations #print axioms: propext, Classical.choice, Quot.sound only"
    - "git diff --check and placeholder, hidden/BiDi Unicode, private-path, and Formal-to-Research import scans: pass"
  blocking_findings: []
  next_obligation: "construct the integral-to-rational law-value coefficient comparison from presentationGroupEquivBlocks and blockLabelEquiv"
```

## Cycle 4 — 整数係数から有理Law-value係数への比較

```yaml
ledger_type: target_cycle_result
goal: G-125-aat-obstruction-diagnostic-bridge
cycle: 4
goal_blob_sha: 1e8df2624cf35704299c2cf47a879f2dc6565b03
base_oid: 78534435b39c58cc94aaad65d38b3f30cc0913f7
tracking_issue: 4791
report_path: research/reports/G-125-aat-obstruction-diagnostic-bridge.md
selection:
  proof_state_ref: "Issue #4791 paper design sections 1-2 and equations (4)-(5), after Cycle 3 merge 78534435b39c58cc94aaad65d38b3f30cc0913f7"
  proof_dag_predecessors:
    - "GeneratorPresentation.blockLabel and blockLabel_injective: PR #4799, merge dfcc02b073ac1b8cc7d7c76533dcac24827cf24b"
    - "GeneratorPresentation.presentationGroupEquivBlocks: PR #4802, merge 78534435b39c58cc94aaad65d38b3f30cc0913f7"
  proof_obligation: "construct epsilon_R from presentation classes to rational law-value coefficients and derive its injectivity from R_q"
  selection_reason: "this is the coefficient-level map required before lifting the comparison cellwise to the actual obstruction and diagnostic cochain complexes"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean"
    - "GeneratorPresentation.coefficientComparison"
    - "GeneratorPresentation.coefficientComparison_injective"
  risks:
    - "assuming a coefficient isomorphism between integer obstruction coefficients and rational diagnostic coefficients"
    - "storing injectivity as a field instead of deriving it from R_q"
    - "using R_q only syntactically while moving the real reflection obligation into an input equality"
  unchecked:
    - "fixed-head independent review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The coefficient map sends each primitive presentation generator to the rational delta function at its generated law-value label. Under R_q, evaluating at a block's label recovers its embedded integer coefficient, so the map is injective. A disconnected fixture proves that injectivity can fail without R_q."
  completion_candidate: no
  lean_artifacts:
    - "GeneratorPresentation.blockToLawCoefficients"
    - "GeneratorPresentation.blockToLawCoefficients_apply_eq_fiberSum"
    - "GeneratorPresentation.blockToLawCoefficients_apply_blockLabel"
    - "GeneratorPresentation.blockToLawCoefficients_injective"
    - "GeneratorPresentation.coefficientComparison"
    - "GeneratorPresentation.coefficientComparison_generatorClass_apply"
    - "GeneratorPresentation.coefficientComparison_injective"
    - "CoefficientComparisonFixtures.connected_coefficientComparison_injective"
    - "CoefficientComparisonFixtures.disconnected_blockToLawCoefficients_not_injective"
    - "CoefficientComparisonFixtures.disconnected_coefficientComparison_not_injective"
  evidence:
    - "coefficientComparison_generatorClass_apply proves equation (4) on every primitive generator and law-value coordinate"
    - "blockToLawCoefficients_apply_eq_fiberSum proves equation (5) for every component normal-form element and law-value coordinate"
    - "blockToLawCoefficients_apply_blockLabel uses blockLabel_injective hReflection to isolate one block coefficient"
    - "coefficientComparison_injective composes coefficient recovery with the Cycle 3 presentation normal-form equivalence"
    - "the negative fixture has two distinct relation components with one common law-value label and proves noninjectivity of the full presentation coefficient comparison"
  claim_mapping:
    theorem_names:
      - "GeneratorPresentation.coefficientComparison_generatorClass_apply"
      - "GeneratorPresentation.blockToLawCoefficients_apply_eq_fiberSum"
      - "GeneratorPresentation.coefficientComparison_injective"
    source_labels:
      - "GOAL A coefficient comparison"
      - "GOAL B structural reflection condition R_q"
      - "Issue #4791 paper design equations (4)-(5) and section 2"
    conjuncts:
      - "primitive class maps to delta at e(g) -> coefficientComparison_generatorClass_apply"
      - "general component coefficients map by the finite blockLabel-fiber sum -> blockToLawCoefficients_apply_eq_fiberSum"
      - "R_q separates relation components by law-value labels -> blockToLawCoefficients_apply_blockLabel"
      - "coefficient equality reflects presentation equality -> coefficientComparison_injective"
    undischarged_assumptions:
      - "selected G-125 input and fixed finite example must prove ReflectionCondition from their declared primitive relations"
    acceptance_point: "the map exists without R_q; only the injectivity theorem assumes R_q and consumes it through blockLabel_injective"
    port_status: not-applicable
audits:
  material_premises:
    ambient_boundary:
      - "FiniteLawFamily and GeneratorPresentation are Cycle 1 input data"
      - "the presentation normal form and blockLabel are reviewed predecessor constructions"
    direction_hypothesis:
      - "ReflectionCondition supplies injectivity of blockLabel and is used to recover each block coefficient"
    discharge_required:
      - "construct ReflectionCondition for the selected input and fixed finite example"
    conclusion_equivalent_risk:
      - "ReflectionCondition concerns primitive generator connectivity, not coefficient or H1 injectivity"
  premise_delta:
    discharged:
      - "construct the presentation-to-rational-law-value coefficient map"
      - "derive coefficient-level injectivity from R_q"
      - "show by a negative fixture that R_q cannot be dropped in general"
    remaining:
      - "lift epsilon_R to the actual degree 0-2 obstruction and diagnostic cochain complexes"
      - "A1, B1, full B2, C1, C2 and the fixed finite example"
  certificate_provenance:
    discharged:
      - "each target delta coordinate is computed from the source-generated blockLabel"
      - "integer coefficients are recovered via FreeAbelianGroup.coeff after applying R_q"
    unresolved:
      - "selected-input and fixed-example construction of R_q"
  proof_use:
    used:
      - "presentationToBlocks consumes the Cycle 3 quotient normal form"
      - "blockLabel_injective hReflection is used in the generator case of coefficient recovery"
      - "integer cast injectivity converts rational coordinate equality back to integer coefficient equality"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: not-applicable
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean: pass; 14 namespace declarations, standard axioms only"
    - "main declarations #print axioms: propext, Classical.choice, Quot.sound only"
    - "git diff --check and placeholder, hidden/BiDi Unicode, private-path, and Formal-to-Research import scans: pass"
  blocking_findings: []
  next_obligation: "lift epsilon_R cellwise to actual obstruction and law-generated diagnostic cochains and prove the degree 0-2 cochain-map equations"
```
