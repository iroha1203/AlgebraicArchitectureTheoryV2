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
  同じ辺差を持つ整数0-cochainを構成する。`B ≃ Λ` を使うB2向けspecializationも構成した。
- 未完了: `M_R ≃ ℤ^B`、整数係数から有理law-value係数への比較、Aの
  実障害複体・診断複体と次数0–2の比較写像。
- 未完了: B1・B2、C1・C2、同一入力上の有限例、論文対応、最終検証・査読。
- 次のproof obligation: primitive relationから整数presentation groupと `ℤ^B` の
  同値を構成し、導出済み `B ≃ Λ` を通る整数係数比較へ接続する。

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
    - "GeneratorPresentation.blockLabelEquiv: PR #4799, merge dfcc02b073ac1b8cc7d7c76533dcac24827cf24b, fixed-head audit https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4799#issuecomment-5742401350"
    - "Int.floor_add_intCast from the pinned mathlib dependency"
  proof_obligation: "construct an integral zero-cochain from a rational witness whose edge differences are integral, then specialize it along the R_q-derived B equivalent Lambda"
  selection_reason: "this is the arithmetic kernel of B2 and the paper design's next recommended module after the generator presentation"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean"
    - "IntegralReflection.exists_integral_correction"
    - "GeneratorPresentation.exists_block_integral_correction"
  risks:
    - "treating floor as an additive homomorphism would assert a false general coefficient retraction"
    - "assuming an integral correction would make zero-class reflection circular"
    - "failing to use the derived block-label equivalence would leave Cycle 1 disconnected from B2"
  unchecked:
    - "fixed-head independent review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "A rational vertex witness with integral edge differences now constructs an integral vertex correction by floor. The block specialization reads diagnostic coordinates through the R_q-derived B equivalent Lambda, so no additive inverse from rationals to integers and no H1 injectivity premise is introduced."
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
    - "exists_block_integral_correction indexes b by LawValueLabel and transports each obstruction block through blockLabelEquiv"
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
      - "R_q-derived B equivalent Lambda indexes the diagnostic witness -> exists_block_integral_correction"
    undischarged_assumptions:
      - "the later diagnostic comparison must supply the rational edge-difference witness h from diagnostic zero-class data"
      - "the selected input and fixed finite example must discharge ReflectionCondition as recorded in Cycle 1"
    acceptance_point: "the theorem extracts one integral coboundary witness from one rational witness; it does not define an additive rational-to-integer inverse or assume obstruction zero-class reflection"
    port_status: not-applicable
audits:
  material_premises:
    ambient_boundary:
      - "Vertex, Edge, Block, source, target, and the integral edge cochain are input data"
    direction_hypothesis:
      - "h states that the supplied rational zero-cochain has the cast integral edge cochain as its edge difference"
      - "hReflection supplies the Cycle 1 block-label equivalence in the specialized theorem"
    discharge_required:
      - "B1 and the actual diagnostic complex must construct h from a diagnostic zero-class witness"
      - "the selected input and fixed finite example must prove hReflection from primitive relations"
    conclusion_equivalent_risk:
      - "h is diagnostic-side rational coboundary data, not the integral correction concluded by the theorem; the latter is constructed by floor"
  premise_delta:
    discharged:
      - "rational edge differences known to be integral have an explicitly constructed integral correction"
      - "the construction is compatible with the Cycle 1 block-label equivalence"
    remaining:
      - "construct M_R equivalent to the free integer coefficients on relation components"
      - "construct the actual coefficient and cochain comparison maps"
      - "A1, B1, full B2, C1, C2 and the fixed finite example"
  certificate_provenance:
    discharged:
      - "the integral correction is the coordinatewise floor of the supplied rational witness"
      - "the block-label coordinate change is the Cycle 1 derived equivalence, not a new certificate field"
    unresolved: []
  proof_use:
    used:
      - "h is rearranged into b(target) = b(source) + z and consumed by Int.floor_add_intCast"
      - "hReflection is consumed by blockLabelEquiv when selecting each rational coordinate"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
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
