# G-110-aat-doctrine-fiber-product — doctrine fiber product と base change

- 一次仕様: [`research/goals/G-110-aat-doctrine-fiber-product.md`](../goals/G-110-aat-doctrine-fiber-product.md)
- tracking Issue: [#4034](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4034)
- target theorem: Doctrine Fiber Product and Base Change Theorem
- proof state: `target-proof-checkpoint`
- completion candidate: `no`

この report は固定 GOAL の証拠索引、proof obligation delta、material premise
監査を記録する。target statement と completion criteria の正本は GOAL カードで
あり、この report はそれらを再定義しない。target-theorem mode のため SCORE は
使わない。

## Cycle ledger

### Cycle 1 — F0a reviewed FiniteModel-backed cartesian schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 1
goal_blob_sha: e30fdd52903abe30ae4063dafa4bcea8f7feae8b
goal_sha256: f41553936da313160e10e490c7f73a9ea6d6ed93345d295b10b35a3aa680faa1
base_oid: 6a7a4391ab0e24b2e6072d513eb5bf63812fcac6
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 active/not-started and fixed GOAL strategy F0
  proof_dag_predecessors:
    - G-101 FiniteModel extractionDoctrine
    - G-101 finiteTransportTargetDoctrine / finiteTransportExactDoctrineHom
  proof_obligation: type the reviewed FiniteModel-backed four-field raw/validated CartPresentation layer, its named CartSemanticInput realization and actual morphism-law soundness, RealizableHom provenance, and the fixed equality/membership/finite-universal CartConditionSyntax
  selection_reason: every later finite base-change obligation consumes the same realizable pointed-arrow type; F0a fixes that shared cartesian input without bundling the independent G-106 diagnostic schema of F0b
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
  risks:
    - a new semantic tag family could replace the reviewed FiniteModel schema
    - a manufactured doctrine could make a desired noninvertible hom exact by construction
    - allCells could be a hom-tag truth table instead of a finite universal equality
    - a fixed two-source schema could fail to represent its own source pullbacks
  unchecked:
    - revised fixed-head independent review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed a universe-polymorphic presentation whose authored raw payload is exactly four fields over existing FiniteModel value types; restricted the validated image to the reviewed extraction/transport frames and identity source table; constructed actual ExactDoctrineHom/ExtInstHom laws; fixed a presentation-level equality/membership/finite-universal condition grammar; and proved the source-table pullback is the two-element diagonal
  completion_candidate: no
  lean_artifacts:
    - FiniteModelBacking / FiniteModelBacking.liftAtomEquiv
    - FiniteInstanceDescription (standard product abbreviation)
    - CartRawCode / CartRawCode.WellFormed / ValidatedCartCode
    - CartSemanticInput / CartPresentation / decodeCartHom / toSemanticCart
    - toSemanticCart_sound
    - RealizableHom / realizableHomOf
    - CartFieldKind / CartProjection / CartNamedConstant / CartFieldTerm
    - CartDerivedSet / CartUniversalEquality / CartConditionSyntax
    - evalCartCondition
    - finiteSourceDiagonalPullbackEquiv
  evidence:
    - finiteReviewedAtomSwapEquiv_eq_reviewed
    - finiteFramedDoctrine_componentC_extracts_iff_reviewed
    - finiteFramedDoctrine_dependsAB_extracts_iff_reviewed
    - validatedCartCode_sourceMap_eq_id
    - finitePointMismatchRawCode_not_wellFormed
    - finiteAtomTransportPresentation_atomEquiv_eq_reviewed
    - finiteAtomTransportPresentation_nonidentity
    - finiteSourceDiagonalPullback_card
    - validatedSourcePullbackEquiv
    - validatedSourcePullback_card
    - evalCartCondition_identity_sourceMap
    - evalCartCondition_transport_atomMap_nonidentity
    - evalCartCondition_transport_targetExcluded_not_sourceExcluded
    - evalCartCondition_identity_sourcePoint_not_unit
  claim_mapping:
    theorem_names:
      - finiteReviewedAtomSwapEquiv_eq_reviewed
      - finiteFramedDoctrine_componentC_extracts_iff_reviewed
      - finiteFramedDoctrine_dependsAB_extracts_iff_reviewed
      - toSemanticCart_sound
      - finiteSourceDiagonalPullback_card
      - validatedSourcePullback_card
      - evalCartCondition_transport_atomMap_nonidentity
    source_labels:
      - target theorem (B), two-layer input typing and reviewed FiniteModel-backed schema
      - target proof artifacts, raw/validated CartPresentation and named CartSemanticInput
      - H_cart qualification clause (i), fixed equality/membership/finite-universal language
      - realization-image closure precondition for later pullbackPresentation
    conjuncts:
      - raw code has four authored fields: source instance, target instance, finite source-map table, finite Atom-map table
      - source/target fields use only FiniteModel.FiniteAtom and FiniteModel.ExtractionSource values
      - validated decoder admits only componentC/dependsAB reviewed frames, identity source maps, source_eq-compatible points, and the endpoint-generated Atom table
      - semantic decoding builds actual normalize_eq / extraction_iff / source_eq proofs
      - RealizableHom carries presentation provenance equality and no lift certificate
      - condition relations are field equality, presentation-derived singleton membership, finite universal equality, and conjunction
      - every allCells branch iterates an explicit exhaustive FiniteModel cell list
      - every validated source map is identity and its binary source pullback is the two-element diagonal
    undischarged_assumptions:
      - F0b base-change diagnostic presentation and cartesian regime typing
      - presentation constructors and realization/replacement invariance
      - K1 disjunction; in particular the right-branch noninvertible positive-family qualification is not supplied by this reviewed groupoid schema
      - all K0-K4 theorem obligations
    acceptance_point: the decoder uses only the existing reviewed FiniteModel extraction and G-101 transport frames; no new doctrine tag, all-True doctrine, constant hom, lift, strong-cartesian certificate, mate, checker result, or target conclusion is authored
    port_status: unported
audits:
  premise_delta:
    discharged:
      - F0a named CartPresentation / CartSemanticInput / RealizableHom typing
      - four-field finite raw code and decidable validated decoder domain
      - reviewed FiniteModel extraction/transport comparison and actual morphism laws
      - fixed equality/membership/finite-universal CartConditionSyntax and presentation evaluator
      - source-level diagonal pullback does not escape the reviewed finite source type
    remaining:
      - F0b and K0-K4 fixed GOAL obligations
      - K1 left/right branch determination and any right-branch noninvertible family
  certificate_provenance:
    discharged:
      - executable Atom swap is proved equal to G-101 finiteTransportAtomEquiv
      - endpoint doctrine frames are proved extraction-equivalent to FiniteModel.extractionDoctrine and finiteTransportTargetDoctrine
      - exact-morphism law proofs are constructed inside decodeCartHom from validated endpoint data
    unresolved:
      - later checker bridge, regime producer, pullback/pasting constructors and BC constructions
  proof_use:
    used:
      - FiniteModelBacking.atomEquiv in both endpoint doctrines and Atom-equivalence lifting
      - all five CartRawCode.WellFormed conjuncts in decodeCartHom and endpoint realization
      - reviewed finite source/Atom enumerations in condition evaluation
      - validated identity source-map theorem in source-pullback readiness
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - ./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass
    - ./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.Schema: exact target pass; no aggregate/full Research build
    - '#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct: 299 declarations, pass'
    - direct '#print axioms' of 18 public-spine declarations: standard axioms only
    - placeholder / hidden-BiDi / privacy / reverse-import / git diff scan: pass
  blocking_findings: []
  next_obligation: F0b BCPresentation / BCSemanticInput / pre-BC diagnostic schema / CartesianRegime / authored-relative BC domain typing
```

## Review history

### Initial head `da1b6266` — rejected

独立4査読は数学A/B、Lean A/Bの全 lane で Major 判定となり、PR #4035
[監査コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4035#issuecomment-5351555665)
に統合した。主 finding は次の三点だった。

1. 昇格レビューで撤回した新 code 族と全 `True` の
   `finiteSourceIndependentDoctrine` / constant hom を再導入していた。
2. `allCells` が有限全称ではなく hom tag の truth tableで、固定 relation
   vocabulary 外の injectivity / surjectivity predicateを追加していた。
3. constant cospan の source pullback は4要素だが、2要素 Source だけの
   schemaでは表現できず、後続の必須 pullback closure が不可能だった。

全 finding を受理した。revised implementation は bespoke code enum、全 `True`
doctrine、constant hom、property tag tableを削除した。raw payloadを既存
`FiniteModel` 値だけの4 fieldへ置換し、reviewed extraction/transportとの比較
theorem、実有限全称 evaluator、対角 pullback同値を追加した。declarationと
statementを変更したため、新fixed headに4 laneを全再実行する。

## Remaining scope

次 obligation は F0b (`BCPresentation` / `BCSemanticInput` / diagnostic schema /
`CartesianRegime` / authored-relative BC domain)であり、F0 全体の省略ではない。
revised F0a は reviewed finite groupoidを正直に表現し、非可逆射を発明しない。
したがって K1 で左枝を証明できず右枝が必要になった場合、右枝の
「非恒等かつ非可逆な底射を含む正例族」は未放電の中心 gateである。固定された
reviewed schema内で構成不能なら、GOALを弱めず `goal defect` で停止する。
