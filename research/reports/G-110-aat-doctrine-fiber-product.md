# G-110-aat-doctrine-fiber-product — doctrine fiber product と base change

- 一次仕様: [`research/goals/G-110-aat-doctrine-fiber-product.md`](../goals/G-110-aat-doctrine-fiber-product.md)
- tracking Issue: [#4034](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4034)
- target theorem: Doctrine Fiber Product and Base Change Theorem
- proof state: `target-proof-checkpoint`
- completion candidate: `no`
- loop stop: `goal defect` (Cycle 1 revised head review)

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
  unchecked: []
result:
  proposed_result_type: rejected
  proof_obligation_delta: the revised candidate removed the initial target-fitting doctrine and truth-table language, then exposed a fixed-contract incompatibility; the resulting reviewed extraction/transport realization image is a groupoid, while the fixed GOAL requires BCPresentation cospans from CartPresentation and an H_bc positive family with a nonidentity noninvertible leg
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
    rejection_point: satisfying the mandatory noninvertible-leg family requires either a new finite doctrine/source code family or an existing all-admitting doctrine with a noninjective source map; the latter's self-pullback has four sources and escapes the reviewed two-source schema, so either repair changes the fixed presentation contract
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
  structure_field_escape: found
  route_integrity: fail
  target_fitting: found
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
  blocking_findings:
    - every revised validated CartPresentation decodes to an isomorphism, so BCPresentation cannot express the fixed H_bc qualification's nonidentity noninvertible leg
    - using the existing all-admitting refinement doctrine admits a noninjective constant source map, but its self-pullback has four sources and cannot be represented by the fixed reviewed two-source schema
    - FiniteModelBacking is semantic data beyond the claimed four authored fields unless fixed as a new ambient premise
    - unitSource renames the fixture value ExtractionSource.all despite no source-unit operation or law
    - the reviewed doctrine and exact-hom comparison theorems are not consumed by the decoder proof DAG
  next_obligation: none inside the fixed GOAL; human decision must re-fix the presentation contract or predecessor schema before F0b
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

### Revised head `9641f8bb8f00cbaccdfb4a8d38a974e0b85a5f7a` — rejected / goal defect

独立4査読の結果は数学A `Major`、数学B `Major`、Lean A
`No major findings`、Lean B `Major` だった。統合判定は `Needs changes`。
三 lane が独立に確認した中心 finding は、revised validated image が
identity source map と Atom equivalence だけの groupoid であるため、固定 GOAL
(D) の `H_bc` 資格に必須の「非恒等かつ非可逆な脚を含む square 族」を
`BCPresentation` の authored `CartPresentation` cospan として型付けできない点で
ある。この義務は K1 右枝だけではなく (D) に無条件に存在する。

既存 reviewed source を再探索すると、具体 `ExactDoctrineHom` の source map は
すべて identity だった。G-101 の既存 all-admitting
`refinementTargetDoctrine` 上なら constant exact endomorphismは作れるが、その
自己 pullback source は2元集合の直積4要素となり、2要素
`FiniteModel.ExtractionSource` に同値ではない。したがって realization 像内の
`pullbackPresentation` を閉じるには、新しい source/doctrine code familyまたは
pullback-closed predecessor schemaが必要になる。前者は固定カードが明示的に禁止
している。

これは定理 statement 自体の反例ではなく、F0 へ移管された presentation contract
の不足・相互不整合である。固定 GOAL を自動で弱めず `goal defect` で停止し、PRは
mergeしない。人間が選べる改訂方向は、(a) pullback-closed finite source codeを
明示的に許す、(b) 先行カードで reviewed schemaを拡張してから G-110を再固定する、
(c) 非可逆族またはclosure claimを変更する、のいずれかであり、本loopでは選ばない。

## Remaining scope

F0b、K0–K4 はすべて未着手のまま残る。次 obligation は自動選定しない。
presentation contract または reviewed predecessor schemaを人間が再固定した後だけ、
新しい fixed GOAL head から loop を再開する。
