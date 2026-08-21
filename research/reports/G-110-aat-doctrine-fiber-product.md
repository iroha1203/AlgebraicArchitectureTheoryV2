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

### Cycle 3 — F0b1 basic BC presentation and condition schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 3
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5dd7bbb297c50498e6cff706258a5237381df9d4
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 2 merge update comment 5363876694 and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - G-106 FiniteTransportPresentation and AdmissibleTransportData
  proof_obligation: fix an elaborating basic BCPresentation whose authored groups are a typed finite-code cospan, a finite compatible-point table, and a pre-base-change G-106 diagnostic presentation; generate the semantic pullback square and selected-point equations; and enumerate the complete four-constructor BC condition vocabulary over all finite cartesian, compatible-point, and diagnostic fields
  selection_reason: the fixed GOAL explicitly permits F0 to be split; the basic BC input boundary and evaluator can be checked independently before adding pasting, authored 2-cell, and regime-producer signatures
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - the pullback square or IsPullback proof could become a caller-authored field
    - the compatible-point table could be retained but not consumed by validation or realization soundness
    - semantic G-106 package values could leak into the finite condition projection language
    - a target-result bit, regime, mate, or transported diagnostic could be smuggled into raw code
    - empty diagnostic geometry could make every structural diagnostic check vacuous
    - every semantic square could be silently accepted as realizable
  unchecked:
    - fixed-head four-lane math-lean-review after the computability and operand-sort repair
    - whether the F0b2 pasting and authored-2-cell layer requires an auxiliary typed square category
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed the basic BC raw/validated boundary, generated semantic pullback realization and provenance, an executable compatible-source rank/unrank producer, exhaustive first-order serialization of the pre-BC G-106 finite geometry, the fixed four-constructor BC condition language with a shared natural operand sort, and concrete positive, negative, nonempty-diagnostic, and non-realizable semantic-square witnesses
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - BCRawCode.checkWellFormed_eq_true_iff
    - toSemanticBC_authored_point_table_sound
    - toSemanticBC_sound
    - finiteConstantBCDiagnosticInterpretation
    - finiteConstantBC_generated_leg_source_cards
    - finiteConstantBC_generated_top_source_point_mem
    - finiteConstantBC_bottom_point_eq_compatible_first
    - evalBCCondition_firstAtomMapIdentity_bridge
    - evalBCCondition_firstAtomMapIdentity_replacement_invariant
    - finiteBCDiagnostic_vertices_nonempty
    - finiteBCDiagnostic_twoCells_nonempty
    - finiteBCDiagnostic_threeFaces_nonempty
    - finiteBadBCRawCode_check_false
    - finiteNonPullbackSquare_not_isPullback
    - finiteNonPullbackBCInput_has_no_realizableSquare
  claim_mapping:
    theorem_names:
      - FiniteDiagnosticPresentation
      - CartCospanPresentation
      - BCPresentation
      - BCSemanticInput
      - BCDiagnosticInterpretation
      - decodeBCSquare
      - toSemanticBC
      - toSemanticBC_sound
      - RealizableSquare
      - BCProjection
      - BCConditionSyntax
      - evalBCCondition
    source_labels:
      - target theorem (B), schema invariants (s1)-(s6)
      - target proof strategy F0 schema typing
      - G-106 pre-base-change diagnostic presentation
    conjuncts:
      - BCRawCode has exactly the typed cospan, compatible-point table, and finite pre-BC diagnostic-presentation groups
      - BCPresentation is the validated layer and its Boolean checker is exact
      - the pullback object, projections, square commutativity, and IsPullback proof are generated from the cospan
      - the authored compatible-point table is consumed by validation and agrees componentwise with decoded selected sources and images
      - BCSemanticInput has only the square, compatible points, and underlying pre-BC diagnostic geometry, with no authored enumeration, package interpretation, regime, condition result, mate, or transported diagnostic
      - BCDiagnosticInterpretation places G-106 AdmissibleTransportData in a separate dependent semantic-input layer
      - every finite cartesian field of all four square legs and every compatible-point and G-106 combinatorial component is represented in BCProjection
      - all cartesian derived sets and finite universals are available for all four generated legs
      - cartesian natural fields share the BC natural operand sort, so generated-leg membership and cross-group equality are well typed
      - the compatible-pair source is explicitly enumerated and the complete four-leg evaluator is executable rather than a noncomputable Bool specification
      - semantic G-106 interpretation data is absent from presentation fields and projection evaluation
      - BCNamedConstant contains no natural/source-index value constant
      - BCConditionSyntax has exactly field equality, membership, finite universal equality, and conjunction constructors
      - the selected finite universal has a semantic bridge and semantic-replacement invariance theorem
      - nonempty 0/1/2/3-cell diagnostic data and oriented pasting faces exercise the structural serialization
      - malformed point tables are rejected and identity/nonidentity Atom conditions both fire
      - a concrete commutative non-pullback semantic input has neither presentation provenance nor a RealizableSquare certificate
    undischarged_assumptions: []
    acceptance_point: the finite-only basic BC presentation generates rather than stores its pullback conclusion; package interpretation is a separate dependent semantic input; the compatible table is tied to decoded semantics; explicit compatible-pair enumeration makes the four-leg evaluator executable; the shared natural operand sort lets membership and equality consume generated Cart fields; the evaluator sees the complete authored finite combinatorics but has neither semantic package values nor a fixture source-value constant; positive and negative validators and realization boundaries close the nonvacuity audit; and no F0b2 pasting, authored-2-cell, or regime claim is included
    port_status: unported
audits:
  premise_delta:
    discharged:
      - basic finite-code BCPresentation and named BCSemanticInput boundary
      - separate dependent BCDiagnosticInterpretation package layer
      - generated categorical pullback square and selected-point soundness
      - complete four-leg basic BC condition field vocabulary and evaluator
      - executable compatible-source enumeration and shared natural relation operands
      - finite diagnostic presentation capabilities and nonempty structural witness
      - basic realization provenance and a semantic non-realizability boundary witness
    remaining:
      - F0b2 pastePresentation and admissible-square pasting closure
      - F0b2 AuthoredBC2CellPresentation and MateCoherentRel typing
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations
  certificate_provenance:
    discharged:
      - BCRawCode validation consumes the authored compatible-point table against the cospan
      - BCRawCode and BCSemanticInput contain no AdmissibleTransportData field; finiteConstantBCDiagnosticInterpretation inhabits the separate dependent package layer
      - decodeBCSquare invokes the F0a pullback producer; BCRawCode stores no pullback object or proof
      - toSemanticBC_sound obtains IsPullback from pullbackPresentation_isPullback
      - realizableSquareOf is generated from a validated presentation
      - finiteNonPullbackBCInput_has_no_realizableSquare rules out a generic certificate wrapper for an invalid square
    unresolved: []
  proof_use:
    used:
      - all seven compatible-point equalities in validation; the first five are consumed directly by the authored-table soundness theorem, while the final two redundant image/base equalities remain checked by the validator
      - both typed cospan legs in generated pullback object, projections, and IsPullback proof
      - all four square legs in BCProjection, BCDerivedSet, and BCUniversalEquality; generated top/left source-card projections fire, generated top source membership executes to true, and a Cart/compatible-point natural equality executes to true
      - every finite diagnostic field family in a listed projection or structural universal
      - finite support/table data in the Atom-identity semantic bridge
      - collapse and constant source maps in the non-pullback contradiction
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 498 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean: pass, namespace audit 506 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean: pass, namespace audit 61 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - executable #eval of generated-top source membership and Cart/compatible-point equality: true, true
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted umbrella module check
    - direct #print axioms on all 92 F0b1 acceptance-spine declarations plus 14 directly changed F0a producer declarations: only standard axioms
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, wiring, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b2 pasting, authored 2-cell, mate-relation, and regime-producer signature typing
```

### Cycle 3 initial fixed-head review and response

初回 fixed head `4c942ab188072de3e227568bf559df9e1b33e178` の標準
review-pr / math-lean-review 監査は
[#4039 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364183765)
に固定した。4 lane の統合判定は `Needs changes` で、次の3点を検出した。

1. `AdmissibleTransportData` を `BCRawCode` / `BCPresentation` に格納し、
   finite presentation と package semantic interpretation の二層を混同した。
2. `BCNamedConstant.zero` が authored source index との fixture-dependent
   等式原子を許した。
3. `BCSquareLeg` が authored cospan の2脚しか列挙せず、生成された pullback
   脚 `top / left` を condition projection から落とした。

修正では `BCRawCode.diagnostic` を `FiniteDiagnosticPresentation` のみにし、
`BCSemanticInput.diagnostic` は underlying `FiniteTransportPresentation`、
G-106 package 値は別 dependent structure `BCDiagnosticInterpretation` に分離した。
natural/source-index 定数は全廃し、`BCSquareLeg` は `top / left / right /
bottom` の4脚を列挙する。さらに全 `CartDerivedSet` /
`CartUniversalEquality` を各脚へ埋め込み、生成 `top / left` の source-card
projection が具体的4元 pullback codeを読む witness を追加した。signature と
declaration を変更したため、修正 head は直接対応ではなく4 lane 正式再査読を要する。

### Cycle 3 second fixed-head review and response

第2 fixed head `b9f278dd292e2a4a03a60628cf8bfe509aadfb37` の4 lane 再査読は
[#4039 rereview comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364364812)
に固定した。旧3 finding の解消を確認した一方、統合判定は再び
`Needs changes` となり、次の2点を検出した。

1. Cart の自然数 projection が `BCFieldKind.cart .natural`、membership と
   compatible/diagnostic projection が `BCFieldKind.natural` に分かれ、生成
   `top / left` の `sourcePoint ∈ sourceCells` と cross-group equality が
   型付け不能だった。
2. `compatibleSourceEquiv` が `Fintype.equivFin` / classical choice を使ったため、
   `bcCartPresentation` から `evalBCCondition` までの complete evaluator chain が
   `noncomputable` となり、有限 checker の操作化を満たさなかった。

第2修正は `BCFieldKind.ofCart` で Cart natural を共通 BC natural sort に写し、
`cartFieldValueToBC` で値を型付き移送する。さらに左右 source の canonical list
product を compatibility equality で `filterMap` し、nodup / complete 証明から
list rank/unrank equivalence `compatibleSourceEquiv` を計算可能に再構成した。
pullback code と全四脚 evaluator から `noncomputable` を除去し、生成 top の
source membership と Cart/compatible-point equality がどちらも実際の `#eval` で
`true` を返すことを確認した。この signature repair も4 lane 正式再査読を要する。

### Cycle 2 — F0a finite-code cartesian schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 2
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ea6eb80d3f9388f0eeeb550370664ae1a6b3e0b0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 fixed-head update comment 5363348621 and revised GOAL strategy F0
  proof_dag_predecessors:
    - G-101 AtomFoundation exact doctrine and pointed morphism API
    - PR 4037 finite-code schema invariants s1-s6
  proof_obligation: fix an elaborating finite-code bottom schema whose Source varies by presentation, together with raw/validated CartPresentation, named CartSemanticInput realization and soundness, RealizableHom provenance, the complete CartConditionSyntax, and id/comp/pullback closure signatures with realization compatibility
  selection_reason: every F0b and K0-K4 node consumes this bottom realization image; fixing the pullback-closed cartesian spine directly removes the former fixed-two-source blocker without bundling the independent BC diagnostic and regime layer
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - semantic payload or conclusion certificates could escape into the four authored raw fields
    - a fixed fixture Source could reintroduce the Cycle 1 pullback-closure defect
    - sourceMap could be silently restricted to equivalences and lose mandatory noninvertible inputs
    - finite-support Atom permutations could be asserted rather than decoded with inverse data
    - pullback closure could be equality-shaped data instead of an IsPullback theorem
    - condition syntax could add a target-result predicate or fixture constant
  unchecked:
    - exact signature supported by the current AtomFoundation category API
    - whether id/comp/pullback realization compatibility can all be proved in this cycle without changing s1-s6
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed an elaborating four-field finite-code realization spine with presentation-varying first-order Source, a quotient category of typed code presentations and its ExtInst realization functor, decoded finite/cofinite Atom predicates and finite-support permutations, arbitrary source maps, raw/validated separation, semantic soundness and provenance, id/comp/pullback constructors, and a pullback realization theorem against every semantic ExtInst cone
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - pullbackPresentation_isPullback
    - finiteCodeCartRealization_pullback_isPullback
    - finiteModelDoctrineRealizationIso
    - toSemanticCart_sound
    - toSemanticCart_idPresentation_hom
    - toSemanticCart_compPresentation_hom
    - finiteConstantPresentation_not_isIso
    - finiteBadPointRawCode_check_false
    - infiniteIdentityInput_has_no_realizableHom
    - finiteConstantPullback_sourceCard
    - finiteConstantPullback_isPullback
    - evalCartCondition_atomMapIdentity_bridge
    - evalCartCondition_atomMapIdentity_replacement_invariant
  claim_mapping:
    theorem_names:
      - FiniteDoctrineCode.toDoctrine
      - decodeCartDoctrineHom
      - toSemanticCart_sound
      - finiteCodeCartRealization
      - finiteCodeCartRealization_pullback_isPullback
      - pullbackPresentation_isPullback
      - CartConditionSyntax
      - evalCartCondition
      - finiteConstantPresentation_not_isIso
      - finiteModelDoctrineRealizationIso
    source_labels:
      - target theorem (B), schema invariants (s1)-(s6)
      - target proof strategy F0 schema typing
      - presentation closure constructors id / comp / pullback
    conjuncts:
      - presentation-owned finite Source and finite doctrine/instance codes
      - four authored raw fields with decidable well-formedness and validated decoder
      - named semantic input and realization provenance with semantic-law soundness
      - finite-support Atom permutation identity, inverse, and composition closure
      - arbitrary noninvertible source maps remain in the realization image
      - identity and composition realization compatibility
      - typed code presentations modulo decoded equality form a category and realization is a functor to ExtInst_U
      - pullback source re-enumeration and projection presentations remain finite-code
      - generated semantic projection square is an ExtInst categorical pullback for arbitrary semantic cones
      - the reviewed FiniteModel extraction doctrine lies in the object realization image up to Doct_U isomorphism
      - Holds, WellFormed/checker, and RealizableHom provenance have explicit positive and negative finite/infinite instances
      - fixed four-constructor Cart condition syntax over the completely enumerated cartesian projections, constants, relations, and derived finite sets
    undischarged_assumptions: []
    acceptance_point: every selected F0a artifact is generated from the four raw fields; typed composability is explicit in FiniteCodeCartCategory and finiteCodeCartRealization rather than inferred from independently chosen semantic endpoint presentations; neither semantic morphisms nor pullback proofs nor condition bits are caller-authored; positive/negative validator and realization instances close the vacuity audit; and the finite constant witness proves that sourceMap was not narrowed to equivalences
    port_status: unported
audits:
  premise_delta:
    discharged:
      - finite-code Cart presentation and semantic realization bridge
      - realization soundness for normalize_eq, extraction_iff, and source_eq
      - id / comp closure of the typed finite-code quotient category and functorial semantic realization
      - pullbackPresentation output remains in the code family and realizes to an ExtInst pullback against arbitrary semantic cones
      - fixed CartConditionSyntax signature
    remaining:
      - F0b BC presentation, BC condition language, authored 2-cell, and regime signatures
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations
  certificate_provenance:
    discharged:
      - validated well-formedness is finite-table data consumed by decodeCartDoctrineHom
      - pullback object and projections are generated by pullbackPresentation from the cospan
      - IsPullback is proved by pullbackSemanticLift and uniqueness, not stored in PullbackPresentation
      - finiteConstantPresentation_check_true and finiteBadPointRawCode_check_false form the validator instance pair
      - finiteConstantRealizableHom and infiniteIdentityInput_has_no_realizableHom form the realization-certificate boundary pair
      - finiteModelDoctrineRealizationIso derives both exact comparison arrows from the finite source equivalence
    unresolved: []
  proof_use:
    used:
      - both cospan source-map equations in CompatibleSource and semantic cone lift construction
      - both cospan atomEquiv components in the second projection and cone factorization
      - normalize_eq, extraction_eq, and source_eq in decoder soundness and pullback realization
      - finite-support support/table data in permutation decoding and condition evaluation
      - quotient-category composition laws consume the id/comp semantic compatibility theorems
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 492 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted module check
    - direct #print axioms on all 87 acceptance-spine declarations: only propext, Classical.choice, and Quot.sound
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b BC presentation, authored 2-cell, condition-language, and CartesianRegime typing
```

Cycle 1 の旧 fixed-card head に対する `goal defect` と PR #4035 の rejected
artifact は tracking Issue #4034 を正本とする。PR #4037 でカードが改訂されたため、
旧 fixed-two-source schema は本 cycle の受理証拠として再利用しない。

### Initial fixed-head review and response

初回 fixed head `3a3e60a8` の標準 review-pr / math-lean-review 監査は
[#4038 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4038#issuecomment-5363718027)
に固定した。4 lane の統合判定は `Needs changes` で、(i) code endpoint を
定義的に共有する constructor の閉性を semantic realization image 全体の閉性と
過大表示しないこと、(ii) `Holds` / `WellFormed` / `RealizableHom` の正負
instance を固定すること、の2点を是正対象とした。

修正後は `FiniteCodeCartCategory` と `finiteCodeCartRealization` により typed
code calculus と semantic interpretation を型で分離した。pullback の普遍性は
`finiteCodeCartRealization_pullback_isPullback` として任意 semantic cone 上に
維持する。あわせて predicate、validator、realization certificate の正負対と、
既存 `FiniteModel.extractionDoctrine` の `Doct_U` 同型
`finiteModelDoctrineRealizationIso` を追加した。修正 fixed head
`a486f2f105ac097c287abf1fcac18c267fde1bea` は4 lane の独立再査読で全 lane
`No major findings`、CI 7/7 pass となり、統合監査を
[#4038 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4038#issuecomment-5363868928)
に固定した。PR #4038 は merge commit
`5dd7bbb297c50498e6cff706258a5237381df9d4` として main に統合済みである。

## F0b1 acceptance spine

F0b1 の直接 axiom audit 対象は次の92 declaration に固定する。semantic package
layerの `BCDiagnosticInterpretation.data` は presentation / decoded square と
別の dependent input であり、condition projection/evaluator の対象には含めない。

- raw/validated and semantic boundary: `FiniteDiagnosticPresentation`,
  `BCDiagnosticInterpretation`, `CartCospanPresentation`, `CompatiblePointCode`,
  `CompatiblePointCode.WellFormed`, `CompatiblePointCode.checkWellFormed`,
  `CompatiblePointCode.checkWellFormed_eq_true_iff`, `BCRawCode`,
  `BCRawCode.WellFormed`, `BCRawCode.checkWellFormed`,
  `BCRawCode.checkWellFormed_eq_true_iff`, `ValidatedBCCode`,
  `BCPresentation`, `ExtInstSquare`, `CompatiblePointSemanticInput`,
  `compatiblePointSemanticInputOfSquare`, `BCSemanticInput`, `decodeBCSquare`,
  `toSemanticBC`, `toSemanticBC_authored_point_table_sound`,
  `toSemanticBC_sound`, `RealizableSquare`, `realizableSquareOf`
- diagnostic serialization: `DiagnosticEdgeValue`,
  `DiagnosticWhiskeredFaceValue`, `finiteListIndex`, `diagnosticPathValue`,
  `diagnosticWhiskeredFaceValue`, `diagnosticPastingValue`,
  `diagnosticEdgeCardTable`, `diagnosticTwoSources`, `diagnosticTwoTargets`,
  `diagnosticTwoLeftPaths`, `diagnosticTwoRightPaths`,
  `diagnosticThreeSources`, `diagnosticThreeTargets`,
  `diagnosticThreeStartPaths`, `diagnosticThreeFinishPaths`,
  `diagnosticThreeLeftPastings`, `diagnosticThreeRightPastings`
- fixed BC vocabulary: `BCFieldKind`, `BCFieldKind.ofCart`, `BCFieldValue`,
  `cartFieldValueToBC`, `BCSquareLeg`,
  `BCProjection`, `BCNamedConstant`, `BCFieldTerm`, `bcCartPresentation`,
  `readBCProjection`, `readBCNamedConstant`, `evalBCFieldTerm`,
  `BCDerivedSet`, `evalBCDerivedSet`, `BCUniversalEquality`,
  `diagnosticFaces`, `evalBCUniversalEquality`, `BCConditionSyntax`,
  `evalBCCondition`, `evalBCCondition_firstAtomMapIdentity_eq_true_iff`,
  `FirstLegIdentityAtomComponent`,
  `evalBCCondition_firstAtomMapIdentity_bridge`,
  `evalBCCondition_firstAtomMapIdentity_replacement_invariant`
- finite checks: `FiniteBCDiagnosticCell`,
  `finiteBCDiagnosticTwoPresentation`, `finiteBCDiagnosticGeometry`,
  `finiteBCDiagnosticPresentation`, `finiteBCDiagnosticTransportData`,
  `finiteConstantBCDiagnosticInterpretation`,
  `finiteBCDiagnostic_vertices_nonempty`,
  `finiteBCDiagnostic_twoCells_nonempty`,
  `finiteBCDiagnostic_threeFaces_nonempty`, `finiteConstantBCCospan`,
  `finiteConstantCompatiblePointCode_wellFormed`,
  `finiteConstantBCRawCode_wellFormed`,
  `finiteConstantBCRawCode_check_true`,
  `finiteConstantBC_generated_leg_source_cards`,
  `finiteConstantBC_generated_top_source_point_mem`,
  `finiteConstantBC_bottom_point_eq_compatible_first`,
  `finiteBadBCRawCode_not_wellFormed`, `finiteBadBCRawCode_check_false`,
  `finiteConstantBC_firstAtom_check`,
  `finiteConstantBC_diagnostic_structure_check`,
  `finiteSwapBC_firstAtom_check_false`, `finiteConstantRealizableSquare`,
  `finiteConstantRealizableSquare_firstLegIdentity`,
  `finiteSwapRealizableSquare_not_firstLegIdentity`,
  `finiteTwoCollapseSemantic_ne_id`,
  `finiteTwoCollapse_comp_finiteConstant`,
  `finiteNonPullbackSquare_not_isPullback`,
  `finiteNonPullbackBCInput_not_presented`,
  `finiteNonPullbackBCInput_has_no_realizableSquare`

## F0a acceptance spine

F0a の報告対象 declaration は次に固定する。補助 lemma と生成された
recursor を completion claim の代用品にはしない。

- predicate/permutation code: `AtomPredicateCode.eval_transport`,
  `AtomPredicateCode.transport_refl`, `AtomPredicateCode.transport_trans`,
  `AtomPredicateCode.transport_symm_cancel`,
  `AtomPermutationCode.toEquiv_ofPerm`, `AtomPermutationCode.toEquiv_refl`,
  `AtomPermutationCode.toEquiv_symm`, `AtomPermutationCode.toEquiv_trans`
- decoder/provenance: `FiniteDoctrineCode.toDoctrine`,
  `FiniteDoctrineCode.toDoctrine_extracts_iff`, `CartRawCode.WellFormed`,
  `CartRawCode.checkWellFormed_eq_true_iff`, `decodeCartDoctrineHom`,
  `toSemanticCart`, `toSemanticCart_sound`, `RealizableHom`,
  `realizableHomOf`
- closure: `idPresentation`, `toSemanticCart_idPresentation_hom`,
  `compPresentation`, `toSemanticCart_compPresentation_hom`,
  `cartPresentationSetoid`, `FiniteCodeCartHom`,
  `FiniteCodeCartHom.ofPresentation`, `typedPresentationToSemantic`,
  `FiniteCodeCartHom.toSemantic`, `FiniteCodeCartHom.comp`,
  `FiniteCodeCartCategory`, `finiteCodeCartCategory`,
  `finiteCodeCartRealization`,
  `finiteSourceCells`, `finiteSourceCells_nodup`,
  `finiteSourceCells_complete`, `CompatibleSource`,
  `compatibleSourceValues`, `compatibleSourceValues_nodup`,
  `compatibleSourceValues_complete`, `compatibleSourceEquiv`,
  `compatibleSourceValues_length_eq_card`, `pullbackDoctrineCode`,
  `pullbackInstanceCode`,
  `pullbackFstPresentation`, `pullbackSndPresentation`,
  `PullbackPresentation`, `pullbackPresentation`,
  `pullbackPresentation_commutes`, `pullbackSemanticLift`,
  `pullbackSemanticLift_fst`, `pullbackSemanticLift_snd`,
  `pullbackSemanticLift_unique`, `pullbackPresentation_isPullback`,
  `finiteCodeCartRealization_pullback_isPullback`
- fixed cartesian vocabulary: `CartProjection`, `CartNamedConstant`,
  `CartDerivedSet`, `CartUniversalEquality`, `CartConditionSyntax`,
  `evalCartCondition`, `evalCartCondition_atomMapIdentity_eq_true_iff`,
  `IdentityAtomComponent`, `evalCartCondition_atomMapIdentity_bridge`,
  `evalCartCondition_atomMapIdentity_replacement_invariant`
- finite checks: `finiteConstantSourceMap_not_injective`,
  `finiteWithoutComponentCAtomPredicate`,
  `finiteWithoutComponentC_holds_componentA`,
  `finiteWithoutComponentC_not_holds_componentC`,
  `finiteModelCodeSourceToFixture`, `finiteModelFixtureSourceToCode`,
  `finiteModelSourceEquiv`, `finiteModelSourceEquiv_zero`,
  `finiteModelSourceEquiv_one`, `finiteModelSourceEquiv_symm_all`,
  `finiteModelSourceEquiv_symm_withoutComponentC`,
  `finiteModelDoctrineCode`, `finiteModelDoctrineToFixture`,
  `finiteModelDoctrineFromFixture`, `finiteModelDoctrineRealizationIso`,
  `finiteConstantPresentation_check_true`, `finiteBadPointRawCode`,
  `finiteBadPointRawCode_not_wellFormed`,
  `finiteBadPointRawCode_check_false`,
  `extInstHom_sourceMap_injective_of_isIso`,
  `finiteConstantPresentation_not_isIso`,
  `finiteConstantRealizableHom`, `infiniteAllDoctrine`,
  `infiniteAllInstance`, `infiniteIdentityInput`,
  `infiniteIdentityInput_not_presented`,
  `infiniteIdentityInput_has_no_realizableHom`,
  `finiteConstantCompatibleSource_card`,
  `finiteConstantPullback_sourceCard`, `finiteConstantPullback_isPullback`,
  `finiteSwapPermutationCode_componentC`,
  `finiteConstant_identityAtom_check`,
  `finiteSwap_identityAtom_check_false`

この cycle は K0 の真部分 fiber witness を主張しない。constant cospan は
非可逆入力と Source 成長を検査する F0 witness であり、成分直積への
canonical map の非全射性を必要とする K0 witness は次段以降で別途構成する。
