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
  proof_obligation_delta: fixed an elaborating four-field finite-code realization spine with presentation-varying first-order Source, decoded finite/cofinite Atom predicates and finite-support permutations, arbitrary source maps, raw/validated separation, semantic soundness and provenance, id/comp/pullback constructors, and a pullback realization theorem against every semantic ExtInst cone
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - pullbackPresentation_isPullback
    - toSemanticCart_sound
    - toSemanticCart_idPresentation_hom
    - toSemanticCart_compPresentation_hom
    - finiteConstantPresentation_not_isIso
    - finiteConstantPullback_sourceCard
    - finiteConstantPullback_isPullback
    - evalCartCondition_atomMapIdentity_bridge
    - evalCartCondition_atomMapIdentity_replacement_invariant
  claim_mapping:
    theorem_names:
      - FiniteDoctrineCode.toDoctrine
      - decodeCartDoctrineHom
      - toSemanticCart_sound
      - pullbackPresentation_isPullback
      - CartConditionSyntax
      - evalCartCondition
      - finiteConstantPresentation_not_isIso
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
      - pullback source re-enumeration and projection presentations remain finite-code
      - generated semantic projection square is an ExtInst categorical pullback for arbitrary semantic cones
      - fixed four-constructor Cart condition syntax over the completely enumerated cartesian projections, constants, relations, and derived finite sets
    undischarged_assumptions: []
    acceptance_point: every selected F0a artifact is generated from the four raw fields; neither semantic morphisms nor pullback proofs nor condition bits are caller-authored, and the finite constant witness proves that sourceMap was not narrowed to equivalences
    port_status: unported
audits:
  premise_delta:
    discharged:
      - finite-code Cart presentation and semantic realization bridge
      - realization soundness for normalize_eq, extraction_iff, and source_eq
      - id / comp / pullback closure of the Cart realization image
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
    unresolved: []
  proof_use:
    used:
      - both cospan source-map equations in CompatibleSource and semantic cone lift construction
      - both cospan atomEquiv components in the second projection and cone factorization
      - normalize_eq, extraction_eq, and source_eq in decoder soundness and pullback realization
      - finite-support support/table data in permutation decoding and condition evaluation
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 482 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 22 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted module check
    - direct #print axioms on all 53 acceptance-spine declarations: only propext, Classical.choice, and Quot.sound
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b BC presentation, authored 2-cell, condition-language, and CartesianRegime typing
```

Cycle 1 の旧 fixed-card head に対する `goal defect` と PR #4035 の rejected
artifact は tracking Issue #4034 を正本とする。PR #4037 でカードが改訂されたため、
旧 fixed-two-source schema は本 cycle の受理証拠として再利用しない。

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
  `CompatibleSource`, `pullbackDoctrineCode`, `pullbackInstanceCode`,
  `pullbackFstPresentation`, `pullbackSndPresentation`,
  `PullbackPresentation`, `pullbackPresentation`,
  `pullbackPresentation_commutes`, `pullbackSemanticLift`,
  `pullbackSemanticLift_fst`, `pullbackSemanticLift_snd`,
  `pullbackSemanticLift_unique`, `pullbackPresentation_isPullback`
- fixed cartesian vocabulary: `CartProjection`, `CartNamedConstant`,
  `CartDerivedSet`, `CartUniversalEquality`, `CartConditionSyntax`,
  `evalCartCondition`, `evalCartCondition_atomMapIdentity_eq_true_iff`,
  `IdentityAtomComponent`, `evalCartCondition_atomMapIdentity_bridge`,
  `evalCartCondition_atomMapIdentity_replacement_invariant`
- finite checks: `finiteConstantSourceMap_not_injective`,
  `extInstHom_sourceMap_injective_of_isIso`,
  `finiteConstantPresentation_not_isIso`,
  `finiteConstantCompatibleSource_card`,
  `finiteConstantPullback_sourceCard`, `finiteConstantPullback_isPullback`,
  `finiteSwapPermutationCode_componentC`,
  `finiteConstant_identityAtom_check`,
  `finiteSwap_identityAtom_check_false`

この cycle は K0 の真部分 fiber witness を主張しない。constant cospan は
非可逆入力と Source 成長を検査する F0 witness であり、成分直積への
canonical map の非全射性を必要とする K0 witness は次段以降で別途構成する。
