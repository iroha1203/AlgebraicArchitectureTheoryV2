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

### Cycle 1 — F0a FiniteModel-backed cartesian presentation typing

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
    - G-101 ExactDoctrineHom / ExtInstHom / packageProjection
    - G-101 FiniteModel finiteTransportExactDoctrineHom
  proof_obligation: construct the FiniteModel-backed raw/validated CartPresentation layer, its CartSemanticInput realization and law-level soundness theorem, RealizableHom witness type and canonical constructor, and the fully enumerated conclusion-free CartConditionSyntax with a computable evaluator
  selection_reason: the base-change presentation and every K0-K4 node consume the same realizable pointed-arrow type; fixing this first dependent layer closes the nearest common dependency without bundling the independent G-106 diagnostic schema into the same cycle
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
  risks:
    - a decoder interface could accept arbitrary semantic payload instead of the reviewed FiniteModel data
    - a condition syntax could mention lift existence, mate coherence, or checker output
    - universe zero finite data could silently weaken the required universe-polymorphic interfaces
  unchecked:
    - fixed-head independent review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed a universe-polymorphic FiniteModel-backed pointed-arrow presentation with 108 raw codes and 10 validated codes, generated all semantic morphism laws in the decoder, exposed a noninjective exact source map, and fixed the four-constructor conclusion-free cartesian condition language with nonconstant evaluation
  completion_candidate: no
  lean_artifacts:
    - FiniteModelBacking / FiniteModelBacking.transportAtomEquiv
    - FiniteDoctrineCode / FiniteSourceCode / FiniteInstanceCode / FiniteHomCode
    - CartRawCode / CartRawCode.WellFormed / ValidatedCartCode
    - CartSemanticInput / CartPresentation / toSemanticCart
    - finiteAtomTransportHom / finiteConstantToAllHom
    - toSemanticCart_sound
    - RealizableHom / realizableHomOf
    - CartFieldKind / CartProjection / CartDerivedSet / CartCellTest
    - CartConditionSyntax / evalCartCondition
  evidence:
    - Schema.lean single-file focused elaboration
    - namespace axiom audit with 334 declarations and standard axioms only
    - direct axiom audit of 13 public-spine declarations
    - finite code evaluation: doctrine=3, source=2, instance=6, hom=3, raw=108, validated=10
    - positive identity/transport/constant raw codes and a rejected malformed identity code
    - finiteConstantPresentation_not_injective
    - condition evaluator true/false firing theorems
  claim_mapping:
    theorem_names:
      - FiniteModelBacking.transportAtomEquiv_ne_refl
      - finiteMalformedIdentityRawCode_not_wellFormed
      - finiteConstantToAllHom_not_injective
      - toSemanticCart_sound
      - finiteConstantPresentation_not_injective
      - evalCartCondition_atomTransport_injective
      - evalCartCondition_constant_not_injective
      - evalCartCondition_atomTransport_nonidentity
    source_labels:
      - target theorem (B), two-layer input typing and FiniteModel-backed schema
      - target proof artifacts, raw/validated CartPresentation and CartSemanticInput
      - H_cart qualification clause (i), fully enumerated fixed condition language
    conjuncts:
      - raw code and decidable well-formedness are separated from semantic decoding
      - semantic decoding produces actual ExactDoctrineHom and ExtInstHom laws
      - RealizableHom carries a presentation provenance equality rather than a lift certificate
      - condition syntax has exactly equality, derived membership, finite-cell universal test, and conjunction constructors
      - a decoded nonidentity/noninjective bottom morphism exists in the finite schema
    undischarged_assumptions:
      - F0b base-change diagnostic presentation and cartesian regime typing
      - presentation constructors and replacement invariance
      - all K0-K4 theorem obligations
    acceptance_point: all semantic arrows are generated from the fixed finite codes and a representation backing; no authored field contains a package lift, strong-cartesian certificate, mate, checker result, or target conclusion
    port_status: unported
audits:
  premise_delta:
    discharged:
      - F0a CartPresentation / CartSemanticInput / RealizableHom typing
      - FiniteModel-backed raw/validated decoder and actual normalize_eq / extraction_iff / source_eq laws
      - fixed conclusion-free CartConditionSyntax and evaluator
    remaining:
      - F0b and K0-K4 fixed GOAL obligations
  certificate_provenance:
    discharged:
      - atom transport is conjugated from G-101 finiteTransportAtomEquiv
      - exact-morphism law proofs are constructed inside finiteAtomTransportHom / finiteConstantToAllHom
      - toSemanticCart reads only validated finite code and FiniteModelBacking
    unresolved:
      - later checker bridge, regime producer, pullback and BC constructions
  proof_use:
    used:
      - FiniteModelBacking.atomEquiv in both doctrine decoding and conjugated nonidentity transport
      - CartRawCode.WellFormed in endpoint-dependent ExtInstHom decoding
      - decoded ExactDoctrineHom laws in toSemanticCart_sound
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
    - lake build ResearchLean.AG.DoctrineFiberProduct.Schema: targeted dependency closure pass; no aggregate/full Research build
    - '#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct: 334 declarations, pass'
    - direct '#print axioms': only propext, Classical.choice, Quot.sound where present
    - placeholder / hidden-BiDi / privacy / reverse-import / git diff scan: pass
  blocking_findings: []
  next_obligation: F0b BCPresentation / BCSemanticInput / pre-BC diagnostic schema / CartesianRegime / authored-relative BC domain typing
```

次 obligation は F0b(`BCPresentation` / `BCSemanticInput` / diagnostic schema /
`CartesianRegime` / authored-relative BC domain)であり、F0 全体の省略ではない。
