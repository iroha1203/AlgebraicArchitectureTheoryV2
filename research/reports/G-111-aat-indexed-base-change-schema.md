# G-111 — indexed base-change schema と full-domain 診断共変性

- 一次仕様: [`research/goals/G-111-aat-indexed-base-change-schema.md`](../goals/G-111-aat-indexed-base-change-schema.md)
- tracking Issue: [#4158](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4158)
- target theorem: Indexed Base-Change Schema and Full-Domain Diagnostic Covariance Theorem
- proof state: `active / revised-card Cycle 3 F0 schema typing`
- completion candidate: `no`

この report は改訂後の固定 GOAL に対する proof obligation delta を記録する。
旧カードに対する PR #4161 / #4162 はいずれも棄却済みであり、改訂後 target の
checkpoint または predecessor evidence として使用しない。

## Cycle ledger

### Cycle 3 — 改訂後 F0 morphism-indexed schema typing

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 3
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 58bc52a3a4d5acee234e6cbe00108224faa5773f
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158: active / F0 schema typing pending after PR #4163"
  proof_dag_predecessors:
    - "G-110 PR #4153 final head a1471483, merge 315a2537"
    - "G-109 CorePseudofunctor reviewed API: coreFiberLift/coreFiberTransportFunctor/compositor/unitor"
  proof_obligation: >-
    F0 schema typing: fix an intrinsically typed finite syntax whose leaves range
    over every ExtInst_U arrow and commutative square, whose constructors retain
    identity, sequential composition, horizontal paste, and vertical paste, and
    whose decode and generated action retain construction provenance, and whose
    only allowed producers are the canonical cleavage-derived fiber action,
    total lift, universal edge law, and square comparison
  selection_reason: >-
    F0 is the root of K0-K5 and decides whether the revised non-relabel statement
    is typeable without authored functor values or diagnostic conclusion fields
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
    - IndexedBaseHom
    - IndexedBaseSquareTerm
    - indexedFiberAction
    - indexedTotalLift
    - indexedSquareAction
  risks:
    - raw syntax restricts leaves to a proper subclass of ExtInst_U arrows or squares
    - an authored field supplies a functor, comparison, cocartesian certificate, or diagnostic conclusion
    - square paste is collapsed into sequential square composition after decode or action
    - package-total and CoreFiber universes do not align
  unchecked:
    - K0 horizontal/vertical component-route coherence proofs against the generated outer comparison
    - K1 generated-action/canonical-cleavage comp and paste compatibility as a new theorem
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The revised morphism-indexed F0 signature elaborates. IndexedBaseHom leaves
    quantify over arbitrary ExtInst_U arrows. IndexedBaseSquareTerm leaves quantify
    over arbitrary commutative squares, and comp/pasteHorizontal/pasteVertical are
    distinct finite constructors. Decoding and generated term actions retain an
    `IndexedSquareRoute`, with proved disequality between `comp` and
    `pasteVertical`. Well-formedness states decoder existence or the actual square
    boundary equation, rather than `True`. The universal package-total edge law,
    explicit horizontal/vertical component routes, their theorem-level coherence
    types against the generated outer comparison, and the theorem-level 3-cell
    equality type are fixed at F0.
    The only action producers are definitions generated from
    coreFiberTransportFunctor, coreFiberLift, coreFiberCompositor, and coreFiberUnitor.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - IndexedBaseHom.decode
    - IndexedBaseSquareTerm.commutes
    - IndexedBaseSquareTerm.decode
    - indexedFiberAction
    - indexedTotalLift
    - indexedTotalLift_projection
    - indexedUniversalEdgeLaw
    - indexedTotalLift_isStronglyCocartesian
    - indexedFiberIdentityComparison
    - indexedFiberCompositionComparison
    - indexedSquareAction
    - indexedSquareTermAction
    - IndexedBaseSquareTerm.decode_comp_route_ne_pasteVertical
    - indexedSquareTermAction_comp_route_ne_pasteVertical
    - IndexedHorizontalPastingCoherenceType
    - indexedHorizontalComponentRoute
    - IndexedVerticalPastingCoherenceType
    - indexedVerticalComponentRoute
    - IndexedThreeCellCoherenceType
  claim_mapping:
    theorem_names:
      - IndexedBaseHom.decode
      - IndexedBaseSquareTerm.commutes
      - IndexedBaseSquareTerm.decode
      - IndexedBaseSquareTerm.decode_comp_route_ne_pasteVertical
      - indexedTotalLift_projection
      - indexedUniversalEdgeLaw
      - indexedSquareAction
    source_labels:
      - "target theorem (a): raw generator layer"
      - "target theorem (a): indexed action type spine"
      - "target theorem stated scope: F0 universe contract"
    conjuncts:
      - "all base arrows -> IndexedBaseHom.leaf"
      - "all commutative base squares -> IndexedBaseSquareTerm.leaf"
      - "id / comp -> IndexedBaseHom.identity / comp and IndexedBaseSquareTerm.identity / comp"
      - "horizontal / vertical paste -> pasteHorizontal / pasteVertical"
      - "fiber output -> indexedFiberAction"
      - "total output over decoded arrow -> indexedTotalLift + indexedTotalLift_projection"
      - "universal package-total edge law -> IndexedUniversalEdgeLaw + indexedUniversalEdgeLaw"
      - "square output with un-erased construction route -> IndexedSquareTermActionType"
      - "horizontal / vertical component routes -> indexedHorizontalComponentRoute / indexedVerticalComponentRoute"
      - "horizontal / vertical coherence theorem types -> IndexedHorizontalPastingCoherenceType / IndexedVerticalPastingCoherenceType"
      - "3-cell choice -> theorem-level IndexedThreeCellCoherenceType"
    undischarged_assumptions:
      - K0 identity/composition and horizontal/vertical component-route coherence proofs
      - K1-K5 cocartesian compatibility, transported data, restriction, covariance, and witnesses
    acceptance_point: >-
      F0 fixes and elaborates the revised diagnostic-free schema signature and
      allowed producer list; it does not claim any later conjunct or GOAL completion.
    port_status: unported
audits:
  premise_delta:
    discharged:
      - "F0 well-formedness: decidable decoder-existence and actual commutative-boundary predicates"
      - "F0 universe contract for ExtInst_U, packageProjection, and CoreFiber"
      - "F0 allowed producer list: canonical cleavage definitions only"
      - "F0 universal edge-law signature and proof for every package-total morphism"
      - "F0 horizontal/vertical component routes, paste-coherence signatures, and theorem-level 3-cell signature"
    remaining:
      - "K0-K5 material premises"
  certificate_provenance:
    discharged:
      - "fiber/total/square outputs are definitions from reviewed G-109 canonical constructions"
    unresolved:
      - "K0 square-pasting coherence proof"
  proof_use:
    used:
      - "G-109 coreFiberTransportFunctor in indexedFiberAction"
      - "G-109 coreFiberLift and projection theorem in indexedTotalLift"
      - "G-109 coreFiberTransportMap_fac in indexedUniversalEdgeLaw"
      - "G-109 compositor/unitor in identity, composition, and square comparisons"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: >-
    No later K0-K5 semantic witness is claimed in F0. The raw domain is nonempty
    and unrestricted: every actual ExtInst_U arrow and every commutative square
    is a leaf. Intrinsic typing makes malformed terms unrepresentable; the
    well-formedness predicates expose the decoder and square equation actually used.
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean: pass"
    - "lake build ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw: targeted module pass"
    - "namespace audit: 179 declarations, standard axioms only"
    - "comp / pasteVertical decode and generated-action route disequality: focused Lean proof pass"
    - "placeholder, prohibited vocabulary, hidden/BiDi Unicode, privacy, import-direction, manifest, umbrella, and git diff scans: pass"
  allowable_producers:
    - "arrow fiber action: indexedFiberAction"
    - "arrow total lift: indexedTotalLift"
    - "universal edge-law proof: indexedUniversalEdgeLaw"
    - "identity comparison: indexedFiberIdentityComparison"
    - "composition comparison: indexedFiberCompositionComparison"
    - "square comparison: indexedSquareAction / indexedSquareTermAction"
  blocking_findings: []
  next_obligation: "K0 prove identity/composition and horizontal/vertical component-route coherence"
```
