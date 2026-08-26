# G-111 — indexed base-change schema と full-domain 診断共変性

- 一次仕様: [`research/goals/G-111-aat-indexed-base-change-schema.md`](../goals/G-111-aat-indexed-base-change-schema.md)
- tracking Issue: [#4158](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4158)
- target theorem: Indexed Base-Change Schema and Full-Domain Diagnostic Covariance Theorem
- proof state: `active / revised-card Cycle 4 F0 schema reselection`
- completion candidate: `no`

旧カードに対する PR #4161 / #4162 は棄却済みであり、改訂後 target の
checkpoint または predecessor evidence として使用しない。

## Cycle ledger

### Cycle 3 — rejected

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 3
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 58bc52a3a4d5acee234e6cbe00108224faa5773f
pr: 4164
reviewed_head: 45e2b936775520d23fd73617616ab898cd2f59de
result:
  result_type: rejected
  checkpoint: target-proof-checkpoint
  review_verdict: "3 Reject / 1 Accept"
  merged: no
  blocking_findings:
    - "comp / pasteVertical generated comparisons remained definitionally equal; route was an inert tag"
    - "public action structure accepted an arbitrary comparison field"
    - "universal edge law quantified only identity-base vertical fiber morphisms"
    - "3-cell alias did not select two generated routes"
    - "typed-term WellFormed views were equivalent to True"
  retained_evidence:
    - "full arrow/square leaf domain elaborated"
    - "horizontal/vertical component-route formulas elaborated"
    - "canonical G-109 action/lift provenance"
```

### Cycle 4 — validated raw input と term-indexed generated action

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 4
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 58bc52a3a4d5acee234e6cbe00108224faa5773f
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158: Cycle 3 rejected; Cycle 4 schema reselection"
  proof_dag_predecessors:
    - "G-110 PR #4153 final head a1471483, merge 315a2537"
    - "G-109 CorePseudofunctor canonical lift/functor/compositor/unitor API"
  proof_obligation: >-
    Reselect F0 so that decoder compatibility has positive and negative raw
    instances, every public producer consumes validated input, pasted terms are
    sent to recursive componentwise comparison routes rather than an inert tag,
    the square universal law quantifies arbitrary package-total morphisms, and
    the theorem-level 3-cell type names the actual comp and paste routes.
  expected_result_type: proof-obligation-discharged
  risks:
    - validated input is bypassed by a public caller-supplied action field
    - comp and pasteVertical generated comparisons are definitionally equal
    - square universal law silently restricts to identity-base fiber morphisms
    - 3-cell equality accepts arbitrary comparison inputs
  unchecked:
    - K0 identity/composition and horizontal/vertical outer-route coherence proofs
    - K1-K5 cocartesian compatibility, restriction, covariance, and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  proof_obligation_delta: >-
    IndexedBaseHomInput and IndexedBaseSquareInput are partial decoder inputs
    with decidable candidate-presence predicates and explicit positive/negative
    instances. Public fiber/total/square producers consume validated inputs.
    The square action is a definition with no caller-supplied comparison field:
    comp selects the canonical outer route, while horizontal/vertical paste
    recursively select componentwise routes. The comp/pasteVertical equality is
    no longer definitional and is the concrete theorem-level 3-cell obligation.
    IndexedUniversalSquareEdgeLaw quantifies every raw commutative square and
    every package-total morphism lying over its left edge, with its factorization
    theorem proved by strong cocartesian universality.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - IndexedBaseHomInput.WellFormed
    - IndexedBaseHomInput.ofTerm_wellFormed
    - IndexedBaseHomInput.missing_not_wellFormed
    - IndexedBaseSquareInput.WellFormed
    - IndexedBaseSquareInput.ofTerm_wellFormed
    - IndexedBaseSquareInput.missing_not_wellFormed
    - ValidatedIndexedBaseHom
    - ValidatedIndexedBaseSquare
    - indexedFiberAction
    - indexedTotalLift
    - indexedUniversalEdgeLaw
    - indexedSquareTotalMap
    - indexedUniversalSquareEdgeLaw
    - indexedSquareTermAction
    - indexedSquareTermAction_pasteHorizontal
    - indexedSquareTermAction_pasteVertical
    - IndexedHorizontalPastingCoherenceType
    - IndexedVerticalPastingCoherenceType
    - IndexedThreeCellCoherenceType
  claim_mapping:
    source_labels:
      - "target theorem (a): raw generator / indexed action / soundness type spine"
      - "target theorem stated scope: F0 universe and producer contract"
    conjuncts:
      - "all base arrows and commutative squares -> typed leaf terms -> positive validated inputs"
      - "malformed decoder candidates -> explicit missing negative instances"
      - "arrow fiber/total action -> validated input + G-109 canonical producer"
      - "all square/package-total edges -> indexedSquareTotalMap + indexedUniversalSquareEdgeLaw"
      - "horizontal/vertical paste -> recursive componentwise generated comparison"
      - "3-cell choice -> equality of actual comp and pasteVertical generated routes"
    undischarged_assumptions:
      - K0 coherence theorem bundle
      - K1-K5 material premises
    acceptance_point: >-
      F0 fixes the diagnostic-free schema signature and allowable generated
      producers. It does not claim K0, later conjuncts, or GOAL completion.
    port_status: unported
audits:
  premise_delta:
    discharged:
      - "decidable decoder compatibility with positive and negative raw instances"
      - "validated-input boundary for every public arrow/square action producer"
      - "universal arrow and square/package-total edge-law signatures"
      - "theorem-level concrete comp/paste 3-cell signature"
    remaining:
      - "K0-K5 material premises"
  certificate_provenance:
    discharged:
      - "fiber/total/square outputs are definitions from G-109 and category iso primitives"
      - "no public structure field accepts an action comparison"
    unresolved:
      - "K0 outer-vs-component route equality proofs"
  proof_use:
    used:
      - "coreFiberTransportFunctor/coreFiberLift in validated arrow action"
      - "IsStronglyCocartesian.map/fac in arbitrary square-total transport law"
      - "child square actions, compositors, whiskering, and associators in paste routes"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: >-
    Raw decoder inputs have concrete positive and negative instances. Every
    actual arrow and commutative square remains representable through ofTerm.
    The comp/paste equality is not definitional and remains an explicit K0 law.
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 235 declarations, standard axioms only"
    - "negative focused refutation: comp/pasteVertical generated comparison equality is not rfl"
    - "diff, Unicode, placeholder, prohibited vocabulary, privacy, import-direction, manifest, and umbrella scans: pass"
  allowable_producers:
    - "validated arrow fiber action: indexedFiberAction"
    - "validated arrow total lift: indexedTotalLift"
    - "validated square-total map: indexedSquareTotalMap"
    - "validated recursive square comparison: indexedSquareTermAction"
    - "canonical identity/composition comparisons"
  blocking_findings: []
  next_obligation: "K0 prove identity/composition and horizontal/vertical outer-route coherence"
```
