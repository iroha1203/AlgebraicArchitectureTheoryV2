# G-111 — indexed base-change calculus と coherent diagnostic assembly

- 一次仕様: [`research/goals/G-111-aat-indexed-base-change-schema.md`](../goals/G-111-aat-indexed-base-change-schema.md)
- tracking Issue: [#4158](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4158)
- target theorem: Indexed Base-Change Calculus and Coherent Diagnostic Assembly Classification Theorem
- proof state: `active / human-approved revision under review; F0 selected after merge`
- completion candidate: `no`

旧カードに対する PR #4161 / #4162 は棄却済みであり、改訂後 target の
checkpoint または predecessor evidence として使用しない。

## 2026-08-26 human-approved target revision

Cycle 7 は、等しい source path と二つの independently validated square
だけから target path equality を一様生成する旧 K1.5 conjunct を有限反例
で否定した。人間裁定により、Gr4 の責務を次の三面へ分離した。

1. 全 base 射・全可換 square 上の pointwise indexed calculus(O1–O2)は
   Cycle 4–6 の reviewed artifact を保持する。
2. incidence-independent (d1)–(d6) は、診断語彙を含まない
   `IndexedBaseDiagram` / `IndexedBaseDiagramHom` が与える coherent
   diagram morphism 全域で、declared base relation に相対して assembly
   する。target `twoCellBase` はこの direction hypothesis の canonical
   realizationであり、raw family からの生成成果とは数えない。
3. arbitrary raw square family の自動 assembly は主張せず、一様持上げ
   可能性と `Epi` の必要十分性、vertexwise-epi producer、非 epi
   coherent 正例、Cycle 7 non-liftable 負例として分類する。

この改訂は Cycle 7 の反証を消去しない。旧 target は
`target-refuted` のまま履歴に残り、その有限反例は改訂 target の必須
負枝へ移る。次の単一 proof obligation は F0:
diagnostic import を持たない base diagram / hom の Lean signature と
path-naturality API の型付けである。raw-family classification は
(i) 一頂点・全 right legs の local uniform liftability iff `Epi`、
(ii) finite family support 上の vertexwise-epi sufficiency producer、
(iii) coherent domain の非 epi positive、(iv) Cycle 7 negative に分ける。
fixed-family の偶発的 liftability iff `Epi` は主張しない。nontrivial
(d4)–(d6) witness は別の named cell / connected subdiagram で構成し、
非 epi positive の因果的 diagnostic 発火とは表示しない。

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

### Cycle 5 — generated transport coherence と canonical lift compatibility

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 5
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: e08c82663ce0f63a173528b06625ca1849a52da2
tracking_issue: 4158
pr: 4166
selection:
  proof_obligation: >-
    Discharge the (a)-soundness/K0 coherence API and the linked K1(b1)
    canonical-lift compatibility for the Cycle 4 validated raw schema: prove
    the generated identity and composition comparisons at the total-lift
    level, prove that every recursively generated square action identifies
    the two canonical iterated lifts, and derive horizontal, vertical, and
    comp-versus-paste 3-cell equalities rather than accepting them as authored
    data. The shared evidence is recorded once and mapped to both obligations.
  expected_result_type: proof-obligation-discharged
  risks:
    - pasting equality follows only from definitional reduction
    - comparison equality is postulated or supplied by the caller
    - proof bypasses the canonical strongly cocartesian lift
  unchecked:
    - K1(b2) strongly cocartesian preservation
    - K1.5-K5 transported-data adapter, restriction, covariance, and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  proof_obligation_delta: >-
    Identity and composition comparisons now have total-lift factorization
    theorems. A structural induction over the decoded square term proves that
    leaf, identity, comp, horizontal paste, and vertical paste actions all
    identify the corresponding canonical iterated lifts. Strongly
    cocartesian uniqueness then proves the horizontal outer-route equality,
    vertical outer-route equality, and the actual comp-versus-pasteVertical
    3-cell equality. These theorems discharge the (a)-soundness/K0 API and,
    without being counted a second time, the K1(b1) canonical-lift
    compatibility obligation at the underlying total-morphism level.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - indexedFiberIdentityComparison_hom_fac
    - indexedFiberCompositionComparison_hom_fac
    - indexedSquareOuterComparison_hom_fac
    - indexedSquareTermAction_hom_fac
    - indexedHorizontalPastingCoherence
    - indexedVerticalPastingCoherence
    - indexedThreeCellCoherence
  premise_delta:
    discharged:
      - K0 generated identity/composition coherence
      - K0 horizontal and vertical outer-versus-component route equality
      - K0 comp-versus-pasteVertical 3-cell equality
      - K1(b1) canonical lift compatibility and id/comp/paste coherence
    remaining:
      - K1(b2) strongly cocartesian preservation
      - K1.5-K5 material premises
  certificate_provenance:
    discharged:
      - comparisons are generated by the G-109 unitor, compositor, and square action
      - route equality is derived from canonical lift factorization and uniqueness
    unresolved:
      - K1(b2), K1.5-K5 theorem and witness certificates
  proof_use:
    used:
      - coreFiberUnitorApp_hom_fac
      - coreFiberCompositorApp_hom_fac
      - coreFiberTransportMap_fac
      - coreFiberLift_eqCast_fac
      - coreFiberIteratedLift_isStronglyCocartesian
      - Functor.IsStronglyCocartesian.ext
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 295 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K1(b2) prove strongly cocartesian preservation, then K1.5 construct the morphism-indexed transported-data adapter"
audits:
  initial_review:
    exact_head: 8c9e6ee1363acd8659507734e30fc0614a647bd0
    verdict: "3 Accept / 1 Reject"
    central_finding:
      - >-
        The report counted all total-lift factorization and paste coherence as
        K0 while leaving K1(b1) canonical lift compatibility wholly pending,
        creating a proof-DAG mismatch and double-counting risk.
    correction:
      - >-
        Split the claim mapping between (a)-soundness/K0 and K1(b1), mark
        K1(b1) discharged by the same evidence without duplicate credit, and
        retain K1(b2) plus K1.5-K5 as the exact remaining obligations.
  rerun:
    exact_head: f90a1e2a4132504e73f0af7c59650942e4652fa8
    verdict: "4 Accept / 0 Reject; No major findings"
    blocking_findings: []
```

### Cycle 6 — square transport preserves strongly cocartesian morphisms

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 6
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 200401e9c2f6ca9adb29bb4e0c946ed49ba32aa8
tracking_issue: 4158
pr: 4167
selection:
  proof_obligation: >-
    Discharge K1(b2): for every validated commutative square and every
    strongly cocartesian total morphism over its left edge, prove that the
    square-generated total morphism is strongly cocartesian over the right
    edge. This preservation theorem must use the same Cycle 4 producer and
    may not be replaced by the strongness of a single canonical lift.
  expected_result_type: proof-obligation-discharged
  risks:
    - restating canonical-lift existence instead of preservation
    - accepting target strongness as an input certificate
    - defining a separate action that bypasses indexedSquareTotalMap
  unchecked:
    - K1.5-K5 transported-data adapter, restriction, covariance, and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  proof_obligation_delta: >-
    indexedSquareTotalMap_isStronglyCocartesian consumes a strongly
    cocartesian left-edge total morphism, composes it with the canonical
    bottom lift, rewrites the resulting strong composite through the universal
    square-edge law and square commutativity, and cancels the canonical top
    lift by IsStronglyCocartesian.of_comp. The conclusion is strongness of the
    exact indexedSquareTotalMap output over the right edge.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - indexedSquareTotalMap_isStronglyCocartesian
    - indexedUniversalSquareEdgeLaw
    - indexedSquareTotalMap_isHomLift
  premise_delta:
    discharged:
      - K1(b2) strongly cocartesian preservation
    remaining:
      - K1.5-K5 material premises
  certificate_provenance:
    discharged:
      - target strongness is derived from the source direction hypothesis and the generated square map
    unresolved:
      - K1.5-K5 theorem and witness certificates
  proof_use:
    used:
      - indexedUniversalSquareEdgeLaw
      - coreFiberLift_isStronglyCocartesian
      - Functor.IsStronglyCocartesian.comp
      - Functor.IsStronglyCocartesian.of_comp
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 296 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K1.5 construct the morphism-indexed transported-data adapter"
audits:
  initial_review:
    exact_head: 0040adab3b2926f4c206ba5e85d0f3862ed90494
    verdict: "4 Accept / 0 Reject; No major findings"
    blocking_findings: []
```

### Cycle 7 — K1.5 two-cell base-congruence no-go

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 7
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: d552c4b57c12b523cb2f94dc093b892f60abfdd8
tracking_issue: 4158
selection:
  proof_obligation: >-
    Construct K1.5, the morphism-indexed adapter from the Cycle 4 generated
    action to the G-110 DiagnosticPackageTotalAction interface, and then use
    that same output in K2. In particular, determine whether source two-cell
    base equalities generate the target twoCellBase field without accepting
    target diagnostic data or a target equality certificate from the caller.
  expected_result_type: proof-obligation-discharged-or-formal-stop
  risks:
    - supplying target twoCellBase as authored adapter input
    - silently cancelling a non-epimorphic vertex transport index
    - restricting the full ExtInst_U domain to epimorphic indices
result:
  proposed_result_type: target-refuted
  completion_candidate: no
  proof_obligation_delta: >-
    Pasting validated edge squares transports a source equality only to an
    equality after precomposition by the vertex index. The generic theorem
    indexedTargetBaseCongruenceAt_iff_epi identifies unrestricted cancellation
    with Epi. More decisively, the target-scoped witness duplicates every
    source of the reviewed finite doctrine by a Boolean tag. The false-tag
    inclusion is a valid ExtInst arrow. Target identity and constant-tag
    endomorphisms are distinct but agree after that inclusion. They form two
    actual ValidatedIndexedBaseSquare leaves over the same source identity
    edge. finiteTwoLoopPresentation and finiteTwoLoopSourceData provide one
    finite two-loop presentation with an admissible source two-cell whose path
    bases are equal. IndexedValidatedTwoCellBaseGeneration states the exact
    full-domain bridge from an equal source-path pair plus its two validated
    squares to the target path-base equality, and
    finiteValidatedSquares_refute_twoCellBaseGeneration proves its negation.
    Thus the fixed full-domain K1.5/K2 target twoCellBase conjunct has a
    concrete counterexample.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeTwoCellNoGo.lean
  evidence:
    - indexedTargetBaseCongruenceAt_iff_epi
    - finiteOneToTwo_comp_identity_eq_constant
    - finiteTwoSourceIdentity_ne_constant
    - finiteOneToTwoIndex_not_epi
    - finiteOneToTwo_no_targetBaseCongruence
    - indexedTargetBaseCongruenceAt_identity
    - finiteDuplicateIndex_comp_identity_eq_constant
    - finiteDuplicateIdentity_ne_constant
    - finiteDuplicateIdentitySquare
    - finiteDuplicateConstantSquare
    - finiteTwoLoopPresentation
    - finiteTwoLoopSourceData
    - finiteTwoLoopValidatedSquare
    - IndexedValidatedTwoCellBaseGeneration
    - finiteValidatedSquares_refute_twoCellBaseGeneration
  premise_delta:
    discharged: []
    candidate_route_only:
      - >-
        Existing APIs suggest component mappings for vertex packages, edge
        maps, edge strongness, and endpoint comparators; no assembled adapter
        is constructed or discharged in this cycle.
    remaining:
      - K1.5 target twoCellBase generation and complete transported-data adapter
      - K2 arbitrary-source target transported data
      - K3 C0-C3 restriction comparison
      - K4 d1-d6 full-domain covariance
      - K5 named nonvacuity and proper-extension witnesses
  certificate_provenance:
    rejected_inputs:
      - caller-supplied target twoCellBase
      - caller-supplied global base action or base-congruence certificate
    rejected_repairs:
      - >-
        Requiring every index to be epi removes the finite witness but weakens
        the fixed full ExtInst_U domain.
      - >-
        Replacing arbitrary validated right-edge squares by images of a global
        endofunctor changes the fixed all-square meaning; it is a possible new
        target, not a same-semantics signature repair.
  proof_use:
    used:
      - CategoryTheory.epi_iff_forall_injective
      - cancel_epi
      - ExtInstHom.ext
      - ExactDoctrineHom.ext
      - typedPresentationToSemantic
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 31 declarations, standard axioms only"
  blocking_findings: []
  stop_condition: >-
    target-refuted: one admissible finite source two-cell and two actual F0
    validated square leaves have equal source path bases but distinct target
    path bases. Epi restriction or globally generated right edges would change
    the fixed target. Any replacement target is reserved to the human owner.
audits:
  initial_review:
    exact_head: 377145efb4956445414a8283c88e38e7b38713d4
    verdict: "0 Accept / 4 Reject"
    central_findings:
      - >-
        The first artifact proved only a generic non-epi cancellation
        obstruction and did not connect it to finite admissible source data,
        actual F0 validated squares, or the K1.5/K2 target bridge.
      - >-
        The goal-defect classification assumed without proof that a global
        base action preserved the same all-square semantics; if the fixed
        bridge is refuted, the failure policy instead requires target-refuted.
      - >-
        Component API mappings were described as constructible without an
        assembled Lean adapter.
    correction:
      - >-
        Add a satisfying identity-index instance, a duplicated-source finite
        doctrine, two explicit validated square leaves, a one-vertex/two-loop
        presentation with admissible source data, and the exact target
        twoCellBase generation law plus its refutation.
      - >-
        Reclassify the stop as target-refuted and mark component mappings as an
        unassembled candidate route rather than discharged output.
  rerun:
    exact_head: c1b50f467f8734543d7270d17e88ca5bba293a83
    verdict: "4 Accept / 0 Reject; No major findings"
    blocking_findings: []
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
    IndexedBaseHomInput and IndexedBaseSquareInput are recursive partial raw
    syntax. Their decoders fail on missing arrow leaves or missing square
    commutativity witnesses, yielding decidable positive and negative trees.
    Validated artifacts retain the successfully decoded typed term and its
    decoder equation. Public fiber/total/square producers consume those
    validated artifacts.
    The square action is a definition with no caller-supplied comparison field:
    comp selects the canonical outer route, while horizontal/vertical paste
    recursively select componentwise routes. The comp/pasteVertical equality is
    no longer definitional and is the concrete theorem-level 3-cell obligation.
    IndexedUniversalSquareEdgeLaw quantifies every raw commutative square and
    every package-total morphism lying over its left edge, with its factorization
    theorem proved by strong cocartesian universality; a separate public theorem
    records that the generated morphism lies over the square's right edge.
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
    - indexedSquareTotalMap_isHomLift
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
      - "raw trees with a missing arrow or commutativity leaf -> explicit negative instances"
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
  initial_review:
    exact_head: e621df12e6c8240c9a382372f20b641e4c51d8f1
    verdict: "4 Reject / 0 Accept"
    central_findings:
      - "typed-term Option wrappers did not validate a recursive raw payload"
      - "public raw/decoded square comparison helpers bypassed validated recursive action"
      - "square-total output lacked a public right-edge IsHomLift theorem"
    correction:
      - "replace whole-term Option wrappers by recursive partial raw trees"
      - "store decoder success equation and decoded term in validated artifacts"
      - "make raw outer helpers private and require validated children in public component routes"
      - "publish indexedSquareTotalMap_isHomLift"
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
    Recursive raw decoder inputs have concrete successful trees and failed
    trees with missing leaves. Every actual arrow and commutative square remains
    representable through ofTerm.
    The comp/paste equality is not definitional and remains an explicit K0 law.
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit after initial-review correction: 288 declarations, standard axioms only"
    - "negative focused refutation: comp/pasteVertical generated comparison equality is not rfl"
    - "diff, Unicode, placeholder, prohibited vocabulary, privacy, import-direction, manifest, and umbrella scans: pass"
  allowable_producers:
    - "validated arrow fiber action: indexedFiberAction"
    - "validated arrow total lift: indexedTotalLift"
    - "validated square-total map: indexedSquareTotalMap"
    - "validated recursive square comparison: indexedSquareTermAction"
    - "validated outer square comparison: indexedSquareOuterComparison"
    - "validated child horizontal/vertical component routes"
    - "canonical identity/composition comparisons"
  blocking_findings: []
  next_obligation: "K0 prove identity/composition and horizontal/vertical outer-route coherence"
```
