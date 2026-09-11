# G-121 — Finite decoder representability

一次仕様は
[`research/goals/G-121-aat-finite-decoder-representability.md`](../goals/G-121-aat-finite-decoder-representability.md)
である。本 report は固定 target A--E の proof obligation、Lean 宣言、前提の出所、
proof-use、検証、査読結果を cycle ごとに記録する。

## Proof state

- fixed activation head: `492ed27ac66c0c89e8a680f986efa659cbba2472`
- fixed GOAL blob: `6ad52ff6177f3b895b3bed89e399a5afb9821f18`
- common criteria base: `492ed27ac66c0c89e8a680f986efa659cbba2472`
- acceptance contract blob: `eb8e1b230e1106cc3d2c826a037578d8dfea7a1f`
- tracking Issue: [#4458](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4458)
- current proof obligation: Cycle 1 review of A's raw code/continuous-map equivalence
- pending proof obligations: the remaining claims in A, then B--E
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: A's evaluation quotient and finite/infinite carrier classification

## Cycle 1 — Raw finite-exception code / continuous-map equivalence

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 1
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: dc226b7e1f6bfc5f2a4075be2cd1d0fbf32ccb56
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 initial proof state: A--E unproved"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode.eval
    - OnePoint.continuous_iff_from_discrete
  proof_obligation: "A1: construct the raw equivalence between finite-exception codes and continuous Bool-valued maps on the one-point compactification of the discrete Atom carrier, including both evaluations and both inverse laws"
  selection_reason: "A1 is the common topological predecessor for A's evaluation classification, B's continuous-extension characterization, and C's identification of default values with values at infinity."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/OnePointCode.lean
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeContinuousMapEquiv
  risks:
    - "taking finiteness of the inverse exception set as a supplied certificate"
    - "quotienting by pointwise evaluation instead of proving raw code equality"
    - "leaving the Atom topology as an additional parameter rather than fixing the discrete topology"
    - "forgetting the empty or finite carrier's value at infinity"
  unchecked:
    - "A's evaluation quotient, finite/infinite classification, existing-code comparison, and permutation transport"
    - "B--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the continuous extension directly from each finite-exception table; recovered the inverse exception Finset from continuity at infinity via the cofinite filter; proved the value at infinity and on every Atom; and proved both inverse laws at raw code and ContinuousMap level."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/OnePointCode.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap
    - AAT.AG.FiniteDecoderRepresentability.continuousMapToAtomPredicateCode
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_apply_infty
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_apply_coe
    - AAT.AG.FiniteDecoderRepresentability.continuousMapToAtomPredicateCode_exception_mem
    - AAT.AG.FiniteDecoderRepresentability.continuousMapToAtomPredicateCode_leftInverse
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_rightInverse
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeContinuousMapEquiv
  claim_mapping:
    theorem_names:
      - atomPredicateCodeToContinuousMap_apply_infty
      - atomPredicateCodeToContinuousMap_apply_coe
      - continuousMapToAtomPredicateCode_exception_mem
      - continuousMapToAtomPredicateCode_leftInverse
      - atomPredicateCodeToContinuousMap_rightInverse
      - atomPredicateCodeContinuousMapEquiv
    source_labels:
      - "fixed target A: E_D on raw codes and continuous maps"
      - "fixed target A: inverse finite set obtained from continuity"
    conjuncts:
      - "E_D(q)(infinity) is q.defaultValue"
      - "E_D(q)(x) is the existing q.eval x"
      - "the inverse exceptions are exactly the Atoms whose values differ from infinity"
      - "the inverse exception set is finite because continuity gives eventual equality along the cofinite filter"
      - "both inverse laws hold for raw codes and ContinuousMap values"
    undischarged_assumptions: []
    acceptance_point: "The public equivalence quantifies an arbitrary Atom carrier with DecidableEq only; the discrete topology is fixed locally, inverse finiteness is derived from continuity, and the left inverse proves structural code equality including the default field."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A1 continuous extension and inverse finiteness construction"
      - "A1 raw-code and continuous-map inverse laws"
    remaining:
      - "remaining A classification, comparison, and transport obligations"
      - "all B--E construction obligations"
  certificate_provenance:
    discharged:
      - "inverse Finset is constructed from the finite set derived by continuous_iff_from_discrete and eventually_cofinite"
    unresolved: []
  proof_use:
    used:
      - "AtomPredicateCode.exceptions finiteness supplies forward continuity"
      - "ContinuousMap.continuous supplies inverse exception finiteness"
      - "defaultValue and every exception membership are used in the raw left inverse"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/OnePointCode.lean; exit 0"
    - "namespace #assert_standard_axioms_only: standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "A2: define the evaluation relation and construct its quotient equivalence with finite-or-cofinite Bool predicates, then prove the finite and infinite carrier fiber classifications"
```

### Cycle 1 acceptance spine

`atomPredicateCodeToContinuousMap` extends `AtomPredicateCode.eval` and uses the authored
`defaultValue` at infinity. Its continuity proof consumes the existing finite `exceptions`
table. Conversely, `continuousMapToAtomPredicateCode` applies
`OnePoint.continuous_iff_from_discrete` to the actual `ContinuousMap.continuous` proof and
turns the resulting finite set of deviations from the infinity value into a `Finset`.
The two inverse theorems compare every field and every point; no semantic quotient or
caller-supplied continuity certificate stands between them.

Cycle 1 material premise roles are:

- `ambient-boundary`: an arbitrary fixed `AtomCarrier U` and the existing
  `AtomPredicateCode U`, with `DecidableEq U.Atom` required by its existing evaluator.
- `direction-hypothesis`: none.
- `discharge-required`: continuity of the forward map and finiteness of the inverse
  exception set; both are constructed in the definitions.
- `conclusion-equivalent-risk`: none. The inverse accepts a genuine continuous map, and
  its continuity proof is used to construct, rather than store, the finite exception set.
