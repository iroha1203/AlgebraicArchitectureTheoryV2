# G-126 — Operation preserving repair quotients

- Fixed GOAL: [`G-126-aat-operation-preserving-repair-quotients`](../goals/G-126-aat-operation-preserving-repair-quotients.md)
- Tracking Issue: [#4945](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4945)
- Applied GOAL and common-standard commit: `93cbcedece216238edfd40e2329bcc69c4f7ae2d`
- GOAL blob: `255a64df4bdc851f64f799ef89189ea81e78aa70`
- Proof state: A constructed; B–E and the three fixed examples remain open.

The fixed statement and completion criteria are in the GOAL card. This report
indexes proof evidence and the next obligations.

## A: operation congruences and endpoints

| GOAL clause | Declaration | Input and proof use |
| --- | --- | --- |
| Named total operations and finite words, including the empty word | `OperationSystem`, `OperationSystem.eval`, `eval_nil`, `eval_cons`, `eval_append` | `step` is input; evaluation is constructed by `List.foldl` and used by `behavior` |
| Complete lattice of stable equivalence relations | `OperationCongruence`, its `CompleteLattice` instance | Stability is part of the defined class; arbitrary intersections are stable and supply the lattice infimum |
| Least congruence containing `R` | `generated`, `generated_contains`, `generated_le_iff` | `R` is input; the endpoint is an intersection over all stable equivalences containing it |
| Greatest congruence inside the observation kernel | `behavior`, `behavior_iff`, `behavior_le_kernel`, `le_behavior_iff` | `observe` is input; word evaluation proves stability and the maximality implication |
| Compatibility of the two endpoints | `generated_le_behavior_iff` | Uses generated minimality with the constructed behavioral endpoint |

The accepted spine proposed for A is `OperationCongruence` → `generated` and
`behavior` → `generated_le_iff` and `le_behavior_iff`. The supporting word
lemmas are scaffolding. The endpoint construction uses no finite, nonempty,
operation invariance, or finite-observation premise.

## Remaining proof obligations

1. B: repair quotient objects and all structure preserving maps; order
   classification, existence equivalences, endpoint universal properties, and
   factorization into arbitrary target sets.
2. C: joins, sequential quotients, coherence, and maps between inputs.
3. D: one executable finite table algorithm with correctness, short failure
   words, and the stated cost upper bound.
4. E: the existing `FiniteLawFamily` and `Reading` bridge and path requests.
5. Three fixed examples and empty input cases, evaluated through the same
   general API and finite algorithm.

## Cycle 1 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 1
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: edffbae079fee4544fae8c2f5d5df83b393c1e74
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 initial proof state"
  proof_dag_predecessors: ["Mathlib.Data.Setoid.Basic"]
  proof_obligation: "A: construct the complete lattice and both endpoints from raw inputs"
  selection_reason: "B through E depend on these endpoints and their universal properties"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/Basic.lean", "OperationRepair/Endpoints.lean"]
  risks: ["intersection stability", "word direction", "empty state and operation types"]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "A's complete lattice, generated minimum, and behavioral maximum are constructed"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/Basic.lean", "OperationRepair/Endpoints.lean"]
  evidence: ["generated_le_iff", "le_behavior_iff", "generated_le_behavior_iff"]
  claim_mapping:
    theorem_names: ["generated_le_iff", "behavior_le_kernel", "le_behavior_iff"]
    source_labels: ["G-126 A"]
    conjuncts: ["complete lattice: CompleteLattice instance", "least generated: generated_le_iff", "greatest behavioral: le_behavior_iff"]
    undischarged_assumptions: []
    acceptance_point: "A's endpoints arise from T, R, and observe without a supplied certificate"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["stable equivalence lattice", "generated leastness", "behavior maximality"]
    remaining: ["B", "C", "D", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["generated and behavior constructed from input"]
    unresolved: []
  proof_use:
    used: ["R in generated_contains", "T and observe in behavior and le_behavior_iff"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["check_research_modules.sh --focused ResearchLean/AG/OperationRepair/Endpoints.lean: pass", "lake build ResearchLean.AG.OperationRepair.Endpoints: pass", "#print axioms: standard axioms only", "git diff --check: pass", "placeholder and hidden Unicode scans: no matches"]
  blocking_findings: []
  next_obligation: "B: structure preserving repair quotients and kernel classification"
```
