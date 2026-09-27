# G-126 — Operation preserving repair quotients

- Fixed GOAL: [`G-126-aat-operation-preserving-repair-quotients`](../goals/G-126-aat-operation-preserving-repair-quotients.md)
- Tracking Issue: [#4945](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4945)
- Applied GOAL and common-standard commit: `93cbcedece216238edfd40e2329bcc69c4f7ae2d`
- GOAL blob: `255a64df4bdc851f64f799ef89189ea81e78aa70`
- Proof state: A–C proved in ResearchLean; D–E and the three fixed examples
  remain open.

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

1. D: prove the cost bound for the same finite success/failure procedure.
2. E: the existing `FiniteLawFamily` and `Reading` bridge and path requests.
3. Three fixed examples and empty input cases, evaluated through the same
   general API and finite algorithm.

## D: finite endpoint table loops (partial)

`FiniteTables.lean` stores the transition, observation, and request as
size-indexed arrays over `Fin m` and `Fin n`. It derives `system` and
`requestRel` from those tables. No repairability or answer certificate is an
input field. `FiniteClosure.lean` performs exactly `n²` synchronous rounds,
reading only the old Boolean relation and writing converse, transitive, and
operation-image cells into a new table. `closeStep_get_iff` proves the update
formula, `lower_fixed` proves stabilization by counting at most `n²` pairs,
and `computedLower_eq_generated` identifies the output with A's least
operation congruence.

`FiniteBehavior.lean` stores an optional concrete word for every pair.
`rounds_none_iff` proves that `none` means all words of the current bounded
length preserve observation equality; `rounds_some_sound` proves every stored
word separates its pair. `short_separator` removes loops in the pair-state
DFA, giving a separating word shorter than `n²` whenever one exists.
`computedUpper_iff_behavior` identifies the final `none` cells with A's
behavioral congruence, and `upper_some_certificate` proves the strict length
bound for stored words. The empty state and operation types require no
default element.

`FiniteConstruction.lean` builds ordered class representatives and concrete
sections from each computed partition, even for zero states. The success
branch of `runRepair` returns both numbered quotient tables, quotient maps,
descended operations and observations, and their factor map. Its equations
identify the kernels with `generated` and `behavior`, and its concrete section
gives the canonical quotient equivalence. The failure branch returns a pair
from the original request table and a stored word shorter than `n²`.
`runRepair_success_iff_repair_exists` and
`runRepair_failure_iff_no_repair` connect both outcomes to B's classification.
`FiniteEnumeration.lean` turns explicit state and operation numberings into
the exact raw tables consumed by this procedure; the transition, observation,
and request value equations are proved. The remaining D obligation is a
costed implementation of this same procedure and the stated uniform bound.

## Cycle 8 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 8
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: b970a93d1c00ec3cffe4c8aeb45bcea62e100869
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 7 comment and report D section"
  proof_dag_predecessors: ["OperationRepair/FiniteClosure.lean", "OperationRepair/FiniteBehavior.lean", "OperationRepair/Classification.lean"]
  proof_obligation: "D common output: numbered quotient tables, concrete maps, failure witness, and explicit enumeration bridge"
  selection_reason: "The verified endpoint engines need one output connected to B before cost instrumentation"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/FiniteConstruction.lean", "OperationRepair/FiniteEnumeration.lean"]
  risks: ["numbered class kernel", "empty states", "shared endpoint values", "classification equivalence", "cost model still open"]
  unchecked: ["D cost proof", "E", "fixed examples"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "A single finite outcome returns computed numbered endpoints or a stored original-request separator, with both cases matched to B"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/FiniteConstruction.lean", "OperationRepair/FiniteEnumeration.lean"]
  evidence: ["PartitionTable.standardEquiv", "runRepair_failure", "runRepair_success_iff_repair_exists", "runRepair_success_payload", "successLowerRepair", "successUpperRepair", "successFactorHom", "runRepair_failure_iff_no_repair", "FiniteEnumeration.Input.toTables_step", "FiniteEnumeration.Input.toTables_observe", "FiniteEnumeration.Input.toTables_wants"]
  claim_mapping:
    theorem_names: ["runRepair_failure", "runRepair_success_iff_repair_exists", "runRepair_failure_iff_no_repair", "success_lower_map_kernel", "success_upper_map_kernel"]
    source_labels: ["G-126 D output and correctness subclauses"]
    conjuncts: ["both numbered quotient tables", "descending operations and observations", "factor map", "short original-request separator", "existence and nonexistence equivalence", "numbered raw input bridge"]
    undischarged_assumptions: []
    acceptance_point: "Output and correctness subclaims only; D cost remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["numbered quotient representatives and sections", "output branch correctness", "classification connection", "explicit finite numbering"]
    remaining: ["D cost", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["both endpoints computed from raw input", "failure word stored by upper recurrence", "quotient maps built from computed partitions"]
    unresolved: []
  proof_use:
    used: ["lower closure in lower quotient", "upper words in decision and upper quotient", "request table in failure search", "operation and observation tables in descended output"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused checks: FiniteConstruction and FiniteEnumeration pass with standard axioms", "parent targeted build: FiniteConstruction pass", "module-level standard-axiom audits pass", "git diff --check and placeholder, hidden Unicode, privacy, import-direction scans pass"]
  blocking_findings: []
  next_obligation: "D costed execution and uniform O((m+1)(n+1)^5) proof"
```

## Cycle 7 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 7
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 83115265429dadc0794e2e098f4fe5d73cafcbaa
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 6 comment and report C section"
  proof_dag_predecessors: ["OperationRepair/Endpoints.lean"]
  proof_obligation: "D endpoint engines: numbered raw tables, lower synchronous closure, upper stored separator words"
  selection_reason: "The common decision and quotient constructor must use computed endpoints from the same raw tables"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/FiniteTables.lean", "OperationRepair/FiniteClosure.lean", "OperationRepair/FiniteBehavior.lean"]
  risks: ["sync update", "n² stabilization", "empty states", "word direction and bound", "cost model still open"]
  unchecked: ["common runRepair", "numbered quotient tables", "cost proof"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Both finite endpoint tables and stored short separator words are constructed and matched to generated and behavior"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/FiniteTables.lean", "OperationRepair/FiniteClosure.lean", "OperationRepair/FiniteBehavior.lean"]
  evidence: ["closeStep_get_iff", "lower_fixed", "computedLower_eq_generated", "rounds_none_iff", "short_separator", "computedUpper_iff_behavior", "upper_some_certificate"]
  claim_mapping:
    theorem_names: ["computedLower_eq_generated", "computedUpper_iff_behavior", "upper_some_certificate"]
    source_labels: ["G-126 D endpoint construction and separator-bound subclauses"]
    conjuncts: ["lower partition", "upper partition", "stored separator correctness", "strict n² word bound"]
    undischarged_assumptions: []
    acceptance_point: "Endpoint subclaims only; full D remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["numbered table input", "lower closure and fixed point", "upper behavior and short witness"]
    remaining: ["D common output and cost", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["lower and upper tables computed from raw inputs", "witness word stored by the same upper recurrence"]
    unresolved: []
  proof_use:
    used: ["request table in initial lower", "operation table in closure and word search", "observation table in base word cases"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused checks: FiniteTables, FiniteClosure, FiniteBehavior pass with standard axioms", "parent targeted builds: FiniteTables, FiniteClosure, FiniteBehavior pass", "#print axioms for eight endpoint spine declarations: propext, Classical.choice, Quot.sound only", "git diff --check and placeholder, hidden Unicode, import-direction scans: pass"]
  blocking_findings: []
  next_obligation: "D common success/failure output, numbered quotient tables, and cost"
```

## B: quotient and kernel core

| GOAL clause | Declaration | Proof route |
| --- | --- | --- |
| Repair quotient object, finite target, and uniqueness of descents | `RepairQuotient`, `RepairQuotient.finite_target`, `descended_step_unique`, `descended_observation_unique` | Input quotient is surjective by definition; finite target follows from finite source; any other descending operations or observation are equal by surjectivity; the target may live in an independent universe |
| Structure preserving morphisms and uniqueness/surjectivity | `RepairHom`, `RepairHom.unique`, `RepairHom.subsingleton`, `RepairHom.surjective`, `RepairHom.id`, `RepairHom.comp` | Surjectivity of the source map determines every morphism on all target values, including maps between target universes |
| Kernel in the interval | `RepairQuotient.kernel`, `generated_le_kernel`, `kernel_le_behavior`, `intervalPoint`, `standardEquiv`, `standardEquiv_mk` | Commuting operation and observation equations give stability and present observation equality; A's universal properties give both inequalities; a surjection canonically identifies its target with the standard kernel quotient |
| Actual quotient from each interval congruence | `quotientRepair`, `quotientRepair_kernel` | Quotient lifts the operations and observation; the relation is recovered exactly |
| Morphism existence and order direction | `RepairHom.nonempty_iff_kernel_le` | The reverse direction constructs a map from source representatives and proves both preservation laws |
| Existence and endpoints | `repair_exists_iff`, `generated_le_kernel_observe_iff`, `repair_exists_iff_request_behavior`, `lowerRepair`, `upperRepair`, `lower_hom`, `upper_hom` | Existence is derived from the interval; endpoint morphisms use kernel inclusion |

These declarations discharge the quotient-to-kernel and kernel-to-quotient
construction, uniqueness of descended data, and the morphism existence
criterion. The class order and arbitrary-target universal property are mapped
below. The constructed quotient proves its own operation,
observation, and request equations; it receives no repaired quotient data.

## Cycle 2 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 2
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 382e1562be529ca2b922f8c47edeca34ac116217
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 1 comment and this report's A section"
  proof_dag_predecessors: ["OperationRepair/Basic.lean", "OperationRepair/Endpoints.lean"]
  proof_obligation: "B core: two-way construction of repair quotient and interval kernel, and morphism existence"
  selection_reason: "A's endpoints now support the objects and maps required by B and C"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/Classification.lean"]
  risks: ["surjectivity", "operation/observation lift", "kernel order orientation", "structure-field escape"]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Both quotient/kernel constructions, descended-data uniqueness, and morphism iff kernel inclusion are proved"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/Classification.lean"]
  evidence: ["RepairQuotient.intervalPoint", "quotientRepair", "quotientRepair_kernel", "descended_step_unique", "descended_observation_unique", "RepairHom.nonempty_iff_kernel_le", "repair_exists_iff"]
  claim_mapping:
    theorem_names: ["quotientRepair_kernel", "RepairHom.nonempty_iff_kernel_le", "repair_exists_iff"]
    source_labels: ["G-126 B"]
    conjuncts: ["object/kernel correspondence", "morphism iff kernel inclusion", "repair existence iff endpoint inclusion"]
    undischarged_assumptions: []
    acceptance_point: "The selected B core is constructed from T, observe, R, and an interval congruence; remaining B obligations stay explicit"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["quotient operation/observation descent and uniqueness", "repair quotient kernel bounds", "morphism construction"]
    remaining: ["B isomorphism-class OrderIso", "B arbitrary-target universal property", "C", "D", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["interval congruence from actual quotient kernel or supplied classification variable", "constructed quotient from c"]
    unresolved: []
  proof_use:
    used: ["surjective read in morphism properties", "step_comm in kernel stability", "observation_comm in kernel upper bound", "c.stable and hobs in quotient construction"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["check_research_modules.sh --focused ResearchLean/AG/OperationRepair/Classification.lean: pass", "lake build ResearchLean.AG.OperationRepair.Classification: pass", "Classification in-module axiom audit: 60 declarations, standard axioms only", "#print axioms for 12 B spine declarations plus two descent uniqueness declarations: standard axioms only", "git diff --check: pass", "placeholder and hidden Unicode scans: no matches"]
  blocking_findings: []
  next_obligation: "B isomorphism-class OrderIso and arbitrary-target factorization"
```

## B: isomorphism classes and universal factorization

| Fixed B component | Lean declaration | Construction and proof use |
| --- | --- | --- |
| Actual structure-preserving isomorphism across target universes | `RepairIso`, `repairIso_iff_kernel_eq`, `canonicalRepairIso` | Opposite repair morphisms are inverses by surjectivity; every target is isomorphic over `S` to its kernel quotient |
| Classes exactly up to actual isomorphism | `repairClassSetoid`, `repairClass_eq_iff_iso`, `RepairClass` | The quotient relation is kernel equality and the equivalence theorem identifies it with actual isomorphism |
| Order isomorphism with the interval | `classKernel`, `classOfInterval`, `classKernel_classOfInterval`, `classOfInterval_classKernel`, `repairOrderIso` | Both inverse laws use `quotientRepair_kernel`; the order is kernel inclusion |
| Identity and composition | `repairHomOfLe`, `repairHomOfLe_refl`, `repairHomOfLe_comp` | `RepairHom.subsingleton` identifies the canonical map for each inclusion with identities and composites |
| Factorization into arbitrary target, without surjectivity | `mapKernel`, `generated_le_mapKernel`, `repairable_of_map`, `generatedLift`, `generatedLift_step`, `generatedLift_observation`, `generatedLift_unique`, `generated_universal` | An input map's kernel is a congruence; source request identification yields a lift by `Quotient.lift`; quotient induction proves preservation and uniqueness |

The abstract class construction uses a common universe for representatives;
`canonicalRepairIso` connects every repair quotient in an independent target
universe to a standard quotient in that class. `X` in `generated_universal` has
an independent universe and no finite or surjective hypothesis. The factor
is built from the original map and generated relation, not provided as data.

## Cycle 3 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 3
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 14f4cb24a4394aa3af5890a691706ca1061ef834
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 2 comment and report B core"
  proof_dag_predecessors: ["OperationRepair/Basic.lean", "OperationRepair/Endpoints.lean", "OperationRepair/Classification.lean"]
  proof_obligation: "B completion: actual-isomorphism class OrderIso and arbitrary-target universal factorization"
  selection_reason: "Closes B's remaining classification and universal-property obligations before C"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/ClassOrder.lean", "OperationRepair/Universal.lean"]
  risks: ["actual iso versus kernel equality", "universe strength", "identity/composition", "factor proof-use", "non-surjective target map"]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed actual repair isomorphisms, class OrderIso, functorial maps, and universal lift to arbitrary target"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/ClassOrder.lean", "OperationRepair/Universal.lean"]
  evidence: ["repairIso_iff_kernel_eq", "repairClass_eq_iff_iso", "repairOrderIso", "repairHomOfLe_comp", "generated_universal"]
  claim_mapping:
    theorem_names: ["repairIso_iff_kernel_eq", "repairOrderIso", "repairHomOfLe_refl", "repairHomOfLe_comp", "generated_universal"]
    source_labels: ["G-126 B"]
    conjuncts: ["actual isomorphism classes", "interval order isomorphism", "identity/composition", "arbitrary-target factorization and uniqueness"]
    undischarged_assumptions: []
    acceptance_point: "B's remaining claims follow from the constructed A endpoints and cycle-2 quotient/kernel core"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["actual iso/class equivalence", "class OrderIso", "arbitrary-target universal factorization"]
    remaining: ["C", "D", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["repairHomOfLe from kernel inclusion", "generatedLift from input map and generated relation"]
    unresolved: []
  proof_use:
    used: ["quotientRepair_kernel in inverse class laws", "source surjectivity in actual iso inverse", "hstep/hobserve/hR in universal factor"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["ClassOrder focused check: pass, 32 declarations standard axioms", "Universal focused check: pass, 9 declarations standard axioms", "lake build ResearchLean.AG.OperationRepair.Universal: pass", "#print axioms for 16 B completion declarations: standard axioms only", "git diff --check: pass", "placeholder and hidden Unicode scans: no matches"]
  blocking_findings: []
  next_obligation: "C: generated union/join, sequential quotient, and input maps"
```

## C: request families and maps between inputs

| Fixed C component | Lean declaration | Construction and proof use |
| --- | --- | --- |
| Union of a request family and generated join | `requestUnion`, `generated_requestUnion`, `generated_empty` | Universal property of `generated` gives both inclusion directions; the empty family yields equality relation |
| Individual versus joint repairability | `repairable_requestUnion_iff` | The generated join is below the fixed behavioral upper endpoint iff each term is below it |
| Maps between inputs | `InputHom`, `eval_comm`, `generated_preserve`, `behavior_preserve` | Pullback of target generated congruence proves lower preservation; word evaluation and observation preservation prove upper preservation |
| Maps between endpoint quotients and their square | `lowerMap`, `upperMap`, `_mk` rules, `endpoint_square`, `lowerMap_step`, `lowerMap_observation`, `upperMap_step`, `upperMap_observation` | Quotient lifts preserve the source map, descended operations, observation, and the lower-to-upper factorization |
| Identity, composition, and input isomorphisms | `InputHom.id`, `InputHom.comp`, `lowerMap_id`, `upperMap_id`, `lowerMap_comp`, `upperMap_comp`, `InputIso.lowerEquiv`, `InputIso.upperEquiv` | Quotient induction proves identity/composition; inverse input maps induce inverse quotient maps |

The maps of inputs require the fixed GOAL equations, with no injectivity or
surjectivity assumption on the input map. The endpoint quotient maps are
constructed from the preserved congruence relations, not supplied as data.
The finite-order and bracketing coherence evidence is indexed below.

## C: two-stage sequential quotient

| Fixed C component | Lean declaration | Construction and proof use |
| --- | --- | --- |
| Operations on the first quotient and image of the second request | `quotientSystem`, `imageRequest`, `quotientMap` | Descend each named operation using operation stability; form the literal image relation under the first quotient map |
| Second generated congruence | `generated_imageRequest_eq_kernel` | The image-generated operation congruence is proved equal to the kernel of the map from `S/c` to `S/(c ⊔ generated T R)`; the reverse inclusion pulls the generated congruence back to `S` and uses join minimality |
| Sequential quotient equivalence over `S` | `sequentialEquiv`, `sequentialEquiv_mk`, `sequentialEquiv_unique` | The third isomorphism theorem is applied after kernel identification; source representatives prove source compatibility and uniqueness |
| Operation and observation preservation | `sequentialEquiv_step`, `imageRequest_repairable`, `sequentialEquiv_observation` | Quotient induction proves the operation equation; repairability of both stages descends the observations and proves their agreement through the same equivalence |

The kernel theorem has no repairability premise. Observation descent uses exactly
`c ≤ behavior T observe` and `generated T R ≤ behavior T observe`, which hold
for the first generated congruence and second request in the fixed C claim.
The finite-order and bracketing coherence evidence is indexed below.

## C: finite orders, bracketings, and coherence

| Fixed C component | Lean declaration | Construction and proof use |
| --- | --- | --- |
| Quotient-stage infrastructure | `SequentialStage`, `sequentialBase`, `sequentialExtend`, `generated_mappedRequest_kernel` in `FiniteSequential.lean` | Each extension forms an actual quotient by a request's image under the composite source map and proves that its kernel joins the previous kernel with the new generated request |
| Recursive binary parentheses | `fullTreeStage`, `fullRepairTreeStage` in `FullTree.lean` | Both child subtrees are recursively constructed as quotient systems. The right child's actual kernel is mapped into the left child's current quotient; it is not replaced by an unconstructed leaf union |
| Raw-request image at each node | `generated_mappedRequest_congr`, `fullTree_branch_image`, `fullRepairTree_branch_image` | The right-child kernel and the union of its raw leaf requests generate the same congruence after mapping to the current left stage |
| Repair and observation at every node | `sequentialExtend_image_repairable`, `sequentialExtend_observation_comm`, `RepairableSequentialStage`, `repairableSequentialExtend` | Every node has descended observation, the next image request is repairable against it, and the next observation agrees on its actual quotient map |
| All orders and parentheses | `fullRepairTreeStage_generated`, `fullRepairTreeCompare`, `_read`, `_step`, `_observation`, `_unique` | Any two fully evaluated trees whose leaf lists are permutations have a unique source-commuting operation- and observation-preserving comparison |
| Coherence | `fullRepairTreeCompare_coherent` | Source surjectivity makes the composite comparison equal to the direct comparison |
| Finite indexed family | `indexedFamilyTree_request_iff`, `fullIndexedFamilyStage_kernel`, `fullIndexedFamilyEquiv`, `_read`, `_step`, `_observation`, `_unique` | `Fintype` enumeration gives a fully recursive repair tree and a direct comparison with the union quotient, including an empty index type |

`FiniteSequential.lean` also provides flat leafwise and left-spine block
calculi. The fixed all-parenthesizations claim uses `FullTree.lean`, whose
branch evaluator calls itself on **both** children. The constructed right
child contributes its proved kernel as a request, and the image-congruence
theorem identifies that request with the original right leaves. At every
node, the per-leaf repairability premise builds the descended observation.
No stage, kernel, comparison, or intermediate observation certificate is
supplied by the caller.

## Cycle 6 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 6
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: f4b20da0d9e06a2c269e34b92cf507976a568d64
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 5 comment and report C two-stage section"
  proof_dag_predecessors: ["OperationRepair/Sequential.lean", "OperationRepair/Composition.lean"]
  proof_obligation: "C all finite orders and bracketings, comparison coherence, and finite-indexed-family bridge"
  selection_reason: "Completes the remaining fixed C composition claim using actual repeated quotient steps"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/FiniteSequential.lean", "OperationRepair/FullTree.lean"]
  risks: ["kernel invariant escape", "request image at wrong stage", "tree order", "empty family", "observation premise", "comparison coherence"]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed actual finite sequential stages and tree parenthesizations, their canonical structure-preserving comparisons, and coherence"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/FiniteSequential.lean", "OperationRepair/FullTree.lean"]
  evidence: ["generated_mappedRequest_kernel", "fullRepairTreeStage_generated", "fullRepairTree_branch_image", "fullRepairTreeCompare_coherent", "fullRepairTreeCompare_observation", "fullIndexedFamilyEquiv"]
  claim_mapping:
    theorem_names: ["generated_mappedRequest_kernel", "sequentialExtend_image_repairable", "sequentialExtend_observation_comm", "fullRepairTreeStage_generated", "fullRepairTree_branch_image", "fullRepairTreeCompare_read", "fullRepairTreeCompare_step", "fullRepairTreeCompare_observation", "fullRepairTreeCompare_unique", "fullRepairTreeCompare_coherent", "fullIndexedFamilyEquiv_observation"]
    source_labels: ["G-126 C finite-family sequential quotient and coherence"]
    conjuncts: ["actual staged quotient", "every finite order and bracketing", "empty family", "source commuting unique isomorphism", "operations and observations", "comparison coherence"]
    undischarged_assumptions: []
    acceptance_point: "Both child subtrees are recursively constructed; kernel, raw-image congruence, repairability, and observation descent are proved at each node"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["C finite-order and bracketing coherence"]
    remaining: ["D", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["stage kernel invariants built by sequentialBase/sequentialExtend", "intermediate observation descent built by repairableSequentialExtend", "comparison maps built from source quotients"]
    unresolved: []
  proof_use:
    used: ["right subtree's constructed kernel and its equality with raw leaf-union generation", "new request image under current left composite source map", "surjectivity for kernel and comparison uniqueness", "each repairability premise at every recursively constructed observation stage"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["FiniteSequential focused check: pass, 162 declarations standard axioms", "FullTree focused check: pass, 25 declarations standard axioms", "lake build ResearchLean.AG.OperationRepair.FullTree: pass", "eight FullTree spine #print axioms: standard axioms only", "git diff --check: pass", "placeholder and hidden Unicode scans: no matches"]
  blocking_findings: []
  review_findings_resolved: ["initial flat tree did not realize grouped bracket carriers", "initial sequence lacked explicit intermediate observation descent", "left-spine grouping did not recursively evaluate right subtrees"]
  next_obligation: "D executable finite table procedure and proof of correctness/cost"
```

## Cycle 5 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 5
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 6fa4bbf62c04ef4a2bd94b47c25fab16ae806ebf
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 4 comment and report C section"
  proof_dag_predecessors: ["OperationRepair/Composition.lean", "OperationRepair/InputMaps.lean", "Mathlib.Data.Setoid.Basic"]
  proof_obligation: "C two-stage sequential quotient with generated image request and structure-preserving comparison"
  selection_reason: "Kernel identification is the required prerequisite for the third-isomorphism comparison and finite-family coherence"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/Sequential.lean"]
  risks: ["image relation direction", "kernel equality", "quotient operation stability", "observation descent", "source commuting uniqueness"]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Identified the second generated congruence with the join quotient-map kernel and constructed the unique operation/observation-preserving sequential equivalence"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/Sequential.lean"]
  evidence: ["generated_imageRequest_eq_kernel", "sequentialEquiv_mk", "sequentialEquiv_step", "imageRequest_repairable", "sequentialEquiv_observation", "sequentialEquiv_unique"]
  claim_mapping:
    theorem_names: ["generated_imageRequest_eq_kernel", "sequentialEquiv", "sequentialEquiv_step", "sequentialEquiv_observation", "sequentialEquiv_unique"]
    source_labels: ["G-126 C sequential two-stage clause"]
    conjuncts: ["image-generated congruence", "third-isomorphism comparison", "source compatibility", "operation and observation preservation", "uniqueness"]
    undischarged_assumptions: []
    acceptance_point: "Two-stage comparison is constructed from raw congruences and request image; all finite-order coherence remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["C two-stage sequential quotient"]
    remaining: ["C finite-order and bracketing coherence", "D", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["quotient-map kernel and third-isomorphism equivalence constructed"]
    unresolved: []
  proof_use:
    used: ["first congruence in quotient operations", "second request in image generator", "both repairability hypotheses in observation descent"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["Sequential focused check: pass, 18 declarations standard axioms", "lake build ResearchLean.AG.OperationRepair.Sequential: pass", "#print axioms for six C spine declarations: propext and Quot.sound only", "git diff --check: pass", "placeholder and hidden Unicode scans: no matches"]
  blocking_findings: []
  next_obligation: "C finite-family order/bracketing coherence"
```

## Cycle 4 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 4
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 64c24ee31d10b821d7f0521a20a9fb63e297e985
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 3 comment and report B section"
  proof_dag_predecessors: ["OperationRepair/Endpoints.lean", "OperationRepair/Classification.lean", "OperationRepair/Universal.lean"]
  proof_obligation: "C structural functoriality: union/join and maps between raw inputs and endpoint quotients"
  selection_reason: "Supplies the request and input-map calculus used by sequential repair and Law path requests"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/Composition.lean", "OperationRepair/InputMaps.lean"]
  risks: ["join orientation", "empty family", "future-word direction", "input map non-surjectivity", "endpoint square"]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed generated joins, repairability equivalence, and input-induced lower/upper quotient maps with laws"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/Composition.lean", "OperationRepair/InputMaps.lean"]
  evidence: ["generated_requestUnion", "repairable_requestUnion_iff", "generated_preserve", "behavior_preserve", "endpoint_square", "lowerMap_comp", "upperMap_comp"]
  claim_mapping:
    theorem_names: ["generated_requestUnion", "repairable_requestUnion_iff", "generated_preserve", "behavior_preserve", "endpoint_square"]
    source_labels: ["G-126 C union and input-map clauses"]
    conjuncts: ["request join", "joint repairability", "both endpoint maps", "commuting square", "identity/composition/input iso"]
    undischarged_assumptions: []
    acceptance_point: "Selected C structural subclaims follow from raw family/input maps; sequential quotient remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["generated union/join", "family repairability", "input-preserved endpoints and quotient maps"]
    remaining: ["C sequential quotient/coherence", "D", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["induced quotient maps from input map and congruence preservation"]
    unresolved: []
  proof_use:
    used: ["request_preserve in lower map", "step_comm in both congruences and quotient operations", "observe_comm in behavior and quotient observations"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["Composition focused check: pass, 4 declarations standard axioms", "InputMaps focused check: pass, 52 declarations standard axioms", "lake build ResearchLean.AG.OperationRepair.InputMaps: pass", "#print axioms for 17 C spine declarations: standard axioms only", "git diff --check: pass", "placeholder and hidden Unicode scans: no matches"]
  blocking_findings: []
  next_obligation: "C sequential quotient and finite-order coherence"
```

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
