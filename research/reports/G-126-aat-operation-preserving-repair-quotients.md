# G-126 — Operation preserving repair quotients

- Fixed GOAL: [`G-126-aat-operation-preserving-repair-quotients`](../goals/G-126-aat-operation-preserving-repair-quotients.md)
- Tracking Issue: [#4945](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4945)
- Applied GOAL and common-standard commit: `93cbcedece216238edfd40e2329bcc69c4f7ae2d`
- GOAL blob: `255a64df4bdc851f64f799ef89189ea81e78aa70`
- Proof state: A–C proved in ResearchLean; D RAM cost and cumulative E/fixed-example
  review remain open.

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

1. D: prove that the lower counter covers the specified RAM primitives; cost
   the upper word loop and remaining output work, combine them into the same
   success/failure procedure, and prove the total bound.
2. E: final crosscheck of the complete Law/path declaration map against the
   fixed GOAL remains. The general path-numbering bridge is now constructed
   in `PathEnumeration.lean`; E completion is subject to independent review.
3. Independently review all three fixed examples as a whole after the cycle
   15 additions, and check empty input cases through the general API and
   finite algorithm.

## Cycle 16: general finite-output transport

`FiniteGeneralBridge.lean` reindexes the original request, generated
congruence, and behavioral congruence through the supplied state and
operation equivalences. The unchanged D `runRepair` succeeds exactly when a
repair exists for the original source. Its returned lower and upper tables
construct source-level repair quotients with kernels exactly `generated` and
`behavior`; the same returned factor table gives a source-level repair
morphism. On failure, the returned numbered pair and word reindex to the
original requested pair and a separating word of length less than `n²`.
The construction accepts zero states and zero operation names without a
nonempty input or default state. This discharges D's general output bridge;
the cost clause remains open.

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 16
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 23dafef7d3d1b42652e459ee81534920e4005783
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 15 comment and D remaining obligations"
  proof_dag_predecessors: ["OperationRepair/FiniteConstruction.lean", "OperationRepair/FiniteEnumeration.lean", "OperationRepair/PathEnumeration.lean"]
  proof_obligation: "Transport the unchanged finite procedure's success, failure, both quotient outputs, and factor map to arbitrary enumerated source types"
  selection_reason: "Closes the remaining D output-to-B gap before the RAM cost proof"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/FiniteGeneralBridge.lean"]
  risks: ["numbering transport of generated kernel", "arbitrary universes", "zero states and operations", "actual returned factor map"]
  unchecked: ["D RAM primitive cost and total bound", "cumulative E and fixed-example review", "empty input evaluation"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The same runRepair output now gives source-level endpoint quotients, factor map, and bounded failure certificate for arbitrary enumerated input"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/FiniteGeneralBridge.lean"]
  evidence: ["Input.generated_iff_tables", "Input.run_success_iff_repair_exists", "Input.sourceLowerRepair_kernel_eq", "Input.sourceUpperRepair_kernel_eq", "Input.sourceFactorHom", "Input.run_failure"]
  claim_mapping:
    theorem_names: ["Input.sourceLowerRepair_kernel_eq", "Input.sourceUpperRepair_kernel_eq", "Input.sourceFactorHom", "Input.run_failure"]
    source_labels: ["G-126 D success/failure output and B connection"]
    conjuncts: ["both original-source endpoint tables and maps", "descended operations and observations", "same factor table", "original requested pair and short separating word"]
    undischarged_assumptions: []
    acceptance_point: "D output bridge; D RAM cost remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["generated and behavior transport through the input numberings", "source-level quotient, factor, and failure output from the same table run"]
    remaining: ["D RAM primitive correspondence and total cost bound", "cumulative E and fixed-example review"]
  certificate_provenance:
    discharged: ["success tables and factor from runRepair", "failure pair and word from runRepair"]
    unresolved: []
  proof_use:
    used: ["both enumeration equivalences", "generated and behavior endpoint characterizations", "runRepair success/failure soundness"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["targeted lake build FiniteGeneralBridge passed", "#assert_standard_axioms_only passed"]
  blocking_findings: []
  next_obligation: "D actual RAM primitive correspondence, upper/output cost, and total polynomial bound"
```

## Cycle 15: sequential and Law completion candidates for fixed examples

`ExampleSequential.lean` uses `sequentialList` for both chronological orders
of the four-state requests. `first12_map_eq_iff` and
`first21_map_eq_iff` calculate each first-stage source map kernel as the
specified three-block partition. `order12_source_map` and
`order21_source_map` exhibit each composite source map through its actual
second quotient map, formed from the image of the second request.
`generated_join_eq_behavior` and the two final map equations calculate both
composite kernels as `{0,1}|{2,3}`. `orderCompare_read` and
`orderCompare_step` identify the two orders. The one-shot D run on the
combined Boolean request table succeeds; `runBoth_counts` calculates its two
two-state endpoint outputs. `order12ToD` and `order21ToD` compare both
sequential carriers to that actual returned D upper target, with source-map,
operation, and observation commutation. The first individual and second
individual D runs have three/two class-count success outputs as well.

`ExampleLaw.lean` takes the original four-state Boolean observation as a
single `FiniteLawFamily` evaluation. `behavior_law_eq` checks that its future
Law kernel is the same upper endpoint. Both feasible endpoint repairs are
Law-adequate and the standard joint-kernel Reading factors through their
Readings, using the general E theorem. The path example reuses this very
Law family: its upper repair satisfies the specified path equation on every
target point, is Law-adequate, receives the joint-kernel factorization, and
has a nonconstant Law value. `run_upper_law_value` identifies the actual D
upper output's observation table with the same Law evaluation at every
source state. These are fixed-example completion candidates pending
independent review; they do not discharge D's general cost obligation.

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 15
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: c07c6fb12d72eb62cdbd6ad0cda481b2b868c594
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 14 comment and remaining fixed-example obligations"
  proof_dag_predecessors: ["OperationRepair/Examples.lean", "OperationRepair/FiniteSequential.lean", "OperationRepair/ClassOrder.lean", "OperationRepair/LawBridge.lean"]
  proof_obligation: "Complete both chronological sequential quotient maps and original single-Law adequacy/factorization in the prescribed feasible examples"
  selection_reason: "Closes the fixed examples' missing C and E connections while preserving the actual D outputs"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/ExampleSequential.lean", "OperationRepair/ExampleLaw.lean"]
  risks: ["chronological list direction", "first-stage image request", "one-shot D payload comparison", "Law observation mismatch"]
  unchecked: ["independent cumulative fixed-example review", "D RAM cost and general finite-output transport", "cumulative E crosscheck", "empty input evaluation"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Both sequential orders and their source/operation/observation comparison to the actual one-shot D output; single original Law adequacy, factorization, and path output value"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/ExampleSequential.lean", "OperationRepair/ExampleLaw.lean"]
  evidence: ["Four.first12_map_eq_iff", "Four.first21_map_eq_iff", "Four.order12_source_map", "Four.order21_source_map", "Four.generated_join_eq_behavior", "Four.order12ToD_read", "Four.order21ToD_read", "Four.order12ToD_step", "Four.order21ToD_step", "Four.order12ToD_observation", "Four.order21ToD_observation", "Four.lawLower_adequate", "Four.lawUpper_jointKernel_factors", "Path.lawUpper_path_equations", "Path.lawUpper_nonconstant", "Path.run_upper_law_value"]
  claim_mapping:
    theorem_names: ["Four.generated_join_eq_behavior", "Four.order12ToD_read", "Four.order21ToD_read", "Four.lawLower_jointKernel_factors", "Path.lawUpper_path_equations", "Path.run_upper_law_value"]
    source_labels: ["G-126 fixed examples 2 and 4, C/E connections"]
    conjuncts: ["both sequential quotient maps", "combined one-shot D output comparison", "single original Law adequacy and standard Reading factorization", "path equation and Law value on target"]
    undischarged_assumptions: []
    acceptance_point: "fixed-example C/E additions; G-126 completion remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["two explicit request orders", "actual one-shot D success output", "original single Boolean Law evaluation"]
    remaining: ["D RAM cost and general finite-output bridge", "cumulative E and fixed-example review", "empty input evaluation"]
  certificate_provenance:
    discharged: ["stage kernels from sequentialList", "D upper target from runRepair_success_payload", "Law values from original evaluation"]
    unresolved: []
  proof_use:
    used: ["both original raw requests", "source surjectivity", "kernel equality", "operation and observation commutation", "Law descent and joint-kernel factorization"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
```

## Cycle 14: fixed finite instances (partial)

`Examples.lean` instantiates the actual `FiniteRepairInput` tables and
`runRepair` procedure. In the four-state instance, `lowerOne_cells` gives
`{0,1}|{2}|{3}`, `upper_cells` gives `{0,1}|{2,3}`, and
`lowerOne_count`/`upper_count` compute three and two classes. The source
quotient map kernels are exposed by `lowerOne_map_eq_iff` and
`upper_map_eq_iff`. `interval_two_endpoints` uses the general A/B interval,
and `exactly_two_repair_classes` proves there are exactly two repair
isomorphism classes. The two individual and combined requests all make the
finite failure search return `none`; `lowerBoth_cells` computes the combined
generated endpoint as the behavioral endpoint. `runOne_counts` connects the
concrete counts to the actual success payload.

In the three-state instance, `lower_universal` and `upper_equality` compute
the two partitions. `run_failure_exact` shows the actual D procedure returns
the original pair `(0,1)` and the one-letter word `[0]`;
`run_failure_certificate` uses D's general soundness theorem, and `no_repair`
uses its impossibility equivalence. `empty_word_same` and
`one_step_separates` distinguish present and future observations.
`law_kernel_not_stable` and `joint_law_operation_not_descended` use the
single original Boolean Law and the general E descent criterion.

For the path example, `generated_cells` and `future_cells` compute the same
two-block relation from `[(ε,T)]`, and `generated_eq_behavior` identifies the
general A endpoints. `run_upper_two_states`, `run_upper_operation_identity`,
and `run_law_nonconstant` prove properties of the same returned D upper
tables: two classes, identity operation, and two distinct observation values.
The observation is the intended single Boolean Law evaluation, but the
explicit Law-family adequacy/factorization connection and both sequential
repair orders are still open.

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 14
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 145ca9fb4598fd0a93390f3e9c889fee7a46dbfb
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 13 comment and fixed-example completion criteria"
  proof_dag_predecessors: ["OperationRepair/Classification.lean", "OperationRepair/FiniteConstruction.lean", "OperationRepair/PathBridge.lean", "OperationRepair/LawBridge.lean"]
  proof_obligation: "Evaluate the three prescribed concrete inputs through A/B and the actual D procedure"
  selection_reason: "Establishes concrete source partitions, repair-class count, failure certificate, and path output facts required by completion"
  expected_result_type: proof-checkpoint
  lean_targets: ["OperationRepair/Examples.lean"]
  risks: ["table computation vs actual run output", "exactly two repair classes", "original failure witness", "path quotient operation"]
  unchecked: ["sequential quotient maps", "four-state Law adequacy and factorization", "path Law bridge", "D RAM cost and general finite-output transport", "cumulative E review"]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Concrete four-state classification, three-state D failure and Law obstruction, path-generated endpoint equality and actual upper output properties"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/Examples.lean"]
  evidence: ["Four.exactly_two_repair_classes", "Four.runOne_counts", "Three.run_failure_exact", "Three.no_repair", "Three.joint_law_operation_not_descended", "Path.generated_eq_behavior", "Path.run_upper_two_states", "Path.run_upper_operation_identity", "Path.run_law_nonconstant"]
  claim_mapping:
    theorem_names: ["Four.exactly_two_repair_classes", "Three.run_failure_certificate", "Path.generated_eq_behavior", "Path.run_upper_operation_identity"]
    source_labels: ["G-126 fixed examples 2-4, partial"]
    conjuncts: ["four-state endpoint tables and exactly two classes", "three-state actual one-letter failure witness", "path generated=behavior, two-state identity-operation output"]
    undischarged_assumptions: []
    acceptance_point: "fixed-example proof checkpoint; G-126 completion remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["concrete state, transition, and observation tables for all three instances", "three-state single Law data", "four-state inputOne and path success payload facts; three-state actual failure payload"]
    remaining: ["sequential repairs", "Law adequacy/factorization for feasible instances", "D cost and general finite-output bridge"]
  certificate_provenance:
    discharged: ["three-state pair and word from runRepair", "success table from runRepair_success_payload", "path target operation from computed upper quotient"]
    unresolved: []
  proof_use:
    used: ["concrete finite input tables", "A/B interval classification", "D success/failure result", "E Law descent criterion"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
```

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

`FiniteCostLower.lean` instruments each lower closure pass with an accumulated
numeric counter and proves its value is exactly `FiniteClosure.closeStep`.
`lowerWithCost_value` matches the complete `n²`-round computation, and
`lowerWithCost_bound` bounds the chosen counter by
`200 * (m+1) * (n+1)^5`. Four independent reviewers of PR #4956 found that
the counter was not proved to cover the RAM primitives of the actual
initialization, list construction, and table updates. Thus this module is a
value/counter scaffold; no D cost subclaim is discharged by that inequality.
The next step is a primitive-operation cost semantics and a correspondence
proof for the executed loops before charging the whole `runRepair` procedure.

## E: Law observation and standard reading (partial)

`LawBridge.lean` uses the actual `FiniteLawFamily.eval` as a dependent-product
observation. `lawObserve_eq_iff` identifies equality of this observation with
the existing `FiniteLawFamily.Equivalent` relation. For a same-universe
surjective `Reading`, `LawReadingConditions` states operation descent, Law
adequacy, and request identification. `repair_to_lawReadingConditions` and
`lawReadingToRepair` construct both directions; the latter obtains descended
operations and the joint observation from the Reading factorization theorems,
without accepting a prepared repair quotient as an input.
`lawReadingToRepair_toReading` proves the Reading round trip. Conversely,
`repair_lawReading_roundtrip_step` and
`repair_lawReading_roundtrip_observation` recover the descended data from
surjectivity; the two identity `RepairHom`s give mutually inverse maps that
preserve operations and the Law observation.

`behavior_eq_jointKernel_iff_stable` and
`lawKernelStable_iff_jointKernelFactors` prove E's present-Law-kernel /
future-observation / operation-descent criterion. `betaReading_adequate`,
`jointKernel_coarser_beta`, and `jointKernel_factorsThrough_beta` establish the
specified Reading order. For an empty operation type,
`betaJointEquiv_of_isEmpty` and its source-commuting and uniqueness theorems
identify this quotient with G-103's `jointKernelReading`.
`betaJointEquiv_of_isEmpty_law` also records preservation of every Law value.

This is an E core checkpoint. The D finite-output comparison, the general
path-pair request and its output/reading consequences, and C input-map
compatibility for Law/path data remain open. E as a whole is not proved.

## E: finite path-pair requests (partial)

`PathBridge.lean` constructs `pathRequest` from a finite list of word pairs
and all source states. `RepairQuotient.eval_comm` proves that every word
descends, and `pathRequest_identified_iff` identifies the request condition
with the target operation equations for every surjective repair quotient.
`withPathEquations` constructs the repair from an unconstrained quotient and
those equations, while `forgetPathRequests` retains the source and descended
data. `pathRepair_exists_iff` specializes B's classification to the generated
relation. `pathLawRepair_adequate` derives descent of every original Law value.

For numbered inputs, `FiniteRepairInput.withPathRequest` constructs the
Boolean request table by finite word-pair and state enumeration.
`runPathRepair` passes it to the same D `runRepair` procedure;
`runPathRepair_success_iff`, `runPathRepair_upper_equations`, and
`runPathRepair_failure` give success, target equations, and the original
path-generated pair with a short distinguishing word. `pathInputHom` shows
that operation- and observation-preserving maps preserve this generated
relation; `pathLawInputHom` supplies the same interface for pulled-back Law
evaluations, hence the existing C endpoint maps apply. This is a partial E
result: general finite Law output comparison, arbitrary universe quotient
normalization, and the fully general independently specified Law input map
remain open.

## E: arbitrary repair targets and numbered Law output (partial)

`LawUniverse.lean` maps any B repair target universe to the existing
`Reading S` by quotienting the source by its actual kernel. The resulting
Reading satisfies operation descent, Law adequacy, and request identification.
Recovering its repair preserves the kernel and yields mutually inverse
`RepairHom`s to the original target; the forward map is B's standard quotient
equivalence. This extends cycle 10's same-universe round trip to all B repair
quotients up to structure-preserving isomorphism.

`FiniteLawBridge.lean` takes explicit state and operation numberings, the
original finite Law family, operation system, and Boolean request. It builds
D's input tables with the dependent-product Law observation and derives its
decidable equality from the finite Law index and value decisions.
`behavior_iff_tables` transports future words through both numberings, and
`run_success_iff_repair_exists` compares D's actual branch to B's condition
on the original states. On success, `returnedUpper` is the actual upper table
output. `betaReturnedEquiv` compares it to `betaReading` by exact kernels,
commutes with the source map, preserves each descended named operation and
every Law value, and is the unique
source-commuting map. With no operation names,
`returnedJointEquiv_of_isEmpty` compares the returned output with G-103's
`jointKernelReading`, again uniquely and with Law preservation.

`LawInputMaps.lean` accepts two independently specified evaluations over
shared Law names and value types. Pointwise Law preservation and operation
commutation construct C's `InputHom` for path-generated requests, so C's
endpoint maps, square, identity, and composition theorems apply. The
remaining E connection is the explicit theorem sending a general source
path-pair list through arbitrary numberings into `runPathRepair`'s table.
D's general finite-output and RAM-cost obligations and the fixed examples
remain open.

## E: general finite path numbering and output (candidate)

`PathEnumeration.lean` maps each source operation word through the supplied
`E ≃ Fin m`, proves the numbered word action commutes with `S ≃ Fin n`, and
proves the finite Boolean request table is exactly the image of the original
`pathRequest`. `runPaths` invokes the existing D `runRepair` on that table.
`runPaths_success_iff_repair_exists` matches success to B's repairability on
the original source. `runPaths_failure` maps the returned requested pair and
short separating word back to original states and operation names.

On success, `pathUpperRepairSource` transports the actual numbered upper
output to a repair quotient of the original system; its kernel is exactly the
original future-observation congruence. `runPaths_upper_equations` proves
all listed operation-word equations on every returned target point after
reindexing operation names. For the original Law family, `FiniteLawPath.runPaths`
uses the same path table and procedure, and `FiniteLawPath.betaEquiv` compares
its returned upper quotient to the Law future-observation Reading. This
equivalence commutes with the source map, preserves each named operation and
Law value, and is uniquely determined by source commutation. The full E
claim remains a candidate until independent review checks the cumulative
declaration mapping; D's RAM cost and general finite-output transport remain
open.

## Cycle 13 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 13
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: ac7aa033f8b81f7ea913c9ae5396432a26073561
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 12 comment and report E path numbering obligation"
  proof_dag_predecessors: ["OperationRepair/PathBridge.lean", "OperationRepair/FiniteEnumeration.lean", "OperationRepair/FiniteConstruction.lean", "OperationRepair/FiniteLawBridge.lean", "OperationRepair/LawUniverse.lean"]
  proof_obligation: "E general source path-pair list through explicit numberings to D's request table and Law upper output"
  selection_reason: "Closes the gap between semantic path requests on arbitrary finite sources and the actual numbered D run"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/PathEnumeration.lean"]
  risks: ["word transport order", "path relation image", "failure certificate back-transport", "returned target equations", "Law output comparison"]
  unchecked: ["D RAM cost and general finite-output bridge", "fixed examples", "cumulative E crosscheck"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Transported general source path requests into the exact D table, proved source-level success/failure and upper output equations, and linked the Law path output to beta"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/PathEnumeration.lean"]
  evidence: ["FiniteEnumeration.Input.numberPaths_request_iff", "FiniteEnumeration.Input.pathTables_requestRel", "FiniteEnumeration.Input.runPaths_success_iff_repair_exists", "FiniteEnumeration.Input.runPaths_failure", "FiniteEnumeration.Input.runPaths_upper_equations", "FiniteEnumeration.Input.pathUpperRepairSource", "FiniteEnumeration.Input.pathUpperRepairSource_kernel_eq", "FiniteLawPath.betaEquiv_read", "FiniteLawPath.betaEquiv_step", "FiniteLawPath.betaEquiv_law", "FiniteLawPath.betaEquiv_unique"]
  claim_mapping:
    theorem_names: ["FiniteEnumeration.Input.numberPaths_request_iff", "FiniteEnumeration.Input.runPaths_success_iff_repair_exists", "FiniteEnumeration.Input.runPaths_failure", "FiniteEnumeration.Input.runPaths_upper_equations", "FiniteEnumeration.Input.pathUpperRepairSource_kernel_eq", "FiniteLawPath.betaEquiv_step", "FiniteLawPath.betaEquiv_law"]
    source_labels: ["G-126 E arbitrary finite path-pair output clauses"]
    conjuncts: ["original R_P to numbered table", "same D success/failure", "original source and operation-word failure witness", "all target path equations", "Law and operation preserving returned upper comparison"]
    undischarged_assumptions: []
    acceptance_point: "general E path input/output bridge; G-126 completion remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["arbitrary original finite source and operation numberings", "finite path list", "D's actual returned success/failure payload", "original Law evaluation"]
    remaining: ["D RAM cost and general finite-output bridge", "fixed examples", "cumulative E review"]
  certificate_provenance:
    discharged: ["request table from original path pairs", "failure pair and word from runRepair", "upper quotient from successUpperRepair", "Law comparison from exact source kernel"]
    unresolved: []
  proof_use:
    used: ["both numbering inverses", "behavior transport for all words", "source surjectivity", "path relation identification", "successUpperRepair_kernel_eq"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["PathEnumeration focused check pass", "targeted PathEnumeration build pass", "module audit: 21 declarations with standard axioms only", "sixteen spine #print axioms: propext, Classical.choice, Quot.sound only", "git diff --check and placeholder, Unicode, privacy, import-direction scans pass"]
  blocking_findings: []
  next_obligation: "D general finite-output transport and RAM cost, then fixed examples"
```

## Cycle 12 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 12
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: e6c5d6fd0d50a9b657cbe40d0e2992f8c024ccbd
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 11 comment and report E finite Law obligation"
  proof_dag_predecessors: ["OperationRepair/LawBridge.lean", "OperationRepair/PathBridge.lean", "OperationRepair/FiniteEnumeration.lean", "OperationRepair/FiniteConstruction.lean", "OperationRepair/InputMaps.lean"]
  proof_obligation: "E arbitrary target universe Reading normalization, numbered finite Law upper output comparison, and independent Law input maps"
  selection_reason: "Connects the original Law evaluations and actual D upper output to the semantic Reading without a prepared quotient input"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/LawUniverse.lean", "OperationRepair/FiniteLawBridge.lean", "OperationRepair/LawInputMaps.lean"]
  risks: ["universe normalization", "word relabeling", "returned output versus semantic quotient", "Law value transport", "independent Law input maps"]
  unchecked: ["D RAM cost and general finite-output bridge", "E general source path input through numberings", "fixed examples"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Normalized every repair universe into an existing Reading, identified the numbered Law upper output with beta and the empty-operation standard resolution, and built independent Law/path input maps"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/LawUniverse.lean", "OperationRepair/FiniteLawBridge.lean", "OperationRepair/LawInputMaps.lean"]
  evidence: ["RepairQuotient.standardReading_conditions", "RepairQuotient.standardReadingHomTo", "RepairQuotient.standardReadingHomFrom", "RepairQuotient.standardReadingHomTo_eq_standardEquiv", "FiniteLawBridge.behavior_iff_tables", "FiniteLawBridge.run_success_iff_repair_exists", "FiniteLawBridge.betaReturnedEquiv", "FiniteLawBridge.betaReturnedEquiv_step", "FiniteLawBridge.betaReturnedEquiv_law", "FiniteLawBridge.returnedJointEquiv_of_isEmpty_law", "independentLawPathInputHom"]
  claim_mapping:
    theorem_names: ["RepairQuotient.standardReading_conditions", "RepairQuotient.standardReadingHom_left_inv", "RepairQuotient.standardReadingHom_right_inv", "FiniteLawBridge.betaReturnedEquiv_read", "FiniteLawBridge.betaReturnedEquiv_step", "FiniteLawBridge.betaReturnedEquiv_law", "FiniteLawBridge.returnedJointEquiv_of_isEmpty_unique", "independentLawPathInputHom"]
    source_labels: ["G-126 E Reading correspondence, finite Law upper output, input-map clauses"]
    conjuncts: ["all repair target universes up to isomorphism", "actual finite Law upper output", "source, operation, and Law preserving beta Reading comparison", "empty-operation G-103 comparison", "independently specified Law maps"]
    undischarged_assumptions: []
    acceptance_point: "selected E Law/output bridge only; full E and G-126 remain open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["arbitrary repair target universe by kernel normalization", "Law value decisions from original family", "explicit state and operation numberings", "actual D upper success output", "independent Law evaluations with shared names and values"]
    remaining: ["D cost and general finite-output bridge", "E arbitrary source path list to numbered D table", "fixed examples"]
  certificate_provenance:
    discharged: ["standard Reading from original repair kernel", "finite table from original system and Law evaluations", "upper quotient from runRepair success", "comparison from kernel equality and source surjectivity"]
    unresolved: []
  proof_use:
    used: ["kernel stability and Law factorization", "both inverse RepairHom compositions", "word relabeling in both directions", "successUpperRepair_kernel_eq", "pointwise Law preservation for C InputHom"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["LawUniverse, FiniteLawBridge, LawInputMaps focused checks pass", "targeted builds for LawUniverse, FiniteLawBridge, LawInputMaps pass", "module audits: 10, 20, 2 declarations with standard axioms only", "twenty-one spine #print axioms: propext, Classical.choice, Quot.sound only", "git diff --check and placeholder, Unicode, privacy, import-direction scans pass"]
  blocking_findings: []
  next_obligation: "E general path input numbering bridge, then D general finite-output and RAM cost"
```

## Cycle 11 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 11
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: bfd1449322859a7b9e5f9a15aaf1db539de6d5da
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 10 comment and report E path obligation"
  proof_dag_predecessors: ["OperationRepair/Classification.lean", "OperationRepair/InputMaps.lean", "OperationRepair/FiniteConstruction.lean", "OperationRepair/LawBridge.lean"]
  proof_obligation: "E finite path-pair request generation, quotient equations, C map preservation, and same D procedure on the generated table"
  selection_reason: "This makes the path data an actual generated request table and connects the E equations to B and D without assuming a prebuilt repair"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/PathBridge.lean"]
  risks: ["unbounded existential in finite table", "operation-word order", "target surjectivity", "Law evaluation preservation", "D output use"]
  unchecked: ["D RAM cost and general finite-output bridge", "E finite Law output and arbitrary-universe correspondence", "independent Law-family input maps", "fixed examples"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed finite path requests and the D input table, proved path equation classification and same-procedure success/failure statements"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/PathBridge.lean"]
  evidence: ["pathRequest", "RepairQuotient.eval_comm", "RepairQuotient.pathRequest_identified_iff", "RepairQuotient.withPathEquations", "pathRepair_exists_iff", "pathLawRepair_adequate", "pathInputHom", "pathLawInputHom", "FiniteRepairInput.withPathRequest_requestRel", "FiniteRepairInput.runPathRepair_success_iff", "FiniteRepairInput.runPathRepair_upper_equations", "FiniteRepairInput.runPathRepair_failure"]
  claim_mapping:
    theorem_names: ["RepairQuotient.pathRequest_identified_iff", "pathRepair_exists_iff", "pathLawRepair_adequate", "pathLawInputHom", "FiniteRepairInput.runPathRepair_success_iff", "FiniteRepairInput.runPathRepair_upper_equations", "FiniteRepairInput.runPathRepair_failure"]
    source_labels: ["G-126 E finite path-pair clauses"]
    conjuncts: ["request generated from path pairs", "target path equations iff identification", "B feasibility criterion", "Law adequacy", "C map compatibility for pulled-back Laws", "D table success and failure"]
    undischarged_assumptions: []
    acceptance_point: "finite path request core only; full E remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["finite path relation from original word pairs and transitions", "target equations from source requests via surjectivity", "same D algorithm applied to generated request table"]
    remaining: ["D cost and general finite-output bridge", "E finite Law output and arbitrary universes", "independent Law-family input maps", "fixed examples"]
  certificate_provenance:
    discharged: ["request Bool cells from finite list and state enumeration", "failure pair and word from runRepair", "Law evaluation from original family"]
    unresolved: []
  proof_use:
    used: ["surjectivity for equations at every target state", "operation commutation for words", "actual request table for D", "C InputHom for path maps"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["PathBridge focused check pass", "targeted PathBridge build pass", "module audit: 25 declarations with standard axioms only", "fourteen spine #print axioms: no axiom or only propext, Classical.choice, Quot.sound", "git diff --check and placeholder, Unicode, privacy, import-direction scans pass"]
  blocking_findings: []
  next_obligation: "E general finite Law output and arbitrary-universe correspondence"
```

## Cycle 10 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 10
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 148b6b0bbe5e5ab750290197e7d57a33f221967e
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 9 comment and report E open obligation"
  proof_dag_predecessors: ["OperationRepair/Endpoints.lean", "OperationRepair/Classification.lean", "CanonicalResolution/Reading.lean", "CanonicalResolution/JointKernel.lean"]
  proof_obligation: "E Law observation, existing Reading repair conditions, standard Law-kernel stability/descent, empty-operation quotient comparison"
  selection_reason: "The Law bridge is independent of the unresolved RAM cost model and supplies E's required source-of-truth correspondence"
  expected_result_type: proof-obligation-discharged
  lean_targets: ["OperationRepair/LawBridge.lean"]
  risks: ["dependent-product observation", "Reading order orientation", "same-universe correspondence", "empty operation type", "remaining path bridge"]
  unchecked: ["D RAM cost and general finite-output bridge", "E finite-output Law comparison", "E path requests and input-map compatibility", "fixed examples"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the same-universe Reading/repair round trips with operation and Law-observation preservation, and proved the standard Law kernel equals future behavior exactly under operation stability/descent"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/LawBridge.lean"]
  evidence: ["lawObserve_eq_iff", "repair_to_lawReadingConditions", "lawReadingToRepair", "lawReadingToRepair_toReading", "repair_lawReading_roundtrip_step", "repair_lawReading_roundtrip_observation", "repair_lawReading_roundtrip_hom", "repair_lawReading_roundtrip_hom_inv", "behavior_eq_jointKernel_iff_stable", "lawKernelStable_iff_jointKernelFactors", "betaReading_adequate", "jointKernel_coarser_beta", "betaJointEquiv_of_isEmpty_law", "betaJointEquiv_of_isEmpty_unique"]
  claim_mapping:
    theorem_names: ["repair_to_lawReadingConditions", "lawReadingToRepair_toReading", "repair_lawReading_roundtrip_hom", "repair_lawReading_roundtrip_hom_inv", "lawKernel_behavior_stability_descent", "betaReading_adequate", "jointKernel_factorsThrough_beta", "betaJointEquiv_of_isEmpty_law", "betaJointEquiv_of_isEmpty_unique"]
    source_labels: ["G-126 E Law and standard-reading subclauses"]
    conjuncts: ["joint Law observation", "Reading repair correspondence", "present versus future kernel criterion", "Reading factorization order", "empty-operation canonical quotient"]
    undischarged_assumptions: []
    acceptance_point: "Law/reading core only; full E remains open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["dependent-product observation from original Law evaluations", "operation descent and Law adequacy from Reading conditions", "both same-universe Reading/repair round trips", "standard Law kernel criterion", "empty-operation quotient comparison with Law preservation"]
    remaining: ["D cost and finite-output comparison", "E path requests and input maps", "fixed examples"]
  certificate_provenance:
    discharged: ["Law observation built from eval", "repair quotient operations and observation constructed from Reading factorization", "beta Reading constructed from behavior"]
    unresolved: []
  proof_use:
    used: ["operation factorization to construct descended step", "Law adequacy to construct joint observation", "request identification to construct repair", "behavior maximality for kernel criterion"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused LawBridge check and standard-axiom audit pass after round-trip repair", "targeted LawBridge build pass after round-trip repair", "initial fourteen spine #print axioms: propext, Classical.choice, Quot.sound only", "git diff --check and placeholder, hidden Unicode, privacy, import-direction scans pass"]
  blocking_findings: []
  next_obligation: "E finite-output Law comparison and path-pair requests"
```

## Cycle 9 ledger

```yaml
ledger_type: target_cycle_result
goal: G-126-aat-operation-preserving-repair-quotients
cycle: 9
goal_blob_sha: 255a64df4bdc851f64f799ef89189ea81e78aa70
base_oid: 56a9d6e04590f9f2c9eda4119d749eac7bb6f425
tracking_issue: 4945
report_path: research/reports/G-126-aat-operation-preserving-repair-quotients.md
selection:
  proof_state_ref: "Issue #4945 cycle 8 comment and report D section"
  proof_dag_predecessors: ["OperationRepair/FiniteClosure.lean", "OperationRepair/FiniteConstruction.lean"]
  proof_obligation: "D lower-loop value/counter coupling and candidate component bound"
  selection_reason: "The most expensive closure component must be instrumented before the common procedure can carry a justified charge"
  expected_result_type: proof-checkpoint
  lean_targets: ["OperationRepair/FiniteCostLower.lean"]
  risks: ["value/charge coupling", "list construction charge", "zero states", "uniform polynomial arithmetic", "full procedure cost still open"]
  unchecked: ["RAM primitive correspondence for lower counter", "D upper/output cost and same-procedure total bound", "D general finite-output bridge", "E", "fixed examples"]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Lower folds produce exactly the existing closure value and a fixed polynomial bound for a numeric counter; RAM correspondence remains open"
  completion_candidate: no
  lean_artifacts: ["OperationRepair/FiniteCostLower.lean"]
  evidence: ["markPassWithCost_value", "markPassWithCost_cost", "closeStepWithCost_value", "closeStepWithCost_cost", "lowerWithCost_value", "lowerWithCost_cost", "lowerWithCost_bound"]
  claim_mapping:
    theorem_names: ["closeStepWithCost_value", "lowerWithCost_value", "lowerWithCost_bound"]
    source_labels: ["G-126 D lower closure cost preparation"]
    conjuncts: ["same lower loop value", "finite rounds", "numeric counter bound"]
    undischarged_assumptions: ["counter covers GOAL D RAM primitives"]
    acceptance_point: "Value/counter checkpoint only; RAM cost and total D cost remain open"
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["lower value/counter tied to loop", "numeric counter polynomial bound"]
    remaining: ["lower RAM primitive correspondence", "D upper/output/total cost", "D general finite-output bridge", "E", "fixed examples"]
  certificate_provenance:
    discharged: ["value and numeric counter accumulated by the same lower folds and iteration"]
    unresolved: ["RAM interpretation of the counter"]
  proof_use:
    used: ["request table in lower initialization", "old relation table in each closure pass", "transition table in the operation-image pass"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["focused check and standard-axiom audit: FiniteCostLower pass", "parent targeted build: FiniteCostLower pass", "seven spine #print axioms: propext, Classical.choice, Quot.sound only", "git diff --check and placeholder, hidden Unicode, privacy, import-direction scans pass"]
  blocking_findings: ["First four-lane PR review found that the numeric counter does not yet cover the RAM primitive operations; revised scope requires new review"]
  next_obligation: "D RAM primitive correspondence for lower loop, then upper/output and common runRepairWithCost"
```

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
