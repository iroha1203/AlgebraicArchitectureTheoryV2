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
- current proof obligation: Cycle 2 review of A's evaluation-quotient classification
- pending proof obligations: A's finite/infinite carrier and transport claims, then B--E
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: A's finite/infinite carrier fiber classification

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

## Cycle 2 — Evaluation quotient and the existing finite/cofinite encoder

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 2
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: edfe21ec29a0fb582d21d8b44460d82ba9269fba
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 1: raw code/continuous-map equivalence discharged"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.finiteOrCofiniteAtomPredicateCode
    - AAT.AG.DoctrineFiberProduct.finiteOrCofiniteAtomPredicateCode_holds_iff
    - AAT.AG.DoctrineFiberProduct.atomPredicateCode_finiteOrCofinite
  proof_obligation: "A2: define pointwise evaluation equality, construct the quotient equivalence with Bool predicates whose true set is finite or cofinite, and identify the inverse with the existing G-112 encoder"
  selection_reason: "The quotient classification is the next direct conjunct of A and fixes the canonical semantic image used by the finite/infinite fiber classification. Cycle 1 is an already accepted earlier conjunct, not a proof-term predecessor of this independent quotient theorem; the actual external predecessor connection here is the accepted G-112 encoder."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/EvaluationClassification.lean
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationQuotientEquiv
  risks:
    - "installing a global Setoid instance that changes unrelated quotient inference"
    - "encoding an arbitrary Bool predicate rather than proving the finite/cofinite image condition"
    - "constructing a parallel canonical encoder instead of using the accepted G-112 code"
    - "proving only one inverse or only a Prop-valued surrogate"
  unchecked:
    - "A's finite/infinite carrier fiber classification"
    - "A's permutation transport and identity/inverse/composition coherence"
    - "B--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined an explicit evaluation setoid without a global instance; mapped every raw code to its finite-or-cofinite Bool predicate using the accepted code-classification theorem; used the existing finiteOrCofiniteAtomPredicateCode as the inverse; proved its Bool evaluation formula and both quotient inverses; and packaged the required equivalence."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/EvaluationClassification.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationEq
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationSetoid
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationEq_positive_instance
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationEq_negative_instance
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode_eval
    - AAT.AG.FiniteDecoderRepresentability.evaluationQuotientToFiniteOrCofiniteBoolPredicate
    - AAT.AG.FiniteDecoderRepresentability.finiteOrCofiniteBoolPredicateToEvaluationQuotient
    - AAT.AG.FiniteDecoderRepresentability.evaluationQuotient_leftInverse
    - AAT.AG.FiniteDecoderRepresentability.evaluationQuotient_rightInverse
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationQuotientEquiv
  claim_mapping:
    theorem_names:
      - atomPredicateCodeEvaluationEq
      - atomPredicateCodeEvaluationSetoid
      - FiniteOrCofiniteBoolPredicate.toCode_eval
      - evaluationQuotient_leftInverse
      - evaluationQuotient_rightInverse
      - atomPredicateCodeEvaluationQuotientEquiv
    source_labels:
      - "fixed target A: q~q' is equality of evaluation on D"
      - "fixed target A: Code(D)/~ is equivalent to Bool predicates with finite or cofinite true set"
      - "fixed target A: existing finiteOrCofiniteAtomPredicateCode agrees with the classification"
    conjuncts:
      - "evaluation equality is an equivalence relation on raw codes"
      - "every raw code evaluates to a Bool predicate with finite true set or finite false set"
      - "the canonical inverse is the existing G-112 finite/cofinite encoder"
      - "the canonical encoder evaluates pointwise to the input Bool predicate"
      - "both quotient-level inverse laws hold"
    undischarged_assumptions: []
    acceptance_point: "The relation is exactly pointwise equality of existing eval values, the codomain retains Bool rather than replacing it by an unrelated Prop quotient, and the inverse is generated by the accepted finite/cofinite code construction from the subtype evidence."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A2 evaluation relation and setoid"
      - "A2 finite/cofinite semantic image and quotient equivalence"
      - "A2 pointwise agreement with the existing G-112 encoder"
    remaining:
      - "A finite/infinite carrier fiber claims and transport coherence"
      - "all B--E construction obligations"
  certificate_provenance:
    discharged:
      - "finite/cofinite property of a code is derived by atomPredicateCode_finiteOrCofinite"
      - "inverse raw code is constructed by finiteOrCofiniteAtomPredicateCode from the predicate subtype evidence"
      - "the reused G-112 K1 encoder was accepted in PR #4193 (head 7c1262b16687b2c89c88932f3b4ffa3c53819adb, merge 9e85f70df25eedae54914fbfbc235e56118420f6) and G-112 completion was accepted in PR #4197 (head bf882573945a45780b022bc811754f8444846c53, merge e9f891b8b0d763c6c29cb2d8b6e723b43a6bb9bb); ExactBottomCoverageClassification.lean has blob 760ed9c70de06405a6f40c7c79d6f9ff9a212d6c at both the G-121 activation source and this cycle base"
    unresolved: []
  proof_use:
    used:
      - "pointwise evaluation equality supplies quotient well-definedness"
      - "finite/cofinite evidence constructs the inverse code"
      - "finiteOrCofiniteAtomPredicateCode_holds_iff proves the actual Bool evaluation formula"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/EvaluationClassification.lean; exit 0"
    - "the evaluation relation has explicit satisfying and falsifying finite-fixture instances"
    - "namespace #assert_standard_axioms_only: 16 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "A3: prove evaluation injectivity for infinite carriers and the exact two-code fiber classification, including the empty carrier, for finite carriers"
```

### Cycle 2 acceptance spine

`atomPredicateCodeEvaluationSetoid` is an explicit value rather than a global instance.
The forward map uses the existing theorem that every exception table is finite or
cofinite. The inverse calls `finiteOrCofiniteAtomPredicateCode` itself, and
`FiniteOrCofiniteBoolPredicate.toCode_eval` proves that this accepted G-112 construction
has exactly the requested Bool evaluation. Quotient soundness closes the raw-code class
direction; subtype extensionality closes the predicate direction.

Cycle 2 material premise roles are:

- `ambient-boundary`: arbitrary fixed `AtomCarrier U`, `[DecidableEq U.Atom]`, and
  either an existing raw code or a Bool predicate carrying the target's finite/cofinite
  image condition.
- `direction-hypothesis`: none.
- `discharge-required`: finite/cofinite image of existing codes, inverse code
  construction, quotient well-definedness, pointwise encoder agreement, and both
  inverse laws; all are constructed in the module.
- `conclusion-equivalent-risk`: none. The subtype evidence states membership in the
  target semantic image; it does not contain a raw code, quotient inverse, or equality
  certificate.

## Cycle 3 — Infinite injectivity and exact finite code fibers

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 3
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 1e46e7da3dc002bfeb307fb60c661759fd056e89
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 2: evaluation quotient classification discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeEvaluationEq
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap
    - AAT.AG.FiniteDecoderRepresentability.continuousMapToAtomPredicateCode
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_rightInverse
  proof_obligation: "A3: prove raw evaluation injectivity and continuous-extension uniqueness for infinite carriers, and classify the complete raw-code fiber as exactly the default-false and default-true codes for finite carriers, including the empty carrier"
  selection_reason: "A2 fixed the semantic quotient. A3 now determines precisely when raw authored defaults retain extra information and supplies the finite/infinite split required by the remaining G-112 agreement and morphism clauses."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CodeFibers.lean
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eval_injective_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCodeFiberEquiv
  risks:
    - "assuming equality of authored defaults instead of deriving it outside finite exception supports"
    - "stating only existence or cardinality two without identifying the complete raw-code fiber"
    - "losing one code on the empty carrier by identifying codes only through evaluation"
    - "claiming extension uniqueness without connecting through the raw A1 equivalence"
  unchecked:
    - "A's agreement of the G-112 encoder with the finite default-false and infinite unique choices"
    - "A's permutation transport and identity/inverse/composition coherence"
    - "B--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Derived default equality on infinite carriers by evaluating outside the union of two finite exception tables, then recovered raw code equality and continuous-extension uniqueness. On finite carriers, constructed the code for each authored Bool default, proved evaluation and uniqueness, exhibited an equivalence from the actual fiber subtype to Bool, identified the two exception tables, separated the two raw codes even for an empty carrier, and separated their infinity values."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CodeFibers.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eq_of_evaluationEq_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eval_injective_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.continuousMap_eq_of_coe_eq_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_eval
    - AAT.AG.FiniteDecoderRepresentability.eq_finitePredicateCode_of_eval_eq
    - AAT.AG.FiniteDecoderRepresentability.FinitePredicateCodeFiber
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCodeFiberEquiv
    - AAT.AG.FiniteDecoderRepresentability.eval_eq_iff_eq_false_or_eq_true
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_false_ne_true
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_false_exceptions
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_true_exceptions
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_extensions_ne
  claim_mapping:
    theorem_names:
      - atomPredicateCode_eval_injective_of_infinite
      - continuousMap_eq_of_coe_eq_of_infinite
      - finitePredicateCodeFiberEquiv
      - eval_eq_iff_eq_false_or_eq_true
      - finitePredicateCode_false_exceptions
      - finitePredicateCode_true_exceptions
      - finitePredicateCode_false_ne_true
      - finitePredicateCode_extensions_ne
    source_labels:
      - "fixed target A: evaluation is injective and continuous extension is unique when D is infinite"
      - "fixed target A: every finite-carrier predicate has exactly the two specified raw codes"
      - "fixed target A: the two codes and their infinity values remain distinct for empty D"
    conjuncts:
      - "infinite raw-code evaluation injectivity"
      - "infinite continuous-map uniqueness from equality on D"
      - "finite fiber equivalence with Bool through authored default"
      - "explicit default-false true-set and default-true false-set exception tables"
      - "raw-code and infinity-value distinction without a nonempty premise"
    undischarged_assumptions: []
    acceptance_point: "Infinite default equality is constructed from the existing finite exception fields. Finite classification is an equivalence of the actual raw-code fiber, and the distinctness theorems require no Nonempty assumption, so the empty carrier is included."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A3 infinite evaluation injectivity"
      - "A3 infinite continuous-extension uniqueness"
      - "A3 exact finite raw-code fiber, explicit exception sets, and empty-carrier distinction"
    remaining:
      - "A G-112 choice agreement and transport coherence"
      - "all B--E construction obligations"
  certificate_provenance:
    discharged:
      - "the infinite witness Atom is derived by Infinite.exists_notMem_finset from the two authored exception tables"
      - "the finite inverse code is constructed from Finset.univ.filter and a chosen Bool default"
      - "continuous uniqueness consumes the A1 inverse and right-inverse theorems"
    unresolved: []
  proof_use:
    used:
      - "Infinite U.Atom supplies an Atom outside both finite exception tables"
      - "pointwise evaluation equality first recovers default equality and then exception-table equality"
      - "Fintype U.Atom supplies the complete finite exception tables"
      - "the fiber subtype proof is used in the equivalence left inverse"
      - "A1 continuous-map right inverse transports raw injectivity to extension uniqueness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/CodeFibers.lean; exit 0"
    - "namespace #assert_standard_axioms_only: 15 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "A4: prove the existing G-112 encoder selects the default-false fiber code on finite carriers and the unique raw code on infinite carriers; then prove transport compatibility and identity/inverse/composition coherence"
```

### Cycle 3 acceptance spine

For infinite `U.Atom`, the proof chooses an Atom outside the union of the two actual
finite exception tables. Evaluation there equals each authored default, so the assumed
pointwise equality derives default equality rather than accepting it. Evaluation at every
remaining Atom then determines exception membership, giving raw code equality. Applying
this theorem to codes recovered by the accepted A1 equivalence gives uniqueness of a
continuous extension from its values on `U.Atom`.

For finite `U.Atom`, `finitePredicateCode predicate defaultValue` records exactly the
points where the predicate differs from the authored default. Its evaluation theorem and
the converse uniqueness theorem make the full fiber subtype equivalent to `Bool`. The
two exception-table theorems identify the target's exact displayed codes. Their default
fields, and hence their A1 extensions at infinity, are unequal without assuming the
carrier is nonempty.

Cycle 3 material premise roles are:

- `ambient-boundary`: arbitrary fixed `AtomCarrier U` and the existing evaluator's
  `[DecidableEq U.Atom]`; the two branches add exactly `[Infinite U.Atom]` or
  `[Fintype U.Atom]` from the fixed target.
- `direction-hypothesis`: pointwise evaluation equality in the raw-code lemma and
  equality on the embedded Atom carrier in the continuous-map lemma.
- `discharge-required`: recovery of the infinite default, both raw structure fields,
  construction and exhaustiveness of the finite fiber, exact exception tables, and
  empty-carrier-safe distinction; all are proved in the module.
- `conclusion-equivalent-risk`: none. The finite fiber stores the target pointwise
  evaluation condition only; it does not store a second code, a classification theorem,
  or either inverse law.
