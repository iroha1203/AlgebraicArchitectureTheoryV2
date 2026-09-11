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
- current proof obligation: terminal fixed-target completion audit
- pending proof obligations: none in the fixed A--E statement; terminal completion gates remain
- current target state: `target-proof-candidate`
- completion candidate: yes
- next proof obligation: standard PR review, schema-complete final packet, and fresh whole-target Math A/B plus Lean A/B review

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
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/OnePointCode.lean"
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
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/EvaluationClassification.lean"
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
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_defaultValue
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_eval
    - AAT.AG.FiniteDecoderRepresentability.eq_finitePredicateCode_of_eval_eq
    - AAT.AG.FiniteDecoderRepresentability.FinitePredicateCodeFiber
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCodeFiberEquiv
    - AAT.AG.FiniteDecoderRepresentability.eval_eq_iff_eq_false_or_eq_true
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_false_ne_true
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_false_exceptions
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_true_exceptions
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode_extensions_apply_infty_ne
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
      - finitePredicateCode_extensions_apply_infty_ne
      - finitePredicateCode_extensions_ne
    source_labels:
      - "fixed target A: evaluation is injective and continuous extension is unique when D is infinite"
      - "fixed target A: every finite-carrier predicate has exactly the two specified raw codes"
      - "fixed target A: the two codes and their infinity values remain distinct for empty D"
    conjuncts:
      - "infinite raw-code evaluation injectivity"
      - "infinite continuous-map uniqueness from equality on D"
      - "finite fiber equivalence with Bool through authored default under the target's Finite premise"
      - "explicit default-false true-set and default-true false-set exception tables"
      - "raw-code and directly stated infinity-value distinction without a nonempty premise"
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
      - "Finite U.Atom is noncomputably enumerated inside the constructor to supply the complete finite exception tables"
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
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/CodeFibers.lean"
    - "namespace #assert_standard_axioms_only: 18 declarations, standard axioms only"
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
  `[DecidableEq U.Atom]`.
- `direction-hypothesis`: the fixed target's branch assumptions `[Infinite U.Atom]`
  and `[Finite U.Atom]`, pointwise evaluation equality in the raw-code lemma, and
  equality on the embedded Atom carrier in the continuous-map lemma. Finite
  enumeration is constructed noncomputably inside `finitePredicateCode` and is not
  an exposed premise.
- `discharge-required`: recovery of the infinite default, both raw structure fields,
  construction and exhaustiveness of the finite fiber, exact exception tables, and
  empty-carrier-safe distinction; all are proved in the module.
- `conclusion-equivalent-risk`: none. The finite fiber stores the target pointwise
  evaluation condition only; it does not store a second code, a classification theorem,
  or either inverse law.

## Cycle 4 — Agreement with the accepted G-112 encoder

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 4
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 9708c57b387df40ae2d8a93ff75cb19eca66ef6a
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 3: finite/infinite raw-code fibers discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode_eval
    - AAT.AG.FiniteDecoderRepresentability.eq_finitePredicateCode_of_eval_eq
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eval_injective_of_infinite
  proof_obligation: "A4: identify the accepted G-112 finite/cofinite encoder with the default-false code on finite carriers and with the unique raw code on infinite carriers"
  selection_reason: "A2 connected the quotient inverse to G-112 and A3 classified the raw fibers. This cycle now fixes which member the accepted encoder actually selects in each finite/infinite branch."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/EncoderChoice.lean
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode_eq_finitePredicateCode_false
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.eq_toCode_iff_eval_eq_of_infinite
  risks:
    - "proving only evaluation equivalence on finite carriers instead of raw equality to the default-false code"
    - "exposing Fintype rather than the fixed target Finite premise"
    - "reimplementing the G-112 encoder instead of using its accepted definition and evaluation theorem"
    - "assuming uniqueness on infinite carriers rather than deriving it from raw evaluation injectivity"
  unchecked:
    - "A's permutation transport and identity/inverse/composition coherence"
    - "B--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved that finite carrierhood forces the accepted G-112 encoder into its finite-true-set branch and hence authored default false; combined this with A3 fiber uniqueness at a fixed default to obtain raw code equality. On infinite carriers, combined the accepted encoder evaluation theorem with A3 raw injectivity to prove that every raw code carrying the predicate equals the G-112 code, and packaged the uniqueness as an iff."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/EncoderChoice.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode_defaultValue_of_finite
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.toCode_eq_finitePredicateCode_false
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.eq_toCode_of_eval_eq_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.FiniteOrCofiniteBoolPredicate.eq_toCode_iff_eval_eq_of_infinite
  claim_mapping:
    theorem_names:
      - FiniteOrCofiniteBoolPredicate.toCode_defaultValue_of_finite
      - FiniteOrCofiniteBoolPredicate.toCode_eq_finitePredicateCode_false
      - FiniteOrCofiniteBoolPredicate.eq_toCode_of_eval_eq_of_infinite
      - FiniteOrCofiniteBoolPredicate.eq_toCode_iff_eval_eq_of_infinite
    source_labels:
      - "fixed target A: existing finiteOrCofiniteAtomPredicateCode agrees with the classification"
      - "fixed target A: on finite D it selects the default-false code"
      - "fixed target A: on infinite D it agrees with the unique raw code"
    conjuncts:
      - "finite G-112 authored default is false"
      - "finite G-112 raw code equals the explicit default-false fiber code"
      - "infinite raw code has the prescribed evaluation iff it equals the G-112 code"
    undischarged_assumptions: []
    acceptance_point: "The finite conclusion is raw structure equality, not quotient equality. The infinite conclusion quantifies an arbitrary raw code and derives uniqueness from evaluation, rather than carrying uniqueness in the predicate subtype."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A4 finite default-false selection by the accepted G-112 encoder"
      - "A4 infinite agreement with the unique raw code"
    remaining:
      - "A permutation transport and identity/inverse/composition coherence"
      - "all B--E construction obligations"
  certificate_provenance:
    discharged:
      - "finite default is derived by unfolding the accepted G-112 branch test and discharging set finiteness from Finite U.Atom"
      - "finite raw equality uses the accepted G-112 evaluation theorem and A3 fixed-default uniqueness"
      - "infinite uniqueness uses the accepted G-112 evaluation theorem and A3 raw injectivity"
    unresolved: []
  proof_use:
    used:
      - "Finite U.Atom refutes the non-finite branch of the accepted encoder"
      - "G-112 pointwise evaluation supplies membership in the finite and infinite raw fibers"
      - "A3 fixed-default uniqueness upgrades finite evaluation equality to raw equality"
      - "A3 infinite injectivity upgrades pointwise evaluation equality to raw equality"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/EncoderChoice.lean"
    - "namespace #assert_standard_axioms_only: 4 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "A5: extend arbitrary Atom permutations to OnePoint homeomorphisms and prove code/continuous-map/evaluation transport compatibility with identity, inverse, and composition"
```

### Cycle 4 acceptance spine

For finite `U.Atom`, the existing G-112 definition tests whether the true locus is
finite. The target's `Finite U.Atom` premise discharges this test, so the selected
raw code has default `false`. Its accepted pointwise evaluation theorem places it
in the A3 fiber; A3 uniqueness at that fixed default then identifies the entire raw
structure with `finitePredicateCode predicate false`.

For infinite `U.Atom`, the proof does not inspect the encoder branch. Any raw code
with the requested evaluation agrees pointwise with the accepted G-112 code by its
existing evaluation theorem, and A3 injectivity forces raw equality. The iff form
records both the evaluation and uniqueness directions.

Cycle 4 material premise roles are:

- `ambient-boundary`: arbitrary fixed `AtomCarrier U` and the existing evaluator's
  `[DecidableEq U.Atom]`.
- `direction-hypothesis`: the fixed target's branch assumptions `[Finite U.Atom]`
  and `[Infinite U.Atom]`; the infinite uniqueness theorem also assumes the actual
  pointwise evaluation formula for the arbitrary code.
- `discharge-required`: accepted encoder default selection, finite raw equality, and
  infinite raw uniqueness; all are proved in the module.
- `conclusion-equivalent-risk`: none. The predicate subtype contains only the target's
  finite/cofinite image condition, not a code, default, raw equality, or uniqueness proof.

## Cycle 5 — Arbitrary permutation transport coherence

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 5
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 7317a1a83462fdd9f58c8e0ab608de32c8797b86
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 4: accepted G-112 encoder choice agreement discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode.transport
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode.eval_transport
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode.transport_refl
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode.transport_trans
    - AAT.AG.DoctrineFiberProduct.AtomPredicateCode.transport_symm_cancel
  proof_obligation: "A5: extend every Atom permutation to a OnePoint homeomorphism fixing infinity and prove that A1 intertwines existing code transport with inverse pullback, coherently with identity, inverse, composition, and evaluation"
  selection_reason: "Cycles 1-4 complete A's object and raw-fiber classification. The remaining A clause is functoriality under unrestricted Atom permutations and is the transport API needed later by C and E."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/PermutationTransport.lean
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm
    - AAT.AG.FiniteDecoderRepresentability.continuousPredicateTransport
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_transport
  risks:
    - "restricting the permutation to finite support"
    - "using the forward permutation rather than inverse pullback on continuous maps"
    - "reversing the composition order relative to Equiv.trans and existing code transport"
    - "proving only embedded-Atom evaluation and omitting infinity or whole-map equality"
  unchecked:
    - "B--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Extended an arbitrary Equiv.Perm U.Atom through its discrete homeomorphism to Homeomorph.onePointCongr; proved its infinity and embedded-Atom evaluations and identity/inverse/composition laws; defined continuous pullback along the inverse and proved its identity/composition/inverse laws; exposed the arbitrary-point inverse evaluation formula for existing code transport; and proved whole ContinuousMap equality intertwining A1 with the two actions."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/PermutationTransport.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm_apply_infty
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm_apply_coe
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm_refl
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm_symm
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm_trans
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eval_transport_apply
    - AAT.AG.FiniteDecoderRepresentability.continuousPredicateTransport
    - AAT.AG.FiniteDecoderRepresentability.continuousPredicateTransport_apply
    - AAT.AG.FiniteDecoderRepresentability.continuousPredicateTransport_refl
    - AAT.AG.FiniteDecoderRepresentability.continuousPredicateTransport_trans
    - AAT.AG.FiniteDecoderRepresentability.continuousPredicateTransport_symm_cancel
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_transport
  claim_mapping:
    theorem_names:
      - onePointAtomPerm_apply_infty
      - onePointAtomPerm_apply_coe
      - onePointAtomPerm_refl
      - onePointAtomPerm_symm
      - onePointAtomPerm_trans
      - atomPredicateCode_eval_transport_apply
      - continuousPredicateTransport_refl
      - continuousPredicateTransport_trans
      - continuousPredicateTransport_symm_cancel
      - atomPredicateCodeToContinuousMap_transport
    source_labels:
      - "fixed target A: every Atom permutation extends to a OnePoint homeomorphism fixing infinity"
      - "fixed target A: E_D(q.transport sigma) equals E_D(q) precomposed with inverse sigma-plus"
      - "fixed target A: code, continuous map, and evaluation correspondences respect identity, inverse, and composition"
    conjuncts:
      - "unrestricted permutation extension and point evaluations"
      - "identity, inverse, and composition coherence of the OnePoint extension"
      - "inverse-point evaluation formula for existing raw-code transport"
      - "identity, composition, and inverse coherence of continuous pullback"
      - "whole-map equivariance of the A1 equivalence"
    undischarged_assumptions: []
    acceptance_point: "All theorems quantify Equiv.Perm U.Atom directly. The continuous action is explicitly inverse pullback, and the final conclusion is equality of bundled ContinuousMap values including infinity."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A5 unrestricted OnePoint permutation extension"
      - "A5 code/continuous/evaluation transport compatibility"
      - "A5 identity, inverse, and composition coherence"
    remaining:
      - "all B--E construction obligations"
  certificate_provenance:
    discharged:
      - "OnePoint homeomorphism is constructed by mathlib Homeomorph.onePointCongr from the actual arbitrary permutation"
      - "continuous action is constructed as ContinuousMap.comp with the actual inverse homeomorphism"
      - "code action is the existing AtomPredicateCode.transport, with its accepted laws reused"
    unresolved: []
  proof_use:
    used:
      - "the input permutation supplies both the OnePoint homeomorphism and existing code transport"
      - "existing eval_transport proves the inverse-point evaluation formula"
      - "OnePoint.rec checks both infinity and every embedded Atom"
      - "existing A1 evaluation at infinity and embedded Atoms proves whole-map equivariance"
      - "existing transport_refl, transport_trans, and transport_symm_cancel remain the code-side coherence laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/PermutationTransport.lean"
    - "namespace #assert_standard_axioms_only: 15 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "B1: characterize Nonempty AnchoredCoverageWitness by finite endpoints and continuous extension of every target extraction predicate, then restate endpoint finiteness as compactness"
```

### Cycle 5 acceptance spine

`onePointAtomPerm` uses the arbitrary input permutation itself, first as a homeomorphism
of the fixed discrete Atom space and then through mathlib's one-point-congruence constructor.
Its point API proves that infinity is fixed and embedded Atoms follow the input permutation.
The identity, inverse, and composition theorems are equalities of bundled homeomorphisms.

`continuousPredicateTransport` is precomposition by the inverse extended homeomorphism.
Its composition order matches `Equiv.trans`, and its inverse law follows from that composition
law. The existing code transport is not replaced: its accepted evaluation law is converted to
the arbitrary-target-Atom formula, while its existing identity/composition/inverse laws supply
the code-side coherence. Finally, `atomPredicateCodeToContinuousMap_transport` proves equality
of bundled continuous maps by checking both OnePoint constructors.

Cycle 5 material premise roles are:

- `ambient-boundary`: arbitrary fixed `AtomCarrier U`, the fixed discrete topology, and the
  existing evaluator's `[DecidableEq U.Atom]` where code evaluation is used.
- `direction-hypothesis`: the arbitrary input `Equiv.Perm U.Atom`; no support hypothesis.
- `discharge-required`: construction of the extended homeomorphism, restriction and infinity
  values, action direction, whole-map equivariance, and all three coherence laws; all are
  proved in this module or explicitly reused from the existing code API.
- `conclusion-equivalent-risk`: none. The input is the permutation itself, not a transport
  equality, homeomorphism extension, or coherence certificate.

## Cycle 6 — Anchored coverage and continuous target extensions

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 6
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: cef553ba77ce56853dde7f84d8d8e2026dfc3599
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 5: all fixed target A clauses discharged"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.coveredObjectWitness_necessary
    - AAT.AG.DoctrineFiberProduct.endpointFiniteTargetCofiniteCoverage
    - AAT.AG.DoctrineFiberProduct.atomPredicateCode_finiteOrCofinite
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap
    - AAT.AG.FiniteDecoderRepresentability.continuousMapToAtomPredicateCode
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_rightInverse
  proof_obligation: "B1: characterize Nonempty AnchoredCoverageWitness by finite source and target Source types together with a continuous OnePoint extension of every target extraction predicate"
  selection_reason: "The accepted G-112 theorem already gives necessity and sufficiency using finite/cofinite extraction sets. Target A converts exactly that predicate condition to continuous extension, so the fixed B equivalence can be proved without creating a parallel coverage construction."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CoverageTopology.lean
    - AAT.AG.FiniteDecoderRepresentability.nonempty_anchoredCoverageWitness_iff_finite_continuousExtensions
  risks:
    - "building a new coverage certificate instead of invoking the accepted G-112 constructor"
    - "proving only sufficiency and not extracting both finite endpoints from an actual witness"
    - "storing continuous extension as a field rather than quantifying the actual map and pointwise formula"
    - "losing the Bool=true iff extracts specification when converting through A1"
  unchecked:
    - "B compactness reformulation for discrete Source spaces"
    - "B source-map and Atom-permutation agreement with decoder identity/composition"
    - "C--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved both directions between target finite/cofinite extraction and actual continuous Bool extensions using A1 and the accepted G-112 code theorem. From an anchored witness, extracted finite Source types and target finite/cofinite extraction through both actual endpoint anchors; converted the latter to continuous extensions. Conversely, converted supplied extensions to the accepted target condition, installed the two derived Finite instances, and invoked endpointFiniteTargetCofiniteCoverage."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CoverageTopology.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.allExtractionsFiniteOrCofinite_of_continuousExtensions
    - AAT.AG.FiniteDecoderRepresentability.continuousExtensions_of_allExtractionsFiniteOrCofinite
    - AAT.AG.FiniteDecoderRepresentability.allExtractionsFiniteOrCofinite_iff_continuousExtensions
    - AAT.AG.FiniteDecoderRepresentability.nonempty_anchoredCoverageWitness_iff_finite_continuousExtensions
  claim_mapping:
    theorem_names:
      - allExtractionsFiniteOrCofinite_iff_continuousExtensions
      - nonempty_anchoredCoverageWitness_iff_finite_continuousExtensions
    source_labels:
      - "fixed target B: target extraction predicates extend continuously exactly when finite or cofinite"
      - "fixed target B: anchored coverage exists iff both Sources are finite and every target extraction has such an extension"
    conjuncts:
      - "actual continuous maps with Bool=true iff target extracts"
      - "finite source and target Source types extracted from actual endpoint anchors"
      - "necessity and sufficiency of the complete anchored coverage condition"
      - "sufficiency routed through the accepted G-112 coverage constructor"
    undischarged_assumptions: []
    acceptance_point: "The main theorem quantifies the actual continuous map for every target source cell. Its reverse direction constructs finite/cofinite evidence from those maps and calls the existing endpointFiniteTargetCofiniteCoverage theorem; no coverage witness appears as a premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B1 anchored coverage iff finite endpoints and continuous target extensions"
    remaining:
      - "B compactness restatement and decoded arrow identity/composition coherence"
      - "all C--E construction obligations"
  certificate_provenance:
    discharged:
      - "finite endpoints and target extraction conditions are derived from actual sourceAnchor and targetAnchor fields"
      - "continuous-extension necessity derives a raw code from the genuine ContinuousMap through A1"
      - "coverage sufficiency is constructed by the accepted G-112 endpointFiniteTargetCofiniteCoverage"
    unresolved: []
  proof_use:
    used:
      - "each supplied continuous map and pointwise iff derives the finite/cofinite target condition"
      - "A1 right inverse identifies recovered-code evaluation with the actual continuous map"
      - "both endpoint anchors yield their respective Finite Source instances"
      - "the derived target condition is passed to the accepted G-112 coverage constructor"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/CoverageTopology.lean"
    - "namespace #assert_standard_axioms_only: 6 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans: no findings"
  blocking_findings: []
  next_obligation: "B2: restate endpoint Source finiteness as compactness of discrete Source spaces and connect coverage presentation source maps, Atom permutations, identity, and composition to typedPresentationToSemantic and finiteCodeCartRealization"
```

### Cycle 6 acceptance spine

For one endpoint object, continuous-extension necessity applies the A1 inverse to each
genuine continuous map and uses the A1 right inverse to identify its raw evaluation.
The accepted theorem that every raw exception table is finite or cofinite then transfers
through the supplied pointwise iff to the semantic extraction set. Sufficiency uses the
accepted G-112 finite/cofinite encoder followed by the A1 continuous-map construction.

For a semantic arrow, an actual `AnchoredCoverageWitness` contains both endpoint anchors.
The accepted anchor-necessity theorem supplies both Source finiteness conclusions and the
target finite/cofinite condition, which the endpoint lemma converts to continuous maps.
Conversely, the two finite proof terms become local instances, continuous extensions yield
the target finite/cofinite condition, and the accepted G-112 coverage constructor produces
the full anchors, typed presentation, endpoint isomorphisms, and commuting square.

Cycle 6 material premise roles are:

- `ambient-boundary`: arbitrary fixed `AtomCarrier U`, the fixed discrete Atom topology,
  and the existing evaluator's `[DecidableEq U.Atom]`.
- `direction-hypothesis`: either an actual anchored witness, or the two target-level
  `Finite` propositions and an actual continuous extension with its pointwise formula for
  every target source cell.
- `discharge-required`: both endpoint finite conclusions, conversion in both directions
  between target extraction and continuous extension, and construction of the full coverage
  witness; all are proved or routed to the accepted G-112 constructors.
- `conclusion-equivalent-risk`: none. No new input structure stores a code, endpoint anchor,
  coverage square, finite/cofinite proof, or inverse law.

## Cycle 7 — Discrete Source compactness

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 7
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: ddb66f6af38674531d35ed8de5092cf11351786b
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 6: B1 coverage/continuous-extension equivalence discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.nonempty_anchoredCoverageWitness_iff_finite_continuousExtensions
    - Finite.compactSpace
    - finite_of_compact_of_discrete
  proof_obligation: "B2 object clause: identify finiteness with compactness for the explicitly discrete Source topology and restate the complete B1 coverage criterion using compactness at both endpoints"
  selection_reason: "The compactness clause is an exact logical restatement of the accepted B1 endpoint finiteness propositions. Keeping it separate from arrow coherence makes the fixed topology and the later decoder comparison independently reviewable."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/DiscreteCompactness.lean
    - AAT.AG.FiniteDecoderRepresentability.nonempty_anchoredCoverageWitness_iff_compact_continuousExtensions
  risks:
    - "assuming an ambient topology on Source rather than fixing the discrete topology"
    - "proving compactness only from finiteness and omitting the converse"
    - "dropping either endpoint or the target continuous-extension clause"
  unchecked:
    - "B source-map and Atom-permutation agreement with decoder identity/composition"
    - "C--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved for an arbitrary type that Finite is equivalent to CompactSpace under the explicit bottom topology, using the standard finite compactness instance and compact-discrete finiteness theorem. Rewrote the accepted B1 criterion to require compactness of both discrete Source spaces while preserving every actual target continuous extension and its pointwise specification."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/DiscreteCompactness.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.finite_iff_compactSpace_bot
    - AAT.AG.FiniteDecoderRepresentability.nonempty_anchoredCoverageWitness_iff_compact_continuousExtensions
  claim_mapping:
    theorem_names:
      - finite_iff_compactSpace_bot
      - nonempty_anchoredCoverageWitness_iff_compact_continuousExtensions
    source_labels:
      - "fixed target B: Source finiteness is equivalent to compactness of its discrete topology"
      - "fixed target B: coverage criterion stated by compactness of both Sources and continuous target extensions"
    conjuncts:
      - "Finite X iff CompactSpace X under TopologicalSpace.bot"
      - "compactness of the source Source type"
      - "compactness of the target Source type"
      - "all target extraction predicates have the B1 continuous extensions"
    undischarged_assumptions: []
    acceptance_point: "Both CompactSpace propositions carry an explicit bottom topology in the public statement, so no caller-selected topology or compactness certificate can change the meaning of the fixed discrete-space claim."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B discrete Source finiteness/compactness equivalence"
      - "B complete compactness form of the coverage criterion"
    remaining:
      - "B decoded-arrow identity/composition coherence"
      - "all C--E construction obligations"
  certificate_provenance:
    discharged:
      - "finite-to-compact uses the standard Finite.compactSpace construction"
      - "compact-to-finite uses finite_of_compact_of_discrete after fixing TopologicalSpace.bot"
    unresolved: []
  proof_use:
    used:
      - "both directions of finite_iff_compactSpace_bot rewrite the two endpoint propositions"
      - "the accepted B1 equivalence supplies the unchanged continuous-extension clause"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/DiscreteCompactness.lean"
    - "namespace #assert_standard_axioms_only: standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans"
  blocking_findings: []
  next_obligation: "B3: connect coverage presentation source maps and Atom permutations to typedPresentationToSemantic and finiteCodeCartRealization, including identity and composition"
```

### Cycle 7 acceptance spine

`finite_iff_compactSpace_bot` states the topology in the proposition itself.  Its forward
direction installs only the supplied `Finite` proof and uses the standard compactness
construction; its reverse direction installs the explicit bottom topology and applies the
compact-discrete finiteness theorem.  The main theorem rewrites both endpoint propositions
of the accepted Cycle 6 equivalence and leaves the quantified continuous maps unchanged.

Cycle 7 material premise roles are:

- `ambient-boundary`: arbitrary Source types and their explicitly fixed bottom topology,
  plus the existing G-121 discrete Atom topology inherited from B1.
- `direction-hypothesis`: either a `Finite` proposition or a `CompactSpace` proposition for
  the same explicit discrete topology; the main theorem has the same two directions as B1.
- `discharge-required`: both finite/compact implications and both endpoint rewrites; all are
  proved in `finite_iff_compactSpace_bot` and used by the main theorem.
- `conclusion-equivalent-risk`: none. Compactness is not supplied for an arbitrary topology,
  and the continuous-extension clause is neither stored nor weakened.

## Cycle 8 — Coverage presentation and decoder arrow coherence

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 8
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 5bf2d3f74ba75abaf23ab5f9631f60a8fcfa2d32
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 7: B object/topology compactness clause discharged"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.endpointFiniteTargetCofinitePresentation
    - AAT.AG.DoctrineFiberProduct.endpointFiniteTargetCofinitePresentation_hom_comm
    - AAT.AG.DoctrineFiberProduct.typedPresentationToSemantic
    - AAT.AG.DoctrineFiberProduct.idTypedPresentation
    - AAT.AG.DoctrineFiberProduct.compPresentation
    - AAT.AG.DoctrineFiberProduct.finiteCodeCartRealization
  proof_obligation: "B3: expose agreement of the G-112 coverage presentation's source map and Atom permutation with its typed decoder, connect its endpoint square to typedPresentationToSemantic, and prove that direct typed decoding and D0 evaluation agree for represented morphisms, identity, and composition"
  selection_reason: "B1 and B2 already characterize existence and endpoint topology. The remaining fixed B clause is arrow-level: it must point to the actual G-112 generated presentation and the existing quotient functor rather than merely cite category laws abstractly."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/ArrowCoherence.lean
    - AAT.AG.FiniteDecoderRepresentability.endpointFiniteTargetCofinitePresentation_typed_hom_comm
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_map_ofPresentation
  risks:
    - "stating only abstract functor laws without identifying the generated coverage presentation fields"
    - "confusing the presentation's identity Atom table with the semantic input permutation carried by the target endpoint isomorphism"
    - "proving source-map or Atom agreement only for raw presentations rather than for typedPresentationToSemantic"
    - "introducing a second decoder or composition operation"
  unchecked:
    - "C--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Exposed that typedPresentationToSemantic reads the authored sourceMap and decoded Atom permutation exactly. Specialized the source-map formula and identity presentation permutation to the concrete G-112 coverage constructor, and restated its accepted endpoint commuting square with typed decoding. Proved that finiteCodeCartRealization maps a quotient representative to that same typed arrow and that the existing typed identity and composition constructors decode to categorical identity and composition."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/ArrowCoherence.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.typedPresentationToSemantic_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.typedPresentationToSemantic_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.endpointFiniteTargetCofinitePresentation_decoded_sourceMap_apply
    - AAT.AG.FiniteDecoderRepresentability.endpointFiniteTargetCofinitePresentation_decoded_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.endpointFiniteTargetCofinitePresentation_typed_hom_comm
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_map_ofPresentation
    - AAT.AG.FiniteDecoderRepresentability.typedPresentationToSemantic_id
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_map_compPresentation
  claim_mapping:
    theorem_names:
      - typedPresentationToSemantic_sourceMap
      - typedPresentationToSemantic_atomEquiv
      - endpointFiniteTargetCofinitePresentation_decoded_sourceMap_apply
      - endpointFiniteTargetCofinitePresentation_decoded_atomEquiv
      - endpointFiniteTargetCofinitePresentation_typed_hom_comm
      - finiteCodeCartRealization_map_ofPresentation
      - typedPresentationToSemantic_id
      - finiteCodeCartRealization_map_compPresentation
    source_labels:
      - "fixed target B: coverage presentation source map and Atom permutation agree with the decoder arrow"
      - "fixed target B: identity and composition agree under typedPresentationToSemantic and D0"
    conjuncts:
      - "typed decoding exposes the exact authored source map"
      - "typed decoding exposes AtomPermutationCode.toEquiv"
      - "the G-112 generated source map is the semantic source map conjugated by the endpoint enumerations"
      - "the G-112 presentation's own Atom table is identity while the semantic permutation is carried by the target anchor"
      - "the accepted G-112 endpoint square uses the same typed decoder"
      - "D0.map on an authored representative is direct typed decoding"
      - "idTypedPresentation decodes to identity"
      - "compPresentation decodes to composition"
    undischarged_assumptions: []
    acceptance_point: "The theorems inspect the actual generated presentation and existing D0 functor. The identity Atom table is not mislabeled as the semantic input permutation: the latter remains explicitly in the target endpoint isomorphism of the commuting-square theorem."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B generated-presentation source-map and Atom-permutation agreement"
      - "B coverage square connection to typed decoding"
      - "B D0 representative, identity, and composition evaluation coherence"
    remaining:
      - "all C--E construction obligations"
  certificate_provenance:
    discharged:
      - "coverage fields come from endpointFiniteTargetCofinitePresentation, not from a supplied parallel witness"
      - "the semantic square is endpointFiniteTargetCofinitePresentation_hom_comm with its existing generated endpoint isomorphisms"
      - "D0 evaluation is the quotient lift FiniteCodeCartHom.toSemantic"
    unresolved: []
  proof_use:
    used:
      - "the actual presentation fields determine both decoded components"
      - "the generated finiteSourceEquiv maps identify the coverage source table"
      - "the target endpoint isomorphism retains input.hom.doctrineHom.atomEquiv"
      - "finiteCodeCartRealization.map_id and the existing composition theorem supply identity and composition"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/ArrowCoherence.lean"
    - "namespace #assert_standard_axioms_only: 8 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans"
  blocking_findings: []
  next_obligation: "C1: prove the iff between existence of a fixed-endpoint typed presentation decoding a semantic arrow and finite Atom support plus preservation of normalized extraction-code default values"
```

### Cycle 8 acceptance spine

The generic accessor theorems identify the two data components of every typed decoder
without adding a certificate.  For the G-112 constructor, the decoded source map is the
input semantic source map transported through the generated finite endpoint enumerations.
Its authored Atom table is identity; the input semantic Atom permutation is retained by
the generated target endpoint isomorphism, and the accepted commuting theorem explicitly
composes that isomorphism with the same typed decoder.

At the quotient-calculus level, `finiteCodeCartRealization_map_ofPresentation` shows that
`D₀.map` of an authored representative is definitionally the direct typed decode.  The
identity and composition theorems then consume the existing `idTypedPresentation`,
`compPresentation`, functor identity law, and decoded-composition theorem rather than
constructing a parallel category or decoder.

Cycle 8 material premise roles are:

- `ambient-boundary`: arbitrary fixed Atom carrier, finite generated endpoints where the
  coverage constructor requires them, and the existing `[DecidableEq U.Atom]` evaluator.
- `direction-hypothesis`: the target finite/cofinite extraction condition required by the
  accepted G-112 constructor; arbitrary typed presentations for the generic decoder laws.
- `discharge-required`: exact source-map and Atom components, the generated semantic square,
  representative evaluation, identity, and composition; all are proved by the eight public
  theorems.
- `conclusion-equivalent-risk`: none. No semantic equality, square, or functor law is accepted
  as a new input field; all are read from the existing constructors and decoder.

## Cycle 9 — Finite-support Atom permutation tables

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 9
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 5ddafa8fb30ce7393d4ea40a27db0d4c291a1786
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 8: all fixed target B clauses discharged"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.AtomPermutationCode
    - AAT.AG.DoctrineFiberProduct.AtomPermutationCode.ofPerm
    - AAT.AG.DoctrineFiberProduct.AtomPermutationCode.toEquiv_ofPerm
    - AAT.AG.DoctrineFiberProduct.AtomPermutationCode.toEquiv_apply_not_mem
  proof_obligation: "C1 Atom component: prove that a semantic Atom permutation is exactly decoded by an existing finite Atom table iff its actual moved-point set is finite, and construct the table from that finite set"
  selection_reason: "Finite support is one independent conjunct of the fixed-code morphism criterion. Isolating its exact existing-code classification prevents the later presentation constructor from accepting an authored support table or decoded-equality certificate as an extra premise."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/PermutationCodeClassification.lean
    - AAT.AG.FiniteDecoderRepresentability.exists_atomPermutationCode_toEquiv_iff
  risks:
    - "using a Fintype-only Finset support API for an arbitrary carrier"
    - "taking a support Finset as supplied data instead of deriving it from Set.Finite"
    - "constructing a table whose extension merely agrees on support rather than decoding to the supplied permutation"
    - "omitting invariance of the moved-point set under the permutation"
  unchecked:
    - "remaining C fixed-code presentation construction, default-value necessity/sufficiency, infinite-carrier simplification, quotient faithfulness"
    - "D--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined the actual moved-point support as a Set for arbitrary Atom carriers. Proved every decoded AtomPermutationCode has finite moved support by containment in its authored Finset. Conversely, converted a finite moved-point set to its derived Finset, proved that set invariant and fixedness off it, applied AtomPermutationCode.ofPerm, and proved exact whole-permutation decoding. Packaged both directions as an existence iff."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/PermutationCodeClassification.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.atomPermutationSupport
    - AAT.AG.FiniteDecoderRepresentability.atomPermutationSupport_finite_of_code
    - AAT.AG.FiniteDecoderRepresentability.atomPermutationCodeOfFiniteSupport
    - AAT.AG.FiniteDecoderRepresentability.atomPermutationCodeOfFiniteSupport_toEquiv
    - AAT.AG.FiniteDecoderRepresentability.exists_atomPermutationCode_toEquiv_iff
  claim_mapping:
    theorem_names:
      - atomPermutationSupport_finite_of_code
      - atomPermutationCodeOfFiniteSupport_toEquiv
      - exists_atomPermutationCode_toEquiv_iff
    source_labels:
      - "fixed target C: supp(sigma) is the set of actually moved Atoms"
      - "fixed target C: finite support is necessary and sufficient for the Atom component to have an existing finite-table representation"
    conjuncts:
      - "support is a Set and does not require Fintype on the carrier"
      - "a decoded table moves Atoms only inside its authored Finset"
      - "the finite moved set is converted to the constructor support Finset"
      - "the support is invariant under the permutation"
      - "the constructed table decodes to the supplied permutation as an Equiv equality"
      - "existence iff finite moved support"
    undischarged_assumptions: []
    acceptance_point: "The sufficiency theorem accepts only the semantic permutation and finiteness of its actual moved-point Set. The Finset, invariance proof, off-support fixedness, subtype table, and exact decoding equality are all constructed internally."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C finite-support necessity for decoded Atom tables"
      - "C finite-support sufficiency and exact Atom table construction"
    remaining:
      - "C full typed-presentation representability iff including default values"
      - "C continuous infinity-value restatement, infinite-carrier simplification, and D0 faithfulness"
      - "all D--E obligations"
  certificate_provenance:
    discharged:
      - "the support Finset is hfinite.toFinset for the actual moved-point Set"
      - "the table is AtomPermutationCode.ofPerm and exact decoding is AtomPermutationCode.toEquiv_ofPerm"
    unresolved: []
  proof_use:
    used:
      - "outside-support decoding fixes each Atom, proving necessity"
      - "permutation injectivity proves moved-set invariance"
      - "finite-set membership proves off-support fixedness"
      - "the constructed table witnesses the reverse implication"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/PermutationCodeClassification.lean"
    - "namespace #assert_standard_axioms_only: 5 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans"
  blocking_findings: []
  next_obligation: "C2: construct and classify CartPresentationBetween source target decoding a fixed semantic arrow from finite Atom support plus normalized default-value preservation"
```

### Cycle 9 acceptance spine

The support predicate is the fixed target's actual moved-point set, represented as a `Set`
so arbitrary carriers remain allowed.  Necessity uses the existing decoder law that every
Atom outside an authored support Finset is fixed.  Sufficiency canonically derives one finite
table from the actual moved-point set via `Set.Finite.toFinset`, proves invariance from permutation
injectivity, proves fixedness
outside the actual support by membership negation, and invokes the existing constructor.
The result is equality of whole `Equiv.Perm` values, not pointwise agreement restricted to
the chosen table.

Cycle 9 material premise roles are:

- `ambient-boundary`: arbitrary fixed Atom carrier and `[DecidableEq U.Atom]` inherited from
  the existing permutation table decoder.
- `direction-hypothesis`: either an actual `AtomPermutationCode` decoding to the semantic
  permutation, or finiteness of the permutation's actual moved-point Set.
- `discharge-required`: support containment, derived Finset, invariance, off-support fixedness,
  subtype table construction, and exact decoding; all are proved in the five declarations.
- `conclusion-equivalent-risk`: none. No authored Finset, table, invariance proof, or decoding
  equality is supplied to the sufficiency constructor.

## Cycle 10 — Fixed-endpoint morphism representability

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 10
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 0e61656cf4b3f4539d7ea725c5f3a49986390e31
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 9: C Atom finite-support table classification discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.atomPermutationCodeOfFiniteSupport
    - AAT.AG.FiniteDecoderRepresentability.atomPermutationSupport_finite_of_code
    - AAT.AG.DoctrineFiberProduct.CartPresentationBetween
    - AAT.AG.DoctrineFiberProduct.typedPresentationToSemantic
    - AAT.AG.DoctrineFiberProduct.FiniteDoctrineCode.toDoctrine_extracts_iff
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_map_ofPresentation
  proof_obligation: "C2 main iff: for literal finite-code endpoints and an actual semantic arrow, classify existence of a decoding CartPresentationBetween and of a D0 quotient morphism by finite actual Atom support plus preservation of normalized extraction-code default values"
  selection_reason: "This is the central fixed-endpoint theorem of C. Cycle 9 supplies the only nontrivial finite table constructor; semantic exactness must now discharge normalization and evaluation while the default condition recovers raw code equality."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowClassification.lean
    - AAT.AG.FiniteDecoderRepresentability.exists_fixedPresentation_decode_iff
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff
  risks:
    - "accepting source-map or Atom-component equality as an extra sufficiency certificate"
    - "proving only evaluation equality rather than raw extraction-code equality"
    - "forgetting that normalized tables, not arbitrary extraction-table positions, govern the default condition"
    - "choosing new endpoint codes or endpoint isomorphisms instead of keeping source and target literal"
    - "stopping at typed presentations without connecting the D0 quotient morphism"
  unchecked:
    - "C infinity-value restatement, infinite-carrier simplification, and D0 faithfulness"
    - "D--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined the normalized extraction code t_P(s). Proved raw finite-exception codes equal from equal defaults and pointwise evaluations. Necessity extracts finite Atom support from the actual presentation table and default preservation from its raw extraction equality after decoder component identification. Sufficiency uses the semantic arrow's source map, Cycle 9's exact finite Atom table, semantic normalization, semantic extraction iff, and default preservation to construct all CartPresentationBetween fields and prove direct decoding equality. Finally proved equivalence with existence of a D0 quotient morphism by choosing and inserting actual quotient representatives."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowClassification.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.normalizedExtractionCode
    - AAT.AG.FiniteDecoderRepresentability.normalizedExtractionCode_defaultValue
    - AAT.AG.FiniteDecoderRepresentability.normalizedExtractionCode_eval
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_transport_defaultValue
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eq_of_defaultValue_eq_of_eval_eq
    - AAT.AG.FiniteDecoderRepresentability.fixedPresentation_necessary
    - AAT.AG.FiniteDecoderRepresentability.fixedPresentationOfFiniteSupport
    - AAT.AG.FiniteDecoderRepresentability.fixedPresentationOfFiniteSupport_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.fixedPresentationOfFiniteSupport_atomEquiv_toEquiv
    - AAT.AG.FiniteDecoderRepresentability.fixedPresentationOfFiniteSupport_decode
    - AAT.AG.FiniteDecoderRepresentability.exists_fixedPresentation_decode_iff
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff_exists_fixedPresentation
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff
  claim_mapping:
    theorem_names:
      - fixedPresentation_necessary
      - fixedPresentationOfFiniteSupport_decode
      - exists_fixedPresentation_decode_iff
      - exists_finiteCodeCartHom_map_iff_exists_fixedPresentation
      - exists_finiteCodeCartHom_map_iff
    source_labels:
      - "fixed target C: t_P(s) is the normalized extraction table"
      - "fixed target C: fixed-code morphism representability iff finite support and normalized default preservation"
      - "fixed target C: equivalent existence of a CartPresentationBetween decoding the same arrow"
    conjuncts:
      - "literal source and target FiniteInstanceCode endpoints"
      - "actual semantic source map and Atom permutation are used by the constructed presentation"
      - "normalization and selected point laws come from the actual semantic arrow"
      - "semantic extraction exactness gives pointwise evaluation equality"
      - "default preservation upgrades evaluation equality to raw code equality"
      - "the constructed typed presentation decodes to the original semantic arrow"
      - "typed-presentation existence and D0 quotient-morphism existence are equivalent"
      - "both existence forms have the same finite-support/default-value iff"
    undischarged_assumptions: []
    acceptance_point: "The sufficient side accepts only the actual semantic arrow, finiteness of its actual moved support, and the fixed target's normalized default equation. The source map, Atom table, three presentation laws, raw code equality, and decode equality are constructed; endpoints are not replaced."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C fixed-endpoint typed-presentation representability iff"
      - "C fixed-endpoint D0 morphism representability iff"
      - "C exact recovery of source map and Atom permutation in the constructed presentation"
    remaining:
      - "C default condition as equality at infinity"
      - "C infinite-carrier reduction to finite support alone"
      - "C D0 faithfulness from the decoded-equality quotient"
      - "all D--E obligations"
  certificate_provenance:
    discharged:
      - "the Atom table is constructed from actual support by Cycle 9"
      - "normalization and source-point laws are actual fields of the semantic arrow"
      - "raw extraction equality is reconstructed from semantic extraction iff and the supplied target-level default condition"
      - "the D0 representative is either inserted with ofPresentation or recovered by Quotient.exists_rep"
    unresolved: []
  proof_use:
    used:
      - "presentation decode equality identifies both computational morphism components in necessity"
      - "presentation extraction_eq yields default preservation"
      - "semantic normalize_eq, extraction_iff, and source_eq populate all validation laws in sufficiency"
      - "finite support constructs the exact AtomPermutationCode"
      - "default preservation is used by raw-code extensionality"
      - "quotient representative equality transports D0.map to direct typed decoding"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowClassification.lean"
    - "namespace #assert_standard_axioms_only: 13 declarations, standard axioms only"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans"
  blocking_findings: []
  next_obligation: "C3: identify normalized default preservation with equality of A's continuous extensions at infinity; derive it from semantic exactness on infinite carriers; reduce representability to finite support alone; and prove D0 faithful from its decoded-equality quotient"
```

### Cycle 10 acceptance spine

For necessity, equality of the typed decoder with the supplied semantic arrow identifies the
presentation's source map and decoded Atom permutation.  The authored Atom table then proves
finite actual support, and applying `defaultValue` to the presentation's raw extraction law
gives exactly the normalized default equation because transport preserves defaults.

For sufficiency, the constructed presentation uses the semantic source map literally and the
Cycle 9 table decoding the semantic Atom permutation exactly.  Semantic normalization and the
selected-point law fill two validation fields.  Semantic extraction exactness, evaluated at the
inverse Atom, gives equality of the target normalized table and the transported source table at
every Atom.  The supplied default equation supplies their missing infinity/default component;
raw-code extensionality then proves the required structure equality.  No endpoint isomorphic
replacement occurs.  Quotient representative existence finally connects exactly these typed
presentations to morphisms of `FiniteCodeCartCategory U` under `finiteCodeCartRealization`.

Cycle 10 material premise roles are:

- `ambient-boundary`: arbitrary fixed Atom carrier, literal finite instance codes `source` and
  `target`, and `[DecidableEq U.Atom]` inherited from the existing evaluator and decoder.
- `direction-hypothesis`: an actual semantic arrow; for sufficiency, finite actual moved support
  and the normalized default equation appearing on the fixed target's right-hand side.
- `discharge-required`: finite Atom table, source map, normalization, raw extraction equality,
  selected point, decode equality, and quotient representative bridge; all are constructed by
  the thirteen declarations.
- `conclusion-equivalent-risk`: none. The sufficient side receives no presentation, source-map
  equality, Atom table, extraction equality, endpoint isomorphism, or decode equality.

## Cycle 11: infinite-carrier consequences and D0 faithfulness

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 11
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 5f8ee568b7f8d7d8b5dac971580faca31f24fd5f
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 10: C fixed-endpoint finite-support/default classification discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eq_of_evaluationEq_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCodeToContinuousMap_apply_infty
    - AAT.AG.FiniteDecoderRepresentability.exists_fixedPresentation_decode_iff
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff
    - AAT.AG.DoctrineFiberProduct.cartPresentationSetoid
  proof_obligation: "C3: identify normalized default preservation with equality at infinity; derive it from semantic exactness on infinite carriers; reduce both representability forms to finite support alone; prove D0 faithful for every carrier"
  selection_reason: "These are exactly the remaining consequences of C after Cycle 10's fixed-arrow classification. They close C before the finite-carrier restriction and normalization work in D."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowConsequences.lean
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_faithful
  risks:
    - "assuming default preservation instead of deriving it from infinity and semantic exactness"
    - "reversing the Atom transport in the extraction evaluation equation"
    - "restricting D0 faithfulness to infinite carriers"
    - "proving representative equality without reconnecting it to the quotient relation"
  unchecked:
    - "D--E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Identified default preservation with equality of the canonical continuous extensions at infinity. Derived transported pointwise evaluation equality from semantic extraction exactness, then used infinite-carrier raw evaluation injectivity to recover default preservation without a support premise. Reduced typed-presentation and D0 quotient representability to finite actual support alone. Proved D0 faithful for arbitrary carriers by an explicit public bridge from realization-map equality of representatives to the defining quotient relation."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowConsequences.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.normalizedExtractionCode_defaultValue_eq_iff_apply_infty_eq
    - AAT.AG.FiniteDecoderRepresentability.normalizedExtractionCode_evaluationEq_transport
    - AAT.AG.FiniteDecoderRepresentability.normalizedExtractionCode_defaultValue_eq_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.exists_fixedPresentation_decode_iff_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.cartPresentationSetoid_rel_of_realization_map_eq
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_map_injective
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_faithful
  claim_mapping:
    theorem_names:
      - normalizedExtractionCode_defaultValue_eq_iff_apply_infty_eq
      - normalizedExtractionCode_defaultValue_eq_of_infinite
      - exists_fixedPresentation_decode_iff_of_infinite
      - exists_finiteCodeCartHom_map_iff_of_infinite
      - finiteCodeCartRealization_faithful
    source_labels:
      - "fixed target C: default preservation is equality at infinity"
      - "fixed target C: on an infinite Atom carrier semantic exactness supplies the default equation"
      - "fixed target C: representability iff finite actual support on an infinite carrier"
      - "fixed target C: D0 is faithful on every carrier"
    undischarged_assumptions: []
    acceptance_point: "Infinity is used only to recover equality of raw finite-exception codes from their actual evaluations. Faithfulness is proved from the existing decoded-equality quotient and does not use carrier finiteness."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C default condition as equality at infinity"
      - "C infinite-carrier reduction to finite support alone"
      - "C D0 faithfulness from the decoded-equality quotient"
    remaining:
      - "all D--E obligations"
  certificate_provenance:
    discharged:
      - "semantic extraction_iff supplies evaluation equality at every actual Atom"
      - "Infinite.exists_notMem_finset, through the Cycle 3 theorem, recovers raw-code and default equality"
      - "the quotient's defining relation is equality of decoded semantic arrows"
    unresolved: []
  proof_use:
    used:
      - "the semantic Atom equivalence transports source evaluation to target evaluation"
      - "the infinite-carrier raw evaluation injectivity theorem supplies default preservation"
      - "Cycle 10 fixed-arrow iff removes the now-automatic default conjunct"
      - "map equality is used exactly as the quotient relation in faithfulness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowConsequences.lean"
    - "namespace #assert_standard_axioms_only: 8 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D: finite-carrier false-default full subcategory, full faithfulness of its restricted decoder, normalization functor, realization natural isomorphism, and finite-carrier non-fullness witness outside the restriction"
```

### Cycle 11 acceptance spine

For each semantic arrow and normalized source, extraction exactness gives pointwise equality
between the target table and the source table transported by the actual Atom permutation.  On
an infinite carrier, Cycle 3 evaluation injectivity upgrades this to raw-code equality, whose
default component is the condition used by Cycle 10.  Thus both typed-presentation and quotient
representability reduce exactly to finite actual support.  Separately, `FiniteCodeCartHom` is
already quotiented by decoded semantic equality, so equality after `D0.map` is precisely the
quotient relation and yields faithfulness without an infinity assumption.

## Cycle 12: finite-carrier full subcategory and restricted decoder

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 12
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 25126f9a34de2b4df2fd6b349354622239e05074
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 11: all C obligations discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization_faithful
    - CategoryTheory.ObjectProperty.FullSubcategory
  proof_obligation: "D1: define the full subcategory on codes whose normalized extraction defaults are false, restrict D0 to it, and prove the restricted decoder full and faithful for finite Atom carriers"
  selection_reason: "The object restriction is the domain of D's normalization functor. Cycle 10 supplies fullness once finite carrier support and endpoint default equality are discharged; Cycle 11 supplies faithfulness."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteFullSubcategory.lean
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization_full
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization_faithful
  risks:
    - "restricting every extraction table instead of only normalized positions"
    - "adding a morphism-side preservation certificate instead of taking a full subcategory"
    - "assuming finite support rather than deriving it from carrier finiteness"
    - "claiming fullness outside the finite-carrier branch"
  unchecked:
    - "D normalization functor, realization natural isomorphism, and Fin 1 counterexample"
    - "E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Defined the exact normalized false-default ObjectProperty and its ordinary full subcategory. Restricted D0 by the standard inclusion. Proved faithfulness from Cycle 11's decoder injectivity for every carrier. Under Finite U.Atom, proved fullness by deriving finite actual support from carrier finiteness and the default equation from the two endpoint object properties, then applying Cycle 10's exact fixed-arrow iff."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteFullSubcategory.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeProperty
    - AAT.AG.FiniteDecoderRepresentability.FalseDefaultFiniteCodeCategory
    - AAT.AG.FiniteDecoderRepresentability.singletonConstantDefaultCode
    - AAT.AG.FiniteDecoderRepresentability.singletonConstantDefaultCode_normalized_defaultValue
    - AAT.AG.FiniteDecoderRepresentability.singletonConstantFalseCode_mem
    - AAT.AG.FiniteDecoderRepresentability.singletonConstantTrueCode_not_mem
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization_obj
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization_map
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization_faithful
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization_full
  claim_mapping:
    theorem_names:
      - falseDefaultFiniteCodeProperty
      - falseDefaultFiniteCodeRealization_faithful
      - falseDefaultFiniteCodeRealization_full
    source_labels:
      - "fixed target D: P0^0 has false defaults at normalized extraction positions"
      - "fixed target D: restricted decoder D0^0 is fully faithful on finite Atom carriers"
    conjuncts:
      - "the subcategory is full and carries no morphism-side condition"
      - "unnormalized extraction-table positions remain unrestricted"
      - "faithfulness holds for every carrier"
      - "fullness derives actual permutation support finiteness from Finite U.Atom"
      - "fullness derives the normalized default equation from endpoint membership"
    undischarged_assumptions: []
    acceptance_point: "The only new direction hypothesis for fullness is the fixed target's finite-carrier branch. No support Finset, presentation, morphism-side certificate, or unnormalized-table condition is accepted."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D false-default full subcategory"
      - "D restricted decoder full and faithful for finite carriers"
    remaining:
      - "D normalization functor, realization natural isomorphism, and Fin 1 counterexample"
      - "all E obligations"
  certificate_provenance:
    discharged:
      - "ObjectProperty.FullSubcategory supplies exactly all existing code morphisms"
      - "Set.toFinite supplies support finiteness from the finite carrier instance"
      - "source.property and target.property supply both sides of the default equation"
      - "Cycle 10 constructs the quotient morphism preimage"
    unresolved: []
  proof_use:
    used:
      - "endpoint membership is used at the normalized source and its actual source-map image"
      - "carrier finiteness is used to make the actual moved-point Set finite"
      - "Cycle 11 map injectivity removes the full-subcategory wrapper in faithfulness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/FiniteFullSubcategory.lean"
    - "namespace #assert_standard_axioms_only: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D2: replace every extraction table by finitePredicateCode of its evaluation with false default, retain Source/normalize/point, lift presentations and quotient morphisms functorially, and build D0^0 composed with R_fin naturally isomorphic to D0"
```

### Cycle 12 acceptance spine

The object predicate reads only `extraction (normalize input)`.  Because the associated
subcategory is the standard full subcategory, its homs carry no new preservation field.
Faithfulness is inherited by equality reflection through the underlying `D0` quotient.
For fullness on a finite carrier, every actual permutation support is finite, while both
normalized endpoint defaults reduce to `false`; Cycle 10 then constructs the exact underlying
quotient arrow, which the full-subcategory hom wrapper retains unchanged.

## Cycle 13: finite code normalization functor

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 13
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 6f6cd96637c0113bfb0a4ffc1ef60ba1182f46b9
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 12: D false-default full subcategory and restricted decoder discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.finitePredicateCode
    - AAT.AG.FiniteDecoderRepresentability.atomPredicateCode_eq_of_defaultValue_eq_of_eval_eq
    - AAT.AG.FiniteDecoderRepresentability.FalseDefaultFiniteCodeCategory
    - AAT.AG.DoctrineFiberProduct.compPresentation
  proof_obligation: "D2a: replace every extraction table by the canonical same-evaluation false-default table; retain Source, normalize, point, source map, and Atom table; lift the construction through presentation quotients to a functor R_fin from P0 to P0^0"
  selection_reason: "Cycle 12 fixed the target full subcategory. The object and morphism normalization must now be constructed before comparing its semantic realization with D0."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteCodeNormalization.lean
    - AAT.AG.FiniteDecoderRepresentability.normalizeCartPresentation
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteCodeCartHom
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeNormalizationFunctor
  risks:
    - "changing semantic evaluations while changing raw defaults"
    - "changing Source, normalize, point, source map, or Atom permutation"
    - "accepting raw extraction equality for normalized codes instead of reconstructing it"
    - "mapping a chosen quotient representative without proving independence"
    - "omitting identity or composition laws"
  unchecked:
    - "D realization natural isomorphism and Fin 1 counterexample"
    - "E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed canonical false-default table normalization with identical evaluation; lifted it pointwise to doctrine and pointed-instance codes while retaining source cardinality, normalize, and point; rebuilt each normalized presentation's raw extraction equality from equal false defaults and the original presentation's evaluation equality; proved decoded-equality relation preservation; mapped quotient morphisms independently of representatives; and proved identity and composition laws for R_fin."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteCodeNormalization.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.normalizeAtomPredicateCode
    - AAT.AG.FiniteDecoderRepresentability.normalizeAtomPredicateCode_eval
    - AAT.AG.FiniteDecoderRepresentability.normalizeAtomPredicateCode_defaultValue
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode_sourceCard
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode_normalize
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode_extraction
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode_extraction_defaultValue
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode_extraction_eval
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode_doctrine
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode_sourceCard
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode_normalize
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode_point
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode_falseDefault
    - AAT.AG.FiniteDecoderRepresentability.normalizeCartPresentation
    - AAT.AG.FiniteDecoderRepresentability.normalizeCartPresentation_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.normalizeCartPresentation_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.normalizeCartPresentation_rel
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteCodeCartHom
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteCodeCartHom_ofPresentation
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeNormalizationFunctor
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeNormalizationFunctor_obj_obj
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeNormalizationFunctor_map_hom
  claim_mapping:
    theorem_names:
      - normalizeAtomPredicateCode_eval
      - normalizeFiniteInstanceCode_falseDefault
      - normalizeCartPresentation
      - normalizeCartPresentation_rel
      - finiteCodeNormalizationFunctor
    source_labels:
      - "fixed target D: replace each table by false and the set of true evaluations"
      - "fixed target D: retain Source, normalize, point, source map, and decoded Atom permutation"
      - "fixed target D: prove typed-presentation laws, representative independence, identity, and composition"
    conjuncts:
      - "each normalized raw table is finitePredicateCode of the original evaluation with false default"
      - "the object lands in the exact normalized false-default full subcategory"
      - "presentation extraction equality is reconstructed from the original law"
      - "quotient mapping respects decoded equality"
      - "identity and composition are proved as quotient equalities"
    undischarged_assumptions: []
    acceptance_point: "Finite U.Atom and the evaluator's DecidableEq are the fixed finite branch. No normalized table, presentation law, quotient representative, identity law, or composition law is supplied by callers."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D finite code normalization on objects"
      - "D normalized typed presentations"
      - "D representative-independent quotient morphism action"
      - "D normalization functor identity and composition laws"
    remaining:
      - "D realization natural isomorphism and Fin 1 counterexample"
      - "all E obligations"
  certificate_provenance:
    discharged:
      - "finitePredicateCode internally enumerates the finite carrier"
      - "original presentation extraction_eq supplies transported evaluation equality"
      - "decoded component equality proves quotient representative independence"
      - "quotient soundness plus retained components proves functor laws"
    unresolved: []
  proof_use:
    used:
      - "Finite U.Atom constructs each canonical false-default exception Finset"
      - "original raw extraction equality is evaluated at every Atom"
      - "source-map and Atom-equivalence components are used to preserve the quotient relation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/FiniteCodeNormalization.lean"
    - "namespace #assert_standard_axioms_only: 25 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D2b: construct the identity-source-map, identity-Atom natural isomorphism between D0^0 composed with R_fin and D0, with explicit component and naturality computations"
```

### Cycle 13 acceptance spine

`normalizeAtomPredicateCode` is exactly `finitePredicateCode code.eval false`, so it changes
authored raw structure while preserving evaluation.  The lifted doctrine and instance code keep
the source cardinality, normalization table, and selected point definitionally.  On a typed
presentation, equal false defaults plus the evaluation of its original raw extraction equality
reconstruct the new raw equality.  Source-map and Atom-table retention then proves that decoded
equality is preserved between representatives.  Quotient mapping is therefore well defined, and
the identity and composition laws follow from equality of the retained decoded components.

## Cycle 14: semantic realization natural isomorphism

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 14
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: e48dd46b80e976139eee36aaf779c7dd4a7239d0
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 13: finite normalization functor R_fin constructed"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteDoctrineCode_extraction_eval
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeNormalizationFunctor
    - AAT.AG.FiniteDecoderRepresentability.falseDefaultFiniteCodeRealization
    - AAT.AG.FiniteDecoderRepresentability.finiteCodeCartRealization
  proof_obligation: "D2b: build the identity-source-map, identity-Atom semantic isomorphism between each normalized code and its original decoding; prove naturality; assemble D0^0 composed with R_fin naturally isomorphic to D0"
  selection_reason: "Cycle 13 changes raw defaults while preserving all semantic evaluations. The fixed target requires that distinction to be witnessed by a natural semantic isomorphism rather than raw code equality."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteNormalizationRealizationIso.lean
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIsoApp
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso_naturality
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso
  risks:
    - "claiming raw finite-code equality from evaluation equality"
    - "accepting extraction equivalence or naturality as caller-supplied certificates"
    - "using non-identity source or Atom components"
    - "proving objectwise isomorphism without naturality"
  unchecked:
    - "D Fin 1 counterexample"
    - "E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved a decoded extraction equivalence between every normalized pointed code and its original. Constructed forward and reverse semantic arrows with identity source map and identity Atom equivalence, proved their inverse laws, exposed component APIs, proved naturality for every quotient morphism by representative induction and both decoded components, and assembled the required natural isomorphism."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteNormalizationRealizationIso.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode_toSemantic_extracts_iff
    - AAT.AG.FiniteDecoderRepresentability.normalizedToOriginalHom
    - AAT.AG.FiniteDecoderRepresentability.originalToNormalizedHom
    - AAT.AG.FiniteDecoderRepresentability.normalizedToOriginalHom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.normalizedToOriginalHom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.originalToNormalizedHom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.originalToNormalizedHom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIsoApp
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIsoApp_hom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIsoApp_hom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIsoApp_inv_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIsoApp_inv_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso_naturality
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso_hom_app
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso_inv_app
  claim_mapping:
    theorem_names:
      - normalizeFiniteInstanceCode_toSemantic_extracts_iff
      - finiteNormalizationRealizationIsoApp
      - finiteNormalizationRealizationIso_naturality
      - finiteNormalizationRealizationIso
    source_labels:
      - "fixed target D: normalized and original codes decode to the same extraction predicate"
      - "fixed target D: semantic comparison components have identity source map and Atom permutation"
      - "fixed target D: D0^0 composed with R_fin is naturally isomorphic to D0"
    conjuncts:
      - "forward and reverse exact pointed morphisms are constructed"
      - "both inverse laws are proved"
      - "naturality holds for every quotient morphism"
      - "raw code equality is not asserted"
    undischarged_assumptions: []
    acceptance_point: "Finite U.Atom and DecidableEq are inherited from R_fin. Extraction equivalence, inverse laws, and naturality are derived; no semantic isomorphism or square is accepted from callers."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D realization component isomorphisms"
      - "D realization comparison naturality"
      - "D natural isomorphism D0^0 composed with R_fin isomorphic to D0"
    remaining:
      - "D Fin 1 counterexample"
      - "all E obligations"
  certificate_provenance:
    discharged:
      - "Cycle 13 evaluation preservation derives extraction equivalence"
      - "identity computational maps generate both semantic arrows"
      - "category extensionality proves inverse laws"
      - "quotient representative induction and retained components prove naturality"
    unresolved: []
  proof_use:
    used:
      - "normalized extraction evaluation equality is used in both arrow directions"
      - "source-map equality and Atom-equivalence equality are both used in naturality"
      - "forward and reverse arrows are both used in the Iso constructor"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/FiniteNormalizationRealizationIso.lean"
    - "namespace #assert_standard_axioms_only: 16 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D3: instantiate the specified Fin 1 true-default and false-default codes, prove equal evaluations and semantic isomorphism, identify R_fin(P_t) with P_f at raw code level, and refute morphisms in both original-code directions by the Cycle 10 default criterion"
```

### Cycle 14 acceptance spine

The public decoded bridge says exactly that the normalized and original doctrines extract the
same Atoms.  It fills both directions of an exact pointed isomorphism whose source map and Atom
equivalence are identities.  The inverse laws therefore follow from equality of the two
computational components.  For an arbitrary quotient morphism, representative induction and
Cycle 13's retained source/Atom components prove the naturality square.  Raw codes remain
distinct in general; only their semantic realizations are naturally isomorphic.

## Cycle 15: fixed `Fin 1` raw-code counterexample

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 15
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 8c0ab09d93f5443d9f27f504c12e6c8b85ce0b4f
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 14: semantic realization natural isomorphism constructed"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.fixedPresentation_necessary
    - AAT.AG.FiniteDecoderRepresentability.normalizeFiniteInstanceCode
    - AAT.AG.FiniteDecoderRepresentability.finiteNormalizationRealizationIso
  proof_obligation: "D3: instantiate the specified Fin 1 true-default and false-default codes, prove equal evaluations and semantic isomorphism, identify R_fin(P_t) with P_f as raw code, and refute original-code morphisms in both directions"
  selection_reason: "This is D's final fixed witness and separates semantic isomorphism after decoding from isomorphism in the authored finite-code category."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FinOneCounterexample.lean
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueFalseSemanticIso
    - AAT.AG.FiniteDecoderRepresentability.normalize_finOneTrueCode_eq
    - AAT.AG.FiniteDecoderRepresentability.not_nonempty_finOneTrueFalseCodeIso
  risks:
    - "using evaluation equality as raw code equality"
    - "changing either source map or Atom permutation in the semantic isomorphism"
    - "showing only one direction of original-code nonexistence"
    - "asserting non-isomorphism without connecting it to the actual P0 category"
  unchecked:
    - "E"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the exact one-Atom carrier and the two specified singleton-source codes; proved both tables evaluate true; built inverse semantic arrows with identity source and Atom components; proved normalization of the true-default raw code is exactly the false-default code; used the fixed-presentation default necessity in each direction to refute both original-code hom types; and derived absence of a P0 isomorphism."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FinOneCounterexample.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.finOneCarrier
    - AAT.AG.FiniteDecoderRepresentability.finOneAtom
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueTable
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseTable
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueTable_eval
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseTable_eval
    - AAT.AG.FiniteDecoderRepresentability.finOneTable_evaluation_eq
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueCode
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseCode
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueCode_sourceCard
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseCode_sourceCard
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueCode_normalize
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseCode_normalize
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueCode_extraction
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseCode_extraction
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueCode_point
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseCode_point
    - AAT.AG.FiniteDecoderRepresentability.finOneCode_extracts_iff
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueToFalseSemanticHom
    - AAT.AG.FiniteDecoderRepresentability.finOneFalseToTrueSemanticHom
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueFalseSemanticIso
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueFalseSemanticIso_hom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueFalseSemanticIso_hom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueFalseSemanticIso_inv_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.finOneTrueFalseSemanticIso_inv_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.normalize_finOneTrueTable_eq
    - AAT.AG.FiniteDecoderRepresentability.normalize_finOneTrueCode_eq
    - AAT.AG.FiniteDecoderRepresentability.not_nonempty_finOneTrueToFalseCodeHom
    - AAT.AG.FiniteDecoderRepresentability.not_nonempty_finOneFalseToTrueCodeHom
    - AAT.AG.FiniteDecoderRepresentability.not_nonempty_finOneTrueFalseCodeIso
  claim_mapping:
    theorem_names:
      - finOneTable_evaluation_eq
      - finOneTrueFalseSemanticIso
      - normalize_finOneTrueCode_eq
      - not_nonempty_finOneTrueToFalseCodeHom
      - not_nonempty_finOneFalseToTrueCodeHom
      - not_nonempty_finOneTrueFalseCodeIso
    source_labels:
      - "fixed target D: D equals Fin 1; sourceCard one; normalize identity; point unique"
      - "fixed target D: P_t has true empty and P_f has false singleton at every source"
      - "fixed target D: equal evaluation and identity-component semantic isomorphism"
      - "fixed target D: R_fin(P_t) equals P_f as raw code"
      - "fixed target D: neither original P0 hom direction exists, hence no P0 isomorphism"
    conjuncts:
      - "both raw tables evaluate true on the unique Atom"
      - "semantic hom and inverse use identity source map and identity Atom equivalence"
      - "the normalization equality is a structure equality, not merely semantic equivalence"
      - "default mismatch contradicts the necessary fixed-presentation criterion in both directions"
      - "the semantic isomorphism cannot be replaced by an isomorphism in FiniteCodeCartCategory"
    undischarged_assumptions: []
    acceptance_point: "All carrier, source, table, point, and arrow data are the fixed concrete example. Equality, inverse laws, and both nonexistence results are derived; no witness or contradiction is accepted from callers."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D fixed Fin 1 table evaluation"
      - "D fixed semantic isomorphism with identity components"
      - "D raw normalization equality"
      - "D original-code nonexistence in both directions and non-isomorphism"
    remaining:
      - "all E obligations"
  certificate_provenance:
    discharged:
      - "Fin 1 subsingleton gives the complete table evaluation"
      - "decoded extraction equality constructs both semantic arrows"
      - "finite table extensionality proves the raw normalization equality"
      - "Cycle 10 default necessity yields both contradictions"
    unresolved: []
  proof_use:
    used:
      - "the unique Atom is evaluated in the exceptional false-default table"
      - "identity source and Atom components are used in both inverse laws"
      - "the authored defaults are evaluated at the unique normalized source in each nonexistence proof"
      - "the forward nonexistence theorem consumes the hom of any alleged P0 isomorphism"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake build ResearchLean.AG.FiniteDecoderRepresentability.FiniteNormalizationRealizationIso"
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/FinOneCounterexample.lean"
    - "namespace #assert_standard_axioms_only: 32 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "E1: construct the fixed Nat carrier and all-true singleton-source code, the adjacent-pair swap semantic automorphism, prove every Atom moves, and refute a fixed-endpoint P0 presentation via the finite-support criterion"
```

### Cycle 15 acceptance spine

The two authored tables are structurally different but evaluate to the same constant-true
predicate on `Fin 1`.  That equality supplies inverse decoded arrows with identity computational
components, while finite normalization converts the true-default table to the explicit
false-default singleton exception table and hence identifies the full pointed raw codes.  In the
original code category, Cycle 10's necessary default equality would force `false = true` in one
direction and `true = false` in the other.  Thus the semantic isomorphism exists exactly where
claimed and cannot be promoted to an isomorphism between the original authored codes.

## Cycle 16: fixed infinite-support adjacent-swap automorphism

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 16
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 1186ec9a41071a4f290152d94b0e59e6213513cc
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 15: all D obligations discharged"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.exists_finiteCodeCartHom_map_iff_of_infinite
    - AAT.AG.FiniteDecoderRepresentability.onePointAtomPerm
    - AAT.AG.DoctrineFiberProduct.FiniteInstanceCode.toSemantic
  proof_obligation: "E1: construct the fixed Nat carrier and all-true singleton-source code, adjacent-pair semantic automorphism, all-point movement, fixed-endpoint decoding nonexistence, decoder non-fullness, and one-point lift"
  selection_reason: "The fixed infinite-support witness is the common predecessor for E's anchored coverage contrast and its subset-indexed uncountability strengthening."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatAdjacentSwap.lean
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso
    - AAT.AG.FiniteDecoderRepresentability.not_exists_natSwapCodeHom
    - AAT.AG.FiniteDecoderRepresentability.natSwap_finiteCodeCartRealization_not_full
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapOnePointHomeomorph
  risks:
    - "claiming the fixed endomorphism type is empty even though the identity arrow exists"
    - "replacing the literal code endpoint to manufacture a presentation"
    - "supplying an infinite-support certificate or semantic exactness witness as input"
    - "stating non-fullness without connecting it to an actual target hom"
    - "requiring finite support for the one-point homeomorphism"
  unchecked:
    - "E anchored coverage witness"
    - "E subset-indexed automorphisms, injectivity, and uncountability"
    - "E arbitrary countable decoder non-surjectivity and countable syntax specialization"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the literal Nat carrier, singleton-source identity-normalized all-true code P_*, and X_*=D0(P_*); defined the adjacent swap by XOR with one and proved its even/odd equations and that every Atom moves; built an identity-source semantic involution and Iso; identified its actual support with the whole carrier; used C's infinite-carrier decoder-image iff to refute exactly the existence of a code hom mapping to u_sigma.hom; derived failure of Full for D0; and instantiated A's unrestricted one-point homeomorphism with its infinity and Atom computations."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatAdjacentSwap.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.natSwapCarrier
    - AAT.AG.FiniteDecoderRepresentability.natSwapTrueTable
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode
    - AAT.AG.FiniteDecoderRepresentability.natSwapSemanticObject
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_sourceCard
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_normalize
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_extraction
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_point
    - AAT.AG.FiniteDecoderRepresentability.natSwapTrueTable_eval
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapNat
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_apply
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_even
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_odd
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_ne
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_extracts
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_extracts_iff
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticHom
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso_hom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso_hom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso_inv_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso_inv_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_support_eq_univ
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_support_infinite
    - AAT.AG.FiniteDecoderRepresentability.not_exists_natSwapCodeHom
    - AAT.AG.FiniteDecoderRepresentability.natSwap_finiteCodeCartRealization_not_full
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapOnePointHomeomorph
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapOnePointHomeomorph_infty
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapOnePointHomeomorph_coe
  claim_mapping:
    theorem_names:
      - natAdjacentSwap_even
      - natAdjacentSwap_odd
      - natAdjacentSwap_ne
      - natAdjacentSwapSemanticIso
      - natAdjacentSwap_support_infinite
      - not_exists_natSwapCodeHom
      - natSwap_finiteCodeCartRealization_not_full
      - natAdjacentSwapOnePointHomeomorph
    source_labels:
      - "fixed target E: D is Nat; sourceCard one; normalize identity; point unique; all tables true empty"
      - "fixed target E: sigma swaps 2n with 2n+1"
      - "fixed target E: identity source map produces u_sigma and every Atom moves"
      - "fixed target E: no P_* to P_* arrow decodes u_sigma.hom, so D0 is not full"
      - "fixed target E: sigma-plus is a homeomorphism by A's transport"
    conjuncts:
      - "the exact fixed code and semantic object are constructed"
      - "both adjacent-swap evaluation equations and involutivity are proved"
      - "actual support equals univ and is infinite"
      - "nonexistence concerns only a preimage of the specified semantic hom at literal endpoints"
      - "Full.map_surjective at the witness contradicts fixed-endpoint non-representability"
      - "the one-point extension fixes infinity and restricts to sigma on Atoms"
    undischarged_assumptions: []
    acceptance_point: "Nat infinitude and discrete topology are canonical instances for the fixed carrier. The permutation, semantic laws, support, nonexistence witness, and homeomorphism are all constructed internally."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "E fixed Nat code and semantic object"
      - "E adjacent-pair semantic automorphism and all-point movement"
      - "E fixed-endpoint non-representability"
      - "E D0 non-fullness"
      - "E one-point homeomorphism"
    remaining:
      - "E anchored coverage witness and square"
      - "E arbitrary-subset automorphism family and injectivity"
      - "E uncountability and arbitrary countable decoder non-surjectivity"
      - "E countable syntax specialization"
  certificate_provenance:
    discharged:
      - "XOR involutivity constructs the permutation inverse laws"
      - "the all-true table derives semantic extraction exactness"
      - "pointwise movement identifies support with univ"
      - "Cycle 11's infinite-carrier classification supplies the exact image obstruction"
      - "Cycle 5's arbitrary-permutation lift supplies the one-point homeomorphism"
    unresolved: []
  proof_use:
    used:
      - "the general XOR computation proves the even and odd target equations and all-point movement"
      - "XOR involutivity proves both permutation and semantic Iso inverse laws"
      - "all-point movement is used to prove infinite actual support"
      - "infinite support refutes the exact decoder-preimage existential"
      - "the semantic witness is passed to Full.map_surjective"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake build ResearchLean.AG.FiniteDecoderRepresentability.FinOneCounterexample"
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/NatAdjacentSwap.lean"
    - "namespace #assert_standard_axioms_only: 32 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "E2: construct AnchoredCoverageWitness for u_sigma.hom with identity source anchor, u_sigma target anchor, idTypedPresentation P_*, and evaluate the square"
```

### Cycle 16 acceptance spine

The fixed code has one source, identity normalization, and the constant-true raw table.  XOR with
one is an involution satisfying the two required adjacent-pair equations and moves every natural
number.  The resulting identity-source semantic automorphism therefore has actual support equal
to the infinite whole carrier.  Cycle 11's fixed-endpoint classification rules out precisely a
code arrow mapping to this hom; it does not erase the existing identity endomorphism.  Applying
that counterexample to `Full.map_surjective` proves the decoder is not full.  Independently, the
same unrestricted permutation extends through Cycle 5 to a homeomorphism of the one-point
compactification, fixing infinity and acting by the adjacent swap on every embedded Atom.

## Cycle 17: anchored coverage of the non-representable arrow

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 17
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: e5d560d4d29b4a41a3b6047e5cedcd8ed5d9ff8a
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 16: fixed-endpoint adjacent-swap non-representability proved"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapSemanticIso
    - AAT.AG.FiniteDecoderRepresentability.not_exists_natSwapCodeHom
    - AAT.AG.FiniteDecoderRepresentability.typedPresentationToSemantic_id
    - AAT.AG.DoctrineFiberProduct.AnchoredCoverageWitness
  proof_obligation: "E2: construct anchored coverage of u_sigma.hom with identity source anchor, u_sigma target anchor, idTypedPresentation P_*, and evaluate the commutative square"
  selection_reason: "The fixed target requires the same arrow to witness both literal-endpoint non-representability and coverage after endpoint isomorphisms; this cycle constructs the second side without altering Cycle 16's first side."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatSwapAnchoredCoverage.lean
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_square
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_covered_and_not_fixed_representable
  risks:
    - "using a non-identity presentation that already contains the infinite permutation"
    - "changing the source anchor away from identity"
    - "using an endpoint isomorphism unrelated to u_sigma"
    - "stating coverage without proving the arrow-category square"
    - "letting coverage erase the literal-endpoint non-representability conclusion"
  unchecked:
    - "E subset-indexed automorphisms, injectivity, and uncountability"
    - "E arbitrary countable decoder non-surjectivity and countable syntax specialization"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Bundled u_sigma.hom as the semantic input; constructed its source anchor from P_* and the identity Iso, its target anchor from the same P_* and u_sigma, and its arrow witness from idTypedPresentation P_*; proved the square by the decoded identity theorem; exposed the exact anchor, presentation, and endpoint-Iso computations; and combined coverage with Cycle 16's fixed-endpoint decoder-preimage nonexistence for the identical semantic arrow."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatSwapAnchoredCoverage.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapInput
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapInput_source
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapInput_target
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapInput_hom
    - AAT.AG.FiniteDecoderRepresentability.natSwapIdentityAnchor
    - AAT.AG.FiniteDecoderRepresentability.natSwapIdentityAnchor_code
    - AAT.AG.FiniteDecoderRepresentability.natSwapIdentityAnchor_iso
    - AAT.AG.FiniteDecoderRepresentability.natSwapAdjacentAnchor
    - AAT.AG.FiniteDecoderRepresentability.natSwapAdjacentAnchor_code
    - AAT.AG.FiniteDecoderRepresentability.natSwapAdjacentAnchor_iso
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_sourceAnchor
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_targetAnchor
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_presentation
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_sourceIso
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_targetIso
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwapAnchoredCoverage_square
    - AAT.AG.FiniteDecoderRepresentability.natAdjacentSwap_covered_and_not_fixed_representable
  claim_mapping:
    theorem_names:
      - natAdjacentSwapAnchoredCoverage
      - natAdjacentSwapAnchoredCoverage_presentation
      - natAdjacentSwapAnchoredCoverage_sourceIso
      - natAdjacentSwapAnchoredCoverage_targetIso
      - natAdjacentSwapAnchoredCoverage_square
      - natAdjacentSwap_covered_and_not_fixed_representable
    source_labels:
      - "fixed target E: source endpoint isomorphism is identity"
      - "fixed target E: target endpoint isomorphism is u_sigma"
      - "fixed target E: representing arrow is idTypedPresentation P_*"
      - "fixed target E: evaluate the commutative square"
      - "fixed target E: show endpoint-isomorphic coverage alongside fixed-code nonexistence"
    conjuncts:
      - "both anchors use the literal code P_*"
      - "the source Iso is identity and the target Iso is the constructed adjacent-swap automorphism"
      - "the typed presentation is definitionally the authored identity presentation"
      - "the square reduces through D0's identity law"
      - "the combined theorem retains the no-preimage conclusion for u_sigma.hom"
    undischarged_assumptions: []
    acceptance_point: "All anchors, endpoint isomorphisms, the presentation, and the square are constructed internally from the fixed Cycle 16 data. No coverage witness or commuting equation is accepted from callers."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "E anchored coverage witness"
      - "E exact source and target anchors"
      - "E identity presentation"
      - "E commutative square and coverage/non-representability contrast"
    remaining:
      - "E arbitrary-subset automorphism family and injectivity"
      - "E uncountability and arbitrary countable decoder non-surjectivity"
      - "E countable syntax specialization"
  certificate_provenance:
    discharged:
      - "Cycle 16 supplies the actual semantic automorphism and no-preimage theorem"
      - "Iso.refl constructs the source anchor"
      - "u_sigma itself constructs the target anchor"
      - "the existing authored identity presentation supplies the displayed arrow"
      - "D0's proved identity computation supplies the square"
    unresolved: []
  proof_use:
    used:
      - "u_sigma.hom is both the semantic input arrow and target anchor hom"
      - "typedPresentationToSemantic_id reduces the displayed identity arrow"
      - "not_exists_natSwapCodeHom supplies the other conjunct of the final contrast"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake build ResearchLean.AG.FiniteDecoderRepresentability.NatAdjacentSwap"
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/NatSwapAnchoredCoverage.lean"
    - "namespace #assert_standard_axioms_only: 18 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "E3: for every S subset Nat construct the pairwise swap sigma_S and identity-source semantic automorphism u_S, then prove S maps to u_S injectively from the even-input evaluation iff"
```

### Cycle 17 acceptance spine

The source and target anchors both retain the literal code `P_*`; only their semantic endpoint
isomorphisms differ.  The source uses identity, the target uses the already constructed `u_σ`,
and the displayed code arrow is the authored identity presentation.  Its decoded arrow is
identity, so the arrow-category square reduces to `id ≫ u_σ.hom = id ≫ u_σ.hom`.  The combined
theorem keeps Cycle 16's exact no-preimage statement for that same hom.  Thus endpoint-isomorphic
coverage and fixed-code non-representability coexist without changing either notion.

## Cycle 18: subset-indexed automorphism injection

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 18
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 9b5a0991b62397c6ebf4542d54d5ad5c80d2e1ed
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 17: anchored coverage contrast proved"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.natSwapCode_extracts
    - AAT.AG.FiniteDecoderRepresentability.natSwapSemanticObject
    - Equiv.natSumNatEquivNat
  proof_obligation: "E3: for every subset S of Nat construct the pairwise swap sigma_S and identity-source semantic automorphism u_S; prove sigma_S(2n)=2n+1 iff n belongs to S; prove S maps to u_S injectively"
  selection_reason: "The subset family is the explicit cardinal lower bound required before the abstract countability contradiction can be stated without assuming an uncountability certificate."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatSubsetSwaps.lean
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap_even_eq_odd_iff
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut_injective
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAutEmbedding
  risks:
    - "accepting decidable membership or a finite subset instead of arbitrary Set Nat"
    - "constructing only functions rather than actual permutations and semantic automorphisms"
    - "assuming subset injectivity as a field or external certificate"
    - "proving distinct permutations without connecting them to distinct semantic Iso values"
  unchecked:
    - "E uncountability of Aut(X_*)"
    - "E arbitrary countable decoder non-surjectivity"
    - "E countable alphabet/finite-list/object-and-hom syntax specialization"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For arbitrary S : Set Nat, constructed an involutive conditional swap on Nat + Nat and conjugated it to the pairwise permutation sigma_S of Nat; proved its even and odd behavior in both membership branches and the exact even-output iff; constructed semantic hom and inverse on the fixed all-true object with identity source maps; assembled u_S as an Iso; extracted equality of Atom equivalences from equality of semantic Isos and used the even-output iff to prove subset injectivity; packaged the result as an embedding of Set Nat into Aut(X_*)."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatSubsetSwaps.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwapFn
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwapFn_inl_of_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwapFn_inl_of_not_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwapFn_inr_of_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwapFn_inr_of_not_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwapFn_involutive
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwap
    - AAT.AG.FiniteDecoderRepresentability.subsetSumSwap_apply
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap_even_of_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap_even_of_not_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap_odd_of_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap_odd_of_not_mem
    - AAT.AG.FiniteDecoderRepresentability.subsetAdjacentSwap_even_eq_odd_iff
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwap_extracts_iff
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwapSemanticHom
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwapSemanticInv
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwapSemanticHom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwapSemanticHom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwapSemanticInv_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSwapSemanticInv_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut_hom_sourceMap
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut_hom_atomEquiv
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut_injective
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAutEmbedding
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAutEmbedding_apply
  claim_mapping:
    theorem_names:
      - subsetSumSwapFn_involutive
      - subsetAdjacentSwap_even_of_mem
      - subsetAdjacentSwap_even_of_not_mem
      - subsetAdjacentSwap_odd_of_mem
      - subsetAdjacentSwap_odd_of_not_mem
      - subsetAdjacentSwap_even_eq_odd_iff
      - natSubsetSemanticAut
      - natSubsetSemanticAut_injective
      - natSubsetSemanticAutEmbedding
    source_labels:
      - "fixed target E: swap only the pair at n when n belongs to S"
      - "fixed target E: sigma_S(2n)=2n+1 iff n belongs to S"
      - "fixed target E: identity source map gives u_S in Aut(X_*)"
      - "fixed target E: S maps to u_S injectively"
    conjuncts:
      - "S ranges over arbitrary Set Nat with classical internal choice only"
      - "the conditional function is proved involutive and promoted to Equiv.Perm"
      - "both elements of each pair are swapped for membership and fixed for nonmembership"
      - "semantic hom and inverse are built from the fixed all-true extraction"
      - "Iso equality implies permutation equality through the public hom Atom component"
      - "the even-input iff recovers pointwise subset membership"
    undischarged_assumptions: []
    acceptance_point: "No decidability, finiteness, permutation table, semantic arrow, or injectivity certificate is supplied by callers. Classical logic is used internally only to branch on membership in an arbitrary subset."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "E arbitrary-subset pair permutations"
      - "E subset-indexed identity-source semantic automorphisms"
      - "E exact membership evaluation"
      - "E injection Set Nat into Aut(X_*)"
    remaining:
      - "E uncountability of Aut(X_*)"
      - "E arbitrary countable decoder non-surjectivity"
      - "E countable syntax specialization"
  certificate_provenance:
    discharged:
      - "conditional summand definition and branch proofs yield involutivity"
      - "conjugation by the even/odd equivalence yields a total Nat permutation"
      - "the fixed all-true decoded API yields semantic exactness"
      - "semantic Iso equality is projected to the actual Atom equivalence"
      - "the proved even-output iff reconstructs subset extensional equality"
    unresolved: []
  proof_use:
    used:
      - "summand involutivity supplies the Equiv.Perm constructor"
      - "membership/nonmembership computations prove the exact evaluation iff"
      - "forward and inverse semantic arrows supply the Iso"
      - "hom Atom-equivalence projection and the evaluation iff prove injection"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake build ResearchLean.AG.FiniteDecoderRepresentability.NatSwapAnchoredCoverage"
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/NatSubsetSwaps.lean"
    - "namespace #assert_standard_axioms_only: 27 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "E4: use the embedding Set Nat into Aut(X_*) and Cantor's theorem to prove Aut(X_*) uncountable, then refute surjectivity of every map from a countable type"
```

### Cycle 18 acceptance spine

An arbitrary subset controls a literal involution of `Nat ⊕ Nat`: membership exchanges the two
summands at that index and nonmembership fixes them.  Conjugating by the even/odd equivalence
gives a permutation of `Nat` with the required pair computations.  The constant-true semantic
object admits that permutation with identity source map, and its actual inverse supplies a
semantic automorphism.  Equality of two such Isos forces equality of their hom Atom
equivalences; evaluating at `2n` then recovers membership in the original subsets.  This proves
the injection into `Aut(X_*)` explicitly, before any cardinality theorem is invoked.

## Cycle 19: uncountability and countable-syntax obstruction

```yaml
ledger_type: target_cycle_result
goal: G-121-aat-finite-decoder-representability
cycle: 19
goal_blob_sha: 6ad52ff6177f3b895b3bed89e399a5afb9821f18
base_oid: 605de9580a10d8c7515526167bd118853f71bc99
tracking_issue: 4458
report_path: research/reports/G-121-aat-finite-decoder-representability.md
selection:
  proof_state_ref: "Issue #4458 Cycle 18: Set Nat embeds into Aut(X_*)"
  proof_dag_predecessors:
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAut_injective
    - AAT.AG.FiniteDecoderRepresentability.natSubsetSemanticAutEmbedding
    - Function.cantor_injective
  proof_obligation: "E4: prove Aut(X_*) uncountable; refute surjectivity for every decoder from a countable type; specialize to finite lists over a countable alphabet and combined countable object-and-pairwise-morphism syntax"
  selection_reason: "Cycle 18 supplied the exact injection needed for Cantor's contradiction, leaving only the fixed cardinal and syntax consequences."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CountableSyntaxObstruction.lean
    - AAT.AG.FiniteDecoderRepresentability.setNat_uncountable
    - AAT.AG.FiniteDecoderRepresentability.natSemanticAut_uncountable
    - AAT.AG.FiniteDecoderRepresentability.countableDecoder_not_surjective
    - AAT.AG.FiniteDecoderRepresentability.finiteListDecoder_not_surjective
    - AAT.AG.FiniteDecoderRepresentability.CountablePresentationSyntax.combinedSyntaxDecoder_not_surjective
  risks:
    - "assuming the target automorphism type uncountable instead of deriving it from the subset family"
    - "proving non-surjectivity only for one selected decoder rather than every map from every countable type"
    - "replacing finite lists by streams or requiring a computable encoding"
    - "dropping source or target indices from the pairwise morphism syntax"
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Derived Uncountable (Set Nat) directly from Countable's injection into Nat and Cantor's no-injection theorem; transported uncountability through the proved subset-indexed semantic automorphism injection; applied the generic countable-to-uncountable no-surjection theorem to every decoder; instantiated it for List Alphabet; bundled countably many object codes with a countable morphism-syntax family for each ordered endpoint pair, proved their sum-of-dependent-sums countable, and refuted every decoder from that combined syntax."
  completion_candidate: yes
  lean_artifacts:
    - research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CountableSyntaxObstruction.lean
  evidence:
    - AAT.AG.FiniteDecoderRepresentability.setNat_uncountable
    - AAT.AG.FiniteDecoderRepresentability.natSemanticAut_uncountable
    - AAT.AG.FiniteDecoderRepresentability.countableDecoder_not_surjective
    - AAT.AG.FiniteDecoderRepresentability.finiteListDecoder_not_surjective
    - AAT.AG.FiniteDecoderRepresentability.CountablePresentationSyntax
    - AAT.AG.FiniteDecoderRepresentability.CountablePresentationSyntax.CombinedSyntax
    - AAT.AG.FiniteDecoderRepresentability.CountablePresentationSyntax.combinedSyntax_countable
    - AAT.AG.FiniteDecoderRepresentability.CountablePresentationSyntax.combinedSyntaxDecoder_not_surjective
  claim_mapping:
    theorem_names:
      - setNat_uncountable
      - natSemanticAut_uncountable
      - countableDecoder_not_surjective
      - finiteListDecoder_not_surjective
      - CountablePresentationSyntax.combinedSyntax_countable
      - CountablePresentationSyntax.combinedSyntaxDecoder_not_surjective
    source_labels:
      - "fixed target E: Aut(X_*) is uncountable"
      - "fixed target E: every decoder T -> Aut(X_*) from a countable T is non-surjective"
      - "fixed target E: finite lists over a countable alphabet"
      - "fixed target E: countably many presentation objects and countable morphism syntax for every pair, combined into one type"
      - "fixed target E: the lower bound assumes countability, not computability"
    conjuncts:
      - "powerset uncountability is proved by Cantor rather than supplied"
      - "the Cycle 18 injection is the actual route from Set Nat to Aut(X_*)"
      - "the generic decoder is an arbitrary function from an arbitrary Countable type"
      - "List supplies precisely finite strings"
      - "CombinedSyntax contains object codes and typed morphism expressions with both endpoint indices"
      - "the presentation bundle carries Countable propositions only and no computational fields"
    undischarged_assumptions: []
    acceptance_point: "The only syntax-side hypothesis is Countable. No Encodable, DecidableEq, computability, faithfulness, selected enumeration, or nonempty-domain assumption is introduced."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "E uncountability of Aut(X_*)"
      - "E arbitrary countable decoder non-surjectivity"
      - "E countable-alphabet finite-list specialization"
      - "E countable presentation-object and pairwise morphism-syntax specialization"
    remaining: []
  certificate_provenance:
    discharged:
      - "Countable's actual injection into Nat and Function.cantor_injective prove Set Nat uncountable"
      - "Cycle 18's proved semantic automorphism injection transports that uncountability"
      - "Mathlib's countable-to-uncountable theorem refutes each actual decoder"
      - "Sum, Sigma, and List countability instances derive the syntax specializations"
    unresolved: []
  proof_use:
    used:
      - "natSubsetSemanticAut_injective is the cardinal lower-bound map"
      - "the arbitrary decode parameter is passed directly to not_surjective_countable_uncountable"
      - "both endpoint indices occur in the nested Sigma syntax"
      - "combinedSyntax_countable is installed for the final presentation decoder theorem"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake build ResearchLean.AG.FiniteDecoderRepresentability.NatSubsetSwaps"
    - "cd research/lean && lake env lean ResearchLean/AG/FiniteDecoderRepresentability/CountableSyntaxObstruction.lean"
    - "namespace #assert_standard_axioms_only: 23 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "terminal fixed-target A--E completion audit"
```

### Cycle 19 acceptance spine

Cantor's theorem first rules out any injection from `Set Nat` to `Nat`; the Cycle 18 injection
then forces the actual automorphism type of `X_*` to be uncountable.  The generic theorem accepts
an arbitrary type-class witness `Countable T` and an arbitrary function from `T`, so it assumes
neither an enumeration nor a computation procedure.  `List Alphabet` gives the finite-string
case.  For presentation syntax, the combined type is the sum of object codes and a nested
dependent sum of morphism expressions indexed by both source and target; its countability is
derived from exactly the object and pairwise-morphism countability fields.

## Terminal completion candidate basis

The completion candidate is the fixed GOAL blob
`6ad52ff6177f3b895b3bed89e399a5afb9821f18` together with the cumulative Cycle 1--19
artifacts.  The terminal review must independently reconstruct the following map rather than
accepting this report as mathematical evidence.

| Fixed clause | Cumulative Lean evidence | Status before terminal review |
| --- | --- | --- |
| A: finite-exception codes and continuous Bool maps | `OnePointCode`, `EvaluationClassification`, `CodeFibers`, `EncoderChoice`, `PermutationTransport` | implemented; terminal review pending |
| B: coverage and compactness equivalences | `CoverageTopology`, `DiscreteCompactness`, `ArrowCoherence` | implemented; terminal review pending |
| C: exact image of displayed arrows | `PermutationCodeClassification`, `FixedArrowClassification`, `FixedArrowConsequences` | implemented; terminal review pending |
| D: finite normalization, fullness, realization iso, and fixed counterexample | `FiniteFullSubcategory`, `FiniteCodeNormalization`, `FiniteNormalizationRealizationIso`, `FinOneCounterexample` | implemented; terminal review pending |
| E: infinite-support obstruction, anchored coverage, subset family, and countable-syntax lower bound | `NatAdjacentSwap`, `NatSwapAnchoredCoverage`, `NatSubsetSwaps`, `CountableSyntaxObstruction` | implemented; terminal review pending |

All 19 modules are imported by `ResearchLean.AG` and listed in `research-modules.txt`.  The
candidate carries no known remaining `discharge-required` premise and no known unchecked central
claim, but those are inputs to the formal four-lane review, not a pre-review completion verdict.
`target-theorem-proved` remains unavailable until the same-head standard review, final packet,
all completion gates, CI, and the fresh whole-target review pass.
