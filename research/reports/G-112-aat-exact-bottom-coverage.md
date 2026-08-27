# G-112-aat-exact-bottom-coverage — exact-bottom coverage と全域分類

- 一次仕様: [`research/goals/G-112-aat-exact-bottom-coverage.md`](../goals/G-112-aat-exact-bottom-coverage.md)
- tracking Issue: [#4184](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4184)
- target theorem: Exact-Bottom Coverage Classification and Global Lift Coherence Theorem
- proof state: `active / F0 accepted / K0 pending`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria は GOAL カードを正本とし、SCORE は
使わない。

## Fixed heads

- fixed GOAL blob SHA: `17cad4df309049633617878373246300c1ad24aa`
- fixed GOAL SHA-256:
  `c7025c26418f88509b959326f61fcc576ddc1f1bc877dd2384833483848ac097`
- base OID: `19a0cb3963373f7e948a3eae16fe80d8d6c55bf6`
- language head:
  `ExactBottomConditionSyntax` / `evalExactBottomCondition` /
  `rebaseExactBottomCondition`
- predicate-term head: `exactBottomFirstCandidate` =
  `sourceFinite ∧ targetFinite`
- candidate sequence: `exactBottomConditionCandidates`。4 atomic condition の
  非空 conjunction class 15項を proof 前に固定し、先頭を fixed head とする。
  `ExactBottomCandidateSelection.initial/next` が prior refutation を保持し、
  `ExactBottomCandidateRefutation` が資格不能または concrete semantic input
  における十分性反例を固定する。候補反証後はこの列の次項だけへ移る。
- anchored witness head: `CoveredObjectWitness` /
  `CoverageWitnessOver` / `AnchoredCoverageWitness`。anchor 相対の qualification
  入力は `SharedAnchorComposablePair` / `SharedBaseAnchorCospan`。
- branch head: `GlobalExactBottomCoverage` /
  `CharacterizedExactBottomCoverage` /
  `ExactBottomCoverageDisjunction`
- qualification head: `ExactBottomConditionQualification`。同型不変性、anchor
  相対 id / comp / pullback 閉性、realization 像包含、raw positive family
  からの発火・strict 像外性・非同型対・非可逆性を同じ selected term に
  dependent に結合する。
- regime head: `ExactBottomCoverageRegime` /
  `exactBottomCoverageRegimeOfDisjunction`。regime は named branch artifact
  だけを保持し、coverage producer の直接供給 constructor を持たない。
- finite placement: carrier Atom、source endpoint Source、target endpoint
  Source は `Finite`。`DecidableEq U.Atom` は finite-code interface にだけ
  置き、条件 evaluator は要求しない。
- universe contract: language、rebase、regime、十分性は universe-polymorphic。
  負枝反例 payload は universe ごとに carrier と arrow を同じ universe に
  居住させる symbolic contract を採用した。endpoint 固定への移行はまだ不要。

## Qualification correspondence

| G-112(b) 資格 | F0 surface | 現在状態 |
| --- | --- | --- |
| (i) 探索前固定 | `ExactBottomCandidateSelection.initial/next` | 型固定・正式査読済み |
| (ii) coverage 非参照 | 5 constructor と evaluator unfolding theorem 群 | transitive audit 通過 |
| (iii) 同型不変性 | `ExactBottomConditionQualification.isomorphic_invariant` | theorem output は未構成 |
| (iv) anchor 相対 id / comp / pullback 閉性 | 同 qualification の4 closure field | theorem output は未構成 |
| (v) 像包含と非空発火 | 同 qualification の image / raw family theorem field | raw data と theorem output は未構成 |

## Review round 1 corrections

PR #4188 初回4 lane は `Major revisions`。数学A/B・Lean Aが共通して挙げた
中心 finding を同時に修正した。

1. 負枝 payload に `ExactBottomConditionQualification` を dependent field として
   結合し、資格 (iii)–(v) のない負枝を構成不能にした。
2. `ExactBottomCandidateSelection` が index と全 prior refutation を保持し、
   資格不能または concrete sufficiency counterexample の後に `next` だけが
   次の事前登録 term へ進む型へ変更した。
3. `ExactBottomCoverageRegime` は `ExactBottomCoverageDisjunction` だけを保持し、
   coverage producer を直接受ける constructor を除去した。

型と def 本体を変更した中心修正なので、修正後は新規4 lane の正式レビューを
再実行した。数学2 lane・Lean 2 lane はすべて `No major findings`。
exact head `2e2e039fd51d1bdd3219457ea3cf6ec330aed3f1` の CI は 7/7 通過した。

## Cycle ledger

### Cycle 1 — F0 type surface

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 1
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: 19a0cb3963373f7e948a3eae16fe80d8d6c55bf6
tracking_issue: 4184
report_path: research/reports/G-112-aat-exact-bottom-coverage.md
selection:
  proof_state_ref: "Issue #4184: active / F0 typing pending"
  proof_dag_predecessors:
    - "G-110 PR #4153 / merge 315a2537"
    - CartSemanticInputIso
    - CartPresentationBetween
    - strongCartesianLiftOfTarget
  proof_obligation: >-
    Fix the F0 language, ordered first predicate term, anchored arrow-category
    witness, two-branch payload, regime producer, finite-instance placement,
    and symbolic universe contract without constructing a coverage branch.
  selection_reason: >-
    F0 is the unique next obligation in Issue #4184 and fixes every type needed
    by K0--K4 before any proof result can influence predicate selection.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean
  risks:
    - endpoint isomorphisms could fail to enforce an arrow-category square
    - the closed language could acquire a callback or realization dependency
    - a coverage theorem could escape into a payload input rather than be produced
    - universe-polymorphic qualification could be weakened to one endpoint
  unchecked:
    - fixed-head standard PR review
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    ExactBottomConditionSyntax has exactly the five fixed constructors;
    evalExactBottomCondition reads only endpoint Source finiteness and extraction
    sets; canonical rebase and the fifteen-entry pre-proof candidate sequence are fixed;
    CoverageWitnessOver requires one CartPresentationBetween and one
    CartSemanticInputIso whose endpoint isomorphisms equal the shared anchors;
    candidate selection records all prior refutations and moves only to the next
    registered index; the negative branch requires all five qualifications for
    that same selected term; each regime contains only the named branch artifact.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean
  evidence:
    - exactBottomConditionCandidates_head
    - rebase_exactBottomFirstCandidate
    - evaluator unfolding theorem group
    - CoverageWitnessOver
    - ExactBottomCandidateSelection.initial
    - ExactBottomCandidateSelection.next
    - ExactBottomConditionQualification
    - FiniteEndpointCoverage
    - ExactBottomCoverageDisjunction
    - exactBottomCoverageRegimeOfDisjunction
  claim_mapping:
    theorem_names:
      - exactBottomConditionCandidates_head
      - rebase_exactBottomFirstCandidate
      - FiniteEndpointCoverage
    source_labels:
      - "target theorem (a) witness shape"
      - "target theorem (b) closed language and fixed head"
      - "target theorem (d) regime surface"
    conjuncts:
      - "F0 typing -> ExactBottomCoverageSchema"
    undischarged_assumptions:
      - first-stage coverage construction
      - second-stage branch decision and all five qualification theorems
      - O7 wrapper and proof-use audit
      - coverage closure producers
      - semantic-global coherence package
    acceptance_point: >-
      This cycle fixes only the pre-proof type surface named by F0; no coverage
      existence, sufficient predicate, counterexample, closure, or coherence
      result is claimed.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "closed language type and evaluator / ExactBottomConditionSyntax"
      - "anchored witness type / CoverageWitnessOver"
      - "branch and regime output types / ExactBottomCoverageDisjunction"
      - "candidate transition provenance / ExactBottomCandidateSelection"
      - "qualification coupling surface / ExactBottomConditionQualification"
    remaining:
      - "first-stage coverage theorem / K0"
      - "second-stage two-branch decision / K1"
      - "O7 fixed theorem and proof-use / K2"
      - "coverage closure / K3"
      - "global lift coherence / K4"
  certificate_provenance:
    discharged:
      - "condition language provenance / fixed GOAL constructor table"
      - "anchor square provenance / CartPresentationBetween plus CartSemanticInputIso"
    unresolved:
      - "coverage witnesses are types only; constructors remain K0/K1 obligations"
  proof_use:
    used:
      - CartSemanticInput
      - CartPresentationBetween
      - CartSemanticInputIso
      - pointedPullbackFst
      - pointedPullbackSnd
    unused:
      - strongCartesianLiftOfTarget
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean / exit 0 / standard axioms only"
    - "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.ExactBottomCoverageSchema / exit 0 / targeted module only"
    - "all reported declarations #print axioms / standard axioms only: propext, Classical.choice, Quot.sound where applicable"
    - "exact head 2e2e039fd51d1bdd3219457ea3cf6ec330aed3f1 / fresh mathematics A-B and Lean A-B review / No major findings"
    - "exact head 2e2e039fd51d1bdd3219457ea3cf6ec330aed3f1 / CI 7 of 7 passed"
  blocking_findings: []
  next_obligation: "K0 first-stage finite-endpoint anchored coverage construction"
```

## Current proof state

F0 の type surface を実装し、focused elaboration、standard-axiom audit、
修正後の新規4 lane 正式レビュー、exact-head CI 7/7 を通過した。F0 は
`target-proof-checkpoint` として受理する。全 completion criteria のうち
K0--K4 と K5 final audit は未完である。
