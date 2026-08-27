# G-112-aat-exact-bottom-coverage — exact-bottom coverage と全域分類

- 一次仕様: [`research/goals/G-112-aat-exact-bottom-coverage.md`](../goals/G-112-aat-exact-bottom-coverage.md)
- tracking Issue: [#4184](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4184)
- target theorem: Exact-Bottom Coverage Classification and Global Lift Coherence Theorem
- proof state: `target-theorem-proved`
- completion candidate: `yes (formal math-lean-review: No major findings)`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria は GOAL カードを正本とし、SCORE は
使わない。

## Completion judgment(final、2026-08-27)

- fixed GOAL blob SHA: `17cad4df309049633617878373246300c1ad24aa`
- fixed GOAL SHA-256:
  `c7025c26418f88509b959326f61fcc576ddc1f1bc877dd2384833483848ac097`
- final head: `bf882573945a45780b022bc811754f8444846c53`
- 完了 PR: [#4197](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4197)
  (merge `e9f891b8b0d763c6c29cb2d8b6e723b43a6bb9bb`)
- standard exact-head PR gate: `Mergeable`、4 lane `No major findings`
  ([PR #4197 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4197#issuecomment-5434267456))
- same-head final packet:
  [PR #4197 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4197#issuecomment-5434280215)
- formal completion review: 独立4 lane(Math A / Math B / Lean A /
  Lean B)全て `No major findings`
- formal completion ledger: 全 completion gate pass・残 obligation /
  blocker / unchecked central claim なし
  ([PR #4197 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4197#issuecomment-5434324939))
- exact-head CI: 7/7 success
- 公理監査: 6 target module の focused Lean check で standard axioms
  のみ pass(289/19/99/2/41/34 宣言)、6 module targeted dependency
  build pass(Research aggregate / full build は hard rule に従い
  未実行)
- 固定 target (a)–(e)(担当義務 O5–O7): 全放電 — K0 第一段
  anchored coverage、K1 資格条項付き carrier-global 二枝確定
  (負枝)、K2 O7 semantic-global wrapper と reviewed predecessor
  proof-use、K3 anchor 相対 identity / composition / 両脚 pullback
  closure、K4 semantic-global cleavage・reindexing・compositor /
  unitor・triangle・pentagon、K5 exact-head completion packet と
  fresh final 4 lane audit
- material premise: `discharge-required` は全て discharged。
  direction hypothesis((d) の operand membership と operand
  anchored witness)と `conclusion-equivalent-risk`(O6 反例 raw
  data・資格 (v) raw family data — proof-free commit `2f682235` に
  固定、structure-field escape audit `none-found`)は明示分類の
  ままで、放電クレジットを与えない
- K1 provenance: 2026-08-27 の人間裁定 — 反復修正による履歴順序
  変更を許容し、最終 branch の proof-free checkpoint と raw
  structure の conclusion-side field 不在監査を provenance 証拠と
  して受理(固定 target・statement・material premise・proof-use・
  structure-field escape・route integrity・nonvacuity の各 gate は
  不変)
- remaining known mathematical proof obligations: `[]`
- unchecked completion gates: なし

正式判定は `target-theorem-proved`。達成の記録は次のとおり限定する。
(b) は負枝確定であり、coverage 成立域は selected term
`endpointFiniteTargetCofiniteTerm`(candidate index 11)の外延で
ある(像包含・同型不変性・十分性による外延一致。必要性は独立成果に
数えない)。sector 全域 coverage は同型閉包外反例により反証し、
二枝の網羅性は主張しない。(c) は G-110 reviewed 宣言
`strongCartesianLiftOfTarget` の reviewed predecessor discharge で
あり、新規証明成果に計上しない。BC mate `IsIso` 水準 exchange と
authored lax square exchange は域外(O12 = G-116 担当)。carrier
change・係数 base change・derived 系は域外。診断側(G-111 /
G-113)の量化域は変更しない。universe 契約は負枝反例 payload のみ
per-universe symbolic contract(endpoint 契約への移行は不要
だった)、他は universe-polymorphic。Gr4 達成の記録は行わない —
本カードの担当は O5–O7(Gr4 完遂 gate 第一項後半)であり、診断
保守性 / 反射・refinement 系統・上段 lift・IsIso 水準
exchange-failure 存否決定・capstone 記録は G-113〜G-116 に残る。

tracking Issue 側の完了記録は
[#4184 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4184#issuecomment-5434327304)。

## Fixed heads

- fixed GOAL blob SHA: `17cad4df309049633617878373246300c1ad24aa`
- fixed GOAL SHA-256:
  `c7025c26418f88509b959326f61fcc576ddc1f1bc877dd2384833483848ac097`
- base OID: `19a0cb3963373f7e948a3eae16fe80d8d6c55bf6`
- language head:
  `ExactBottomConditionSyntax` / `evalExactBottomCondition` /
  `rebaseExactBottomCondition`
- initial predicate-term head: `exactBottomFirstCandidate` =
  `sourceFinite ∧ targetFinite`
- accepted selected term: candidate index 11,
  `endpointFiniteTargetCofiniteTerm` =
  `(sourceFinite ∧ targetFinite) ∧ allTargetExtractionsFiniteOrCofinite`。
  `endpointFiniteTargetCofiniteSelection` が prior refutation 0--10 と同じ
  selected term を保持する。
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
| (iii) 同型不変性 | `ExactBottomConditionQualification.isomorphic_invariant` | K1 theorem output 構成済み・正式査読済み |
| (iv) anchor 相対 id / comp / pullback 閉性 | 同 qualification の4 closure field | K1 theorem output 構成済み・正式査読済み |
| (v) 像包含と非空発火 | 同 qualification の image / raw family theorem field | K1 raw family と theorem output 構成済み・正式査読済み |

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
`target-proof-checkpoint` として受理する。K0 は Cycle 2 で受理済みであり、全
completion criteria の theorem obligations F0--K4 はすべて受理済みであり、K5 final
audit だけが未完である。

2026-08-27 の人間裁定により、反復修正で raw data と proof の履歴上の順序が
変わることを許容し、最終 branch に固定された proof-free checkpoint と raw
structure が conclusion-side field を持たないことの監査を K1 provenance の
受理証拠とする。過去の proof route が repository history に存在することだけでは
target-fitting と判定しない。この裁定は固定 target、statement、material premise、
proof-use、structure-field escape、route integrity、nonvacuity の各 gate を変更しない。
K1 はこの contract に基づく fixed-head 4 lane 再監査を通過し、PR #4193
(merge `9e85f70d`) で受理された。K2 は G-110 reviewed predecessor の
semantic-global theorem を正本 wrapper と制限関係へ固定し、PR #4194
(merge `35acdcde`) の4 lane と CI 7/7 を通過して受理された。K3 は named
branch regime の membership と operand の anchored presentation/square を消費し、
identity、composition、共有 pullback anchor と両 projection witness を構成する。
K3 は PR #4195 (merge `a3a4667a`) の4 lane と CI 7/7 を通過して受理された。
K4 は任意 semantic arrow 上の selected cleavage、reindexing functor、自然な
unitor/compositor、および実 component 経路の triangle/pentagon を構成し、PR #4196
(merge `c7fef5c0`) の4 lane と CI 7/7 を通過して受理された。したがって theorem
obligation はすべて放電され、現在は completion packet と独立最終査読を行う K5
completion candidate である。`target-theorem-proved` は K5 合格後にだけ宣言する。

### Cycle 2 — K0 finite-endpoint anchored coverage

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 2
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: bbbdd80f66a5ff2f71312bd9aa068447dcbc0c33
selection:
  proof_state_ref: "Cycle 1 accepted F0; K0 is the next fixed obligation"
  selector_input: "GOAL K0 and FiniteEndpointCoverage"
  unchecked: "construct canonical finite endpoint codes, one typed arrow presentation, and the shared-anchor arrow square"
  evidence_refs:
    - research/goals/G-112-aat-exact-bottom-coverage.md
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/Schema.lean
  discovery_gap: "none"
  selected_delta: "prove FiniteEndpointCoverage without realization or caller-supplied anchor premises"
attempts:
  - route: "tabulate each finite-source doctrine and conjugate the semantic hom across the canonical endpoint enumerations"
    result: "focused elaboration passed; formal PR review pending"
result:
  status: proof-obligation-discharged
  reason: >-
    finiteSourceEquiv enumerates every finite Source by Fin (Nat.card Source);
    finiteAtomPredicateCode tabulates every Atom predicate because the carrier is finite;
    finiteDoctrineCodeOf preserves normalization and the extensional extraction
    relation formed by the conjunction of all four admission fields;
    finiteInstanceCodeOfIso gives the shared endpoint anchors; and
    finiteCartPresentationBetweenOf conjugates the original exact morphism and
    proves the arrow-category square used by finiteEndpointCoverage.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteEndpointCoverage.lean
  theorem_names:
    - finiteSourceEquiv
    - finiteAtomPredicateCode_holds_iff
    - finiteDoctrineCodeOf_extracts_iff
    - finiteDoctrineCodeOfIso
    - finiteInstanceCodeOfIso
    - finiteCartPresentationBetweenOf
    - finiteCartPresentationBetweenOf_hom_comm
    - finiteEndpointCoverage
  premise_discharge:
    - name: "finite carrier Atom"
      role: ambient-boundary
      status: retained
      provenance: "FiniteEndpointCoverage / GOAL (a)"
      proof_use: "constructs the complete Atom truth tables and finite permutation table"
    - name: "finite source endpoint Source"
      role: direction-hypothesis
      status: retained
      provenance: "FiniteEndpointCoverage / GOAL (a)"
      proof_use: "finiteSourceEquiv constructs the source endpoint code and anchor"
    - name: "finite target endpoint Source"
      role: direction-hypothesis
      status: retained
      provenance: "FiniteEndpointCoverage / GOAL (a)"
      proof_use: "finiteSourceEquiv constructs the target endpoint code and anchor"
    - name: "DecidableEq U.Atom"
      role: ambient-interface
      status: retained
      provenance: "F0 finite-code interface placement"
      proof_use: "FiniteInstanceCode decoder and finite Atom tables"
    - name: "semantic exact-bottom hom"
      role: authored-input
      status: consumed
      provenance: "CartSemanticInput.hom"
      proof_use: "sourceMap, atomEquiv, normalize_eq, extraction_iff, and source_eq all construct the typed presentation and square"
  certificate_provenance:
    - certificate: "source/target CoveredObjectWitness"
      source: "finiteInstanceCodeOf plus finiteInstanceCodeOfIso"
    - certificate: "CoverageWitnessOver.presentation"
      source: "finiteCartPresentationBetweenOf"
    - certificate: "CoverageWitnessOver.square"
      source: "finiteCartPresentationBetweenOf_hom_comm with the same endpoint anchor isomorphisms"
  proof_use:
    required:
      - FiniteEndpointCoverage
      - CartPresentationBetween
      - CartSemanticInputIso
      - ExactDoctrineHom.normalize_eq
      - ExactDoctrineHom.extraction_iff
      - ExtInstHom.source_eq
    used:
      - FiniteEndpointCoverage
      - CartPresentationBetween
      - CartSemanticInputIso
      - ExactDoctrineHom.normalize_eq
      - ExactDoctrineHom.extraction_iff
      - ExtInstHom.source_eq
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  definition_unfolding: pass
  dependency_dag: pass
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteEndpointCoverage.lean / exit 0 / 19 declarations / standard axioms only"
  blocking_findings: []
  next_obligation: "K1 carrier-global coverage disjunction and selected-candidate qualification"
```

K0 theorem body は carrier と両 endpoint の有限性を実使用し、semantic hom の
全 field を code-level presentation と arrow square に移す。単一 fixture、端点別
iso、realization premise、caller-supplied anchor は使用しない。PR #4189 の
初回4 lane 指摘を修正後、fresh 4 lane はすべて `No major findings`、exact head
`e1371b4bc4b92a8c47e73f425e697b46adef3abf` の CI は 7/7 通過した。merge
`329d8783a765683a86fbf60c0c933225440458ed` により K0 を受理した。

### Cycle 3 — K1 carrier-global classification

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 3
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: 329d8783a765683a86fbf60c0c933225440458ed
selection:
  proof_state_ref: "Cycles 1--2 accepted; K1 is the next fixed obligation"
  selector_input: "the pre-registered exactBottomConditionCandidates list"
  raw_fixture_checkpoint: 074d4a43
  raw_fixture_artifact: research/fixtures/G-112-k1-o6-raw-data-v2.md
  selected_index: 11
  selected_term: "(sourceFinite and targetFinite) and allTargetExtractionsFiniteOrCofinite"
  unchecked: "none; third formal review completed"
  discovery_gap: "V2 preserved the known refutation and positive-family proof route"
attempts:
  - route: "construct typed sufficiency for candidate 11 and concrete insufficiency refutations for indices 0--10"
    result: "focused elaboration and standard-axiom audit passed"
result:
  status: rejected
  reason: >-
    The Lean statements and constructions passed three lanes, but the fourth
    lane found that V2 retained the old candidate grouping and recoded the
    countable partition and positive-family route.  Under the fail-closed
    provenance gate this did not rule out target fitting.  The third formal
    review exhausted Cycle 3's review budget, so PR #4192 was closed unmerged.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean
  theorem_names:
    - endpointFiniteTargetCofiniteCoverage
    - coveredObjectWitness_necessary
    - endpointFiniteTargetCofiniteSelection
    - endpointFiniteTargetCofiniteQualification
    - characterizedExactBottomCoverage
    - exactBottomCoverageDisjunction
  candidate_refutations:
    count: 11
    range: "exactBottomCandidateRefutation0--exactBottomCandidateRefutation10"
    provenance: "each stores a firing semantic input and a proof that no AnchoredCoverageWitness exists"
  qualification:
    isomorphic_invariant: discharged
    identity_mem: discharged
    comp_mem: discharged
    pullback_fst_mem: discharged
    pullback_snd_mem: discharged
    realization_image_mem: discharged
    positive_fires: discharged
    positive_strictly_outside: discharged
    positive_nonisomorphic_pair: discharged
    positive_noninvertible: discharged
  premise_discharge:
    - name: "selected candidate membership"
      role: direction-hypothesis
      status: consumed
      provenance: "eval_endpointFiniteTargetCofiniteTerm_iff"
      proof_use: "constructs both endpoint codes, anchors, typed presentation, and commuting square"
    - name: "prior candidate order"
      role: fixed-selection-input
      status: consumed
      provenance: "exactBottomConditionCandidates fixed in F0"
      proof_use: "all indices below 11 receive typed ExactBottomCandidateRefutation values"
    - name: "counterexample carrier"
      role: authored-negative-fixture
      status: consumed
      provenance: "ExactBottomGridCarrier at every universe"
      proof_use: "infinite source contradicts the finite Source forced by every object anchor"
  certificate_provenance:
    - certificate: "candidate sufficiency coverage witness"
      source: "finiteCofiniteInstanceCodeOf plus endpointFiniteTargetCofinitePresentation"
    - certificate: "qualification"
      source: "theorem fields constructed from semantic isomorphisms, anchors, cospans, presentations, and raw positive-family geometry"
    - certificate: "negative branch"
      source: "fixed selection, qualification, sufficiency theorem, and authored uncovered semantic arrow"
    - certificate: "O6 raw-data chronology"
      source: "commit 074d4a43 fixes a new product carrier, endpoint doctrines, arrows, candidate assignment, final counterexample, and three-member positive family before their Lean proof"
  proof_use:
    required:
      - ExactBottomCandidateSelection
      - ExactBottomConditionQualification
      - CharacterizedExactBottomCoverage
      - ExactBottomCoverageDisjunction
    used:
      - ExactBottomCandidateSelection
      - ExactBottomConditionQualification
      - CharacterizedExactBottomCoverage
      - ExactBottomCoverageDisjunction
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "rejected: materially independent selection not established"
  vacuity: none-found
  one_way_as_equivalence: none-found
  definition_unfolding: pass
  dependency_dag: pass
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean / exit 0 / 90 declarations / standard axioms only"
  blocking_findings:
    - "central review finding: V2 is an isomorphic/duplicated recoding of the known proof route"
  next_obligation: "reselect K1 raw assignment and positive-family route in Cycle 4"
```

K1 は fixed candidate list の第12項を、先行11項の具体的 refutation とともに
選ぶ。負枝の counterexample は universe ごとに構成され、述語 template、十分性、
qualification は universe-polymorphic のままである。K2--K4 と K5 final audit は
未完であり、G-112 全体の completion candidate ではない。

## K1 review correction

PR #4190 の初回4 lane は O6 raw counterexample の時系列 provenance を中心 finding
とした。initial head `7f6b6317...` は proof と ledger を追加したが raw-data-only
artifact を持たず、GOAL が要求する選定時固定を監査できないため受理しない。
PR #4191 は commit `779bd010` で旧 proof と同じ Nat/even fixture を raw artifact として
先に並べ直した。しかし repository 全履歴では `7f6b6317...` の既知 proof がその
checkpoint より先行するため、fresh 4 lane は chronology laundering と判定した。この
attempt も受理しない。

Cycle 3 の最後の許容 rerun は、旧 proof に存在しない V2 data を commit `074d4a43` で先に固定
した。[`research/fixtures/G-112-k1-o6-raw-data-v2.md`](../fixtures/G-112-k1-o6-raw-data-v2.md)
は Atom を `ULift (Nat × Bool)`、bad predicate を Boolean left slice、無限 Source を
`ULift (Nat × Fin 2)`、mixed Source を `Fin 3` とし、candidate assignment の全 raw
arrow を作り直す。qualification family も `Fin 3` parameter、three-to-one realized
arrow、`Vocabulary := Fin 3` の二つの decorated identity へ変更した。artifact は data
だけを記録し、発火・非coverage・qualification certificate を含まない。後続 Lean
proof はこの固定 data から全 proposition を生成し、旧 Nat/even・Bool family を使用
しない。

非中心 finding に対しては、全新規 public declarationへ docstring と module-level
Implementation notes を追加した。presentation proof の code projection と extraction
comparison には `finiteCofiniteInstanceCodeOf_doctrine`、
`finiteCofiniteInstanceCodeOf_point`、`finiteCofiniteExtractionCode_eq_of_mem_range`、
`finiteCofiniteDoctrineCodeOf_extraction` の API を用い、下流で新規 code 定義を直接
展開しない。V2 proof commit `79a22c64...` の fresh 4 lane は数学2本が
`No major findings`、Lean A が非中心2件、Lean B が中心 provenance finding と判定
した。fail-closed に統合して PR #4192 を閉じ、Cycle 3 を `rejected` とした。

### Cycle 4 — K1 materially new selection

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 4
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: 329d8783a765683a86fbf60c0c933225440458ed
selection:
  proof_state_ref: "Cycle 3 rejected after its third formal review"
  selector_input: "the unchanged pre-registered exactBottomConditionCandidates list"
  raw_fixture_checkpoint: 2f682235
  raw_fixture_artifact: research/fixtures/G-112-k1-o6-raw-data-v3.md
  selected_index: 11
  selected_term: "(sourceFinite and targetFinite) and allTargetExtractionsFiniteOrCofinite"
  unchecked: "status-sync formal re-review at the current fixed head"
  discovery_gap: "repository-wide proof-before-selection provenance is unavailable"
attempts:
  - route: >-
      retain the carrier-uniform candidate-11 construction, but derive prior
      refutations from a changed raw assignment and derive positive-family
      nondegeneracy from two newly authored nonidentity arrows
    result: "focused elaboration and standard-axiom audit passed"
result:
  status: proof-obligation-discharged
  reason: >-
    The Lean package constructs all required K1 statements, refutations,
    qualification fields and the carrier-global branch.  The 2026-08-27 human
    ruling accepts iterative repair reordering and qualifies the final-branch
    proof-free checkpoint plus the absence of conclusion-side fields in the raw
    structures as provenance evidence.  The remaining statement, premise,
    proof-use, field-escape, route-integrity and nonvacuity gates remain active.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean
  theorem_names:
    - endpointFiniteTargetCofiniteCoverage
    - coveredObjectWitness_necessary
    - endpointFiniteTargetCofiniteSelection
    - endpointFiniteTargetCofiniteQualification
    - characterizedExactBottomCoverage
    - exactBottomCoverageDisjunction
  candidate_refutations:
    count: 11
    range: "exactBottomCandidateRefutation0--exactBottomCandidateRefutation10"
    provenance: "V3 table fixed in 2f682235; each firing and noncoverage proposition is generated later"
  premise_discharge:
    - name: "selected candidate membership"
      role: direction-hypothesis
      status: consumed
      proof_use: "constructs endpoint codes, anchors, typed presentation, and commuting square"
    - name: "prior candidate order"
      role: fixed-selection-input
      status: consumed
      proof_use: "all indices below 11 receive typed V3 refutations"
    - name: "O6 raw data"
      role: conclusion-equivalent-risk
      status: consumed
      provenance: "proof-free commit 2f682235"
      proof_use: "summand-bad, mixed-four, and plane endpoints generate firing and noncoverage"
    - name: "qualification raw family"
      role: conclusion-equivalent-risk
      status: consumed
      provenance: "two newly authored nonidentity arrows in proof-free commit 2f682235"
      proof_use: "all firing and nondegeneracy fields are separate theorem outputs"
  structure_field_escape: none-found
  route_integrity: "pass under the 2026-08-27 human provenance ruling"
  target_fitting: "none-found under the 2026-08-27 human provenance ruling"
  vacuity: none-found
  one_way_as_equivalence: none-found
  definition_unfolding: pass
  dependency_dag: pass
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean / exit 0 / 99 declarations / standard axioms only"
  blocking_findings: []
  next_obligation: "K2 O7 semantic-global wrapper and proof-use audit, recorded in Cycle 5"
```

V3 は V1/V2 の反例 index grouping を変更し、有限 bad endpoint を candidate 0、1、
5--8、10 に実使用する。positive family は既存 realized arrow を再利用せず、raw
endpoint と constant source map から二つの非恒等射を構成する。最初の Cycle 4
formal review では、選定時に既知だった proof route を使って data を設計したことを
中心 finding とした。数学B・Lean Bが `Reject`、数学A・Lean Aが中心findingなし
（非中心docstring/import findingあり）で、当時の統合判定は `Needs changes` だった。
2026-08-27 の人間裁定はその provenance 解釈を置換した。既知の非中心 finding を修正し、
同裁定を明示した head `d6f7e624` から K1 を再監査した。非中心 ledger-state drift を
同期した head `7c1262b1` の再査読は4 laneすべて `No major findings` となり、
PR #4193 で K1 を受理した。

### Cycle 5 — K2 O7 semantic-global wrapper

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 5
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: 9e85f70df25eedae54914fbfbc235e56118420f6
selection:
  proof_state_ref: "K1 accepted by PR #4193; K2 is the next fixed obligation"
  proof_dag_predecessors:
    - "G-110 reviewed strongCartesianLiftOfTarget in CartesianTarget.lean"
  proof_obligation: "fix the O7 semantic-global wrapper and its restriction relation to G-110 globalCartesianLift"
  selection_reason: "the reviewed predecessor already has the unrestricted semantic statement required by G-112(c)"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean
  risks:
    - "wrapper must not add realization, finiteness, or caller-supplied lift premises"
    - "proof term must materially consume strongCartesianLiftOfTarget"
    - "G-110 globalCartesianLift must be recorded as the RealizableHom restriction, not conflated with the semantic-global statement"
  unchecked:
    - "fixed-head standard PR review and CI"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "adds the fixed semantic-global O7 wrapper and proves the realization-qualified G-110 branch from it"
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean
  evidence:
    - exact_bottom_semantic_global_strong_cartesian_lift
    - global_cartesian_lift_of_exact_bottom_semantic_global_strong_cartesian_lift
  claim_mapping:
    theorem_names:
      - exact_bottom_semantic_global_strong_cartesian_lift
      - global_cartesian_lift_of_exact_bottom_semantic_global_strong_cartesian_lift
    source_labels:
      - "G-112 target theorem (c)"
      - "G-112 material premise ledger: O7 semantic-global strong cartesian lift"
    conjuncts:
      - "arbitrary CartSemanticInput and arbitrary target CoreFiber package -> HasStrongCartesianLift"
      - "restriction along RealizableHom -> GlobalCartesianLift"
    undischarged_assumptions: []
    acceptance_point: "reviewed predecessor discharge with no new mathematical credit"
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "O7 semantic-global lift / strongCartesianLiftOfTarget"
    remaining:
      - "K3 coverage closure"
      - "K4 global lift coherence"
      - "K5 final audit"
  certificate_provenance:
    discharged:
      - "lift witness / reviewed G-110 strongCartesianLiftOfTarget"
    unresolved: []
  proof_use:
    used:
      - "strongCartesianLiftOfTarget / exact_bottom_semantic_global_strong_cartesian_lift proof body"
      - "exact_bottom_semantic_global_strong_cartesian_lift / realization-qualified restriction theorem"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean / exit 0 / 2 declarations / standard axioms only"
    - "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.ExactBottomGlobalLift / exit 0 / targeted module only"
  blocking_findings: []
  next_obligation: "fixed-head K2 standard review, then K3 coverage regime and closure producers"
```

### Cycle 6 — K3 branch-independent anchored closure

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 6
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: 35acdcdeffa3987ed6e2162da2f63be2d01d513d
selection:
  proof_state_ref: "K2 accepted by PR #4194; K3 is the next fixed obligation"
  proof_dag_predecessors:
    - "K1 ExactBottomCoverageRegime and fixed branch qualification"
    - "G-110 typed identity, composition, and semantic pullback producers"
  proof_obligation: "construct branch-independent anchor-relative identity, composition, and two-leg pullback closure"
  selection_reason: "the fixed order requires K3 before semantic-global coherence"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClosure.lean
  risks:
    - "output coverage witness must not be obtained only by membership closure followed by regime.covers"
    - "composition must consume both operand presentations and commuting squares"
    - "pullback must construct one shared pullback anchor and both projection witnesses"
  unchecked:
    - "fixed-head standard PR review and CI"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "adds direct anchored witness producers for identity, composition, and both pullback projections"
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClosure.lean
  evidence:
    - exact_bottom_identity_closure
    - exact_bottom_composition_closure
    - exact_bottom_pullback_closure
  claim_mapping:
    theorem_names:
      - exact_bottom_identity_closure
      - exact_bottom_composition_closure
      - exact_bottom_transported_code_pullback_is_pullback
      - exact_bottom_pullback_object_iso
      - exact_bottom_pullback_closure
    source_labels:
      - "G-112 target theorem (d)"
    conjuncts:
      - "covered object anchor -> identity membership and anchored identity witness"
      - "two memberships plus shared-anchor operand witnesses -> composite membership and anchored composite witness"
      - "two memberships plus shared-base operand witnesses -> one pullback object anchor and both projection memberships/witnesses"
    undischarged_assumptions: []
    acceptance_point: "direct typed-presentation construction; no regime.covers reuse"
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K3 identity closure"
      - "K3 composition closure"
      - "K3 two-leg pullback closure"
    remaining:
      - "K4 global lift coherence"
      - "K5 final audit"
  certificate_provenance:
    discharged:
      - "identity witness / idTypedPresentation from the supplied object anchor"
      - "composition witness / compPresentation from both operand CoverageWitnessOver values"
      - "pullback witness / pullbackPresentation_isPullback transported by all three anchors and compared with pointedPullback_isPullback"
    unresolved: []
  proof_use:
    used:
      - "both input membership proofs / branch qualification membership producers"
      - "both operand presentations and commuting squares / composite and pullback witness construction"
      - "both pullback legs / shared generated object anchor and projection squares"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClosure.lean / exit 0 / 41 declarations / standard axioms only"
  blocking_findings: []
  next_obligation: "fixed-head K3 standard review, then K4 semantic-global cleavage and coherence"
```

### Cycle 7 — K4 semantic-global lift coherence

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 7
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: a3a4667a3f45f2a712f3f7b7a3a0cc471996b290
selection:
  proof_state_ref: "K3 accepted by PR #4195; K4 is the final implementation obligation"
  proof_dag_predecessors:
    - "K2 exact_bottom_semantic_global_strong_cartesian_lift"
    - "reviewed generic CoreFiberCartesianCleavage.reindexFunctor API"
  proof_obligation: "construct semantic-global cleavage, reindexing functor, natural unitor/compositor, triangle, and pentagon"
  selection_reason: "the fixed order places global lift coherence after coverage closure"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean
  risks:
    - "no realization, finite-code, DecidableEq, coverage, or caller-supplied coherence premise"
    - "unitor and compositor must be natural isomorphisms, not regenerated lift existence"
    - "triangle and pentagon must compare the actual component routes including equality casts"
  unchecked:
    - "none"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "adds unrestricted contravariant reindexing coherence generated by strong-cartesian uniqueness"
  completion_candidate: yes
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean
  evidence:
    - exact_bottom_semantic_global_cartesian_cleavage
    - exact_bottom_semantic_global_reindex_functor
    - exact_bottom_semantic_global_compositor
    - exact_bottom_semantic_global_unitor
    - exact_bottom_semantic_global_triangle
    - exact_bottom_semantic_global_pentagon
  claim_mapping:
    theorem_names:
      - exact_bottom_semantic_global_cartesian_cleavage
      - exact_bottom_semantic_global_reindex_functor
      - exact_bottom_semantic_global_compositor
      - exact_bottom_semantic_global_unitor
      - exact_bottom_semantic_global_left_unit_triangle
      - exact_bottom_semantic_global_right_unit_triangle
      - exact_bottom_semantic_global_triangle
      - exact_bottom_semantic_global_pentagon
    source_labels:
      - "G-112 target theorem (e)"
    conjuncts:
      - "strongCartesianLiftOfTarget-derived cleavage on every semantic base arrow"
      - "cleavage-derived contravariant reindexing functor"
      - "direct-versus-iterated natural compositor iso"
      - "literal-identity-versus-selected natural unitor iso"
      - "source and target unit triangles for actual component routes"
      - "three-arrow pentagon for actual component routes with associativity cast"
    undischarged_assumptions: []
    acceptance_point: "natural-iso-level semantic-global coherence; no lift-existence regeneration"
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 semantic-global cleavage and reindexing"
      - "K4 unitor and compositor natural isomorphisms"
      - "K4 triangle and pentagon coherence"
    remaining: []
  certificate_provenance:
    discharged:
      - "cleavage lift / K2 semantic-global wrapper"
      - "compositor / comparison of literal iterated and direct selected strong lifts"
      - "unitor / comparison of literal identity and selected identity strong lifts"
      - "coherence / strong-cartesian uniqueness after explicit route factor equations"
    unresolved: []
  proof_use:
    used:
      - "exact_bottom_semantic_global_strong_cartesian_lift / cleavage construction"
      - "both constituent selected lifts / iterated lift and compositor"
      - "natural compositor/unitor components / triangle and pentagon route definitions"
      - "equality-induced reindex casts / associativity and unit comparison targets"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean / exit 0 / 34 declarations / standard axioms only"
    - "exact head 7bea9d5bc5122acaf5730217606fc4f17d83200c / fresh mathematics A-B and Lean A-B review / No major findings"
    - "exact head 7bea9d5bc5122acaf5730217606fc4f17d83200c / CI 7 of 7 passed"
    - "PR #4196 audit comment 5434144700 / merge c7fef5c0da651a0848024cec903ce8bfacd81c1a"
  blocking_findings: []
  next_obligation: "K5 final completion packet and fresh math-lean-review"
```

### Cycle 8 — K5 final completion audit

```yaml
ledger_type: target_cycle_result
goal: G-112-aat-exact-bottom-coverage
cycle: 8
goal_blob_sha: 17cad4df309049633617878373246300c1ad24aa
base_oid: c7fef5c0da651a0848024cec903ce8bfacd81c1a
selection:
  proof_state_ref: "F0--K4 accepted; all theorem obligations discharged"
  proof_dag_predecessors:
    - "PR #4193 / K1 classification and qualified branch"
    - "PR #4194 / K2 semantic-global strong cartesian lift"
    - "PR #4195 / K3 identity, composition, and two-leg pullback closure"
    - "PR #4196 / K4 semantic-global reindexing coherence"
  proof_obligation: "publish the exact-head completion packet and run a fresh four-lane final math-lean-review"
  selection_reason: "the fixed order reaches K5 only after every theorem-producing obligation is accepted"
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteEndpointCoverage.lean
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClosure.lean
    - ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean
  risks:
    - "a static Lean pass alone is not a completion verdict"
    - "the completion packet must enumerate every material premise, provenance route, and actual proof-use"
    - "the final four lanes must be fresh and independent from the PR review lanes"
  unchecked:
    - "exact-head standard PR review and CI"
    - "completion packet with command hashes and full premise ledger"
    - "fresh final mathematics A-B and Lean A-B review"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "no new theorem claim; final exact-head integration and adversarial audit only"
  completion_candidate: yes
  lean_artifacts:
    - "the six focused modules listed above"
  evidence:
    - "accepted K1--K4 exact-head audits and merge commits"
    - "fixed GOAL statement and material-premise ledger"
  claim_mapping:
    theorem_names:
      - finiteEndpointCoverage
      - exactBottomCoverageDisjunction
      - exact_bottom_semantic_global_strong_cartesian_lift
      - exactBottomCoverageRegimeOfDisjunction
      - exact_bottom_identity_closure
      - exact_bottom_composition_closure
      - exact_bottom_pullback_closure
      - exact_bottom_semantic_global_cartesian_cleavage
      - exact_bottom_semantic_global_reindex_functor
      - exact_bottom_semantic_global_compositor
      - exact_bottom_semantic_global_unitor
      - exact_bottom_semantic_global_triangle
      - exact_bottom_semantic_global_pentagon
    source_labels:
      - "G-112 target theorem (a)--(e)"
    conjuncts:
      - "finite-endpoint anchored coverage"
      - "qualified exact-bottom classification or global branch"
      - "semantic-global strong cartesian lift"
      - "identity, composition, and shared-anchor two-leg pullback closure"
      - "semantic-global cleavage, reindexing, natural coherence, triangle, and pentagon"
    undischarged_assumptions: []
    acceptance_point: "only a fresh final four-lane pass can change the candidate into target-theorem-proved"
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "all fixed theorem obligations F0--K4"
    remaining: []
  certificate_provenance:
    discharged:
      - "K1 proof-free checkpoint and conclusion-free raw structures under the human provenance ruling"
      - "K2 reviewed predecessor proof-use"
      - "K3 direct typed-presentation witness construction"
      - "K4 actual natural-isomorphism and coherence routes"
    unresolved: []
  proof_use:
    used:
      - "all material producer and closure declarations named by the fixed GOAL"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "pending exact-head K5 evidence"
  blocking_findings: []
  next_obligation: "standard PR review, completion packet, then fresh final math-lean-review"
```

## Historical stop packet — superseded by the 2026-08-27 human ruling

- historical accepted obligations: F0、K0。
- historically unaccepted obligation: K1。Lean theorem package は focused check、99 declaration
  standard-axiom audit、targeted module build、PR #4193 CI 7/7 を通過したが、O6 と
  qualification raw family の `conclusion-equivalent-risk` provenance は未放電。
- review verdict: PR #4190、#4191、#4192、#4193 はいずれも merge しない。#4193 の
  中心 finding は、既知 proof route から独立した選定時記録を現在の repository history
  から生成できないこと。
- historical remaining obligations: K2 O7 wrapper、K3 closure producer、K4 global lift coherence、
  K5 final audit。K1未受理のため開始しない。
- historical stop reason: `target-proof-checkpoint`。K1 proof package は PR #4193 に
  固定されたが、当時は provenance gate を現在の履歴から放電できないと判定した。
- superseding ruling: 2026-08-27、人間が反復修正による順序変更を許容し、最終 branch の
  proof-free checkpoint と raw structure field audit を provenance 証拠として受理した。
  このため historical stop は現行の停止条件ではない。
