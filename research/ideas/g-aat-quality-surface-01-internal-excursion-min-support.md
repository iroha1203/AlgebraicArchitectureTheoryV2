---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: repair-potential / obstruction / traceability / atom-supported-quality-geometry / invariance
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: cycle-41
tags: [quality-surface, internal-excursion, minimal-support, hitting]
created: 2026-06-21
---

# Minimal internal excursion support family hitting theorem

## 主張

route-chain internal excursion に対して selected minimal support family を置き、internal excursion を eliminate する
correction は、その selected minimal internal support family の全 branch を hit しなければならない。

主 witness は Cycle 40 の token-swap/un-swap chain である。この chain の internal support は endpoint/worker
source-ref table coordinates に exact に局在する。これを route-internal support atom vocabulary の二つの singleton
minimal branch として読み、片方だけを correction が触る場合にはもう片方の internal excursion support が残ることを
Lean で固定する。

この主張は supplied finite source-ref packets、selected length-two route chain、selected internal support atom vocabulary、
explicit endpoint/worker table coordinates に相対化される。global additive defect group、canonical repair planning、
source extraction completeness、ArchMap correctness、実コード全体の品質判定は結論しない。

## 候補種別

`unification`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/SupportHitting.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectExcursionSupport.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`

## Lean 証拠

- `research/lean/ResearchLean/AG/QualitySurface/InternalExcursionMinSupport.lean`
- `research/lean/ResearchLean.lean`

主要 declaration:

- `InternalExcursionAtom`
- `internalExcursionAtomComponent`
- `tokenSwapUnswap_internalExcursionAtomSupport`
- `TokenSwapUnswapSelectedInternalSupportGrounded`
- `tokenSwapUnswap_selectedInternalSupport_grounded`
- `InternalExcursionBranch`
- `internalExcursionBranchAtom`
- `InternalExcursionBranchGrounded`
- `internalExcursionBranch_grounded`
- `CorrectionHitsBranch`
- `BranchRemainsAfterCorrection`
- `InternalExcursionEliminates`
- `no_afterCorrection_of_hits`
- `eliminates_no_afterCorrection`
- `missed_branch_remains_afterCorrection`
- `hits_every_minInternalSupport_of_eliminates`
- `endpointTable_minInternalSupport`
- `workerTable_minInternalSupport`
- `internalExcursion_minSupportFamily_nonempty`
- `internalExcursion_minSupportBranches_distinct`
- `endpointTableCorrection`
- `endpointWorkerCorrection`
- `endpointOnlyCorrection_hits_endpointTable`
- `endpointOnlyCorrection_misses_workerTable`
- `endpointOnlyCorrection_workerBranch_remains`
- `endpointOnlyCorrection_does_not_eliminate`
- `endpointWorkerCorrection_eliminates`
- `endpointWorkerCorrection_hits_every_minInternalSupport`
- `internalExcursionMinimalSupport_package`

## 非自明性

Cycle 40 は token-swap/un-swap の exact internal support table pair を固定した。この候補は、それを単なる二つの
positive support fact ではなく、minimal support family と hitting theorem の言語へ持ち上げる。これにより、
endpoint-empty な internal excursion にも correction requirement を与えられる。

## 数学的興味

endpoint support からは消える route-internal excursion が、minimal support family としては repair / correction の
必要条件を持つ。obstruction support と route excursion support を同じ hitting-set calculus で読むことで、
Quality Surface の repair-potential と route-history memory が接続される。

## GOAL への前進

support-local repair theorem frontier と internal route defect excursion frontier を統合する。これは minimal atom support
family、repair-potential、obstruction、traceability の各カテゴリを、endpoint support を越えた route-history surface へ
拡張する。

## SCORE 見込み

- `score_reason`: Cycle 1 の hitting theorem と Cycle 40 の exact internal support を統合し、endpoint-empty excursion に
  selected minimal support family と correction necessity を与える。任意 route chain や大域 repair planning ではないため
  base 65 に抑える。ただし G2 A の指摘通り、Lean-grounded bridge evidence が弱ければ base 50 以下に落とす。
- `dullness_risk`: `SupportHitting` の名前替えだけなら dull。token-swap/un-swap internal support の endpoint/worker table
  pair に grounded な finite support family、off-coordinate nonmembership、片側 correction failure を同時に固定する必要がある。
  特に exact support set `{endpoint, worker}` と selected minimal family `{endpoint}`, `{worker}` を混同しない。
- `proof_or_evidence_plan`: route-internal support atom vocabulary を endpoint table / worker table の二 atom として定義する。
  それを `SourceRefPacketProtectedComponent` へ写し、Cycle 40 の `tokenSwapUnswap_internalSupport_exact_tablePair` と接続する。
  selected minimal family を二つの singleton branch とし、`AfterCorrection` は correction が miss した selected branch を
  残す semantics として定義する。endpoint-only correction が worker branch を miss して eliminate できないこと、
  endpoint+worker correction が all-branch hitting になることを Lean で証明する。

## CS / SWE への帰結

endpoint が clean に見える route でも、内部 excursion を消す correction は少なくとも endpoint-table と worker-table
の両 coordinate を見る必要がある、という drill-down requirement を表現できる。

## 証明・根拠の見込み

Lean では次の declaration を固定した。

- `InternalExcursionAtom`
- `internalExcursionAtomComponent`
- `tokenSwapUnswap_internalExcursionAtomSupport`
- `TokenSwapUnswapSelectedInternalSupportGrounded`
- `tokenSwapUnswap_selectedInternalSupport_grounded`
- `InternalExcursionBranch`
- `internalExcursionBranchAtom`
- `InternalExcursionBranchGrounded`
- `internalExcursionBranch_grounded`
- `CorrectionHitsBranch`
- `BranchRemainsAfterCorrection`
- `InternalExcursionEliminates`
- `missed_branch_remains_afterCorrection`
- `hits_every_minInternalSupport_of_eliminates`
- `endpointTable_minInternalSupport`
- `workerTable_minInternalSupport`
- `endpointOnlyCorrection_misses_workerTable`
- `endpointOnlyCorrection_workerBranch_remains`
- `endpointOnlyCorrection_does_not_eliminate`
- `endpointWorkerCorrection_hits_every_minInternalSupport`
- `internalExcursionMinimalSupport_package`

検証:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/InternalExcursionMinSupport.lean`: pass
- `lake build ResearchLean.AG.QualitySurface.InternalExcursionMinSupport`: pass
- `lake build ResearchLean`: pass
- `.tmp/internal_excursion_min_support_axioms.lean`: 全対象 declaration が axiom 依存なし
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" research/lean/ResearchLean/AG/QualitySurface/InternalExcursionMinSupport.lean research/lean/ResearchLean.lean`: 該当なし

G3 監査:

- 公理検査: pass。全対象 declaration は `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は残っていない。
- Lean 形式化品質監査: pass。初回 revise で、`InternalExcursionEliminates` が all-hit の定義そのものだと hitting theorem が薄い、という指摘を受けた。修正版では `InternalExcursionEliminates` を after-correction branch 不在として定義し、`hits_every_minInternalSupport_of_eliminates` を missed branch remains との矛盾から導く。`CorrectionHitsBranch` は `Bool` correction にして generic Prop の classical split を避けた。

## 審判メモ

- 厳密性: G2 A revise。方向は妥当だが、Cycle 40 の exact two-coordinate support から二 singleton minimal branch は
  自動では出ないため、selected family、after-correction semantics、endpoint-only failure、endpoint+worker all-hit を
  Lean で固定することを要求された。base 50 provisional、Lean-grounded bridge evidence が揃えば base 65。実装後の
  再審判では accept base 65。`InternalExcursionEliminates` が after-correction branch 不在として定義され、
  selected branch grounding、off-coordinate nonmembership、endpoint-only failure、endpoint+worker all-hit が Lean 上で固定されたため、
  `SupportHitting` の単純 rename ではないと判定された。
- 研究価値: G2 B accept base 65。support-local repair theorem、route defect support calculus、internal excursion support
  を同じ hitting-set language にまとめる研究価値あり。
- repo 全体価値: G2 C accept base 65。Cycle 40 の open question `minimal internal excursion support family` を閉じる候補として妥当。

## 関連

- `g-aat-quality-surface-01-route-defect-local-to-global.md`
- `g-aat-quality-surface-01-route-defect-support-calculus.md`
- Cycle 1 minimal-support hitting theorem
- Cycle 40 route-chain internal support

## 進捗ログ

- 2026-06-21: Cycle 41 候補として作成。
- 2026-06-21: G2 A revise を受け、二 singleton family と after-correction semantics を追加定義として明示する方針へ修正。
- 2026-06-21: `InternalExcursionMinSupport.lean` で selected branch type、Cycle 40 exact support grounding、branch-remains-after-correction、endpoint-only failure、endpoint+worker all-hit package を Lean-proved にした。
