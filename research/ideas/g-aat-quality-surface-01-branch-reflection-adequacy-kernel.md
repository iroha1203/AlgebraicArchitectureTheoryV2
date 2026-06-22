---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability
capability_category: computability / certificate-transport / invariance / repair-potential / obstruction / quality-surface
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: ADL / conformance readings can preserve visible component unions, but they do not provide a branch-local support-lift adequacy kernel that decides when coarse repair transversality transports to refined selected branches.
origin: cycle-73
tags: [quality-surface, branch-reflection, repair-transport, adequacy-kernel]
created: 2026-06-22
cycle: 73
lean: proved-in-research
---

# Branch-reflection adequacy kernel for refinement support transport

## 主張

有限の coarse / refined exchange branch family と declared repair support の組に対して、branch-local な
support-lift closure を adequacy 条件として定義する。この条件が通るなら、coarse family の
branch-transversal clearance は refined selected branch family へ transport する。条件が欠ける場合は、
visible component-union projection が一致していても、reflected repair-frontier singleton を missing branch
witness として返せる。

ここで support-lift closure は、refined transversality を仮定しない。Lean では次の形で固定する。

```text
SupportLiftClosedForBranch coarseBranch refinedBranch coarseSupport refinedSupport :=
  forall coarseComponent,
    coarseBranch coarseComponent ->
      coarseSupport coarseComponent.2 ->
        exists refinedComponent,
          refinedBranch refinedComponent /\ refinedSupport refinedComponent.2

BranchReflectionTransportAdequate coarseFamily refinedFamily coarseSupport refinedSupport :=
  forall refinedBranch,
    refinedFamily refinedBranch ->
      exists coarseBranch,
        coarseFamily coarseBranch /\
          SupportLiftClosedForBranch coarseBranch refinedBranch coarseSupport refinedSupport
```

したがって pass theorem は、coarse transversality から得た coarse hit witness を、branch-local closure で refined
hit witness へ移す。refined family がすでに transversal であること、scan residual が none であること、
selected-family hit が直接成り立つことは仮定しない。

この主張は、選ばれた repair/refinement exchange cell、finite exchange branch family、declared repair support、
branch-reflection relation に相対化する。global atlas refinement、canonical refinement theorem、runtime repair synthesis、
source extraction completeness、ArchMap correctness、global sheaf completeness、whole-codebase quality は主張しない。

## 候補種別

`computability`

## 依拠

- Cycle 70: `CurvatureBasisExchange.lean` の selected path-indexed exchange branch family と
  `ExchangeBranchRepairTransversal`。
- Cycle 71: `NaiveRefinementSupportCounterexample.lean` の visible-union preservation と
  reflected repair-frontier singleton failure。
- Cycle 72: `BranchTransversalScanKernel.lean` の selector-relative residual scan と missing branch witness。

## 非自明性

単なる transversality の再命名ではなく、粗い branch の hit witness を refined branch へ移すための
branch-local support-lift closure を別条件として切り出す。これにより、可視 projection の一致だけでは足りないという
no-go を、正方向の transport theorem と失敗 witness を返す finite kernel に変える。

## 数学的興味

branch-transversal repair obligation は、component union ではなく branch incidence と repair support の相互作用で決まる。
この候補は、refinement で何を保持すれば branch-transversal class が移植できるかを、有限 witness を通じて明示する。
Cycle 71 の反例を「どの仮定が抜けたから失敗したか」に変換し、Cycle 72 の residual kernel を transport adequacy の判定面へ接続する。

## GOAL への前進

Quality Surface の repair/refinement transport 軸に、positive pass theorem と missing-branch failure theorem を持つ
計算可能な adequacy kernel を追加し、support / repair / obstruction / traceability を一つの finite branch geometry で読む能力を増やす。

## ライバルに対する有効性

ADL、conformance checker、dashboard は refined component set や visible view の一致を扱えるが、branch ごとの repair-support lift
がないと transversality が transport しないことを同じ artifact 内で証明しにくい。この候補は、可視一致を尊重しつつ、
ADL view では落ちる branch-local support transport と missing reflected branch を明示的に返す。

## SCORE 見込み

- `score_reason`: Cycle 71 の no-go と Cycle 72 の scan kernel を、positive transport / negative witness の二相 kernel に統合するため、80-100 帯の computability / certificate-transport 成果として見込む。ただし selected finite exchange cell の延長なので、通常高得点の 88 点見込みに下げる。
- `dullness_risk`: adequacy 条件を「refined family が transversal」と同値にしてしまうと自明化する。今回の改訂では、coarse hit witness を refined hit witness へ運ぶ branch-local support-lift closure と具体的 missing branch witness を Lean statement に分けて、このリスクを抑える。
- `proof_or_evidence_plan`: Research 側 Lean ファイルで `SupportLiftClosedForBranch`、`BranchReflectionTransportAdequate`、pass theorem、selected all-exchange pass witness、naive/reflected failure witness、package theorem を証明する。

## CS / SWE への帰結

refinement 後の repair obligation が移植できるかを、可視 component set の一致ではなく、branch-local support lift と missing branch
residual の有無として説明できる。これは、既存の構造ビューや conformance view が通っても repair frontier が失われるケースを、
有限 certificate の判定面として扱うための下地になる。

## 証明・根拠

Lean 証拠は `Formal/AG/Research/QualitySurface/BranchReflectionAdequacyKernel.lean` に固定した。

- `SupportLiftClosedForBranch`
- `BranchReflectionTransportAdequate`
- `branchReflectionKernel_pass_preservesTransversal`
- `traceRepairFrontierRepairSupport`
- `traceRepairFrontierSupport_hits_collapsedVisible`
- `selectedAllExchangeAdequate`
- `allExchangeSupport_transports_selectedReflection`
- `BranchReflectionCoverageFailure`
- `reflectedRepairFrontier_coverageFailure`
- `traceOnly_not_branchReflectionAdequate_naive_to_reflected`
- `branchReflectionKernel_fail_returnsMissingBranch`
- `missingReflection_witnessesTransportFailure`
- `visibleUnion_not_faithful_to_reflectionAdequacy`
- `branchReflectionAdequacyKernel_package`

pass theorem は、coarse branch family の各 hit witness を branch-local lift closure で refined branch の hit witness に移す。
failure theorem は、naive paired reading が visible union を保存して trace-only transversality を受け入れる一方で、
reflected selected reading が repair-frontier singleton を missing branch として返す有限 witness を使う。
この failure は既存 scan residual の単なる再掲ではなく、`BranchReflectionCoverageFailure` として
source reading が reflected branch を含まないことを明示し、そのうえで trace-only support が source family では
transversal、reflected family では non-transversal になることを同時に示す。

## G2 審判結果

- 厳密性: revise 後 accept。base 86。`SupportLiftClosedForBranch` が refined transversality を仮定しない形になったため非循環な sufficient condition として通る。
- 研究価値: accept。base 88。no-go を positive adequacy に反転し、pass/fail 判定面を足す。
- repo 全体価値: accept。base 88。Lean / paper / tooling / website surface に接続する。
- ライバル比較: accept。base 92。ADL / conformance view が落とす branch-local support transport を示す。
- genius: 四審判とも `genius_eligibility: no`。通常 SCORE として扱う。

## G3 監査結果

- `lake env lean Formal/AG/Research/QualitySurface/BranchReflectionAdequacyKernel.lean`: pass。
- `lake build FormalAGResearch`: pass。
- `#print axioms`: 報告対象 14 declaration はすべて axiom-free。`sorryAx`、非標準公理、`propext`、`Classical.choice`、`Quot.sound`、`unsafe` なし。
- Lean 形式化品質監査: pass。`BranchReflectionTransportAdequate` は refined transversality、zero residual scan、直接 selected-family hit を仮定していない。failure 側は Cycle 72 scan residual の再掲ではなく、`BranchReflectionCoverageFailure` と transport non-adequacy を追加している。

## G4 SCORE 監査結果

- score_verdict: confirm。
- base_score: 88。
- evidence_multiplier: 2.0。
- penalty: 0。
- final_score: 176。
- category: computability / certificate-transport / invariance / repair-potential / obstruction / quality-surface。
- genius_verdict: downgrade-to-normal。四審判すべて `genius_eligibility: no` なので genius scoring は採らない。
- total_delta: 9794 -> 9970。active threshold 10000 にはまだ 30 SCORE 不足する。

## 審判メモ

- 厳密性: adequacy 条件が transversality 結論そのものを仮定していないかを確認する。
- 研究価値: no-go を positive transport criterion へ反転できているかを確認する。
- repo 全体価値: report の repair/refinement exchange frontier と自然に接続するかを確認する。
- ライバル比較: ADL / conformance view の visible projection と branch-local support transport の差分が明確かを確認する。

## 追加 required fields

- `mathematical_interest`: branch incidence と repair support lift の相互作用を transport adequacy として切り出す点。
- `goal_advancement`: repair/refinement transport の pass/fail kernel を finite branch geometry として追加する。
- `planned_theorem_names`: `SupportLiftClosedForBranch`, `BranchReflectionTransportAdequate`, `branchReflectionKernel_pass_preservesTransversal`, `branchReflectionKernel_fail_returnsMissingBranch`, `visibleUnion_not_faithful_to_reflectionAdequacy`, `branchReflectionAdequacyKernel_package`
- `visible_projection`: `ExchangeVisibleUnion`。これは preservation されても adequacy を決定しない。
- `protected_structure`: path-indexed branch incidence, reflected repair-frontier singleton, branch-local support-lift closure。
- `exactness_or_minimality_claim`: pass 側は branch-local lift closure が hit witness を保存する exact transport condition。fail 側は missing reflected singleton witness。
- `nonfaithfulness_or_failure_mode`: visible component-union projection は branch-reflection adequacy と repair-transversal transport に faithful ではない。
- `previous_cycle_delta`: Cycle 71 の selected branch-reflection failure と Cycle 72 の first-missed branch scanを、positive adequacy kernel へ統合する。
- `genius_potential`: no
- `genius_target`: none
- `genius_support_role`: none

## 関連

- `research/ideas/g-aat-quality-surface-01-curvature-basis-exchange.md`
- `research/ideas/g-aat-quality-surface-01-naive-refinement-support-counterexample.md`
- `research/ideas/g-aat-quality-surface-01-branch-transversal-scan-kernel.md`

## 進捗ログ

- 2026-06-22: Cycle 73 候補として作成。
