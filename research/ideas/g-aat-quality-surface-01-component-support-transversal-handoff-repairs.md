---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure / bridge
capability_category: repair-potential / obstruction / traceability / computability / invariance / certificate-transport
expected_base_score: 82
expected_evidence_multiplier: 2.0
expected_final_score: 164
evidence_stage: proved-in-research
rival_advantage: ADL / conformance tools can display a failing route or component, but this candidate turns protected source-ref handoff component support into a repair transversal theorem and a nonfaithfulness witness for visible one-component repair views.
origin: cycle-64
tags: [quality-surface, source-ref, handoff, repair, transversal]
created: 2026-06-21
cycle: 64
lean: research/lean/ResearchLean/AG/QualitySurface/HandoffRepairTransversal.lean
---

# Component-support transversal theorem for handoff repairs

## 主張

selected finite `SourceRefHandoffAtlas` に対して、Cycle 63 の
`HandoffComponentSupport atlas component` を repair necessity の hypergraph として読む。

repair plan は、触る component support `touched : BridgeComponent -> Prop` と、宣言された
component-support clearance `clears : BridgeComponent -> Prop` を持つ。これは actual runtime repair result
ではなく、selected finite handoff atlas 上で「この component support を clear したと主張できる」という
bounded certificate predicate である。基本境界として、component を clear する repair はその component を
触っていなければならない。

```text
clears_only_if_touched : forall component, clears component -> touched component
```

declared residual component support は

```text
DeclaredResidualComponentSupport atlas plan component :=
  HandoffComponentSupport atlas component and not plan.clears component
```

として読む。したがって、declared component-support clearance

```text
DeclaredHandoffRepairClears atlas plan :=
  forall component, HandoffComponentSupport atlas component -> plan.clears component
```

を満たす repair plan は、もとの `HandoffComponentSupport` をすべて hit しなければならない。

さらに `component-complete` regime、すなわち touched した supported component は必ず clear される regime では、
declared clearance と component support transversal が同値になる。

最後に、Cycle 63 の three one-component deletion witnesses に対して、support-only / trace-only /
repair-frontier-only の singleton repair support がそれぞれ minimal transversal になることを Lean で固定する。
これにより、visible one-component repair shape は同じでも、必要な protected component repair support は
support / trace / repair-frontier で異なることを示す。SCORE の核は、基本 hitting statement そのものではなく、
この exact component-support iff、singleton minimality、lossful visible repair shape nonfaithfulness に置く。

主張は bounded source-ref handoff、selected finite atlas、existing heterogeneous route state、
finite `BridgeComponent` vocabulary、declared component-level repair plan に相対化する。runtime repair synthesis、
global minimal repair planning、source extraction completeness、ArchMap correctness、arbitrary route enumeration、
実コード全体の品質判定は主張しない。

## 候補種別

`closure / bridge`

## 依拠

- Cycle 61: order-independent source-ref handoff obstruction locus
- Cycle 62: repair/transport commutator bridge for handoff obstruction loci
- Cycle 63: source-ref handoff component support bitset and law minimality matrix
- Cycle 1: minimal-support hitting theorem for local repair

## 非自明性

単に `HandoffComponentSupportNonempty` と `HandoffObstructionLocusNonempty` の同値を言い換えるだけなら価値はない。
本候補の非自明性は、declared component-support clearance という boundary を明示したうえで、
三 deletion witness の exact component-support iff、singleton minimal transversal、visible one-component repair shape の
非忠実性を同じ theorem package に入れる点にある。基本 hitting theorem は入口であり、SCORE の核ではない。

## 数学的興味

component support bitset は診断結果ではなく、repair が満たすべき transversal condition として読める。
obstruction locus、component support、repair exactness、minimal transversal が同一有限対象で結ばれることで、
Quality Surface の repair-potential が hypergraph duality として現れる。

## GOAL への前進

Cycle 63 で得た component support invariant を、repair-potential / obstruction / traceability / computability の
共通 object へ進める。これにより、Quality Geometry が failure display ではなく repair reachability geometry を
持つことを示す。

## ライバルに対する有効性

ADL、architecture conformance checker、metric dashboard は failing component や route mismatch を表示できる。
しかし、その表示から「どの protected component support を必ず hit しなければ obstruction が残るか」を
Lean-proved theorem として導くわけではない。さらに、visible one-component repair shape が同じでも
support / trace / repair-frontier の必要 repair support が違うことを theorem として固定しない。

## SCORE 見込み

- `score_reason`: declared clearance theorem、component-complete iff、three deletion witness の exact component-support iff、minimal singleton transversal、visible repair view nonfaithfulness まで通れば、Cycle 63 の support invariant を repair necessity calculus に変換するため strict base 82 を見込む。
- `dullness_risk`: 「support を hit せよ」という一般 hitting-set の名前替えに落ちる危険がある。actual repaired atlas や runtime repair result は主張せず、declared clearance、singleton minimality、visible repair view nonfaithfulness を証拠の核にする。
- `proof_or_evidence_plan`: Lean で `HandoffRepairPlan`、`DeclaredResidualComponentSupport`、`DeclaredHandoffRepairClears`、`HandoffRepairTransversal`、`missedHandoffComponentSupport_survives`、`hitsEveryHandoffComponentSupport_of_declaredClearance`、`declaredClearance_iff_hitsEvery_of_componentComplete`、`*_componentSupport_iff`、singleton deletion minimal transversal、`oneComponentRepairShape_not_faithful_to_repairTransversal` を証明する。

## CS / SWE への帰結

repair UI や review report が「この component を直すべき」と表示するだけでは不十分である。
必要なのは、source-ref handoff obstruction locus が要求する repair transversal を保持し、
visible shape が同じ repair 候補でも protected component support が違う場合を区別することである。

## 証明・根拠の見込み

Lean file: `research/lean/ResearchLean/AG/QualitySurface/HandoffRepairTransversal.lean`

予定 declaration:

- `HandoffRepairSupport`
- `HandoffRepairPlan`
- `DeclaredResidualComponentSupport`
- `DeclaredHandoffRepairClears`
- `HandoffRepairTransversal`
- `ComponentCompleteHandoffRepairPlan`
- `missedHandoffComponentSupport_survives`
- `hitsEveryHandoffComponentSupport_of_declaredClearance`
- `declaredClearance_of_hitsEveryHandoffComponentSupport_of_componentComplete`
- `declaredClearance_iff_hitsEvery_of_componentComplete`
- `supportLawDeletion_componentSupport_iff`
- `traceLawDeletion_componentSupport_iff`
- `repairFrontierLawDeletion_componentSupport_iff`
- `MinimalHandoffRepairTransversal`
- `supportLawDeletion_minimalTransversal`
- `traceLawDeletion_minimalTransversal`
- `repairFrontierLawDeletion_minimalTransversal`
- `oneComponentRepairShape_not_faithful_to_repairTransversal`
- `handoffRepairTransversal_package`

証明方針:

1. `clears_only_if_touched` により、missed component support は declared residual support として残ることを示す。
2. declared clearance なら、各 supported component は clear され、したがって touched されることを示す。
3. component-complete regime では、touched transversal から clear が導かれるため、clearing と hitting が同値になる。
4. Cycle 63 の support / trace / repair-frontier deletion witnesses について、component support が singleton であることを cases で示す。
5. singleton support が minimal transversal であることを証明する。
6. singleton repair shape は同じでも、support-only と trace-only の required repair support は等しくないことを非忠実性 witness として固定する。

## 審判メモ

- 厳密性: G2-A revise -> accept / base 80 / genius no。declared component-support clearance へ相対化し、singleton minimality と visible repair shape nonfaithfulness を SCORE の核に置いた。
- 研究価値: G2-B accept / base 82 / genius no。repair transversal、survival、clearing iff、visible repair nonfaithfulness が揃えば GOAL の repair reachability geometry を増やす。
- repo 全体価値: G2-C accept / base 85 provisional / genius no。AAT / Lean / paper / future Tooling surface に価値があるが、一般 hitting-set の名前替えを避ける必要がある。
- ライバル比較: G2-D accept / base 85 / genius no。ADL / conformance style の failure display を theorem-level repair transversal condition へ持ち上げる差分がある。

## G2 revise response

- G2-A 厳密性: revise、base 70 provisional、genius no。core transversal theorem は
  `PostRepairComponentSupport := support and not clears` の定義展開に近く、actual repaired atlas / runtime repair result と
  誤読される危険がある。SCORE の核を exact component-support iff、singleton minimality、lossful visible repair shape
  nonfaithfulness へ明示的に移す必要がある。
- 対応: `PostRepairHandoffLocusEmpty` という語を避け、`DeclaredHandoffRepairClears` と
  `DeclaredResidualComponentSupport` として bounded certificate predicate を明示した。expected base を 82 に下げ、
  G3 の必須証拠を `*_componentSupport_iff`、`MinimalHandoffRepairTransversal`、三 deletion witness の
  singleton minimality、`oneComponentRepairShape_not_faithful_to_repairTransversal` に絞った。
- G2-A 再審判: accept、base 80、genius no。runtime / post-repair result を避け、declared component-support
  clearance に相対化し、SCORE の核を exact component-support iff、singleton minimality、visible repair shape
  nonfaithfulness に移したため、G3 に進める水準と判定された。

## G3 evidence

- Lean file: `research/lean/ResearchLean/AG/QualitySurface/HandoffRepairTransversal.lean`
- aggregate import: `research/lean/ResearchLean.lean`
- local checks:
  - `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/HandoffRepairTransversal.lean`: pass
  - `cd research/lean && lake env lean ResearchLean.lean`: pass
  - `cd research/lean && lake build ResearchLean`: pass
  - `lake build`: pass。既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。
  - `lake env lean .tmp/handoff_repair_transversal_axioms.lean`: pass
  - target `axiom|admit|sorry|unsafe` scan: no matches

証明済み declaration:

- `HandoffRepairSupport`
- `HandoffRepairPlan`
- `DeclaredResidualComponentSupport`
- `DeclaredHandoffRepairClears`
- `HandoffRepairTransversal`
- `ComponentCompleteHandoffRepairPlan`
- `missedHandoffComponentSupport_survives`
- `hitsEveryHandoffComponentSupport_of_declaredClearance`
- `declaredClearance_of_hitsEveryHandoffComponentSupport_of_componentComplete`
- `declaredClearance_iff_hitsEvery_of_componentComplete`
- `supportLawDeletion_componentSupport_iff`
- `traceLawDeletion_componentSupport_iff`
- `repairFrontierLawDeletion_componentSupport_iff`
- `MinimalHandoffRepairTransversal`
- `singletonRepairSupport`
- `supportLawDeletion_minimalTransversal`
- `traceLawDeletion_minimalTransversal`
- `repairFrontierLawDeletion_minimalTransversal`
- `VisibleRepairShape`
- `visibleOneComponentRepairShapeProjection`
- `support_trace_same_visibleOneComponentRepairShape`
- `support_trace_transversalSupport_distinct`
- `oneComponentRepairShape_not_faithful_to_repairTransversal`
- `handoffRepairTransversal_package`

公理検査の実績:

- axiom-free: repair support / plan / declared residual / declared clearance / transversal / component-complete /
  missed survival / declared clearance to transversal / component-complete iff / minimal support definitions /
  visible shape projection / protected support distinctness。
- standard `propext` only: `*_componentSupport_iff`、singleton minimal transversal、
  `oneComponentRepairShape_not_faithful_to_repairTransversal`、package theorem。
- `sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` はない。

G3 公理検査: pass。`sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` はない。
`propext` は finite `BridgeComponent` case split と Prop-valued support predicate の iff / simplification 側だけに残る。
singleton witness は明示的な `support` / `trace` / `repairFrontier` であり、minimality は explicit transversal argument から出ている。

G3 形式化品質監査: pass。

- 初回 revise: `VisibleOneComponentRepairShape` が Prop predicate で、明示的な lossful projection ではなかった。
- 対応: Lean 側に `VisibleRepairShape` と `visibleOneComponentRepairShapeProjection` を追加し、
  `oneComponentRepairShape_not_faithful_to_repairTransversal` を projection output equality と
  protected support inequality の形へ強めた。
- 再監査: pass。`HandoffRepairPlan.clears` は declared clearance であり、repaired atlas を主張しない。
  三 deletion witness は exact component-support iff と singleton inclusion-minimal transversal を持ち、
  visible-shape nonfaithfulness は明示的な projection equality と protected support inequality で述べられている。

## G3.5 planned sync

G4 後の report には、Cycle 64 section として次の declaration 名を載せる。

- `HandoffRepairPlan`
- `DeclaredResidualComponentSupport`
- `DeclaredHandoffRepairClears`
- `HandoffRepairTransversal`
- `ComponentCompleteHandoffRepairPlan`
- `missedHandoffComponentSupport_survives`
- `hitsEveryHandoffComponentSupport_of_declaredClearance`
- `declaredClearance_iff_hitsEvery_of_componentComplete`
- `supportLawDeletion_componentSupport_iff`
- `traceLawDeletion_componentSupport_iff`
- `repairFrontierLawDeletion_componentSupport_iff`
- `supportLawDeletion_minimalTransversal`
- `traceLawDeletion_minimalTransversal`
- `repairFrontierLawDeletion_minimalTransversal`
- `visibleOneComponentRepairShapeProjection`
- `support_trace_same_visibleOneComponentRepairShape`
- `support_trace_transversalSupport_distinct`
- `oneComponentRepairShape_not_faithful_to_repairTransversal`
- `handoffRepairTransversal_package`

## G4 SCORE audit

```text
score_verdict: confirm
base_score: 82
evidence_multiplier: 2.0
penalty: 0
final_score: 164
category: repair-potential / obstruction / traceability / computability / invariance / certificate-transport
genius_verdict: downgrade-to-normal
```

G4 は proposed base 82 と Lean-proved evidence multiplier x2.0 を confirm した。
G2-A は strict base 80 だったが、revise 後の Lean evidence が exact component-support iff、
三 singleton minimal transversals、projection equality plus protected support inequality を満たし、
G2-B の base 82 と G2-C/D の base 85 側を支えているため、base 82 は過大ではないと判定された。

GOAL delta: Cycle 63 の component support invariant を、declared repair clearance、component-complete iff、
singleton minimal transversal、visible repair shape nonfaithfulness を持つ repair necessity calculus へ進める。

Rival delta: ADL / conformance tools の failure display に対し、protected component support を必ず hit する必要性と、
同じ one-component visible shape が異なる repair support を隠すことを Lean theorem として固定した。

Report sync: `research/reports/G-aat-quality-surface-01.md` は total 8490、proved artifacts 64、
Cycle 64 section、Next Frontier の残り 1510 SCORE として更新する。

## G1 候補 pool

四つの独立候補生成サブエージェントは、重複を除いて次を主要候補として出した。

- Component-support transversal theorem / handoff component support hitting theorem for exact repairs
- Handoff repair hitting theorem with ADL-view nonfaithfulness
- Refinement-invariant source-ref handoff obstruction locus
- Exact refinement invariance for source-ref handoff obstruction loci
- Handoff atlas refinement invariance / support-surjective refinement invariance
- Finite handoff holonomy-obstruction basis theorem
- Finite Cech-style holonomy-obstruction exactness package
- Law-refinement commutator curvature for handoff atlases

三体が repair hitting / transversal theorem を第一候補として出したため、本 cycle ではこれを picked とする。
refinement invariance と finite basis theorem は後続 frontier に残す。

## Genius potential

この候補単体は `genius unlock` ではない。finite holonomy-obstruction repair-transversal duality や
Cech-style exactness package の将来 support cycle にはなりうるが、今回は通常 SCORE 候補として扱う。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-obstruction-locus.md`
- `research/ideas/g-aat-quality-surface-01-repair-transport-handoff-obstruction-bridge.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-component-support-bitset.md`

## 進捗ログ

- 2026-06-21: cycle 64 G1 候補 pool から G2 審判対象として作成。
- 2026-06-21: G2-A revise を受け、actual repair result ではなく declared component-support clearance として主張を相対化し、SCORE の核を singleton minimality と visible repair shape nonfaithfulness へ移した。
- 2026-06-21: Lean proof を固定し、local build と axiom scan を通過。G3 独立監査待ち。
- 2026-06-21: G3 公理検査 / 形式化品質監査 / G3.5 同期監査を通過。G4 SCORE 監査で +164 を confirm。
