---
status: picked
goal: G-sft-conway-01
exploration_role: closer / obstruction / unifier / wildcard convergence
candidate_type: bridge
capability_category: refinement-order, support-receiver, conway-obstruction, finite-witness, receiver
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 2
score_reason: Cycle 1 の Prop-valued zero/nonzero witness を、cover refinement と support-nerve fork receiver 語彙へ安全に載せ替える。true H1 でも full nerve map でもなく、最初の receiver vocabulary bridge として中程度に前進する。
mathematical_interest: Conway 障害の住む場所を「複数 owner が見える」という例から、同じ communication block 上の support-nerve fork が単一 owner support に collapse しない failure として固定する。
goal_advancement: refinement-order と support receiver 語彙を固定する。common-refinement は singleton support edge の補助語彙に留まり、obstruction 判定との非自明な関係は次 cycle に残る。
dullness_risk: support edge や nerve という名前だけなら低価値。`SupportNerveObstructionReceiver ↔ ConwayObstructionWitness` と Cycle 1 examples の zero/nonzero receiver theorem が必要。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwaySupportReceiver.lean` に `CoverRefines`、`CommonRefinementSpan`、`SupportNerveEdge`、`SupportNerveFork`、`SupportNerveObstructionReceiver`、`supportReceiver_iff_conwayObstruction`、Cycle 1 atlas の receiver package を未証明穴なしで置く。
planned_theorem_names: CoverRefines, CommunicationOwnershipRefinement, communicationCompatible_iff_coverRefines, CommonRefinementSpan, SupportNerveEdge, SupportNerveFork, SupportNerveObstructionReceiver, supportReceiver_of_conwayObstruction, conwayObstruction_of_supportReceiver, supportReceiver_iff_conwayObstruction, compatible_no_supportReceiver, compatibleAtlas_noSupportReceiver, mismatchedAtlas_supportReceiver, reorgedAtlas_noSupportReceiver, refactoredAtlas_noSupportReceiver, selectedSupportReceiverPackage
rival_advantage: CODEOWNERS / org-network dashboard / AI review は mismatch を指摘できる。この candidate は selected finite witness を support-nerve edge/fork receiver theorem として保存する点に限定して差分を持つ。
visible_projection: communication block と ownership block の selected support relation。
protected_structure: independent communication/ownership cover data, support edge witness, same-communication fork, single-owner support failure。
exactness_or_minimality_claim: selected receiver levelでは `SupportNerveObstructionReceiver atlas ↔ ConwayObstructionWitness atlas`。true sheaf cohomology や full H1 は主張しない。
nonfaithfulness_or_failure_mode: ownership-indexed degeneracy では communication-to-ownership refinement が構成で入り、receiver が自明化する。
previous_cycle_delta: Cycle 1 の finite witness packageを、first receiver vocabularyに昇格する。
rival_stress_test: rival が同じ owner incidence tableを読めても、same-communication support fork と collapse failureを theoremとして保持できるか。
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, relative-nerve, support-receiver]
created: 2026-07-04
---

# Relative nerve support receiver

## 主張

`TwoCoverAtlas` 上に、cover refinement、common-refinement span、support-nerve edge、support-nerve fork を置く。
Cycle 1 の selected Conway obstruction は、同じ communication block 上に distinct ownership support edge が立ち、
その communication block が単一 owner support を持たないという `SupportNerveObstructionReceiver` と同値である。

## 候補種別

`bridge`

## 依拠

- `research/goals/G-sft-conway-01.md` の `G-sft-conway-01`
- Cycle 1 report: `research/reports/G-sft-conway-01.md`
- Lean evidence: `research/lean/ResearchLean/AG/SFT/ConwayTwoTopology.lean`

## 非自明性

Cycle 1 の finite witness を増やすのではなく、障害の受け皿を support-nerve fork として固定する。
common refinement は edge witness として存在するが、Conway 障害は common refinement の単純な不存在ではなく、
same communication block の owner support が単一 owner に collapse しない failure として表現される。

## 数学的興味

Conway 対応の mismatch を、relative nerve の 0/1 skeleton 上の support receiver へ移す。
これは将来の comparison functor failure や finite `C^1/B^1` quotient に入る前の、最小で安全な receiver である。

## GOAL への前進

`refinement-order`、`support-receiver`、`conway-obstruction`、`finite-witness` に正の増分を与える。
`common-refinement` は singleton edge の語彙導入に留まり、`nerve-map-mismatch` はまだ確定 claim としない。

## ライバルに対する有効性

Team Topologies、CODEOWNERS / org-network dashboard、AI review は owner mismatch を見つけられる。
この artifact は、その selected finite witness を support edge、same-communication fork、
single-owner collapse failure の Lean theorem package として保存する点に限って差分を持つ。

## SCORE 見込み

- `score_reason`: first receiver 語彙を固定し、Cycle 1 の witness を `SupportNerveObstructionReceiver ↔ ConwayObstructionWitness` として再配置するため base 60。
- `dullness_risk`: true H1 や full nerve functor を過大主張しない。support receiver の同値 theorem と finite examples を根拠にする。
- `proof_or_evidence_plan`: `cd research/lean && lake env lean ResearchLean/AG/SFT/ConwaySupportReceiver.lean`、`旧Research aggregate build`、`#print axioms` で検証する。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## CS / SWE への帰結

組織側 communication block と architecture 側 ownership support の不整合を、単なる表の差分ではなく、
support-nerve fork receiver として保持できる。reorg/refactor の後続操作を、この receiver を消す操作として
定式化する一般 criterion は次 cycle に残る。

## 証明・根拠の見込み

Lean file:

- `research/lean/ResearchLean/AG/SFT/ConwaySupportReceiver.lean`

Lean declarations:

- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationCompatible_iff_coverRefines`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownershipIndexedFromCommunication_refines`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportNerveEdge.singletonCommonRefinement`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportReceiver_of_conwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.conwayObstruction_of_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportReceiver_iff_conwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_noSupportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_noSupportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_noSupportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedSupportReceiverPackage`

## 審判メモ

- 厳密性: G2 A/B/D はいずれも revise。Lean 証拠は通るが、Cycle 1 witness の receiver 語彙への再包装に近い。
- 研究価値: base 85 は過大。true nerve / comparison functor / `C^1/B^1` quotient 以前の vocabulary bridge として base 60 に下げる。
- repo 全体価値: SFT 第V部 Conway 対応の足場として有用だが、`CommonRefinementSpan` は obstruction 判定にはまだ使われていない。
- ライバル比較: rival に対する差分は selected finite witness を Lean theorem package として保存する点に限定する。

## 関連

G1 closer / obstruction / unifier / wildcard はいずれも relative nerve support receiver または同等の common-refinement / receiver 化を Cycle 2 の picked 候補として推奨した。

## 進捗ログ

- 2026-07-04: 作成。`cd research/lean && lake env lean ResearchLean/AG/SFT/ConwaySupportReceiver.lean` と
  `cd research/lean && lake build ResearchLean.AG.SFT.ConwaySupportReceiver`、再実行後の `旧Research aggregate build` が通過。
  `#print axioms` では receiver 変換本体は axiom-free、finite example receiver 系は `propext` 依存。
  G2/G3 後、score を base 60 / final 120 に下方修正。
