---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: obstruction / repair-potential / traceability / invariance / quality-surface
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle33
tags: [quality-surface, repair, support, source-ref, obstruction, exactness]
created: 2026-06-20
cycle: 33
lean: research/lean/ResearchLean/AG/QualitySurface/SupportedTokenMismatchObstruction.lean
---

# Supported-token mismatch obstruction: frontier exact but source-ref non-exact

## 主張

Cycle 31 の `SupportLocalSourceRefRepair` が保証する frontier restriction は、source-ref exact visualization を保証しない。
declared storage support 上に `none` ではない token を供給し、support 外 source-ref table を保存する repair action を作る。
この action は support-local であり、

```text
post frontier = pre frontier ∧ ¬ repairSupport
```

を満たす。したがって post frontier は空になる。

しかし support 内 storage に supplied full packet と異なる source-ref token を入れるため、full packet との
source-ref table component defect が残る。visible packet / tuple surface と frontier collapse は成功して見えるが、
packet holonomy は nonzero であり、source-ref exact visualization は失敗する。

## 候補種別

`orientation`

## 依拠

- Cycle 23: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceHolonomyPacket.lean`
- Cycle 24: `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 25: `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`
- Cycle 29: `research/lean/ResearchLean/AG/QualitySurface/SourceRefTableLawObstruction.lean`
- Cycle 31: `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean`
- Cycle 32: `research/lean/ResearchLean/AG/QualitySurface/OutsideSupportMutationObstruction.lean`

## 非自明性

Cycle 32 は support 外 mutation により frontier formula 自体が壊れることを示した。
この候補は逆に、frontier formula が成立しても protected token identity が間違えば source-ref exactness は壊れることを示す。
単なる token swap ではなく、support-local repair、post frontier collapse、visible flatness、component table defect、
lossy packet-to-tuple visualization、non-exactness を同一 finite witness に束ねる。

## 数学的興味

repair success は「missing が消える」ことと「正しい source-ref token に戻る」ことに分かれる。
この候補は frontier calculus と source-ref exactness の独立性を、support 内 token identity obstruction として局所化する。

## GOAL への前進

support-local repair theorem の限界を exact visualization 側から鋭くし、repair-potential / traceability / obstruction の
protected boundary を進める。

## SCORE 見込み

- `score_reason`: Cycle 31 の positive frontier theorem と Cycle 32 の outside-support obstruction に対し、frontier 成功と source-ref exactness failure を分離する sharp obstruction として base 65 を見込む。frontier collapse、visible flatness、protected table defect、lossy visualization を同一 witness に入れるため、単なる token mismatch にはしない。Cycle 29 の token identity obstruction と近いため、G2 で当初見込みの 70 から 65 に下げた。
- `dullness_risk`: medium。Cycle 29 の token identity obstruction の焼き直しになる危険があるため、support-locality と frontier restriction success を明示的に証明対象へ入れる。
- `proof_or_evidence_plan`: wrong-token repair action、support-locality、frontier restriction formula、post frontier collapse、visible packet / tuple equivalence、storage source-ref table component defect、packet holonomy defect、lossy visualization、source-ref exact visualization failure、package theorem を Lean で証明する。

## CS / SWE への帰結

repair dashboard が repair frontier の collapse だけを見ると、wrong source-ref token を入れた repair を成功と誤読する。
loss-aware visualization には frontier state だけでなく source-ref token identity / packet holonomy を含める必要がある。

## 証明・根拠の見込み

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/SupportedTokenMismatchObstruction.lean`

Planned declarations:

- `supportedTokenMismatchRepairAction`
- `supportedTokenMismatchRepairPacket`
- `supportedTokenMismatch_supportLocal`
- `supportedTokenMismatch_frontierRestriction_holds`
- `supportedTokenMismatch_postFrontier_empty`
- `supportedTokenMismatch_visiblePacketSurface`
- `supportedTokenMismatch_visibleTupleSurface`
- `supportedTokenMismatch_storageSourceRefTableDefect`
- `supportedTokenMismatch_storageSourceRefTableComponentDefect`
- `supportedTokenMismatch_hasPacketHolonomyDefect`
- `supportedTokenMismatch_lossyPacketToTupleVisualization`
- `supportedTokenMismatch_not_sourceRefExactVisualization`
- `supportedTokenMismatchObstruction_package`

Local G3 checks:

- `focused Lean check: ResearchLean/AG/QualitySurface/SupportedTokenMismatchObstruction.lean`: pass
- `Research package build`: pass
- `lake env lean .tmp/supported_token_mismatch_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; `supportedTokenMismatch_frontierRestriction_holds` is the full all-atom frontier formula, not only empty-frontier collapse, and the witness is a repair action obstruction rather than a transport token-swap restatement

## 審判メモ

- 厳密性: `accept`、base 65。Cycle 29 の token-swap transport の名前替えではなく、partial packet への declared repair action として `SupportLocalSourceRefRepair` と frontier restriction success を同一 witness に入れる点が差分。`frontierRestriction_holds` を空 frontier だけに弱めず、wrong token と full packet の storage table defect を明示すること。
- 研究価値: `accept`、base 65。repair success を missing/frontier collapse と正しい source-ref token identity に分離し、Cycle 31/32/29 を repair law の二層性として圧縮する。
- repo 全体価値: `accept`、base 65。AAT quality surface、loss-aware visualization、repair-potential、Research report の obstruction 節に自然に接続する。ただし wrong-token witness だけでは弱く、support-locality、frontier restriction 成功、exactness failure を同一 theorem package に入れること。

## 関連

- `research/ideas/g-aat-quality-surface-01-outside-support-mutation-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-table-law-sharp-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-support-local-repair-frontier-restriction.md`

## 進捗ログ

- 2026-06-20: Cycle 33 G1 で作成。二つの G1 候補生成が同系統候補を上位に挙げた。
- 2026-06-20: G2 三審判すべて `accept`。全員 base 65 と判定したため、期待 SCORE を 65 * 2.0 = 130 に下げて picked。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness が pass。
- 2026-06-20: G3 independent axiom audit / formalization-quality audit pass。
