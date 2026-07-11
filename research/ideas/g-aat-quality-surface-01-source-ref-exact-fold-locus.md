---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: traceability / obstruction / invariance / certificate-transport / quality-surface
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle27
tags: [quality-surface, source-ref, exact-visualization, fold-locus, repair]
created: 2026-06-20
cycle: 27
lean: research/lean/ResearchLean/AG/QualitySurface/SourceRefExactFoldLocus.lean
---

# Source-ref exact fold-locus propagation and repair exit

## 主張

Packet-induced tuple pair に対して、visible tuple visualization は一致するが source-ref exact visualization は
失敗する locus を `SourceRefExactFoldLocus` として定義する。この fold locus は、visible equivalence と
packet-level protected holonomy defect の組と同値である。fold locus の伝播は packet zero-holonomy 単独ではなく、
visible-compatible な source-ref exact leg に沿って主張する。
さらに、Cycle 25 の supplied exact storage repair は full/partial の fold locus から exit し、full/repaired
pair は source-ref exact になる。

## 候補種別

`closure`

## 依拠

- Cycle 24: `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 25: `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`
- Cycle 26: `research/lean/ResearchLean/AG/QualitySurface/ComponentDefectPropagation.lean`

## 非自明性

単なる `¬ SourceRefExactVisualization` の再掲ではなく、visible equality、packet holonomy defect、
zero-leg propagation、component-defect obstruction、repair exit をひとつの fold-locus calculus としてまとめる。
これにより lossy visualization は点例ではなく、finite relation として扱える。

## 数学的興味

source-ref exactness は、visible packet-to-tuple quotient が protected source-ref holonomy を失う fold を検出する。
fold locus は visible surface と protected certificate geometry のずれを表し、repair action によって locus から
出られることが finite theorem として読める。

## GOAL への前進

Cycle 24 の lossy/exact detector、Cycle 25 の repair exit、Cycle 26 の component propagation を接続し、
visible layer と protected layer を混同せずに source-ref exact fold-locus frontier を閉じる。

## SCORE 見込み

- `score_reason`: definition + characterization + source-ref-exact leg propagation + component obstruction + repair exit が揃えば base 60。Cycle 24/25/26 に近い finite fold calculus なので 70 以上には置かない。
- `dullness_risk`: medium。full/partial witness の再掲だけなら低価値。zero-leg propagation と repair exit を必須にする。
- `proof_or_evidence_plan`: 新規 Research Lean file で `SourceRefExactFoldLocus` を定義し、Cycle 24 の exactness iff から `visible ∧ HasSourceRefPacketHolonomyDefect` との同値を証明する。left/right propagation は `SourceRefExactVisualization` leg に沿って visible と protected zero の両方を明示し、Cycle 25 の `storageRepairPacket_sourceRefExactVisualization` で repair exit を示す。

## CS / SWE への帰結

同じ visible tuple visualization に見える packet pair でも、source-ref exactness で fold locus にいるかどうかを
分離できる。repair action が fold locus から出る場合、UI / report は visible surface だけではなく protected
source-ref exactness を drill-down する必要がある。

## 証明・根拠

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactFoldLocus.lean`

Declarations:

- `SourceRefExactFoldLocus`
- `sourceRefExactFold_iff_visible_packetDefect`
- `full_partial_sourceRefExactFoldLocus`
- `sourceRefExactFoldLocus_propagates_left_of_exact`
- `sourceRefExactFoldLocus_propagates_right_of_exact`
- `packetComponentDefect_obstructs_sourceRefExactFold`
- `propagatedPacketDefect_obstructs_sourceRefExactFold`
- `storageRepairPacket_exits_sourceRefExactFoldLocus`
- `sourceRefExactFoldLocus_package`

Local G3 checks:

- `focused Lean check: ResearchLean/AG/QualitySurface/SourceRefExactFoldLocus.lean`: pass
- `Research package build`: pass
- `lake env lean .tmp/source_ref_exact_fold_locus_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; propagation uses source-ref exact legs and does not claim packet-zero-only visible propagation

visible_projection: packet-induced visible tuple surface。

protected_structure: packet obligation / repair frontier / source-ref table、packet holonomy defect、tuple protected data。

exactness_or_minimality_claim: visible equivalence の下で fold locus は packet zero holonomy の失敗と同値。伝播には source-ref exact leg を仮定する。

nonfaithfulness_or_failure_mode: visible tuple equality は source-ref exact classes を識別できない。exact repair action は visible support surface を保ったまま fold locus から出る。

previous_cycle_delta: Cycle 26 の component propagation を exact visualization の fold-locus frontier へ適用する。

## 審判メモ

- 厳密性: initial `revise`; packet zero holonomy 単独では visible equivalence を運べないため、source-ref exact / visible-compatible leg に沿う propagation へ修正し、base 60 に下げることを要求。修正後 `accept`。
- 研究価値: initial `accept` at base 70; 修正後は source-ref exact leg propagation として base 60 / final 120 で `accept`。
- repo 全体価値: initial `revise`; visible layer と protected holonomy layer の分離を明示することを要求。修正後 base 60 / final 120 で `accept`。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-exact-visualization.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-repair-holonomy-annihilation.md`
- `research/ideas/g-aat-quality-surface-01-component-holonomy-defect-propagation.md`

## 進捗ログ

- 2026-06-20: Cycle 27 G1 で作成。
- 2026-06-20: G3.5 sync audit pass。candidate card / Lean declarations / report entry は同期済み。
- 2026-06-20: G4 SCORE audit confirm。base 60、evidence multiplier 2.0、penalty 0、final SCORE 120。
