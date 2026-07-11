---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: traceability/certificate-transport/invariance/computability/quality-surface
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle24
tags:
  - source-ref
  - exact-visualization
  - packet-to-tuple
created: 2026-06-20
---

# Source-ref exactness detects lossy packet-to-tuple visualization

## 主張

packet-induced tuple visualization が source-ref exact であることを、visible tuple surface と tuple-level
zero holonomy defect の組として定式化する。packet-to-tuple bridge では、tuple zero holonomy と packet
zero holonomy が同値であり、visible tuple surface だけでは full / partial packet の source-ref packet
holonomy を隠す。したがって source-ref exactness は lossy packet-to-tuple visualization を検出する条件である。

主張は supplied finite source-ref packets、finite code atom vocabulary、explicit packet-to-tuple bridge、
selected endpoint tuple に相対化する。source extraction completeness、ArchMap correctness、canonical
packet extractor、任意 codebase traceability、実コード全体の品質判定は結論しない。

## 候補種別

`bridge`

## 依拠

- `research/lean/ResearchLean/QualitySurface/SourceRefTupleBridge.lean`
- `research/lean/ResearchLean/QualitySurface/SourceRefTokenIdentityReflection.lean`
- `research/lean/ResearchLean/QualitySurface/TupleHolonomyDefect.lean`
- `research/lean/ResearchLean/QualitySurface/CodebaseTraceHolonomyPacket.lean`
- `CodebaseTraceHolonomyPacket.NoSourceRefPacketHolonomyDefect`
- `CodebaseTraceHolonomyPacket.SourceRefPacketHolonomyDefect`
- `CodebaseTraceHolonomyPacket.noPacketHolonomy_projects_to_noTupleHolonomy`
- `SourceRefTokenIdentityReflection.projectedTraceField_reflects_sourceRefTable`

## 非自明性

Cycle 23 は packet defect が tuple defect へ写ることを示した。この候補はそれを detector にし、
packet-induced tuple の zero holonomy が packet-level zero holonomy と同値であることを示す。
これにより、visible tuple surface が同じでも source-ref exactness を欠く visualization は lossy であると
定理として判定できる。

単なる Cycle 23 の再掲にしないため、次を required evidence にする。

- `TupleVisibleVisualizationEquivalent` と `SourceRefExactVisualization`。
- packet-induced tuple zero holonomy iff packet zero holonomy。
- `LossyPacketToTupleVisualization` witness。
- full / partial packet pair が visible tuple surface では一致するが source-ref exact visualization ではないこと。
- packet component defect が source-ref exact visualization を阻害する theorem。
- source-ref table defect は token identity reflection により tuple trace-field defect として検出されること。

## 数学的興味

可視化の exactness を「見た目が同じか」ではなく「source-ref protected data へ戻れるか」として定義する。
これは Quality Surface の reading / projection がどこで hidden holonomy を落とすかを判定する基礎になる。

## GOAL への前進

traceability、certificate-transport、invariance、loss-aware visualization を接続し、finite codebase trace
example を exact-vs-lossy reading の theorem として強化する。

## SCORE 見込み

- `score_reason`: G2-B は base 70 を認めたが、G2-A/C が Cycle 16/23 に近い immediate-corollary risk を
  指摘したため、revised candidate は base 60 / final 120 に下げる。
- `dullness_risk`: medium。`sourceRefOptionMap_eq_iff` や Cycle 23 projection theorem の再掲に落ちないよう、
  zero-holonomy iff、lossy visualization witness、exactness obstruction theorem を required evidence にする。
- `proof_or_evidence_plan`: `SourceRefExactVisualization.lean` に exact / lossy visualization relation、
  zero-holonomy iff、full/partial lossy witness、component obstruction、package theorem を置く。

## CS / SWE への帰結

loss-aware visualization や drill-down report では、tuple visible surface だけでは source-ref packet holonomy を
見落とす。source-ref exactness を要求すると、packet-level source-ref table / repair frontier の defect を
tuple protected data の defect として検出できる。

## 証明・根拠

Lean proof は `research/lean/ResearchLean/QualitySurface/SourceRefExactVisualization.lean` に閉じた。
`research/lean/ResearchLean.lean` はこの Research evidence file を import する。

主要 theorem / declaration:

- `TupleVisibleVisualizationEquivalent`
- `SourceRefExactVisualization`
- `LossyPacketToTupleVisualization`
- `tupleZeroHolonomy_reflects_packetZeroHolonomy`
- `packetTuple_zeroHolonomy_iff_packetZeroHolonomy`
- `sourceRefExactVisualization_iff_visible_packetZeroHolonomy`
- `packetHolonomyDefect_obstructs_sourceRefExactVisualization`
- `lossyVisualization_not_sourceRefExact`
- `sourceRefTableDefect_detected_as_tupleTraceFieldDefect`
- `full_partial_packetTuple_lossyVisualization`
- `full_partial_packetTuple_not_sourceRefExact`
- `full_partial_packetTuple_traceFieldDefect_detected`
- `sourceRefExactVisualization_package`

固定された内容:

- `SourceRefExactVisualization` は visible packet-induced tuple equivalence と tuple-level
  `NoTupleHolonomyDefect` の組であり、packet zero defect を定義へ埋め込まない。
- `packetTuple_zeroHolonomy_iff_packetZeroHolonomy` は、packet-induced tuple zero holonomy と packet-level
  zero holonomy defect の同値を示す。
- `tupleZeroHolonomy_reflects_packetZeroHolonomy` は、tuple trace-field equality から
  `projectedTraceField_reflects_sourceRefTable` によって source-ref table equality を反射する。
- `LossyPacketToTupleVisualization` と `full_partial_packetTuple_lossyVisualization` は、visible tuple surface は
  一致するが packet holonomy defect が残る finite witness を固定する。
- `packetHolonomyDefect_obstructs_sourceRefExactVisualization` は、任意 packet component defect が source-ref
  exact visualization を阻害することを示す。
- `sourceRefTableDefect_detected_as_tupleTraceFieldDefect` は、source-ref table defect が tuple trace-field
  defect として検出されることを示す。

検証:

- `lake env lean research/lean/ResearchLean/QualitySurface/SourceRefExactVisualization.lean`: pass。
- `lake build ResearchLean`: pass。
- `.tmp/source_ref_exact_visualization_axioms.lean` の `#print axioms`: listed declarations are all
  `does not depend on any axioms`。`sorryAx`、`propext`、`Classical.choice`、`Quot.sound` は出ていない。
- 対象 Lean file の `axiom` / `admit` / `sorry` / `unsafe` / `Classical` / `choice` / `propext` /
  `Quot.sound` scan: no hits。
- hidden / bidirectional Unicode scan: no hits。
- G3 Lean 形式化品質監査: pass。`SourceRefExactVisualization` は tuple-zero 側の条件であり、
  `packetTuple_zeroHolonomy_iff_packetZeroHolonomy` の逆向きは token identity reflection を使う。

## 審判メモ

- 厳密性: G2-A は初回 revise、base 60。`SourceRefExactVisualization` が packet zero defect を定義へ
  埋め込むと tautological になるため、tuple zero holonomy 側で定義し、packet zero defect は theorem として
  反射することを required evidence とした。
- 厳密性再審判: G2-A は revised card / Lean proof を accept、base 60 / final 120。
- 研究価値: G2-B は accept、base 70。exact-vs-lossy visualization criterion としての価値を認めた。
- repo 全体価値: G2-C は accept、base 60。Cycle 13/16/22/23 に近いため score は抑えるが、
  loss-aware visualization の report / paper seed として有効と判定した。
- SCORE 監査: G4 は confirm、base 60 / evidence multiplier 2.0 / penalty 0 / final 120。

## 関連

- `research/ideas/g-aat-quality-surface-01-source-ref-tuple-bridge.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-packet-transport.md`
- `research/ideas/g-aat-quality-surface-01-finite-codebase-trace-holonomy-packet.md`
- `research/ideas/g-aat-quality-surface-01-tuple-holonomy-defect-invariant.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-20: Cycle 24 candidate card 作成。
- 2026-06-20: G2-A revise を反映し、`SourceRefExactVisualization` を packet zero defect ではなく
  tuple zero holonomy 側で定義する方針に修正し、expected score を base 60 / final 120 に下げた。
- 2026-06-20: `SourceRefExactVisualization.lean` を追加し、単体 Lean、`ResearchLean`、axiom harness、
  G3 Lean 形式化品質監査を通した。
- 2026-06-20: G4 SCORE 監査 confirm。report の Cycle 24 と Current SCORE を total 2920 に更新した。
