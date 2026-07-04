# G-sft-conway-01 report

この report は `G-sft-conway-01` の research-loop 成果を、SFT 第V部 Conway 対応へ向けた
能力増分として記録する。GOAL 定義と active threshold は `research/GOALS.md` と tracking
Issue `#2962` を正本にする。

## Cycle 1 — 独立二被覆の正準有限 witness package

candidate: `research/ideas/g-sft-conway-01-independent-two-cover-witness-package.md`
candidate_type: `closure`
evidence_stage: `proved-in-research`
base_score: 75
evidence_multiplier: 2.0
penalty: 0
final_score: 150
category: `two-topology-comparison`, `conway-obstruction`, `finite-witness`,
  `reorg-refactor-duality`, `projection-nonfaithfulness`, `rival-separation`
goal_delta: communication cover と ownership cover を独立 selected data として持つ
  finite `TwoCoverAtlas` を置き、適合例の zero obstruction、split ownership に対する
  nonzero selected obstruction witness、reorg/refactor の二方向 zero repair、
  ownership-indexing による循環的自明化を Lean theorem package として固定した。
project_value_delta: SFT 第V部の予告を、AAT 本体を変更せず `Formal/AG/Research/SFT` 上の
  Lean-backed research surface へ動かした。
rival_delta: Team Topologies / mirroring 研究 / CODEOWNERS dashboard / org-network analysis /
  AI review は不一致を説明・可視化できるが、この cycle は独立二被覆上の zero/nonzero
  theorem package と、ownership を communication index から導くと obstruction が自明に消える
  という非忠実性を形式証拠として返す。
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayTwoTopology.lean` と
  `lake build FormalAGResearch` が通過。G3 形式化品質監査は pass。`#print axioms` では
  `selectedConwayTwoCoverWitnessPackage` と `mismatchedAtlas_nonzeroConwayObstruction` が
  `propext` に依存し、`ownershipIndexedFromCommunication_zeroConwayObstruction` は axiom-free。
  G3 公理検査は `propext` を標準的な Prop 外延性として許容した。
open_questions: refinement / common refinement / nerve map、相対 nerve または comparison functor
  の障害受け皿、D6 的な模型内両相非空性、reorg/refactor の一般 operation / hitting criterion は
  未固定であり、次 cycle の主 frontier とする。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayTwoTopology.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_conwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_nonzeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_notCommunicationCompatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownershipIndexedFromCommunication_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedConwayTwoCoverWitnessPackage`

G2 / G3 audit summary:

- G2 A rigor: accept, base 70. Bounded finite witness claim is valid; no refinement / nerve / H1 receiver claim.
- G2 B research value: accept, base 75. High leverage initial foothold; base reduced because obstruction receiver is not yet fixed.
- G2 C repo value: accept, base 80. Strong alignment with SFT 第V部 and research placement.
- G2 D rival comparison: accept, base 80. Not merely rival rephrasing; formal zero/nonzero and degeneracy split are the delta.
- G3 axiom check: pass, `propext` only on the two Prop-valued finite witness declarations listed above.
- G3 formalization quality: pass.

Next frontier:

- Add explicit refinement / common refinement / nerve map vocabulary over `TwoCoverAtlas`.
- Decide the first obstruction receiver: relative nerve support, comparison functor failure, or finite `C^1/B^1`-style quotient.
- Strengthen reorg/refactor from example atlases to one-sided cover-edit operations with a clearance / hitting criterion.
- Keep empirical mirroring claims outside theorem statements; record them only as D7-style hypotheses when needed.

## Cycle 2 — Relative nerve support receiver

candidate: `research/ideas/g-sft-conway-01-relative-nerve-support-receiver.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: `refinement-order`, `support-receiver`,
  `conway-obstruction`, `finite-witness`, `receiver`
goal_delta: Cycle 1 の `TwoCoverAtlas` 上に `CoverRefines`、`CommonRefinementSpan`,
  `SupportNerveEdge`, `SupportNerveFork`, `SupportNerveObstructionReceiver` を置き、
  selected Conway obstruction と support-nerve fork receiver の同値を Lean theorem として固定した。
  `CommonRefinementSpan` は singleton support edge の補助語彙に留まり、obstruction 判定との
  非自明な関係はまだ固定していない。
project_value_delta: SFT 第V部 Conway 対応の最初の receiver を、cohomology 名へ急がず
  finite-combinatorial support nerve として置いた。
rival_delta: 既存 rival は owner mismatch や org/code incidence を可視化できる。この cycle の差分は、
  selected finite witness を same communication block 上の support fork と single-owner collapse failure の
  Lean theorem package として保存する点に限定する。
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwaySupportReceiver.lean` と
  `lake build Formal.AG.Research.SFT.ConwaySupportReceiver` が通過。初回 `lake build FormalAGResearch` は
  新規 `Formal.AG.Research.SFT.ConwaySupportReceiver` まで build した後、既存
  `Formal.AG.Research.QualitySurface.VisibleRepairTransportCommutator` の `.setup.json` 読み込み失敗で停止したが、
  再実行で `lake build FormalAGResearch` は通過した。`#print axioms` では receiver 変換本体は axiom-free、
  finite example receiver 系は Cycle 1 由来の `propext` に依存する。
open_questions: full nerve map / comparison functor、finite `C^1/B^1` quotient、reorg/refactor の
  general cover-edit operation は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwaySupportReceiver.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.communicationCompatible_iff_coverRefines`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownershipIndexedFromCommunication_refines`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportNerveEdge.singletonCommonRefinement`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportReceiver_of_conwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.conwayObstruction_of_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportReceiver_iff_conwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_noSupportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_noSupportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_noSupportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedSupportReceiverPackage`

G2 / G3 audit summary:

- G2 A: revise, base 70. 最初の receiver 語彙化として一段前進だが、full relative nerve / nerve map mismatch には届かない。
- G2 B: revise, base 55. 定義は使えるが、中心 obstruction 条件は Cycle 1 witness の再包装に近い。
- G2 C: revise, base 60. 将来の `C^1/B^1` や comparison functor failure の受け皿として自然だが、`CommonRefinementSpan` は obstruction 判定に未接続。
- G2 D adversarial: revise, base 45. `CommonRefinementSpan` は obstruction 判定に未使用で、rival separation は弱い。
- G3 formalization quality: pass。blocking な健全性問題なし。
- G3 axiom check: pass with `propext` only on finite example receiver declarations; receiver equivalence itself is axiom-free.
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。Cycle 2 は高得点 discovery ではなく、Cycle 1 の selected obstruction を receiver vocabulary へ保守的に移す bridge として扱う。
