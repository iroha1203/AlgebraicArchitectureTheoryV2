# G-sft-conway-01 report

この report は `G-sft-conway-01` の research-loop 成果を、SFT 第V部 Conway 対応へ向けた
能力増分として記録する。GOAL 定義と active threshold は `research/goals/G-sft-conway-01.md` と tracking
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
project_value_delta: SFT 第V部の予告を、AAT 本体を変更せず `research/lean/ResearchLean/AG/SFT` 上の
  Lean-backed research surface へ動かした。
rival_delta: Team Topologies / mirroring 研究 / CODEOWNERS dashboard / org-network analysis /
  AI review は不一致を説明・可視化できるが、この cycle は独立二被覆上の zero/nonzero
  theorem package と、ownership を communication index から導くと obstruction が自明に消える
  という非忠実性を形式証拠として返す。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayTwoTopology.lean` と
  `lake build FormalAGResearch` が通過。G3 形式化品質監査は pass。`#print axioms` では
  `selectedConwayTwoCoverWitnessPackage` と `mismatchedAtlas_nonzeroConwayObstruction` が
  `propext` に依存し、`ownershipIndexedFromCommunication_zeroConwayObstruction` は axiom-free。
  G3 公理検査は `propext` を標準的な Prop 外延性として許容した。
open_questions: refinement / common refinement / nerve map、相対 nerve または comparison functor
  の障害受け皿、D6 的な模型内両相非空性、reorg/refactor の一般 operation / hitting criterion は
  未固定であり、次 cycle の主 frontier とする。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayTwoTopology.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_conwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_nonzeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_notCommunicationCompatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownershipIndexedFromCommunication_zeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedConwayTwoCoverWitnessPackage`

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
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
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
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwaySupportReceiver.lean` と
  `lake build ResearchLean.AG.SFT.ConwaySupportReceiver` が通過。初回 `lake build FormalAGResearch` は
  新規 `ResearchLean.AG.SFT.ConwaySupportReceiver` まで build した後、既存
  `Formal.AG.Research.QualitySurface.VisibleRepairTransportCommutator` の `.setup.json` 読み込み失敗で停止したが、
  再実行で `lake build FormalAGResearch` は通過した。`#print axioms` では receiver 変換本体は axiom-free、
  finite example receiver 系は Cycle 1 由来の `propext` に依存する。
open_questions: full nerve map / comparison functor、finite `C^1/B^1` quotient、reorg/refactor の
  general cover-edit operation は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwaySupportReceiver.lean`
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

G2 / G3 audit summary:

- G2 A: revise, base 70. 最初の receiver 語彙化として一段前進だが、full relative nerve / nerve map mismatch には届かない。
- G2 B: revise, base 55. 定義は使えるが、中心 obstruction 条件は Cycle 1 witness の再包装に近い。
- G2 C: revise, base 60. 将来の `C^1/B^1` や comparison functor failure の受け皿として自然だが、`CommonRefinementSpan` は obstruction 判定に未接続。
- G2 D adversarial: revise, base 45. `CommonRefinementSpan` は obstruction 判定に未使用で、rival separation は弱い。
- G3 formalization quality: pass。blocking な健全性問題なし。
- G3 axiom check: pass with `propext` only on finite example receiver declarations; receiver equivalence itself is axiom-free.
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。Cycle 2 は高得点 discovery ではなく、Cycle 1 の selected obstruction を receiver vocabulary へ保守的に移す bridge として扱う。

## Cycle 3 — Support fork Z2 boundary receiver

candidate: `research/ideas/g-sft-conway-01-support-fork-z2-boundary-receiver.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `boundary-quotient-receiver`, `finite-coefficient`, `support-receiver`,
  `conway-obstruction`, `finite-witness`
goal_delta: Cycle 2 の `SupportNerveFork` を selected degree-one cochain として読み、
  `SupportForkDefect : ZMod 2` と `SupportForkBoundarySubgroup : AddSubgroup ConwayZ2` を置いた。
  selected defect の boundary subgroup membership が単一 owner support と同値であること、functional ownership
  が canonical mismatched fork の non-boundary class を導くことを Lean theorem として固定した。ただし
  boundary subgroup は receiver predicate-driven であり、Cycle 2 receiver の selected finite coefficient
  rephrasing として扱う。
project_value_delta: SFT 第V部 Conway 対応の receiver を、full cohomology へ急がず selected `ZMod 2`
  membership vocabulary と functional non-boundary certificate に移した。true quotient object / boundary map /
  sheaf `H^1` ではない。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、selected `1 : ZMod 2`
  defect が predicate-driven boundary subgroup に吸収されるかを theorem package として保存する点に限定する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryQuotient.lean` と
  `lake build ResearchLean.AG.SFT.ConwayBoundaryQuotient` が通過。`#print axioms` では主要 theorem が
  `propext`, `Classical.choice`, `Quot.sound` に依存する。G3 formalization quality は pass。
open_questions: true sheaf `H^1`、full quotient object、common-refinement exactness、comparison functor failure、
  arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayBoundaryQuotient.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkBoundarySubgroup`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportForkDefect_nonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportForkDefect_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportForkNonzeroClass_iff_noSingleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.boundaryQuotientReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.functionalFork_nonzeroClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.functionalFork_boundaryQuotientReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_ownershipFunctional`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_nonzeroClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_boundaryQuotientReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_boundaryQuotientReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroBoundaryQuotientReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroBoundaryQuotientReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroBoundaryQuotientReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedBoundaryQuotientReceiverPackage`

G2 / G3 audit summary:

- G2 B: revise, base 60. `ZMod 2` defect と boundary subgroup は単なる Prop wrapper を部分的に越えるが、defect は定数で boundary subgroup は predicate-driven。
- G2 C: accept, base 65. Cycle 2 の receiver を selected finite `C^1/B^1`-style receiver に進める repo value はあるが、full quotient object / true `H^1` / common-refinement exactness は未到達。
- G2 D adversarial: revise, base 45-50. `SupportForkBoundarySubgroup` は `ForkHasSingleOwnerSupport` で `⊤/⊥` 分岐するため、receiver 条件を boundary subgroup 定義にほぼ直接埋め込んでいる。
- G3 formalization quality: pass。claim を selected finite receiver に限定する限り blocking finding なし。
- G3 axiom check: pass with `propext`, `Classical.choice`, `Quot.sound`; `SupportForkBoundarySubgroup` の Prop 分岐と `ZMod` / quotient infrastructure 由来。
- G4 score confirmation: base 55、evidence multiplier 2.0、penalty 0、final +110。Cycle 3 は Cycle 2 receiver を selected finite coefficient boundary membership vocabulary へ移す low bridge として扱う。

## Cycle 4 — Explicit boundary generator provenance

candidate: `research/ideas/g-sft-conway-01-explicit-boundary-generator-provenance.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `boundary-generator-provenance`, `finite-coefficient`, `support-receiver`,
  `conway-obstruction`, `finite-witness`
goal_delta: Cycle 3 の predicate-driven boundary subgroup を、explicit
  `SupportForkBoundaryGenerator` 由来の selected generator subgroup membership へ移した。
  generator が selected defect を吸収する theorem、functional ownership が mismatched fork の generator
  existence を排除する theorem、compatible/repaired examples の zero generator receiver を Lean theorem として固定した。
project_value_delta: Cycle 3 adversarial finding の主要点だった「boundary subgroup が receiver predicate-driven」を、
  full boundary map までは進まずに single-owner support witness の explicit provenance 化として弱く改善した。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、selected owner-support generator を
  Lean 内の witness として保存し、後続 boundary-map 候補へ渡せる形にした点に限定する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryGenerator.lean` が通過。
  `lake build ResearchLean.AG.SFT.ConwayBoundaryGenerator` も通過。`#print axioms` では
  `SupportForkBoundaryGenerator.ofSingleOwnerSupport` と `boundaryGenerator_nonempty_iff_singleOwnerSupport` が
  `Classical.choice` に依存し、subgroup / closure 系 theorem は `propext`, `Classical.choice`,
  `Quot.sound` に依存する。G3 formalization quality は pass。
open_questions: independent global boundary map、full quotient object、true sheaf `H^1`、common-refinement exactness、
  comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayBoundaryGenerator.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.boundaryGenerator_nonempty_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkGeneratorBoundarySubgroup`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGeneratorBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.generatorBoundary_absorbs_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.generatorBoundarySubgroup_le_predicateBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.functionalFork_noBoundaryGenerator`
- `ResearchLean.AG.SFT.ConwayTwoTopology.functionalFork_not_generatorBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.GeneratorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.generatorBoundaryReceiver_of_functionalFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notGeneratorBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_generatorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_generatorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroGeneratorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroGeneratorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroGeneratorBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedGeneratorBoundaryReceiverPackage`

G2 / G3 audit summary:

- G2 A: revise, base 60. Cycle 3 の predicate-driven boundary subgroup から explicit generator / closure へ分離できているが、generator は single-owner support と同値で、full boundary map ではない。
- G2 D adversarial: revise, base 55. `SupportForkGeneratorBoundarySubgroup` は generator があれば constant defect を closure に入れるだけで、rival separation もまだ theorem packaging 寄り。
- G3 formalization quality: pass。selected finite receiver 上の explicit boundary generator provenance に限定する限り blocking finding なし。
- G3 axiom check: pass with `propext`, `Classical.choice`, `Quot.sound`; `ofSingleOwnerSupport` の choice と subgroup closure infrastructure 由来。
- G4 score confirmation: base 55、evidence multiplier 2.0、penalty 0、final +110。Cycle 4 は single-owner support witness の explicit provenance 化として扱う。

## Cycle 5 — Global boundary map exactness

candidate: `research/ideas/g-sft-conway-01-global-boundary-map-exactness.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `global-boundary-map`, `finite-coefficient`, `support-receiver`,
  `conway-obstruction`, `finite-witness`
goal_delta: Cycle 4 の fork-local explicit boundary generator を、atlas 全体の
  `CommunicationZeroCochain` と selected `SupportForkGlobalBoundaryMap` へ持ち上げた。
  support-fork defect が global boundary map で吸収されることと
  `CommunicationCoverCompatible` が同値であること、mismatched atlas には global zero-cochain がなく
  canonical fork が global boundary map で消えないこと、compatible/repaired examples の zero receiver を
  Lean theorem として固定した。
project_value_delta: SFT 第V部 Conway 対応を、局所 generator provenance から selected
  `C0 -> C1` exactness statement へ進めた。true chain complex / sheaf `H^1` / functorial comparison ではない。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、
  global owner-support cochain の存在が selected defect absorption と同値であることを theorem package として
  保存する点に限定する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryMap.lean`、
  `lake build ResearchLean.AG.SFT.ConwayBoundaryMap`、`lake build FormalAGResearch` が通過。
  `#print axioms` では `communicationZeroCochain_nonempty_iff_compatible` が `Classical.choice`、
  selected boundary theorem package が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: independent additive boundary on a nontrivial `C0` carrier, full quotient object、
  true sheaf `H^1`、common-refinement exactness、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayBoundaryMap.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationZeroCochain`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationZeroCochain_nonempty_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkGlobalBoundaryMap`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGlobalBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalBoundary_vanishes_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalBoundary_absorbs_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalBoundary_absorbs_into_generatorBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.GlobalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_globalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_noCommunicationZeroCochain`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notGlobalBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_globalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroGlobalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroGlobalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroGlobalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedGlobalBoundaryMapPackage`

G2 / G3 audit summary:

- G2 A rigor: revise, base 60。bounded selected theorem として blocking finding はないが、
  `SupportForkGlobalBoundaryMap` は zero-cochain を使わず constant selected defect を返す。
- G2 B research value: revise, base 60。global owner-support cochain exactness は Cycle 4 からの実在する前進だが、
  independent additive boundary / true quotient / sheaf `H^1` には未到達。
- G2 C repo value: accept/revise, base 60。SFT research surface として PR に載せる価値はあるが、
  claim boundary を selected finite receiver に保つ必要がある。
- G2 D adversarial: revise, base 55-60。rival separation は local mismatch から global cochain gate へ進むが、
  theorem packaging 寄りである。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch` が通過。
- G3 axiom check: pass with `propext`, `Classical.choice`, `Quot.sound`; compatibility witness choice と
  existing `ZMod` / quotient infrastructure 由来。
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。

## Cycle 6 — Owner-choice boundary evaluation

candidate: `research/ideas/g-sft-conway-01-owner-choice-boundary-evaluation.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: `owner-choice-boundary`, `finite-coefficient`, `support-receiver`,
  `conway-obstruction`, `finite-witness`
goal_delta: Cycle 5 の selected global boundary map が zero-cochain value を使わない弱点を受け、
  任意の `CommunicationOwnerChoice` を degree-zero data として置いた。selected boundary evaluation が
  chosen owner の support predicate を実際に読み、defect absorption と chosen-owner support の同値、
  absorption existence と `ForkHasSingleOwnerSupport` の同値、support receiver との同値、finite examples の
  zero/nonzero package を Lean theorem として固定した。
project_value_delta: Conway 対応の receiver を、ただの global compatibility gate から
  degree-zero owner-choice value を参照する selected boundary evaluation へ進めた。full additive complex /
  sheaf `H^1` / functorial comparison ではない。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、選ばれた owner value が
  selected fork defect を吸収するかを Lean theorem package として保存する点に限定する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerChoiceBoundary.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerChoiceBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  `#print axioms` では主要 theorem が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: global additive `C0 -> C1` carrier、common-refinement exactness、true quotient object、
  true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerChoiceBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationOwnerChoice`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerChoiceSupportsFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkOwnerChoiceBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloOwnerChoiceBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerChoiceBoundary_absorbs_iff_supportsFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerChoiceBoundary_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.zeroCochain_ownerChoiceBoundary_absorbs`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerChoiceBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerChoiceBoundaryReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_ownerChoiceBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notOwnerChoiceBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_ownerChoiceBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroOwnerChoiceBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroOwnerChoiceBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroOwnerChoiceBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerChoiceBoundaryPackage`

G2 / G3 audit summary:

- G2 A rigor: revise, base 60。bounded finite theorem として blocking finding はないが、
  existence-level absorption は `ForkHasSingleOwnerSupport` と完全同値で、新しい obstruction 条件ではない。
- G2 B research value: revise, base 60。Cycle 5 の value-insensitivity は改善するが、
  true `C0 -> C1` / common-refinement exactness には未到達。
- G2 C repo value: accept/revise, base 60。次 frontier への finite selected layer として妥当だが、
  claim boundary を selected receiver に保つ必要がある。
- G2 D adversarial: revise, base 55-60。chosen owner value の吸収判定は保存するが、
  rival separation はまだ theorem packaging 寄りである。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass with `propext`, `Classical.choice`, `Quot.sound`; `ZMod` / quotient infrastructure と
  classical Prop branching 由来。
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。

## Cycle 7 — Local owner-potential boundary weakness

candidate: `research/ideas/g-sft-conway-01-local-owner-potential-boundary-weakness.md`
candidate_type: `negative-bridge`
evidence_stage: `proved-in-research`
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: `owner-potential-boundary`, `finite-coefficient`, `local-exactness`,
  `conway-obstruction`, `finite-witness`
goal_delta: Cycle 6 後の open frontier だった additive boundary 候補を、local finite
  `OwnerPotential : OwnerIdx -> ConwayZ2` と endpoint-difference boundary として置いた。canonical
  mismatched fork はこの local additive boundary で吸収される一方、owner-choice/support receiver と global
  zero-cochain receiver はなお mismatch を検出することを Lean theorem として固定した。
project_value_delta: Conway 対応に必要な制約を sharpen した。単なる local additive exactness は
  support/global compatibility に非忠実であり、次 frontier では common-refinement / global compatibility
  constraint が必要になる。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、naive local additive
  boundary が mismatch を消してしまう failure mode を theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerPotentialBoundary.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerPotentialBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  `#print axioms` では主要 theorem が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: constrained additive `C0 -> C1` complex、common-refinement exactness、true quotient object、
  true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerPotentialBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkOwnerPotentialBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloOwnerPotentialBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerPotentialBoundary_absorbs_of_endpointDifference`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedOwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedOwnerPotential_boundary_eq_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_ownerPotentialBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_ownerChoiceReceiver_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_globalBoundary_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerPotentialBoundaryPackage`

G2 / G3 audit summary:

- G2 A rigor: revise, base 60。bounded claim として blocking finding はないが、
  true `C0 -> C1` complex ではなく canonical finite fork 上の negative bridge。
- G2 B research value: accept, base 65 recommendation。ただし 65 は上限寄りで、一般 theorem ではない。
- G2 C repo value: accept/revise, base 60。次 frontier の support/global/common-refinement constraint を明確にする価値がある。
- G2 D adversarial: revise, base 55-60。local additive exactness と support/global compatibility の非忠実性は示すが、
  finite theorem package に留まる。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass with `propext`, `Classical.choice`, `Quot.sound`; `ZMod` / quotient infrastructure 由来。
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。

## Cycle 8 — Support-constrained owner-potential boundary

candidate: `research/ideas/g-sft-conway-01-support-constrained-owner-potential.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: `constrained-owner-potential`, `finite-coefficient`, `support-receiver`,
  `local-exactness`, `conway-obstruction`
goal_delta: Cycle 7 の unconstrained local owner-potential boundary の弱さを受け、
  single-owner support constraint を戻した。decidable owner equality の下で endpoint-separating potential が
  local additive absorption を与えること、support-constrained vanishing が `ForkHasSingleOwnerSupport` と
  同値であること、support-constrained receiver が support receiver と同値であること、finite examples の
  zero/nonzero package を Lean theorem として固定した。
project_value_delta: local additive endpoint boundary と support compatibility の関係を整理した。
  unconstrained exactness は弱すぎるが、support-constrained exactness は Conway support receiver を回復する。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、additive endpoint exactness が
  support constraint を伴うかどうかを theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`、
  `lake build ResearchLean.AG.SFT.ConwayConstrainedOwnerPotentialBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  `#print axioms` では主要 theorem が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: common-refinement constrained boundary、global compatibility constrained potential、
  true quotient object、true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.endpointSeparatingOwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.endpointSeparatingOwnerPotential_boundary_eq_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerPotentialBoundary_vanishes_of_decidableOwners`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportConstrainedOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportConstrainedOwnerPotentialReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_supportConstrainedOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroSupportConstrainedOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroSupportConstrainedOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroSupportConstrainedOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedSupportConstrainedOwnerPotentialPackage`

G2 / G3 audit summary:

- G2 A rigor: accept, base 60。bounded selected theorem として blocking finding はないが、60 が上限。
- G2 B research value: revise, base 55。Cycle 7 failure の最小修復条件として有用だが、
  new obstruction ではなく existing support receiver へ戻る。
- G2 C repo value: accept/revise, base 55。next frontier の common-refinement constraint へ渡す bridge として扱う。
- G2 D adversarial: revise, base 55。support constraint の有無は保存するが、rival separation は限定的。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass with `propext`, `Classical.choice`, `Quot.sound`; `ZMod` / quotient infrastructure 由来。
- G4 score confirmation: base 55、evidence multiplier 2.0、penalty 0、final +110。

## Cycle 9 — Common-refinement constrained boundary

candidate: `research/ideas/g-sft-conway-01-common-refinement-constrained-boundary.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `common-refinement-boundary`, `finite-coefficient`, `support-receiver`,
  `conway-obstruction`
goal_delta: Cycle 8 の support constraint を `CommonRefinementSpan` vocabulary に移した。
  common-refinement block が fork の communication block 全体を覆い one ownership block へ refine することと
  `ForkHasSingleOwnerSupport` の同値、common-refinement constrained owner-potential receiver と support receiver の
  同値、finite examples の zero/nonzero package を Lean theorem として固定した。
project_value_delta: direct support predicate を common-refinement provenance 付きの selected data に移した。
  新 obstruction ではないが、後続の comparison theorem / common-refinement exactness の足場になる。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、support condition が
  common-refinement data で witness されるかを theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCommonRefinementBoundary.lean`、
  `lake build FormalAGResearch`、full `lake build` が通過。`#print axioms` は
  `Classical.choice` / `propext` / `Quot.sound` に収まる。
open_questions: common-refinement exactness beyond support equivalence、global compatibility constrained potential、
  true quotient object、true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayCommonRefinementBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommonRefinementSupportsFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommonRefinementSupportsFork.toSingleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommonRefinementSupportsFork.ofSingleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.commonRefinementSupportsFork_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloCommonRefinementOwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommonRefinementOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.commonRefinementOwnerPotentialReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_commonRefinementOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroCommonRefinementOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroCommonRefinementOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroCommonRefinementOwnerPotentialReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCommonRefinementOwnerPotentialPackage`

G2 / G3 audit summary:

- G2 audit: pass。二審判とも base 55 / multiplier 2.0 / penalty 0 を推奨。
  `CommonRefinementSupportsFork` は `ForkHasSingleOwnerSupport` の common-refinement provenance 化であり、
  新 obstruction ではないため base 60 以上は過大。
- G3 formalization quality: pass。`lake env lean`、`lake build FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass with `Classical.choice`, `propext`, `Quot.sound`; singleton common-refinement construction /
  owner-potential quotient infrastructure 由来。
- G4 score confirmation: base 55、evidence multiplier 2.0、penalty 0、final +110。

## Cycle 10 — Global/common-refinement comparison

candidate: `research/ideas/g-sft-conway-01-global-common-refinement-comparison.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `global-boundary`, `common-refinement`, `finite-coefficient`,
  `conway-obstruction`
goal_delta: Cycle 5 の global zero-cochain boundary と Cycle 9 の common-refinement support provenance を比較した。
  global zero-cochain が every selected fork に common-refinement support を供給すること、combined vanishing が
  communication-cover compatibility と同値であること、combined receiver が global-boundary receiver と同値であることを
  Lean theorem として固定した。
project_value_delta: global exactness と common-refinement provenance の比較層を追加した。新 obstruction ではないが、
  arbitrary cover naturality / comparison map failure を探す次 frontier の基準になる。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、global compatibility が
  common-refinement support provenance を every selected fork へ供給するという theorem package を保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayGlobalCommonRefinementComparison.lean`、
  `lake build ResearchLean.AG.SFT.ConwayGlobalCommonRefinementComparison`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は `Classical.choice` / `propext` / `Quot.sound` に収まる。
open_questions: common-refinement exactness failure beyond global compatibility、arbitrary cover naturality、
  true quotient object、true sheaf `H^1`、comparison functor failure は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayGlobalCommonRefinementComparison.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationZeroCochain.toCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationZeroCochain_commonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGlobalCommonRefinement`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalCommonRefinement_vanishes_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalCommonRefinement_implies_commonRefinementOwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.GlobalCommonRefinementReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalCommonRefinementReceiver_iff_globalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notGlobalCommonRefinementVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_globalCommonRefinementReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_zeroGlobalCommonRefinementReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgedAtlas_zeroGlobalCommonRefinementReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactoredAtlas_zeroGlobalCommonRefinementReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedGlobalCommonRefinementComparisonPackage`

G2 / G3 audit summary:

- G2 audit: pass。二審判とも base 55 / multiplier 2.0 / penalty 0 を推奨。
  combined receiver は `GlobalBoundaryReceiver` と同値で検出力を増やさないため、base 60 以上は過大。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass with `Classical.choice`, `propext`, `Quot.sound`; global-boundary / quotient infrastructure 由来。
- G4 score confirmation: base 55、evidence multiplier 2.0、penalty 0、final +110。

## Cycle 11 — Local vs global/common-refinement separation

candidate: `research/ideas/g-sft-conway-01-local-vs-global-common-refinement.md`
candidate_type: `negative-bridge`
evidence_stage: `proved-in-research`
base_score: 40
evidence_multiplier: 2.0
penalty: 0
final_score: 80
category: `local-potential`, `global-boundary`, `common-refinement`,
  `conway-obstruction`
goal_delta: Cycle 7 の local owner-potential absorption と Cycle 10 の global/common-refinement receiver を分離した。
  canonical mismatched fork は local owner-potential boundary で吸収されるが、combined global/common-refinement
  vanishing と common-refinement constrained owner-potential vanishing では消えないことを Lean theorem として固定した。
project_value_delta: local additive exactness を Conway compatibility と誤読してはいけない境界を明示した。
  新 receiver ではないが、support/common/global constraints の必要性を finite theorem package として保存する。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、local additive absorption が
  global/common-refinement compatibility を含意しないことを theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayLocalVsGlobalCommonRefinement.lean`、
  `lake build ResearchLean.AG.SFT.ConwayLocalVsGlobalCommonRefinement`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は `Classical.choice` / `propext` / `Quot.sound` に収まる。
open_questions: arbitrary cover naturality、non-selected refinement span family、true quotient object、
  true sheaf `H^1`、comparison functor failure は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayLocalVsGlobalCommonRefinement.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_globalCommonRefinement_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_commonRefinementOwnerPotential_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedLocalPotential_separatedBySupportAndGlobalCommonReceivers`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_noLocalGlobalCommonSeparationReceivers`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedLocalVsGlobalCommonRefinementPackage`

G2 / G3 audit summary:

- G2 audit: pass。ただし二審判の推奨は base 50 と base 40。既存 theorem の conjunction package に近いため、
  保守的に base 40 を採用。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass with `Classical.choice`, `propext`, `Quot.sound`; inherited receiver infrastructure 由来。
- G4 score confirmation: base 40、evidence multiplier 2.0、penalty 0、final +80。

## Cycle 12 — Coherent common-refinement family

candidate: `research/ideas/g-sft-conway-01-coherent-common-refinement-family.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 50
evidence_multiplier: 2.0
penalty: 0
final_score: 100
category: `common-refinement`, `coherent-family`, `global-boundary`,
  `conway-obstruction`
goal_delta: fork ごとの singleton support ではなく、one shared `CommonRefinementSpan` から fork family 全体へ
  support block を選ぶ coherent interface を追加した。global zero-cochain が communication-indexed shared span を作り、
  任意の selected fork family に coherent common-refinement support を供給することを Lean theorem として固定した。
project_value_delta: common-refinement provenance を single fork から family-level coherence へ上げた。
  新 obstruction ではないが、arbitrary cover naturality / comparison map failure の前段 interface になる。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、support provenance が one shared
  refinement span から fork family へ coherent に選ばれるかを theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCoherentCommonRefinementFamily.lean`、
  `lake build ResearchLean.AG.SFT.ConwayCoherentCommonRefinementFamily`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は family construction では axiom-free、
  compatibility package で `Classical.choice` / `propext` に収まる。
open_questions: local support はあるが shared span が存在しない finite family、arbitrary cover naturality、
  non-selected refinement span family、true quotient object、true sheaf `H^1` は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentCommonRefinementFamily.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CoherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_implies_eachForkSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationZeroCochain.toCoherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationZeroCochain_coherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement`
- `ResearchLean.AG.SFT.ConwayTwoTopology.familyCoherentGlobalCommonRefinement_vanishes_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSingletonForkFamily_notCoherentGlobalCommonRefinementVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleEmptyForkFamily_coherentGlobalCommonRefinementVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCoherentCommonRefinementFamilyPackage`

G2 / G3 audit summary:

- G2 audit: pass。ただし二審判の推奨は base 55 と base 50。新 family-level structure はあるが、
  global zero-cochain からの構成が直接的で新 obstruction ではないため、保守的に base 50 を採用。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass。core family support construction は axiom-free。compatibility equivalence/package は
  `Classical.choice`, `propext` に依存。
- G4 score confirmation: base 50、evidence multiplier 2.0、penalty 0、final +100。

## Cycle 13 — Coherent family morphism naturality

candidate: `research/ideas/g-sft-conway-01-coherent-family-morphism-naturality.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 35
evidence_multiplier: 2.0
penalty: 0
final_score: 70
category: `common-refinement`, `coherent-family`, `selected-naturality`,
  `conway-obstruction`
goal_delta: Cycle 12 の coherent family support に strict fork-preserving selected family morphism layer を追加した。
  fork equality を保存する reindex / subfamily map に沿って、coherent support と coherent
  global/common-refinement vanishing が pullback すること、selected morphism naturality failure が
  起きないことを Lean theorem として固定した。
project_value_delta: common-refinement provenance を family-level existence から selected morphism-level
  preservation へ上げた。arbitrary cover naturality は主張しないが、その blocker を述べるための
  基準線になる。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、検出力の追加ではなく、
  support provenance が selected family morphism に沿って保存されるかを theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyMorphism.lean`、
  `lake build ResearchLean.AG.SFT.ConwayCoherentFamilyMorphism`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は main declarations すべて axiom-free。
open_questions: arbitrary cover naturality、non-selected refinement span family、local support はあるが shared span が
  存在しない finite family、true quotient object、true sheaf `H^1` は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyMorphism.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.id`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.comp`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.pullbackSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_pullback`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentGlobalCommonRefinement_vanishes_pullback`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.reindex`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.reindexMorphism`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.subfamily`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.subfamilyInclusion`
- `ResearchLean.AG.SFT.ConwayTwoTopology.no_coherentFamilyMorphismNaturalityFailure`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCoherentFamilyMorphismPackage`

G2 / G3 audit summary:

- G2 audit: pass。ただし二審判の推奨は base 40 と base 35。`SupportForkFamilyMorphism` は
  fork equality を保存する strict selected map で、主定理は target support を source へ引き戻す
  closure result なので、保守的に base 35 を採用。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass。`pullbackSupport`、support pullback、vanishing pullback、naturality failure theorem、
  package theorem はすべて axiom-free。
- G4 score confirmation: base 35、evidence multiplier 2.0、penalty 0、final +70。

## Cycle 14 — Coherent family local exactness

candidate: `research/ideas/g-sft-conway-01-coherent-family-local-exactness.md`
candidate_type: `negative-bridge`
evidence_stage: `proved-in-research`
base_score: 50
evidence_multiplier: 2.0
penalty: 0
final_score: 100
category: `common-refinement`, `coherent-family`, `local-global-boundary`,
  `conway-obstruction`
goal_delta: Cycle 12/13 の frontier だった「各 fork に local support はあるが shared span がない」
  failure mode を検証し、現 `CommonRefinementSpan` interface では起こらないことを Lean theorem として固定した。
  forkwise local common-refinement support は Sigma-indexed shared span として coherent family support に assemble できる。
project_value_delta: common-refinement family interface の exactness boundary を明示した。次に非自明な
  obstruction を得るには、non-selected refinement span family、restricted span vocabulary、または
  arbitrary-cover naturality blocker が必要になる。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、local/shared common-refinement
  obstruction が現 vocabulary では潰れるという境界を theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean`、
  `lake build ResearchLean.AG.SFT.ConwayCoherentFamilyExactness`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は `Classical.choice` のみ。
open_questions: restricted common-refinement span vocabulary、non-selected refinement span family、arbitrary cover
  naturality blocker、true quotient object、true sheaf `H^1` は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ForkFamilyHasLocalCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CoherentCommonRefinementSupport.ofEachForkSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_iff_eachForkSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ForkFamilyLocalButNotCoherent`
- `ResearchLean.AG.SFT.ConwayTwoTopology.no_forkFamilyLocalButNotCoherent`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentGlobalCommonRefinementVanishes_implies_localSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localSupport_and_globalZeroCochain_implies_coherentVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCoherentFamilyExactnessPackage`

G2 / G3 audit summary:

- G2 audit: pass。二審判とも base 50 / multiplier 2.0 / penalty 0 を推奨。
  Sigma assembly theorem は candidate claim を証明しており、overclaim はない。ただし one shared span は
  current selected interface の Sigma-indexed shared span に限定して読む。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass。主要 theorem は `Classical.choice` のみに依存し、local support witnesses を
  Sigma-indexed shared span へ束ねる witness choice 由来。
- G4 score confirmation: base 50、evidence multiplier 2.0、penalty 0、final +100。

## Cycle 15 — Owner-uniform restricted family

candidate: `research/ideas/g-sft-conway-01-owner-uniform-restricted-family.md`
candidate_type: `negative-bridge`
evidence_stage: `proved-in-research`
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: `common-refinement`, `coherent-family`, `restricted-span`,
  `conway-obstruction`
goal_delta: Cycle 14 の unrestricted Sigma assembly で潰れた local/shared gap を、
  owner-uniform coherent family support という restricted span vocabulary で復活させた。
  finite two-fork family で forkwise local support はあるが owner-uniform coherent support はないことを
  Lean theorem として固定した。
project_value_delta: common-refinement family interface に restricted local/shared separation witness を追加した。
  local fork support が family-level owner-uniform coherence を保証しない境界を明示する。
rival_delta: 既存 rival は owner mismatch を可視化できる。この cycle の差分は、local support と
  owner-uniform family coherence の分離を theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean`、
  `lake build ResearchLean.AG.SFT.ConwayRestrictedCoherentFamily`、`lake build FormalAGResearch`、
  full `lake build` が通過。core owner-uniform support theorem は axiom-free、finite package は
  `propext` / `Classical.choice` に依存。
open_questions: arbitrary cover naturality、non-selected refinement span family、true quotient object、
  true sheaf `H^1` は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformCoherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformCoherentCommonRefinementSupport.sharedOwner_supports`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSupport_implies_coherentSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_localSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_notOwnerUniformCoherent`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformLocalButNotCoherentReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedRestrictedCoherentFamilyPackage`

G2 / G3 audit summary:

- G2 audit: pass。二審判とも base 60 / multiplier 2.0 / penalty 0 を推奨。
  finite two-fork family で forkwise local support と owner-uniform family coherence の分離が Lean で固定されている。
  ただし arbitrary cover naturality、non-selected span family、true quotient / sheaf `H^1` には未到達なので
  base 60 を上限として扱う。
- G3 formalization quality: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- G3 axiom check: pass。`ownerUniformSupport_implies_coherentSupport` は axiom-free。finite package は
  `propext`, `Classical.choice` に依存し、既存 local witness choice / Prop extensionality 由来。
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。

## Cycle 16 — Owner-uniform subfamily descent receiver

candidate: `research/ideas/g-sft-conway-01-owner-uniform-subfamily-descent.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 45
evidence_multiplier: 2.0
penalty: 0
final_score: 90
category: `restricted-span`, `local-global-boundary`, `conway-obstruction`,
  `projection-nonfaithfulness`
goal_delta: Cycle 15 の owner-uniform restricted two-fork separation を、
  selected finite subfamily-cover receiver として固定した。API singleton subfamily と DB singleton subfamily は
  それぞれ owner-uniform coherent support を持つが、それらを cover として見る full family には
  owner-uniform coherent support がない。
project_value_delta: restricted common-refinement family の local/global boundary を、
  forkwise local support から selected subfamily support へ一段上げた。これは arbitrary-cover naturality、
  overlap descent datum、quotient object、true sheaf `H^1` ではなく、finite selected receiver である。
rival_delta: 既存 rival は local owner や owner mismatch を可視化できる。この cycle の差分は、
  local singleton subfamily support と full-family owner-uniform gluing failure の分離を theorem package として
  保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSubfamilyDescent.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformSubfamilyDescent`、`lake build FormalAGResearch`、
  full `lake build` が通過。新 receiver 定義は axiom-free、finite package は `propext` のみに依存。
open_questions: arbitrary cover naturality、non-selected refinement span family、owner-uniform quotient object、
  true sheaf `H^1` は未固定。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSubfamilyDescent.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilySubcover`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformSubfamilyDescentFailure`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedApiSingletonFamily`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedDbSingletonFamily`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedApiSingletonFamily_ownerUniformSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedDbSingletonFamily_ownerUniformSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_cover`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformSubfamilyDescentFailure`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformSubfamilyDescentPackage`

G2 / G3 audit summary:

- G2 audit: revise/accept mix。審判 A は base 45、B/C は base 50、D は base 60。
  `descent` を selected finite subfamily-cover receiver に限定する必要があるため、保守的に base 45 を採用。
- G3 formalization quality: pass。statement は修正後の限定 claim と一致し、true sheaf descent、
  arbitrary cover naturality、quotient object へ overclaim していない。
- G3 axiom check: pass。`SupportForkFamilySubcover` と `OwnerUniformSubfamilyDescentFailure` は axiom-free。
  reported finite witness package は `propext` のみに依存し、`sorryAx`、`Classical.choice`、`Quot.sound` はない。
- G4 score confirmation: base 45、evidence multiplier 2.0、penalty 0、final +90。

## Cycle 17 — Owner-uniform family quotient receiver

candidate: `research/ideas/g-sft-conway-01-owner-uniform-family-quotient.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `restricted-span`, `finite-quotient-shadow`, `quotient-style-receiver`,
  `conway-obstruction`
goal_delta: Cycle 15/16 の owner-uniform local/global gap を、selected finite quotient-style
  receiver へ上げた。API singleton subfamily と DB singleton subfamily は同じ
  owner-uniform family receiver 上で vanish するが、full restricted two-fork family は
  explicit owner-uniform boundary generator が存在しないため nonzero class を持つ。
project_value_delta: owner-uniform support witness を explicit boundary-generator provenance として記録し、
  `AddSubgroup.closure` で boundary subgroup を生成する finite receiver を追加した。
  これは support predicate の `if/top/bot` 化ではなく、Cycle 4 の generator provenance pattern を
  Cycle 15/16 の family support に持ち上げる。
rival_delta: 既存 rival は owner mismatch や local owner support の可視化はできる。この cycle の差分は、
  local singleton zero と full-family nonzero を同一 `ZMod 2` finite receiver 上の theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformFamilyQuotient.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformFamilyQuotient`、
  `lake build FormalAGResearch`、full `lake build` が通過。
  full build は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。true sheaf `H^1`、arbitrary-cover naturality、
  functorial quotient は主張しない。
open_questions: arbitrary cover naturality、non-selected refinement span selector、true quotient object、
  true sheaf `H^1` は未固定。Issue #2962 の active threshold 2000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformFamilyQuotient.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformFamilyDefect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyDefect_nonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformFamilyBoundaryGenerator`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyBoundaryGenerator_nonempty_iff_support`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformFamilyBoundarySubgroup`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformFamilyClassVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformFamilyNonzeroClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyBoundary_absorbs_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyBoundarySubgroup_le_bot_of_noSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyClass_nonzero_of_noSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyClass_vanishes_iff_support`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformFamilyClass_vanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformFamilyClass_nonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformFamilyQuotientPackage`

G2 / G3 audit summary:

- G2 audit: revise/accept mix。1審判は base 60 / final 120 を許容したが、3審判は
  `true-quotient-object` label が強すぎることと Prop-wrapper risk を理由に base 55 / final 110 を推奨。
  カードは `finite-quotient-shadow` / `quotient-style-receiver` に修正し、保守的に base 55 を採用。
- G3 formalization quality: pass。`OwnerUniformFamilyBoundarySubgroup` は
  support predicate の `if/top/bot` ではなく、explicit generator 由来の `AddSubgroup.closure` で定義した。
  singleton zero / full-family nonzero は同じ receiver 上で証明している。
- G3 axiom check: pass。`OwnerUniformFamilyBoundaryGenerator` と
  `ownerUniformFamilyBoundaryGenerator_nonempty_iff_support` は axiom-free。
  `ZMod` / `AddSubgroup.closure` を含む receiver theorem は `propext`, `Classical.choice`, `Quot.sound` のみに依存し、
  `sorryAx` はない。
- G4 score confirmation: base 55、evidence multiplier 2.0、penalty 0、final +110。

## Cycle 18 — Owner-uniform span selector obstruction

candidate: `research/ideas/g-sft-conway-01-owner-uniform-span-selector.md`
candidate_type: `obstruction`
evidence_stage: `proved-in-research`
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: `non-selected-span-family`, `selector-obstruction`, `restricted-span`,
  `conway-obstruction`
goal_delta: Cycle 14 の unrestricted Sigma assembly と Cycle 15/16 の owner-uniform failure の差を、
  selected finite span-selector obstruction として固定した。restricted two-fork family では、
  explicit forkwise common-refinement span selector は存在するが、shared owner に揃う
  owner-uniform selector は存在しない。
project_value_delta: local span choices と owner-uniform global selector を別 interface として分離した。
  `ForkwiseCommonRefinementSpanSelector` は各 fork の concrete span choice を保持し、
  `OwnerUniformSpanSelector` は shared owner と selected refinement block の owner compatibility を追加要求する。
rival_delta: 既存 rival は local owner choices を列挙できる。この cycle の差分は、local span selections が
  owner-uniform shared-owner selector に glue しないことを finite theorem package として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSpanSelector.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformSpanSelector`、
  `lake build FormalAGResearch`、full `lake build` が通過。
  full build は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。
  canonical selector、arbitrary non-selected span functoriality、arbitrary-cover naturality、true sheaf `H^1` は主張しない。
open_questions: arbitrary cover naturality、true quotient object、true sheaf `H^1` は未固定。
  Issue #2962 の active threshold 2000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSpanSelector.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ForkwiseCommonRefinementSpanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.forkwiseSpanSelector_nonempty_iff_localSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformSpanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformSpanSelector.toOwnerUniformSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSpanSelector_nonempty_iff_support`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformSpanSelectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedApiFork_commonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedDbFork_commonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_forkwiseSpanSelectable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_noOwnerUniformSpanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformSpanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformSpanSelectorObstructionPackage`

G2 / G3 audit summary:

- G2 audit: revise accept。審判は base 55 / 60 / 60。selector が owner-uniform support の薄い別名に見える risk を指摘したため、
  concrete forkwise support witness と shared-owner selector field を明示し、保守的に base 60 を採用。
- G3 formalization quality: pass。restricted two-fork forkwise selector は
  `Classical.choice` 経由ではなく、API/DB fork の concrete common-refinement support から構成した。
- G3 axiom check: pass。core selector structures と `OwnerUniformSpanSelector.toOwnerUniformSupport` は axiom-free。
  generic local-support-to-selector iff は `Classical.choice` のみに依存し、restricted finite witness package は
  `propext` のみに依存する。`sorryAx` はない。
- G4 score confirmation: base 60、evidence multiplier 2.0、penalty 0、final +120。

## Cycle 19 — Owner-uniform selector / quotient bridge

candidate: `research/ideas/g-sft-conway-01-selector-quotient-bridge.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 0
final_score: 60
category: `selector-obstruction`, `finite-quotient-shadow`, `presentation-comparison`,
  `conway-obstruction`
goal_delta: Cycle 17 の owner-uniform family quotient-style receiver と Cycle 18 の
  owner-uniform span-selector obstruction を、selected finite presentation comparison として接続した。
  `OwnerUniformSpanSelector` の存在は `OwnerUniformFamilyClassVanishes` と同値であり、
  `OwnerUniformSpanSelectorObstruction` は forkwise selectability と nonzero family class の conjunction
  と同値である。
project_value_delta: selector obstruction と quotient-style nonzero class を同じ finite boundary の二表示として
  移動できるようにした。これは true quotient object、canonical selector、arbitrary-cover naturality、
  true sheaf `H^1` ではなく、Cycle 17/18 の selected finite presentation bridge である。
rival_delta: 既存 rival は local owner choices や mismatch を列挙できる。この cycle の差分は、
  selected span-selector obstruction と quotient-style nonzero class が同じ finite obstruction を読んでいることを
  theorem として保存する点にある。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformSelectorQuotientBridge`、`lake build FormalAGResearch`、
  full `lake build` が通過。full build は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の
  linter warning のみ。
open_questions: arbitrary cover naturality、true quotient object、true sheaf `H^1` は未固定。
  Issue #2962 の active threshold 2000 にはこの cycle で到達見込み。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSpanSelector_nonempty_iff_familyClassVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyClassVanishes_of_spanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSpanSelector_of_familyClassVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyNonzeroClass_iff_noSpanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformFamilyNonzeroClass_of_spanSelectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSpanSelectorObstruction_of_forkwiseSelectable_nonzeroClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_spanSelectorObstruction_iff_familyClassNonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_spanSelectorObstruction_implies_familyClassNonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_familyClassNonzero_implies_spanSelectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_spanSelector_and_familyClassVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformSelectorQuotientBridgePackage`

G2 / G3 audit summary:

- G2 audit: candidate generation は closer / obstruction / unifier / wildcard の4観点が同じ bridge を推奨。
  G2 A/B/C/D は全員 accept で base 30 / final 60 を推奨。既存 iff の比較に近いため、
  保守的に base 30 / final +60 を採用。
- G3 formalization quality: pass。selector existence と quotient-style class vanishing の exact bridge に限定し、
  arbitrary cover naturality、true quotient object、true sheaf `H^1` へ overclaim していない。
- G3 axiom check: pass。reported declarations は `propext`, `Classical.choice`, `Quot.sound` のみに依存し、
  `sorryAx` はない。
- G4 score confirmation: base 30、evidence multiplier 2.0、penalty 0、final +60。

## Cycle 20 — Owner-uniform selected finite quotient carrier

candidate: `research/ideas/g-sft-conway-01-owner-uniform-true-quotient-object.md`
candidate_type: `unification`
evidence_stage: `proved-in-research`
base_score: 40
evidence_multiplier: 2.0
penalty: 0
final_score: 80
category: `selected-finite-quotient-carrier`, `finite-quotient-shadow`,
  `presentation-comparison`, `conway-obstruction`
goal_delta: Cycle 17 の boundary-generator membership predicate と Cycle 19 の selector /
  quotient-style bridge を、selected finite quotient carrier 上の class theorem として固定した。
  `OwnerUniformConwayClass family = 0` は boundary membership および owner-uniform span selector
  existence と同値であり、selected singleton subfamily は zero、full restricted two-fork family は
  nonzero class を持つ。
project_value_delta: Conway obstruction receiver spine に、明示的な quotient carrier と class API を追加した。
  これは universal quotient theorem、arbitrary-cover naturality、canonical selector、true sheaf `H^1` ではなく、
  selected finite quotient carrier である。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は owner mismatch や
  local repair story を返せるが、selector、boundary-generator、local-zero、full-family-nonzero presentation を
  一つの Lean-checked finite quotient class として保存しない。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformTrueQuotient.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformTrueQuotient`、`lake build FormalAGResearch` が通過。
  `#print axioms` は reported declarations について `propext`, `Classical.choice`, `Quot.sound` のみで
  `sorryAx` はない。
open_questions: arbitrary-cover naturality、universal quotient property、true sheaf `H^1`、
  relative nerve / Cech shadow は未固定。Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformTrueQuotient.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformConwayQuotient`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformConwayClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformConwayClass_eq_zero_iff_familyClassVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformConwayClass_eq_zero_iff_spanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformConwayClass_ne_zero_iff_selectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformConwayClass_ne_zero_iff_familyNonzeroClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformConwayClass_zero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformConwayClass_nonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_conwayClass_nonzero_iff_selectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformTrueQuotientPackage`

G2 / G3 / G4 audit summary:

- G2 audit: A は revise / base 40。selected finite quotient carrier としてなら厳密だが、
  Cycle 17/19 の quotient API restatement に近いと指摘。B/C/D は accept で base 65-75。
  `true quotient object` label は強すぎるため、card と report は selected finite quotient carrier に修正。
- G3 axiom audit: pass。reported declarations は `propext`, `Classical.choice`, `Quot.sound` のみに依存し、
  `sorryAx` はない。
- G3 formalization quality: pass。actual quotient carrier、class zero iff boundary / selector、
  singleton zero、full-family nonzero を主張し、universal quotient / arbitrary-cover naturality / true sheaf `H^1`
  へ overclaim していない。
- G4 score audit: reduce。G2 A の low bound を採用し、base 40、evidence multiplier 2.0、
  penalty 0、final +80。

## Cycle 21 — Owner-uniform finite Cech-style boundary shadow

candidate: `research/ideas/g-sft-conway-01-relative-cech-shadow.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
category: `finite-cech-shadow`, `boundary-generator-provenance`,
  `conway-obstruction`, `finite-witness`
goal_delta: Cycle 20 の selected finite quotient carrier を、有限 `C0 -> C1`
  cochain-style boundary shadow として読む receiver を追加した。`C0` は explicit
  owner-uniform boundary-generator provenance、`C1` は selected `ZMod 2` family defect
  coefficient であり、その boundary image は Cycle 17 の explicit generator subgroup と一致する。
  shadow class は Cycle 20 の `OwnerUniformConwayClass` と同じ zero/nonzero 判定を持ち、
  selected singleton subfamily は zero、full restricted two-fork family は nonzero である。
project_value_delta: `true H^1` へ進む前の有限 receiver spine として、owner-uniform obstruction が
  どの selected `C0 -> C1` boundary image に載っているかを Lean theorem package として固定した。
  これは true sheaf cohomology、arbitrary-site Cech cohomology、arbitrary-cover naturality、
  universal quotient theorem、canonical selector ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  owner mismatch や local/global failure を報告できるが、この cycle は selected local-zero /
  full-family-nonzero obstruction を finite Cech-style boundary shadow と Cycle 20 quotient class の
  比較 theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformRelativeCechShadow.lean` と
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformRelativeCechShadow` が通過。
  `#print axioms` は reported declarations について `propext`, `Classical.choice`, `Quot.sound`
  のみで `sorryAx` はない。
open_questions: independent relative nerve / intersection indexing、arbitrary-cover naturality、
  reorg/refactor obstruction-killing operation theorem、review-route comparison、true sheaf `H^1`
  は未固定。Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformRelativeCechShadow.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformRelativeCechCochain0`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformRelativeCechBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformRelativeCechBoundaryImage`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformRelativeCechBoundaryImage_eq_familyBoundarySubgroup`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformRelativeCechShadow`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformRelativeCechClass`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_eq_zero_iff_familyClassVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_eq_zero_iff_conwayClass_zero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_ne_zero_iff_conwayClass_nonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_eq_zero_iff_spanSelector`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_relativeCechClass_zero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_relativeCechClass_nonzero`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_relativeCechClass_nonzero_iff_selectorObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformRelativeCechShadowPackage`

G2 / G3 / G4 audit summary:

- G2 audit: revise寄り accept。`C0` は `OwnerUniformFamilyBoundaryGenerator` wrapper、
  `C1` は既存 `OwnerUniformFamilyZ2`、boundary は selected defect なので Cycle 17/20 の再提示に近い。
  ただし boundary image 同定、Cycle 20 class との比較、local-zero/global-nonzero witness により、
  bounded finite Cech-style receiver としての整理にはなっている。`relative nerve` という語は弱めた。
  G2 は base 55、final +110 を推奨した。
- G3 axiom audit: pass。reported declarations は `propext`, `Classical.choice`, `Quot.sound`
  のみに依存し、`sorryAx` はない。
- G3 formalization quality: pass。claim は selected finite `C0 -> C1`
  boundary shadow に限定し、true sheaf `H^1`、arbitrary-site cohomology、arbitrary-cover naturality、
  canonical selector を主張しない。
- G4 score audit: reduce。`C0` は existing generator wrapper、boundary は cochain を読まず
  selected defect を返すため、Cycle 17/20 への incremental cochain-style relabeling に近い。
  independent relative nerve / Cech incidence structure はまだ入っていない。G4 の low bound を採用し、
  base 35、evidence multiplier 2.0、penalty 10、final +60 とする。

## Cycle 22 — Owner-uniform finite incidence receiver

candidate: `research/ideas/g-sft-conway-01-owner-uniform-incidence-receiver.md`
candidate_type: `bridge-obstruction`
evidence_stage: `proved-in-research`
base_score: 55
evidence_multiplier: 2.0
penalty: 0
final_score: 110
category: `finite-incidence-receiver`, `conway-obstruction`,
  `local-global-boundary`, `finite-witness`
goal_delta: Cycle 21 の `C0` wrapper 減点に対して、owner/fork incidence relation を
  selected finite receiver として追加した。vertex は owner、edge は selected fork index、
  incidence は owner が fork の communication block を support すること、global section は
  一つの owner が全 edge に incident であることとして定義した。global section は
  owner-uniform coherent support と同値であり、selected Conway class zero と比較できる。
  selected singleton subfamily は global section を持ち、full restricted two-fork family は
  local incidence support を持つが global section を持たない。
project_value_delta: owner-uniform obstruction spine に、boundary-generator wrapper ではない
  finite incidence carrier を追加した。ただしこれは線形な `C0 -> C1` boundary complex ではなく、
  owner/fork incidence の global-section receiver である。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  owner mismatch や local/global failure を報告できるが、この cycle は selected owner/fork incidence
  relation と local/global section gap を Lean theorem package として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformIncidenceReceiver.lean` と
  `lake build ResearchLean.AG.SFT.ConwayOwnerUniformIncidenceReceiver` が通過。
  `#print axioms` では `ownerUniformIncidenceGlobalSection_nonempty_iff_support` は axiom-free。
  class 比較を含む theorem は `propext`, `Classical.choice`, `Quot.sound` のみに依存し、
  `sorryAx` はない。
open_questions: actual linear `C0 -> C1` incidence boundary、refinement naturality failure、
  reorg/refactor obstruction-killing operation theorem、review-route comparison、true sheaf `H^1`
  は未固定。Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformIncidenceReceiver.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceVertex`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceEdge`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceIncident`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceLocallySupported`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceLocalGlobalGap`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceGlobalSection.toOwnerUniformSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformIncidenceGlobalSection.ofOwnerUniformSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformIncidenceGlobalSection_nonempty_iff_support`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformConwayClass_eq_zero_iff_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_incidenceLocallySupported`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_incidenceLocallySupported`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_no_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_incidenceLocalGlobalGap`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_conwayClass_nonzero_iff_no_incidenceGlobalSection`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerUniformIncidenceReceiverPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduced score。Cycle 21 の boundary-generator wrapper より前進し、
  owner/fork incidence relation と local/global section gap を追加している。ただし中核定理は
  global section と既存 owner-uniform support criterion の同値であり、新しい obstruction criterion
  というより incidence graph 表現である。G2 は base 65 / final +130 を推奨。
- G3 formalization quality: pass。`OwnerUniformIncidenceIncident` は owner が fork の communication
  block を support する条件で、`class = 0` を定義へ直接埋めていない。claim は selected finite
  owner/fork incidence receiver に限定している。
- G3 axiom audit: pass。core equivalence
  `ownerUniformIncidenceGlobalSection_nonempty_iff_support` は axiom-free。
  class comparison / package theorem は `propext`, `Classical.choice`, `Quot.sound` のみに依存し、
  `sorryAx` はない。
- G4 score audit: accept with reduced score。Cycle 21 より独立した incidence carrier だが、
  actual linear `C0 -> C1` boundary、incidence matrix exactness、refinement failure、operation theorem は
  まだ入っていない。fail-closed に G4 の low bound を採用し、base 55、evidence multiplier 2.0、
  penalty 0、final +110 とする。

## Cycle 23 — Canonical reorg/refactor obstruction-killing criteria

candidate: `research/ideas/g-sft-conway-01-reorg-refactor-killing.md`
candidate_type: `closure`
evidence_stage: `proved-in-research`
base_score: 50
evidence_multiplier: 2.0
penalty: 10
final_score: 90
category: `reorg-refactor-duality`, `obstruction-killing`,
  `finite-operation`, `conway-obstruction`
goal_delta: Cycle 1 の `reorgedAtlas` / `refactoredAtlas` repaired examples を、
  canonical mismatch に対する finite operation-shaped compatibility criteria へ格上げした。
  `ReorgCoverEdit` は communication cover を編集し split ownership を保つ操作、
  `RefactorOwnershipEdit` は all-communication を保ち ownership cover を編集する操作である。
  それぞれに concrete `HitsEveryConflict` predicate を置き、post-edit compatibility と同値であること、
  canonical edit が hitting criterion を満たして selected Conway obstruction を kill することを証明した。
project_value_delta: reorg/refactor を単なる finite repaired examples から、canonical one-sided operation shape
  と post-edit compatibility criterion の theorem package へ進めた。ただし一般 family の最小 hitting theorem、
  partial edit の negative witness、arbitrary-cover operation calculus ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  reorg/refactor narrative を提案できるが、この cycle は canonical finite operation shape ごとに
  Lean-checked hitting criterion と obstruction-kill theorem を保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayReorgRefactorKilling.lean` と
  `lake build ResearchLean.AG.SFT.ConwayReorgRefactorKilling` が通過。
  `#print axioms` では reorg-side theorem と combined package は `propext` のみ、
  refactor-side theorem は axiom-free。`sorryAx` はない。
open_questions: partial edit が kill しない negative witness、pre/post transition relation from
  `mismatchedAtlas`、conflict set を計算して hit する一般 predicate、reorg-only/refactor-only separation、
  refinement naturality failure は未固定。Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayReorgRefactorKilling.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditHitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit.postCompatible_iff_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit.killsConwayObstruction_of_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_killsConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEditHitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit.postCompatible_iff_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit.killsConwayObstruction_of_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_killsConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CanonicalRepairOperation`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRepairOperation_killsConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedReorgRefactorKillingPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduced score。Cycle 1 repaired examples から canonical one-sided operation
  shape の判定条件へ前進している。ただし obstruction killing は `compatible_no_conwayObstruction` へ戻しており、
  一般 family の最小 hitting theorem、任意 edit 分類、reorg/refactor separation theorem ではない。
  G2 は base 60 / final +120 を推奨。
- G3 formalization quality: pass。hitting criteria は `ConwayObstructionWitness = false` を直接埋め込まず、
  reorg 側は platform/data block が対応 owner に support されること、refactor 側は single owner block が
  all-context を support することとして書かれている。claim は canonical finite operation criteria に限定している。
- G3 axiom audit: pass。reorg-side theorem と combined package は `propext` のみ、
  refactor-side theorem は axiom-free。`sorryAx` はない。
- G4 score audit: reduce。operation scaffold はあるが、中核は post-edit compatibility criterion の再表現であり、
  partial edit negative witness、pre/post transition relation、一般 conflict set hitting predicate は未実装。
  fail-closed に G4 の low bound を採用し、base 50、evidence multiplier 2.0、penalty 10、final +90 とする。

## Cycle 24 — Canonical reorg/refactor missed-conflict witnesses

candidate: `research/ideas/g-sft-conway-01-reorg-refactor-negative-witness.md`
candidate_type: `obstruction`
evidence_stage: `proved-in-research`
base_score: 40
evidence_multiplier: 2.0
penalty: 10
final_score: 70
category: `reorg-refactor-duality`, `negative-witness`,
  `finite-operation`, `conway-obstruction`
goal_delta: Cycle 23 の operation-shaped compatibility criteria に対して、canonical missed-conflict
  negative witness を追加した。`partialReorgMissesDbConflict` は platform communication block が
  API/DB の両方を見るため reorg hitting criterion を満たさず、post-edit compatible でもなく、
  実際に `ConwayObstructionWitness` を残す。`partialRefactorSupportsOnlyApi` は Cycle 23 の
  single-owner refactor shape 上で API のみを support し、hitting/compatibility failure を示す。
project_value_delta: Cycle 23 の「hit すれば kill」の正方向だけでなく、canonical conflict を外すと
  少なくとも reorg 側では obstruction が残ることを Lean witness として固定した。ただし一般 conflict set
  calculus や任意 partial edit theorem ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  partial repair narrative を出せるが、この cycle は canonical missed-conflict edit の failure を
  Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayReorgRefactorNegativeWitness.lean` と
  `lake build ResearchLean.AG.SFT.ConwayReorgRefactorNegativeWitness` が通過。
  `#print axioms` では reorg-side theorem と package は `propext` のみ、refactor-side theorem は
  axiom-free。`sorryAx` / `Classical.choice` / 追加 axiom はない。
open_questions: refactor-side two-owner obstruction witness、pre/post transition relation from `mismatchedAtlas`,
  general conflict-set hitting predicate、reorg-only/refactor-only separation、refinement naturality failure は未固定。
  Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayReorgRefactorNegativeWitness.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_not_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_not_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_nonzeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_not_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_not_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedReorgRefactorNegativeWitnessPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduced score。Cycle 23 に対し、criterion を外した finite edit を作り、
  reorg 側では actual `ConwayObstructionWitness` まで構成している。ただし新規性は Cycle 23 に依存し、
  refactor 側は single-owner shape のため obstruction witness ではなく hitting/compatibility failure に留まる。
  G2 は base 40、penalty 10、final +70 を推奨。
- G3 formalization quality: pass。reorg negative witness は platform が API/DB の両方を見る一方、
  split ownership では単一 owner が両方を support できないことを使っている。refactor 側は
  claim boundary 通り `not_hitsEveryConflict` / `not_compatible` に限定している。
- G3 axiom audit: pass。reorg-side theorem と package は `propext` のみ、refactor-side theorem は
  axiom-free。`sorryAx`、`Classical.choice`、追加 axiom はない。
- G4 score audit: reduce。Cycle 23 gap の一部は埋めたが、一般 theorem ではなく canonical finite
  missed-conflict witness であり、refactor 側が obstruction witness でない。fail-closed に
  base 40、evidence multiplier 2.0、penalty 10、final +70 とする。

## Cycle 25 — Communication-support assignment bridge

candidate: `research/ideas/g-sft-conway-01-communication-support-assignment.md`
candidate_type: `closure`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
category: `communication-support`, `finite-assignment`,
  `interface-closure`, `conway-obstruction`
goal_delta: Cycle 23/24 の operation-shaped compatibility criteria と missed-conflict
  witnesses を、一般の `CommunicationSupportAssignment` interface へ接続した。
  任意の `TwoCoverAtlas` について、communication compatibility は各 communication block を
  support する ownership block の explicit assignment が存在することと同値である。canonical
  mismatch と Cycle 24 の missed-conflict edits は assignment を持たず、canonical reorg/refactor
  repairs は explicit assignment、compatibility、zero selected Conway obstruction を持つ。
project_value_delta: `forall comm, exists owner` を都度展開する段階から、後続の transition /
  selector / preservation theorem が使える support-assignment carrier へ一段抽象化した。価値は
  新しい obstruction 現象ではなく interface closure である。ただし compatibility-to-assignment
  方向は存在命題からの choice であり、canonical assignment theorem や任意 repair calculus ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  support owner の対応関係を経験的に提案できるが、この cycle は finite Conway atlas 上で
  compatibility と explicit assignment data の同値、および canonical repairs / negative witnesses
  への接続を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCommunicationSupportAssignment.lean`
  が通過。`CommunicationSupportAssignment.ofCompatibility` は存在命題から assignment を作るため
  `Classical.choice` を使い、finite Prop 証明の一部は標準 `propext` に依存する。`sorryAx` /
  `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: assignment-preserving transition relation from `mismatchedAtlas` to canonical repairs,
  finite conflict-set hitting predicate、selector-preserving refinement naturality、refactor-side
  two-owner obstruction witness は未固定。Issue #2962 の active threshold 3000 にはこの cycle
  単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayCommunicationSupportAssignment.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationSupportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationSupportAssignment.toCompatibility`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationSupportAssignment.ofCompatibility`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationCoverCompatible_iff_supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CanonicalRepairOperation.supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CanonicalRepairOperation.compatible_of_supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_noCommunicationSupportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_noCommunicationSupportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_noCommunicationSupportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCommunicationSupportAssignmentPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduce。`CommunicationSupportAssignment` は後続の transition /
  selector / preservation theorem の受け皿として有用だが、中核は既存
  `CommunicationCoverCompatible := forall comm, exists owner, ...` の Skolemized interface 化であり、
  新しい obstruction receiver、repair calculus、canonical assignment ではない。G2 は
  base 30、multiplier 2.0、penalty 0、final +60 を推奨。
- G3 formalization quality: pass。重大指摘なし。focused check と module build は通過し、
  `sorry/admit/unsafe/axiom` は対象 Lean にない。axiom audit は `Classical.choice` と
  標準 `propext` の範囲で、`sorryAx` や repo 独自 axiom はない。
- G4 score audit: reduce。Cycle 23/24 の単なる restatement ではないが、一般 theorem の中核は
  存在命題の carrier 化であり、canonical repair / missed-conflict への接続は既存 theorem を
  assignment 側へ流している。fail-closed に G4 の下限を採用し、base 30、evidence multiplier 2.0、
  penalty 10、final +50 とする。

## Cycle 26 — Finite conflict table

candidate: `research/ideas/g-sft-conway-01-finite-conflict-table.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
category: `conway-obstruction`, `finite-conflict-table`,
  `communication-support`, `reorg-refactor-duality`
goal_delta: Cycle 23 の operation-shaped hitting predicates と Cycle 25 の
  communication-support assignment interface を、selected two-module Conway vocabulary の finite
  conflict table へ接続した。reorg/refactor それぞれについて、finite table は hitting predicate と同値であり、
  post-edit atlas の support-assignment existence とも同値である。canonical repairs は table を満たし、
  Cycle 24 の missed-conflict edits は table を満たさない。
project_value_delta: `forall context` 型の hitting criterion を有限表の明示的な判定面へ落とし、
  positive repairs / negative missed-hit witnesses / support assignments を一つの interface に揃えた。
  一般 conflict-set calculus の前段として使えるが、任意 cover の conflict enumeration ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  conflict を表として列挙できるが、この cycle は selected Conway edit shapes 上で table 判定、
  assignment existence、obstruction-killing criterion の接続を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayFiniteConflictTable.lean` と
  `lake build ResearchLean.AG.SFT.ConwayFiniteConflictTable`、`lake build FormalAGResearch` が通過。
  `#print axioms` は reorg table 側で標準 `propext`、support-assignment existence 接続で
  `Classical.choice` に依存する。`sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary-cover conflict-set calculus、assignment-preserving transition relation from
  `mismatchedAtlas`、selector-preserving refinement naturality、refactor-side two-owner obstruction witness は未固定。
  Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayFiniteConflictTable.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditFiniteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgCoverEditHitsEveryConflict_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit.supportAssignment_nonempty_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_not_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEditFiniteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit.supportAssignment_nonempty_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_not_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedFiniteConflictTablePackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduce。finite table interface は有用だが、中核は Cycle 23 の
  `forall context` hitting predicate を selected two-module vocabulary 上で有限個の conjunct へ展開し、
  Cycle 25 の support-assignment existence と接続するもの。新しい obstruction、一般 conflict-set
  calculus、任意 cover enumeration、repair transition theorem ではない。G2 は base 30、multiplier 2.0、
  penalty 10、final +50 を推奨。
- G3 formalization quality: pass once tracked and committed。Lean statement は selected two-module
  vocabulary に限定され、一般 conflict-set calculus や arbitrary cover までは主張しない。
  focused check、module build、`FormalAGResearch` は通過し、`sorry/admit/unsafe/axiom` は対象 Lean にない。
  axiom audit は `propext` と support-assignment existence 由来の `Classical.choice` に収まる。
- G4 score audit: reduce。Cycle 23/25 の単なる restatement だけではないが、同値の中核は
  `Module.api/db` の finite case split と既存 theorem の合成であり、assignment-preserving transition や
  一般 conflict-set calculus までは進まない。fail-closed に G2 の下限を採用し、base 30、
  evidence multiplier 2.0、penalty 10、final +50 とする。

## Cycle 27 — Repair transition objects

candidate: `research/ideas/g-sft-conway-01-repair-transition.md`
candidate_type: `transition`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
category: `conway-obstruction`, `repair-transition`,
  `communication-support`, `finite-operation`
goal_delta: canonical Conway mismatch から canonical one-sided repairs への before/after
  transition object を追加した。`ConwayRepairTransition` は before atlas の obstruction、after atlas の
  support-assignment existence、after atlas の zero selected obstruction を同時に保持する。canonical
  reorg/refactor repairs は `mismatchedAtlas` から各 post-edit atlas への transition として固定される。
  missed-conflict edits は transition failure として固定し、reorg miss は post-edit obstruction も保持する。
project_value_delta: Cycle 25/26 の assignment/table interface を、selected before/after transition
  vocabulary へ packaging した。これは単なる compatibility restatement ではなく、repair success と
  missed-hit failure を同じ transition vocabulary で扱うための基礎 interface である。ただし任意 repair
  calculus、transition law、composition、optimality theorem ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  repair narrative を出せるが、この cycle は selected finite Conway mismatch から repair / failure
  post-state への transition object を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayRepairTransition.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary repair calculus、assignment-preserving transition composition、general conflict-set
  hitting predicate、selector-preserving refinement naturality、refactor-side two-owner obstruction witness は未固定。
  Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayRepairTransition.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ConwayRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ConwayAssignmentFailedTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ConwayObstructionPreservingTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CanonicalRepairOperation.repairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CanonicalRepairOperation.repairTransition_before`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CanonicalRepairOperation.repairTransition_after`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_assignmentFailedTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_obstructionPreservingTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_assignmentFailedTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedRepairTransitionPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduce。first transition vocabulary として価値はあるが、中核は Cycle 25 の
  support-assignment existence と obstruction-killing theorem を record に束ね、Cycle 24/25 の
  missed-conflict negative facts を failure record に入れ直したもの。新しい repair calculus、composition、
  minimality、一般 conflict hitting、または repair impossibility theorem ではない。G2 は base 30、
  multiplier 2.0、penalty 10、final +50 を推奨。
- G3 formalization quality: pass with minor revisions。Lean statement は selected finite Conway vocabulary に
  留まり、任意 repair calculus、optimality、empirical causality、general conflict-set calculus までは主張しない。
  focused check、module build、`FormalAGResearch` は通過し、`sorry/admit/unsafe/axiom` は対象 Lean にない。
  axiom audit は標準 `propext` のみ。
- G4 score audit: reduce。Cycle 23/25/26 の単なる restatement ではないが、before/after transition
  object の第一歩であり、transition composition、assignment-preserving transition、一般 conflict-set
  calculus には未達。fail-closed に G2 の下限を採用し、base 30、evidence multiplier 2.0、
  penalty 10、final +50 とする。

## Cycle 28 — Repair transition criterion

candidate: `research/ideas/g-sft-conway-01-repair-transition-criterion.md`
candidate_type: `criterion`
evidence_stage: `proved-in-research`
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
category: `conway-obstruction`, `repair-transition`,
  `finite-conflict-table`, `communication-support`
goal_delta: selected reorg/refactor edit shapes について、finite conflict-table satisfaction が
  `mismatchedAtlas` から edit post-atlas への selected repair-transition record existence と同値であることを
  Lean theorem として固定した。canonical reorg/refactor edits は repair-transition record を実現し、
  selected missed-conflict reorg / API-only refactor edits はその record を実現しない。
project_value_delta: Cycle 27 の transition record packaging から一歩進み、edit が selected
  repair-transition record を実現するための判定条件を finite table interface で与えた。positive repair と missed-hit failure を
  同じ iff criterion で分類する。ただし任意 repair calculus、transition composition、一般 conflict-set
  calculus ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  repair success/failure を説明できるが、この cycle は selected edit shapes 上で repair transition
  existence の iff criterion を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayRepairTransitionCriterion.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary repair calculus、transition composition、general conflict-set calculus、
  selector-preserving refinement naturality、refactor-side two-owner obstruction witness は未固定。
  Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayRepairTransitionCriterion.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit.repairTransition_nonempty_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit.canonicalRepairTransition_nonempty`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEdit.partialMissesDbConflict_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEditRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit.repairTransition_nonempty_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit.canonicalRepairTransition_nonempty`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEdit.partialSupportsOnlyApi_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedRepairTransitionCriterionPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduce。finite table と repair-transition vocabulary をつなぐ有用な iff だが、
  中核は既存の `supportAssignment_nonempty_iff_finiteConflictTable` を `ConwayRepairTransition` wrapper へ
  持ち上げる合成であり、任意 repair calculus、transition composition、minimality、general conflict-set
  calculus、new obstruction receiver ではない。G2 は base 40、multiplier 2.0、penalty 10、final +70 を推奨。
- G3 formalization quality: pass once tracked and committed。Lean theorem は selected finite Conway vocabulary、
  selected edit shapes、finite table、`mismatchedAtlas -> edit.postAtlas` の record existence に限定される。
  focused check、module build、`FormalAGResearch` は通過し、`sorry/admit/unsafe/axiom` は対象 Lean にない。
  axiom audit は標準 `propext` と support-assignment existence 由来の `Classical.choice` に収まる。
- G4 score audit: reduce。Cycle 26/27 の単なる restatement ではないが、中核は finite table iff と
  transition record の合成であり、新しい repair calculus、composition、一般 conflict-set calculus までは
  進まない。fail-closed に G4 の下限を採用し、base 35、evidence multiplier 2.0、penalty 10、
  final +60 とする。

## Cycle 29 — Selected conflict-set interface

candidate: `research/ideas/g-sft-conway-01-selected-conflict-set.md`
candidate_type: `interface`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
category: `conway-obstruction`, `selected-conflict-set`,
  `repair-transition`, `finite-conflict-table`
goal_delta: selected reorg/refactor edit shapes について、hard-coded finite conflict tables を
  explicit selected table-obligation indices と hitting predicates へ factor した。selected hitting は
  finite-table satisfaction と同値であり、selected repair-transition record existence とも同値である。
  canonical repairs は selected obligation sets を hit し、missed-conflict edits は hit しない。
project_value_delta: finite table の conjunction syntax から explicit selected table-obligation vocabulary へ移した。
  これにより、後続 cycle で membership、refinement、conflict-set morphism を置ける bounded interface ができる。
  ただし任意 conflict enumeration algorithm や general repair calculus ではない。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  conflict を表として列挙できるが、この cycle は selected conflict indices、hitting predicate、repair-transition
  existence criterion の接続を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictSet.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary conflict-set calculus、conflict-set morphism、transition composition、
  selector-preserving refinement naturality、refactor-side two-owner obstruction witness は未固定。
  Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictSet.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgSelectedConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditHitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgHitsSelectedConflictSet_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_not_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorSelectedConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEditHitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorHitsSelectedConflictSet_iff_finiteConflictTable`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_not_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedConflictSetPackage`

G2 / G3 / G4 audit summary:

- G2 audit: accept with reduce。selected finite table の各 conjunct を `ReorgSelectedConflict` /
  `RefactorSelectedConflict` の finite index に移し、Cycle 26 finite table と Cycle 28
  repair-transition criterion に接続する点は有用。ただし新しい obstruction receiver、一般 conflict-set
  calculus、morphism/refinement theorem、enumeration algorithm ではない。G2 は base 30、multiplier 2.0、
  penalty 10、final +50 を推奨。
- G3 formalization quality: pass。reorg 側 hitting は `communication -> ownership` なので、通信がない
  entry は vacuous に hit される。これは actual conflict membership ではなく selected table obligation と
  読む限り bounded claim として問題ない。focused check、module build、`FormalAGResearch` は通過し、
  `sorry/admit/unsafe/axiom` は対象 Lean にない。axiom audit は標準 `propext` と support-assignment
  existence 由来の `Classical.choice` に収まる。
- G4 score audit: reduce。明示的 carrier と hitting predicate を置いた点は Cycle 28 より少し前進だが、
  中核は finite table との iff と repair-transition iff への合成であり、conflict enumeration、morphism、
  refinement naturality、transition composition、一般 conflict-set calculus は未固定。fail-closed に
  G2 の下限を採用し、base 30、evidence multiplier 2.0、penalty 10、final +50 とする。

## Cycle 30 — Selected conflict bridge

candidate: `research/ideas/g-sft-conway-01-selected-conflict-bridge.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 25
evidence_multiplier: 2.0
penalty: 10
final_score: 40
category: `conway-obstruction`, `selected-conflict-set`,
  `support-assignment`, `repair-transition`
goal_delta: Cycle 29 の selected conflict-set hitting を、Cycle 23 の operation-shaped hitting、
  Cycle 25 の support-assignment existence、Cycle 28 の repair-transition existence と接続した。
  selected conflict-set hitting は post-edit selected Conway obstruction を消す十分条件としても使える。
project_value_delta: selected conflict-set vocabulary を孤立した finite index ではなく、既存の repair
  existence criteria と同じ truth condition を持つ bounded bridge point にした。後続 cycle で
  membership、selector-preservation、refinement statement を置く入口になる。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  mismatch や owner incidence を可視化できるが、この cycle は selected conflict hitting が
  support-assignment / repair-transition existence と同値に読め、no-obstruction を含意することを Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictMorphism.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: general conflict-set morphism category、arbitrary conflict enumeration、repair composition、
  selector-preserving refinement naturality、refactor-side two-owner obstruction witness は未固定。
  Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictMorphism.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgHitsSelectedConflictSet_iff_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorHitsSelectedConflictSet_iff_hitsEveryConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgHitsSelectedConflictSet_iff_supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorHitsSelectedConflictSet_iff_supportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgNoConwayObstruction_of_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorNoConwayObstruction_of_hitsSelectedConflictSet`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedConflictBridgePackage`

G2 / G3 / G4 audit summary:

- G2 audit: pass。Cycle 29 の selected conflict-set interface を operation-shaped hitting、
  support-assignment existence、repair-transition existence、no-obstruction consequence に接続する bounded
  bridge として有用。ただし中核は既存 iff の合成であり、一般 conflict-set morphism category、arbitrary
  enumeration、repair composition、selector-preserving refinement naturality ではない。G2 は base 30、
  multiplier 2.0、penalty 10、final +50 を推奨。
- G3 formalization quality: pass。focused check と module build は通過し、`sorry/admit/unsafe/axiom` は
  対象 Lean にない。axiom audit は hitting bridge / no-obstruction bridge が標準 `propext`、
  support-assignment bridge と package が support-assignment existence 由来の `Classical.choice` を継承する。
  ファイル名 `Morphism` はやや強いが、本文と theorem は selected finite bridge に限定される。
- G4 score audit: reduce。`no-obstruction` は selected hitting からの帰結であり、同値 criterion ではないため
  wording を修正した。新規性は Cycle 29 predicate と Cycle 23/25/28 の既存 iff を finite table 経由で
  合成した bounded bridge に留まる。fail-closed に G4 の下限を採用し、base 25、
  evidence multiplier 2.0、penalty 10、final +40 とする。

## Cycle 31 — Refactor two-owner obstruction witness

candidate: `research/ideas/g-sft-conway-01-refactor-two-owner-obstruction.md`
candidate_type: `witness`
evidence_stage: `proved-in-research`
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
category: `conway-obstruction`, `refactor-failure`,
  `two-owner-witness`, `obstruction-preserving-transition`
goal_delta: Cycle 24 で single-owner refactor shape のため未固定だった refactor-side two-owner
  obstruction witness を追加した。all-communication block を保ちながら split two-owner ownership を
  保持する selected refactor failure shape を置き、その post-edit atlas が `mismatchedAtlas` と同じで、
  compatibility failure、support-assignment nonexistence、actual selected Conway obstruction、
  obstruction-preserving transition を持つことを Lean theorem として固定した。
project_value_delta: 以前の refactor negative witness は hitting / compatibility failure に留まったが、
  この cycle は refactor-side でも actual two-owner obstruction preservation を表現できる bounded
  edit shape を追加した。transition vocabulary とも接続し、selected bounded shape の範囲で
  open question を 1 つ閉じる。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  failed refactor や split ownership retention を説明できるが、この cycle は selected two-module Conway
  witness として obstruction-preserving transition まで Lean theorem で保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayRefactorTwoOwnerObstruction.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary refactor calculus、general transition composition、selector-preserving refinement
  naturality、arbitrary conflict enumeration は未固定。Issue #2962 の active threshold 3000 には
  この cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayRefactorTwoOwnerObstruction.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorTwoOwnerFailureEdit`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorTwoOwnerFailureEdit.postAtlas`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorKeepsSplitOwnership`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorKeepsSplitOwnership_postAtlas_eq_mismatchedAtlas`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorKeepsSplitOwnership_not_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorKeepsSplitOwnership_nonzeroConwayObstruction`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorKeepsSplitOwnership_noCommunicationSupportAssignment`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorKeepsSplitOwnership_obstructionPreservingTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedRefactorTwoOwnerObstructionPackage`

G2 / G3 / G4 audit summary:

- G2 audit: pass with reduce。Cycle 24 の single-owner refactor shape では置けなかった two-owner
  obstruction witness を、selected finite / bounded witness として閉じている。ただし中核は
  `refactorKeepsSplitOwnership.postAtlas = mismatchedAtlas` の definitional equality から既存の
  `mismatchedAtlas` obstruction / incompatibility / no-support 証拠を再包装する構成であり、
  新しい refactor calculus、分類定理、minimality、任意 partial refactor theorem、transition composition
  ではない。G2 は base 35、multiplier 2.0、penalty 10、final +60 を推奨。
- G3 formalization quality: pass。focused check、module build、`FormalAGResearch` は通過し、
  `sorry/admit/unsafe/axiom` は対象 Lean にない。axiom audit は対象 theorem が標準 `propext` に収まる。
  `Owner` には `productOwner` もあるが、この witness は `splitOwnership` の bounded two-owner shape を
  保存する claim として書かれている。
- G4 score audit: reduce。open question の selected finite closure として価値はあるが、
  obstruction-preserving transition も実質的には `mismatchedAtlas` から定義上同じ post-atlas への
  bounded record であり、+70/+80 水準の新しい obstruction / invariant / general criterion ではない。
  fail-closed に G2/G4 の一致した下限を採用し、base 35、evidence multiplier 2.0、penalty 10、
  final +60 とする。

## Cycle 32 — Selected conflict membership

candidate: `research/ideas/g-sft-conway-01-selected-conflict-membership.md`
candidate_type: `selector`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
category: `conway-obstruction`, `selected-conflict-set`,
  `membership`, `miss-selector`
goal_delta: selected reorg/refactor edit shapes について、selected hitting が pointwise selected miss
  の不存在と同値であることを追加した。canonical reorg/refactor edits は selected conflict を miss せず、
  existing partial reorg edit は exactly `platformDb`、API-only partial refactor edit は exactly `db`
  を miss する。
project_value_delta: selected conflict-set を aggregate hitting predicate から pointwise membership /
  exact miss selector へ進めた。後続の refinement / diagnostic theorem が failed finite table ではなく
  selected conflict identity を参照できる。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  conflict miss を報告できるが、この cycle は selected miss の同値条件と exact one-entry selector を
  Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictMembership.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary conflict enumeration、runtime diagnostic extraction、selector-preserving refinement
  naturality、general repair calculus は未固定。Issue #2962 の active threshold 3000 には
  この cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwaySelectedConflictMembership.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditActivatesSelectedConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditMissesSelectedConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgHitsSelectedConflictSet_iff_noSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_noSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_missesSelectedConflict_iff`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_hasSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEditMissesSelectedConflict`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorHitsSelectedConflictSet_iff_noSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_noSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_missesSelectedConflict_iff`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_hasSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedConflictMembershipPackage`

G2 / G3 / G4 audit summary:

- G2 audit: reduce。pointwise selected miss membership と exact miss selector は後続 diagnostic /
  refinement theorem の参照点として有用。ただし中核は既存の aggregate hitting predicate を
  `forall conflict, Not miss` に展開し、既存 partial edit の一箇所欠落を finite case split で固定したもの。
  新しい conflict enumeration、runtime diagnostic extraction、selector-preserving refinement naturality、
  general repair calculus、新 obstruction / invariant ではない。G2 は base 35、multiplier 2.0、
  penalty 10、final +60 を推奨。
- G3 formalization quality: pass。focused check、module build、`FormalAGResearch` は通過し、
  `sorry/admit/unsafe/axiom` は対象 Lean にない。axiom audit は no-miss iff / canonical no-miss /
  package が `propext`、既存 infrastructure 由来の `Classical.choice` / `Quot.sound` を継承し、
  exact selector theorem は標準 `propext` に収まる。
- G4 score audit: reduce。exact `platformDb` / `db` selector は便利だが、既存 partial edits の hard-coded
  finite cases を `simp` で分類するもの。canonical no-miss も既存 hit theorem からの帰結であり、
  +100 は過大。fail-closed に G4 の下限を採用し、base 30、evidence multiplier 2.0、
  penalty 10、final +50 とする。

## Cycle 33 — Selected miss scanner

candidate: `research/ideas/g-sft-conway-01-selected-miss-scanner.md`
candidate_type: `selector`
evidence_stage: `proved-in-research`
base_score: 30
evidence_multiplier: 2.0
penalty: 10
final_score: 50
category: `conway-obstruction`, `selected-conflict-set`,
  `first-miss-scanner`, `miss-selector`
goal_delta: selected reorg/refactor edit shapes について、bounded first-miss scanner predicate を追加した。
  first-miss scanner は selected miss existence に対して sound かつ complete である。canonical reorg/refactor
  edits は first miss を持たず、existing partial reorg edit は exactly `platformDb`、API-only partial
  refactor edit は exactly `db` を first miss とする。
project_value_delta: Cycle 32 の pointwise miss membership を、soundness / completeness / exact first
  identity を持つ bounded finite scanner interface へ進めた。bare existence theorem よりも後続の
  diagnostic extraction / refinement theorem へ接続しやすい。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  first failing conflict を返せるが、この cycle は selected finite Conway vocabulary 上で first miss
  の soundness / completeness と exact selector を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwaySelectedMissScanner.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: runtime extraction algorithm、arbitrary conflict enumeration、selector-preserving refinement
  naturality、general repair calculus は未固定。Issue #2962 の active threshold 3000 には
  この cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwaySelectedMissScanner.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ReorgCoverEditFirstSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgFirstSelectedMiss_sound`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgFirstSelectedMiss_exists_iff_hasSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_noFirstSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_firstSelectedMiss_iff`
- `ResearchLean.AG.SFT.ConwayTwoTopology.RefactorOwnershipEditFirstSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorFirstSelectedMiss_sound`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorFirstSelectedMiss_exists_iff_hasSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_noFirstSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_firstSelectedMiss_iff`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedMissScannerPackage`

G2 / G3 / G4 audit summary:

- G2 audit: reduce。Cycle 32 の pointwise miss membership を fixed finite order 上の
  `FirstSelectedMiss` predicate に持ち上げ、soundness / existence completeness / canonical no-first-miss /
  partial edit の exact first selector を Lean theorem として固定する点は有用。ただし中核は Cycle 32 の
  miss predicate と exact selector の ordered wrapper であり、runtime extraction algorithm、任意 conflict
  enumeration、selector-preserving refinement naturality、general repair calculus、新 obstruction / invariant
  ではない。G2 は base 30、multiplier 2.0、penalty 10、final +50 を推奨。
- G3 formalization quality: pass。focused check、module build、`FormalAGResearch` は通過し、
  `sorry/admit/unsafe/axiom` は対象 Lean にない。axiom audit は reorg/refactor existence iff と
  canonical no-first / package が `propext`、既存 infrastructure 由来の `Classical.choice` / `Quot.sound`
  を継承し、exact first selector は標準 `propext` に収まる。
- G4 score audit: reduce。bare pointwise miss membership から first-miss interface、sound/completeness、
  canonical no-first、partial exact first selector まで進めた増分はあるが、中核は selected finite vocabulary の
  Prop predicate と case split であり、+80 水準の新しい scanner calculus や実行可能診断ではない。
  fail-closed に G2 の下限を採用し、base 30、evidence multiplier 2.0、penalty 10、final +50 とする。

## Cycle 34 — Miss repair criterion

candidate: `research/ideas/g-sft-conway-01-miss-repair-criterion.md`
candidate_type: `criterion`
evidence_stage: `proved-in-research`
base_score: 35
evidence_multiplier: 2.0
penalty: 10
final_score: 60
category: `conway-obstruction`, `first-miss-scanner`,
  `repair-transition`, `criterion`
goal_delta: selected reorg/refactor edit shapes について、selected first miss existence が selected
  repair-transition record absence と同値であることを追加した。canonical repairs は no-first-miss と
  repair-transition existence が一致し、partial edits は first miss と no-repair-transition が一致する。
project_value_delta: first-miss selector を diagnostic wrapper から selected repair-transition criterion へ接続した。
  selected first miss は両 edit family で selected repair-transition record existence に対する complete
  obstruction として読める。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  first failing conflict を返せるが、この cycle は selected first miss と repair-transition nonexistence の
  iff criterion を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayMissRepairCriterion.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。
open_questions: arbitrary repair calculus、runtime extraction algorithm、arbitrary conflict enumeration、
  selector-preserving refinement naturality は未固定。Issue #2962 の active threshold 3000 には
  この cycle 単独では未到達。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayMissRepairCriterion.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgSelectedMiss_exists_iff_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgFirstSelectedMiss_exists_iff_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalReorgCoverEdit_repairTransition_iff_noFirstMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialReorgMissesDbConflict_firstMiss_iff_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorSelectedMiss_exists_iff_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorFirstSelectedMiss_exists_iff_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.canonicalRefactorOwnershipEdit_repairTransition_iff_noFirstMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.partialRefactorSupportsOnlyApi_firstMiss_iff_noRepairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedMissRepairCriterionPackage`

G2 / G3 / G4 audit summary:

- G2 audit: reduce。Cycle 33 の bounded first-miss scanner を Cycle 29/30 の selected
  repair-transition existence criterion に接続し、selected first miss が selected repair-transition record
  absence と同値になることを reorg/refactor 両方で固定した点は有用。ただし中核は
  `first miss exists ↔ selected miss exists`、`hits ↔ no selected miss`、
  `repair-transition nonempty ↔ hits` の既存 iff 合成であり、新しい obstruction、不変量、
  general repair calculus、runtime extraction、arbitrary conflict enumeration、selector-preserving refinement
  naturality ではない。G2 は base 35、multiplier 2.0、penalty 10、final +60 を推奨。
- G3 formalization quality: pass。focused check と module build は通過し、`sorry/admit/unsafe/axiom` は
  対象 Lean にない。axiom audit は reported theorem と package が標準 `propext`、既存 infrastructure
  由来の `Classical.choice` / `Quot.sound` を継承する。
- G4 score audit: reduce。canonical / partial examples は有用だが、汎用 iff の具体 edit への適用で、
  exact first selector 自体は Cycle 33 の成果。threshold 到達の都合で増点しない。fail-closed に
  G2/G4 の一致した下限を採用し、base 35、evidence multiplier 2.0、penalty 10、final +60 とする。

## Cycle 35 — No-miss repair criterion

candidate: `research/ideas/g-sft-conway-01-no-miss-repair-criterion.md`
candidate_type: `criterion`
evidence_stage: `proved-in-research`
base_score: 20
evidence_multiplier: 2.0
penalty: 10
final_score: 30
category: `conway-obstruction`, `first-miss-scanner`,
  `repair-transition`, `positive-criterion`
goal_delta: selected reorg/refactor edit shapes について、selected first miss がないこと、
  selected miss がないこと、selected repair-transition record が存在することが同値であることを追加した。
project_value_delta: Cycle 34 の negative miss criterion に対応する positive repair criterion を保存した。
  downstream theorem が double negation を通らず no-miss から repair-transition existence を直接参照できる。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  no failing conflict を repair success と読めるが、この cycle は selected finite Conway vocabulary 上で
  no-miss と repair-transition existence の同値を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayNoMissRepairCriterion.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。reported theorem は標準 `propext`、
  既存 infrastructure 由来の `Classical.choice` / `Quot.sound` を継承する。
open_questions: arbitrary repair calculus、runtime extraction algorithm、arbitrary conflict enumeration、
  selector-preserving refinement naturality は未固定。この cycle 後の ledger は 2960 -> 2990 / 3000 で、
  active threshold 3000 にはあと 10 残る。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayNoMissRepairCriterion.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgNoFirstSelectedMiss_iff_repairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorNoFirstSelectedMiss_iff_repairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgNoSelectedMiss_iff_repairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorNoSelectedMiss_iff_repairTransition`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedNoMissRepairCriterionPackage`

G2 / G3 / G4 audit summary:

- G2 audit: pass。positive repair criterion として no-first-miss / no-selected-miss /
  repair-transition existence を両 edit shape で直接参照できる増分を認め、base 25、multiplier 2.0、
  penalty 10、final +40 を許容した。
- G3 formalization quality: pass。focused check と module build は通過し、対象 theorem/package に
  `sorry/admit/unsafe/axiom` はない。axiom audit は標準 `propext` と、既存 infrastructure 由来の
  `Classical.choice` / `Quot.sound` 依存に収まる。
- G4 score audit: reduce。主な増分は Cycle 34 の `first miss exists ↔ no repair-transition` を
  positive side に反転し、既存 iff package と接続する点であり、新しい finite vocabulary、
  scanner、example、repair calculus ではない。threshold close のために増点せず、fail-closed に
  G4 の下限を採用し、base 20、evidence multiplier 2.0、penalty 10、final +30 とする。

## Cycle 36 — First-miss no-miss bridge

candidate: `research/ideas/g-sft-conway-01-first-miss-no-miss-bridge.md`
candidate_type: `bridge`
evidence_stage: `proved-in-research`
base_score: 15
evidence_multiplier: 2.0
penalty: 10
final_score: 20
category: `conway-obstruction`, `first-miss-scanner`,
  `selected-conflict-set`, `no-miss-criterion`
goal_delta: selected reorg/refactor edit shapes について、selected first miss がないことと
  pointwise selected miss がないことの直接同値を追加した。
project_value_delta: Cycle 33 の first-miss completeness を negative-side criterion として保存し、
  downstream theorem が existential scanner completeness を毎回展開せず no-first-miss と no-miss を
  相互参照できる。
rival_delta: Team Topologies / mirroring research、CODEOWNERS、org-network analysis、AI review は
  first failing conflict と no failing conflict を診断できるが、この cycle は selected finite Conway
  vocabulary 上で no-first-miss と pointwise no-selected-miss の同値を Lean theorem として保存する。
formalization_quality: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayFirstMissNoMissBridge.lean` が通過。
  `sorryAx` / `admit` / `unsafe` / 追加 axiom は使わない。reported theorem は標準 `propext`、
  既存 infrastructure 由来の `Classical.choice` / `Quot.sound` を継承する。
open_questions: arbitrary conflict enumeration、runtime extraction algorithm、general repair calculus、
  selector-preserving refinement naturality は未固定。この cycle 後の ledger は 2990 -> 3010 / 3000 で、
  Issue #2962 の active threshold 3000 に到達する。

Lean evidence:

- `research/lean/ResearchLean/AG/SFT/ConwayFirstMissNoMissBridge.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.reorgNoFirstSelectedMiss_iff_noSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.refactorNoFirstSelectedMiss_iff_noSelectedMiss`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedFirstMissNoMissBridgePackage`

G2 / G3 / G4 audit summary:

- G2 audit: reduce。Cycle36 は正しいが、主な増分は Cycle 33 の
  `exists first miss ↔ exists selected miss` を negative side の criterion として保存する点であり、
  新しい scanner、repair calculus、obstruction、不変量、例ではない。G2 は base 15、multiplier 2.0、
  penalty 10、final +20 を推奨。
- G3 formalization quality: pass。focused check、module build、`FormalAGResearch`、`git diff --check` は
  通過し、対象 Lean/card に `sorry/admit/unsafe/axiom/sorryAx` はない。axiom audit は reported theorem
  と package が標準 `propext`、既存 infrastructure 由来の `Classical.choice` / `Quot.sound` を継承する。
- G4 score audit: reduce。downstream API として no-first-miss と pointwise no-miss を直接参照できる
  価値はあるが、threshold 到達の都合は score に入れない。Cycle35 の repair-transition positive
  criterion より研究増分は小さいため、fail-closed に G2/G4 の一致した下限を採用し、base 15、
  evidence multiplier 2.0、penalty 10、final +20 とする。
