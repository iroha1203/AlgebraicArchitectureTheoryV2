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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean` と
  `lake build Formal.AG.Research.SFT.ConwayBoundaryQuotient` が通過。`#print axioms` では主要 theorem が
  `propext`, `Classical.choice`, `Quot.sound` に依存する。G3 formalization quality は pass。
open_questions: true sheaf `H^1`、full quotient object、common-refinement exactness、comparison functor failure、
  arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkBoundarySubgroup`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportForkDefect_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportForkDefect_vanishes_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportForkNonzeroClass_iff_noSingleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.boundaryQuotientReceiver_iff_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.functionalFork_nonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.functionalFork_boundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_ownershipFunctional`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_nonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_boundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_boundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroBoundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroBoundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroBoundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedBoundaryQuotientReceiverPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayBoundaryGenerator.lean` が通過。
  `lake build Formal.AG.Research.SFT.ConwayBoundaryGenerator` も通過。`#print axioms` では
  `SupportForkBoundaryGenerator.ofSingleOwnerSupport` と `boundaryGenerator_nonempty_iff_singleOwnerSupport` が
  `Classical.choice` に依存し、subgroup / closure 系 theorem は `propext`, `Classical.choice`,
  `Quot.sound` に依存する。G3 formalization quality は pass。
open_questions: independent global boundary map、full quotient object、true sheaf `H^1`、common-refinement exactness、
  comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayBoundaryGenerator.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.boundaryGenerator_nonempty_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkGeneratorBoundarySubgroup`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGeneratorBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.generatorBoundary_absorbs_defect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.generatorBoundarySubgroup_le_predicateBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.functionalFork_noBoundaryGenerator`
- `Formal.AG.Research.SFT.ConwayTwoTopology.functionalFork_not_generatorBoundaryVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.GeneratorBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.generatorBoundaryReceiver_of_functionalFork`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_notGeneratorBoundaryVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_generatorBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_generatorBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroGeneratorBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroGeneratorBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroGeneratorBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedGeneratorBoundaryReceiverPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayBoundaryMap.lean`、
  `lake build Formal.AG.Research.SFT.ConwayBoundaryMap`、`lake build FormalAGResearch` が通過。
  `#print axioms` では `communicationZeroCochain_nonempty_iff_compatible` が `Classical.choice`、
  selected boundary theorem package が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: independent additive boundary on a nontrivial `C0` carrier, full quotient object、
  true sheaf `H^1`、common-refinement exactness、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayBoundaryMap.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommunicationZeroCochain`
- `Formal.AG.Research.SFT.ConwayTwoTopology.communicationZeroCochain_nonempty_iff_compatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkGlobalBoundaryMap`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGlobalBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.globalBoundary_vanishes_iff_compatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.globalBoundary_absorbs_defect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.globalBoundary_absorbs_into_generatorBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.GlobalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_globalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_noCommunicationZeroCochain`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_notGlobalBoundaryVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_globalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroGlobalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroGlobalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroGlobalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedGlobalBoundaryMapPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerChoiceBoundary.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerChoiceBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  `#print axioms` では主要 theorem が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: global additive `C0 -> C1` carrier、common-refinement exactness、true quotient object、
  true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerChoiceBoundary.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommunicationOwnerChoice`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerChoiceSupportsFork`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkOwnerChoiceBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloOwnerChoiceBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerChoiceBoundary_absorbs_iff_supportsFork`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerChoiceBoundary_vanishes_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.zeroCochain_ownerChoiceBoundary_absorbs`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerChoiceBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerChoiceBoundaryReceiver_iff_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_ownerChoiceBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_notOwnerChoiceBoundaryVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_ownerChoiceBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroOwnerChoiceBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroOwnerChoiceBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroOwnerChoiceBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerChoiceBoundaryPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerPotentialBoundary.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerPotentialBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  `#print axioms` では主要 theorem が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: constrained additive `C0 -> C1` complex、common-refinement exactness、true quotient object、
  true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerPotentialBoundary.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerPotential`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkOwnerPotentialBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloOwnerPotentialBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerPotentialBoundary_absorbs_of_endpointDifference`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedOwnerPotential`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedOwnerPotential_boundary_eq_defect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_ownerPotentialBoundaryVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_ownerChoiceReceiver_detects`
- `Formal.AG.Research.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_globalBoundary_detects`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerPotentialBoundaryPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`、
  `lake build Formal.AG.Research.SFT.ConwayConstrainedOwnerPotentialBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  `#print axioms` では主要 theorem が `propext`, `Classical.choice`, `Quot.sound` に依存する。
open_questions: common-refinement constrained boundary、global compatibility constrained potential、
  true quotient object、true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential`
- `Formal.AG.Research.SFT.ConwayTwoTopology.endpointSeparatingOwnerPotential`
- `Formal.AG.Research.SFT.ConwayTwoTopology.endpointSeparatingOwnerPotential_boundary_eq_defect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerPotentialBoundary_vanishes_of_decidableOwners`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportConstrainedOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportConstrainedOwnerPotentialReceiver_iff_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_supportConstrainedOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroSupportConstrainedOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroSupportConstrainedOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroSupportConstrainedOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedSupportConstrainedOwnerPotentialPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayCommonRefinementBoundary.lean`、
  `lake build FormalAGResearch`、full `lake build` が通過。`#print axioms` は
  `Classical.choice` / `propext` / `Quot.sound` に収まる。
open_questions: common-refinement exactness beyond support equivalence、global compatibility constrained potential、
  true quotient object、true sheaf `H^1`、comparison functor failure、arbitrary cover naturality は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayCommonRefinementBoundary.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommonRefinementSupportsFork`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommonRefinementSupportsFork.toSingleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommonRefinementSupportsFork.ofSingleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.commonRefinementSupportsFork_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloCommonRefinementOwnerPotential`
- `Formal.AG.Research.SFT.ConwayTwoTopology.commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommonRefinementOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.commonRefinementOwnerPotentialReceiver_iff_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_commonRefinementOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroCommonRefinementOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroCommonRefinementOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroCommonRefinementOwnerPotentialReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedCommonRefinementOwnerPotentialPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayGlobalCommonRefinementComparison.lean`、
  `lake build Formal.AG.Research.SFT.ConwayGlobalCommonRefinementComparison`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は `Classical.choice` / `propext` / `Quot.sound` に収まる。
open_questions: common-refinement exactness failure beyond global compatibility、arbitrary cover naturality、
  true quotient object、true sheaf `H^1`、comparison functor failure は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayGlobalCommonRefinementComparison.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommunicationZeroCochain.toCommonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.communicationZeroCochain_commonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGlobalCommonRefinement`
- `Formal.AG.Research.SFT.ConwayTwoTopology.globalCommonRefinement_vanishes_iff_compatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.globalCommonRefinement_implies_commonRefinementOwnerPotential`
- `Formal.AG.Research.SFT.ConwayTwoTopology.GlobalCommonRefinementReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.globalCommonRefinementReceiver_iff_globalBoundaryReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_notGlobalCommonRefinementVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_globalCommonRefinementReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroGlobalCommonRefinementReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroGlobalCommonRefinementReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroGlobalCommonRefinementReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedGlobalCommonRefinementComparisonPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayLocalVsGlobalCommonRefinement.lean`、
  `lake build Formal.AG.Research.SFT.ConwayLocalVsGlobalCommonRefinement`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は `Classical.choice` / `propext` / `Quot.sound` に収まる。
open_questions: arbitrary cover naturality、non-selected refinement span family、true quotient object、
  true sheaf `H^1`、comparison functor failure は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayLocalVsGlobalCommonRefinement.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_globalCommonRefinement_detects`
- `Formal.AG.Research.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_commonRefinementOwnerPotential_detects`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedLocalPotential_separatedBySupportAndGlobalCommonReceivers`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_noLocalGlobalCommonSeparationReceivers`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedLocalVsGlobalCommonRefinementPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayCoherentCommonRefinementFamily.lean`、
  `lake build Formal.AG.Research.SFT.ConwayCoherentCommonRefinementFamily`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は family construction では axiom-free、
  compatibility package で `Classical.choice` / `propext` に収まる。
open_questions: local support はあるが shared span が存在しない finite family、arbitrary cover naturality、
  non-selected refinement span family、true quotient object、true sheaf `H^1` は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayCoherentCommonRefinementFamily.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamily`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CoherentCommonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_implies_eachForkSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CommunicationZeroCochain.toCoherentCommonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.communicationZeroCochain_coherentCommonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement`
- `Formal.AG.Research.SFT.ConwayTwoTopology.familyCoherentGlobalCommonRefinement_vanishes_iff_compatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSingletonForkFamily_notCoherentGlobalCommonRefinementVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleEmptyForkFamily_coherentGlobalCommonRefinementVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedCoherentCommonRefinementFamilyPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayCoherentFamilyMorphism.lean`、
  `lake build Formal.AG.Research.SFT.ConwayCoherentFamilyMorphism`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は main declarations すべて axiom-free。
open_questions: arbitrary cover naturality、non-selected refinement span family、local support はあるが shared span が
  存在しない finite family、true quotient object、true sheaf `H^1` は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayCoherentFamilyMorphism.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamilyMorphism`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.id`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.comp`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.pullbackSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_pullback`
- `Formal.AG.Research.SFT.ConwayTwoTopology.coherentGlobalCommonRefinement_vanishes_pullback`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamily.reindex`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamily.reindexMorphism`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamily.subfamily`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamily.subfamilyInclusion`
- `Formal.AG.Research.SFT.ConwayTwoTopology.no_coherentFamilyMorphismNaturalityFailure`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedCoherentFamilyMorphismPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayCoherentFamilyExactness.lean`、
  `lake build Formal.AG.Research.SFT.ConwayCoherentFamilyExactness`、`lake build FormalAGResearch`、
  full `lake build` が通過。`#print axioms` は `Classical.choice` のみ。
open_questions: restricted common-refinement span vocabulary、non-selected refinement span family、arbitrary cover
  naturality blocker、true quotient object、true sheaf `H^1` は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayCoherentFamilyExactness.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ForkFamilyHasLocalCommonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.CoherentCommonRefinementSupport.ofEachForkSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_iff_eachForkSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ForkFamilyLocalButNotCoherent`
- `Formal.AG.Research.SFT.ConwayTwoTopology.no_forkFamilyLocalButNotCoherent`
- `Formal.AG.Research.SFT.ConwayTwoTopology.coherentGlobalCommonRefinementVanishes_implies_localSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.localSupport_and_globalZeroCochain_implies_coherentVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedCoherentFamilyExactnessPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayRestrictedCoherentFamily.lean`、
  `lake build Formal.AG.Research.SFT.ConwayRestrictedCoherentFamily`、`lake build FormalAGResearch`、
  full `lake build` が通過。core owner-uniform support theorem は axiom-free、finite package は
  `propext` / `Classical.choice` に依存。
open_questions: arbitrary cover naturality、non-selected refinement span family、true quotient object、
  true sheaf `H^1` は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayRestrictedCoherentFamily.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformCoherentCommonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformCoherentCommonRefinementSupport.sharedOwner_supports`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformSupport_implies_coherentSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_localSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_notOwnerUniformCoherent`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformLocalButNotCoherentReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedRestrictedCoherentFamilyPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerUniformSubfamilyDescent.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerUniformSubfamilyDescent`、`lake build FormalAGResearch`、
  full `lake build` が通過。新 receiver 定義は axiom-free、finite package は `propext` のみに依存。
open_questions: arbitrary cover naturality、non-selected refinement span family、owner-uniform quotient object、
  true sheaf `H^1` は未固定。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerUniformSubfamilyDescent.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkFamilySubcover`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformSubfamilyDescentFailure`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedApiSingletonFamily`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedDbSingletonFamily`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedApiSingletonFamily_ownerUniformSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedDbSingletonFamily_ownerUniformSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_cover`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformSubfamilyDescentFailure`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerUniformSubfamilyDescentPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerUniformFamilyQuotient.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerUniformFamilyQuotient`、
  `lake build FormalAGResearch`、full `lake build` が通過。
  full build は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。true sheaf `H^1`、arbitrary-cover naturality、
  functorial quotient は主張しない。
open_questions: arbitrary cover naturality、non-selected refinement span selector、true quotient object、
  true sheaf `H^1` は未固定。Issue #2962 の active threshold 2000 にはこの cycle 単独では未到達。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerUniformFamilyQuotient.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformFamilyDefect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyDefect_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformFamilyBoundaryGenerator`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyBoundaryGenerator_nonempty_iff_support`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformFamilyBoundarySubgroup`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformFamilyClassVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformFamilyNonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyBoundary_absorbs_defect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyBoundarySubgroup_le_bot_of_noSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyClass_nonzero_of_noSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyClass_vanishes_iff_support`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformFamilyClass_vanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformFamilyClass_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerUniformFamilyQuotientPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerUniformSpanSelector.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerUniformSpanSelector`、
  `lake build FormalAGResearch`、full `lake build` が通過。
  full build は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。
  canonical selector、arbitrary non-selected span functoriality、arbitrary-cover naturality、true sheaf `H^1` は主張しない。
open_questions: arbitrary cover naturality、true quotient object、true sheaf `H^1` は未固定。
  Issue #2962 の active threshold 2000 にはこの cycle 単独では未到達。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerUniformSpanSelector.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ForkwiseCommonRefinementSpanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.forkwiseSpanSelector_nonempty_iff_localSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformSpanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformSpanSelector.toOwnerUniformSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformSpanSelector_nonempty_iff_support`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformSpanSelectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedApiFork_commonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedDbFork_commonRefinementSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_forkwiseSpanSelectable`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_noOwnerUniformSpanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformSpanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerUniformSpanSelectorObstructionPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerUniformSelectorQuotientBridge`、`lake build FormalAGResearch`、
  full `lake build` が通過。full build は既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の
  linter warning のみ。
open_questions: arbitrary cover naturality、true quotient object、true sheaf `H^1` は未固定。
  Issue #2962 の active threshold 2000 にはこの cycle で到達見込み。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformSpanSelector_nonempty_iff_familyClassVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyClassVanishes_of_spanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformSpanSelector_of_familyClassVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyNonzeroClass_iff_noSpanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformFamilyNonzeroClass_of_spanSelectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformSpanSelectorObstruction_of_forkwiseSelectable_nonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_spanSelectorObstruction_iff_familyClassNonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_spanSelectorObstruction_implies_familyClassNonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_familyClassNonzero_implies_spanSelectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_spanSelector_and_familyClassVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerUniformSelectorQuotientBridgePackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerUniformTrueQuotient.lean`、
  `lake build Formal.AG.Research.SFT.ConwayOwnerUniformTrueQuotient`、`lake build FormalAGResearch` が通過。
  `#print axioms` は reported declarations について `propext`, `Classical.choice`, `Quot.sound` のみで
  `sorryAx` はない。
open_questions: arbitrary-cover naturality、universal quotient property、true sheaf `H^1`、
  relative nerve / Cech shadow は未固定。Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerUniformTrueQuotient.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformConwayQuotient`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformConwayClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformConwayClass_eq_zero_iff_familyClassVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformConwayClass_eq_zero_iff_spanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformConwayClass_ne_zero_iff_selectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformConwayClass_ne_zero_iff_familyNonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_ownerUniformConwayClass_zero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformConwayClass_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_conwayClass_nonzero_iff_selectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerUniformTrueQuotientPackage`

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
formalization_quality: `lake env lean Formal/AG/Research/SFT/ConwayOwnerUniformRelativeCechShadow.lean` と
  `lake build Formal.AG.Research.SFT.ConwayOwnerUniformRelativeCechShadow` が通過。
  `#print axioms` は reported declarations について `propext`, `Classical.choice`, `Quot.sound`
  のみで `sorryAx` はない。
open_questions: independent relative nerve / intersection indexing、arbitrary-cover naturality、
  reorg/refactor obstruction-killing operation theorem、review-route comparison、true sheaf `H^1`
  は未固定。Issue #2962 の active threshold 3000 にはこの cycle 単独では未到達。

Lean evidence:

- `Formal/AG/Research/SFT/ConwayOwnerUniformRelativeCechShadow.lean`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformRelativeCechCochain0`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformRelativeCechBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformRelativeCechBoundaryImage`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformRelativeCechBoundaryImage_eq_familyBoundarySubgroup`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformRelativeCechShadow`
- `Formal.AG.Research.SFT.ConwayTwoTopology.OwnerUniformRelativeCechClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_eq_zero_iff_familyClassVanishes`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_eq_zero_iff_conwayClass_zero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_ne_zero_iff_conwayClass_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownerUniformRelativeCechClass_eq_zero_iff_spanSelector`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedSingletonSubfamilies_relativeCechClass_zero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_relativeCechClass_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.restrictedTwoForkFamily_relativeCechClass_nonzero_iff_selectorObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedOwnerUniformRelativeCechShadowPackage`

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
