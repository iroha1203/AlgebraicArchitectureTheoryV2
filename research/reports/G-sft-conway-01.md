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
