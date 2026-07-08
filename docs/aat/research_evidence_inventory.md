# Research 成果棚卸し台帳(research evidence inventory)

`Formal/AG/Research/` の宣言を、索引登録済みの受理成果と、その証明・探索を
支える支持補題 / 足場へ全数勘定するための台帳。

現時点の表は `docs/aat/research_evidence_index_backfill_prd.md` R2 の
小塔先行棚卸し slice であり、`Basic.lean`、`SFTDynamics/`、`SFT/` を対象にする。
QualitySurface 一般ファイル群と `SemanticRepairCechGrounding.lean` は未棚卸しで、
AC1 全体の完了根拠ではない。

## 記載契約

- 1行 = 1 Lean ファイル。
- 区分語彙は3値とする。
  - `spine`: 受理された研究成果の中核宣言(theorem / 主要 def / structure)。`docs/aat/research_evidence_index.md` に1行ずつ登録する。
  - `support`: spine の証明を支えるが単独では受理成果でない補題・構成。索引には登録せず、この台帳で件数と代表名を勘定する。
  - `scaffold`: cycle 足場、premise 順列帯、再入口変種、checkpoint 帯、探索残骸。索引には登録せず、この台帳で件数と帯の説明を勘定する。
- ファイルごとに `spine 件数 + support 件数 + scaffold 件数 = 宣言総数` を満たす。
- 宣言総数は次で数える。

```bash
rg -c "^(theorem|def|lemma|structure|class|inductive|abbrev|instance)\s" <file>
```

- 区分の一次証拠は、受理記録(`research/reports/` の cycle section・proof portfolio、候補カード)と Lean statement の実読である。宣言名の字面・ファイル内の位置だけで区分しない。
- spine と判定したが受理記録(report / 候補カード)に遡れない宣言は、索引の `受理` 列を `unrecorded (backfill)` とする。
- `ported` 判定は本体側宣言名+conjunct 対応の確認記録が必須である。`unported` が既定値。
- この台帳は Research corpus を変更しない。発見した疑義は tracking Issue へ finding として記録する。

## Inventory

| file | 宣言総数 | spine | support | scaffold | 突合 | support / scaffold 帯 |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| `Formal/AG/Research/Basic.lean` | 1 | 0 | 0 | 1 | 0+0+1=1 | sandbox 生存確認 `sandbox_alive` |
| `Formal/AG/Research/SFTDynamics/TraceSite.lean` | 12 | 0 | 12 | 0 | 0+12+0=12 | L1 finite trace DAG / merge family / diamond / trajectory carrier と canonical diamond facts |
| `Formal/AG/Research/SFTDynamics/ForceSchema.lean` | 7 | 1 | 6 | 0 | 1+6+0=7 | spine: `ForceSchema.distant_commute`; support: `ForceSchema`, `DisjointClosures`, order-left lemma, merge config API |
| `Formal/AG/Research/SFTDynamics/MergeResidue.lean` | 12 | 1 | 11 | 0 | 1+11+0=12 | spine: `roundingDatum_not_obstructionVanishes`; support: two-branch law datum, stage-1 membership API, zero residue bridge, resolved datum |
| `Formal/AG/Research/SFT/ConwayTwoTopology.lean` | 25 | 1 | 24 | 0 | 1+24+0=25 | spine: `selectedConwayTwoCoverWitnessPackage`; support: two-cover atlas, compatible/mismatched/repaired witness lemmas |
| `Formal/AG/Research/SFT/ConwaySupportReceiver.lean` | 19 | 1 | 18 | 0 | 1+18+0=19 | spine: `selectedSupportReceiverPackage`; support: refinement / support receiver equivalences and selected examples |
| `Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean` | 22 | 1 | 21 | 0 | 1+21+0=22 | spine: `selectedBoundaryQuotientReceiverPackage`; support: `ZMod 2` defect, quotient receiver, functional fork facts |
| `Formal/AG/Research/SFT/ConwayBoundaryGenerator.lean` | 17 | 1 | 16 | 0 | 1+16+0=17 | spine: `selectedGeneratorBoundaryReceiverPackage`; support: explicit generator, subgroup membership, selected examples |
| `Formal/AG/Research/SFT/ConwayBoundaryMap.lean` | 20 | 1 | 19 | 0 | 1+19+0=20 | spine: `selectedGlobalBoundaryMapPackage`; support: global zero-cochain, selected map, receiver lemmas |
| `Formal/AG/Research/SFT/ConwayOwnerChoiceBoundary.lean` | 16 | 1 | 15 | 0 | 1+15+0=16 | spine: `selectedOwnerChoiceBoundaryPackage`; support: owner choice witness, receiver equivalence, examples |
| `Formal/AG/Research/SFT/ConwayOwnerPotentialBoundary.lean` | 10 | 1 | 9 | 0 | 1+9+0=10 | spine: `selectedOwnerPotentialBoundaryPackage`; support: local owner-potential absorption / weakness facts |
| `Formal/AG/Research/SFT/ConwayConstrainedOwnerPotentialBoundary.lean` | 14 | 1 | 13 | 0 | 1+13+0=14 | spine: `selectedSupportConstrainedOwnerPotentialPackage`; support: support-constrained owner-potential receiver facts |
| `Formal/AG/Research/SFT/ConwayCommonRefinementBoundary.lean` | 14 | 1 | 13 | 0 | 1+13+0=14 | spine: `selectedCommonRefinementOwnerPotentialPackage`; support: common-refinement support and receiver facts |
| `Formal/AG/Research/SFT/ConwayGlobalCommonRefinementComparison.lean` | 14 | 1 | 13 | 0 | 1+13+0=14 | spine: `selectedGlobalCommonRefinementComparisonPackage`; support: global/common-refinement comparison facts |
| `Formal/AG/Research/SFT/ConwayLocalVsGlobalCommonRefinement.lean` | 5 | 1 | 4 | 0 | 1+4+0=5 | spine: `selectedLocalVsGlobalCommonRefinementPackage`; support: local/global separation receiver facts |
| `Formal/AG/Research/SFT/ConwayCoherentCommonRefinementFamily.lean` | 14 | 1 | 13 | 0 | 1+13+0=14 | spine: `selectedCoherentCommonRefinementFamilyPackage`; support: coherent family support carriers and examples |
| `Formal/AG/Research/SFT/ConwayCoherentFamilyMorphism.lean` | 15 | 1 | 14 | 0 | 1+14+0=15 | spine: `selectedCoherentFamilyMorphismPackage`; support: strict fork-preserving morphism and naturality facts |
| `Formal/AG/Research/SFT/ConwayCoherentFamilyExactness.lean` | 7 | 1 | 6 | 0 | 1+6+0=7 | spine: `selectedCoherentFamilyExactnessPackage`; support: local support / shared span exactness facts |
| `Formal/AG/Research/SFT/ConwayRestrictedCoherentFamily.lean` | 22 | 1 | 21 | 0 | 1+21+0=22 | spine: `selectedRestrictedCoherentFamilyPackage`; support: restricted communication/ownership atlas and receiver facts |
| `Formal/AG/Research/SFT/ConwayOwnerUniformSubfamilyDescent.lean` | 14 | 1 | 13 | 0 | 1+13+0=14 | spine: `selectedOwnerUniformSubfamilyDescentPackage`; support: owner-uniform subfamily support and descent failure facts |
| `Formal/AG/Research/SFT/ConwayOwnerUniformFamilyQuotient.lean` | 18 | 1 | 17 | 0 | 1+17+0=18 | spine: `selectedOwnerUniformFamilyQuotientPackage`; support: family quotient receiver and nonzero class facts |
| `Formal/AG/Research/SFT/ConwayOwnerUniformSpanSelector.lean` | 19 | 1 | 18 | 0 | 1+18+0=19 | spine: `selectedOwnerUniformSpanSelectorObstructionPackage`; support: span selector, obstruction, selected families |
| `Formal/AG/Research/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean` | 13 | 1 | 12 | 0 | 1+12+0=13 | spine: `selectedOwnerUniformSelectorQuotientBridgePackage`; support: selector / quotient equivalence facts |
| `Formal/AG/Research/SFT/ConwayOwnerUniformTrueQuotient.lean` | 10 | 1 | 9 | 0 | 1+9+0=10 | spine: `selectedOwnerUniformTrueQuotientPackage`; support: selected finite quotient carrier facts |
| `Formal/AG/Research/SFT/ConwayOwnerUniformRelativeCechShadow.lean` | 14 | 1 | 13 | 0 | 1+13+0=14 | spine: `selectedOwnerUniformRelativeCechShadowPackage`; support: finite cochain shadow and class comparison facts |
| `Formal/AG/Research/SFT/ConwayOwnerUniformIncidenceReceiver.lean` | 19 | 1 | 18 | 0 | 1+18+0=19 | spine: `selectedOwnerUniformIncidenceReceiverPackage`; support: owner/fork incidence carrier and receiver facts |
| `Formal/AG/Research/SFT/ConwayReorgRefactorKilling.lean` | 20 | 1 | 19 | 0 | 1+19+0=20 | spine: `selectedReorgRefactorKillingPackage`; support: canonical reorg/refactor edit criteria and examples |
| `Formal/AG/Research/SFT/ConwayReorgRefactorNegativeWitness.lean` | 8 | 1 | 7 | 0 | 1+7+0=8 | spine: `selectedReorgRefactorNegativeWitnessPackage`; support: missed-conflict witness facts |
| `Formal/AG/Research/SFT/ConwayCommunicationSupportAssignment.lean` | 11 | 1 | 10 | 0 | 1+10+0=11 | spine: `selectedCommunicationSupportAssignmentPackage`; support: support assignment equivalences and examples |
| `Formal/AG/Research/SFT/ConwayFiniteConflictTable.lean` | 11 | 1 | 10 | 0 | 1+10+0=11 | spine: `selectedFiniteConflictTablePackage`; support: finite conflict table equivalences and examples |
| `Formal/AG/Research/SFT/ConwayRepairTransition.lean` | 10 | 1 | 9 | 0 | 1+9+0=10 | spine: `selectedRepairTransitionPackage`; support: before/after transition records and examples |
| `Formal/AG/Research/SFT/ConwayRepairTransitionCriterion.lean` | 9 | 1 | 8 | 0 | 1+8+0=9 | spine: `selectedRepairTransitionCriterionPackage`; support: selected transition criterion facts |
| `Formal/AG/Research/SFT/ConwaySelectedConflictSet.lean` | 19 | 1 | 18 | 0 | 1+18+0=19 | spine: `selectedConflictSetPackage`; support: selected conflict carriers and hitting predicates |
| `Formal/AG/Research/SFT/ConwaySelectedConflictMorphism.lean` | 7 | 1 | 6 | 0 | 1+6+0=7 | spine: `selectedConflictBridgePackage`; support: conflict-set morphism equivalences |
| `Formal/AG/Research/SFT/ConwayRefactorTwoOwnerObstruction.lean` | 9 | 1 | 8 | 0 | 1+8+0=9 | spine: `selectedRefactorTwoOwnerObstructionPackage`; support: two-owner refactor witness facts |
| `Formal/AG/Research/SFT/ConwaySelectedConflictMembership.lean` | 12 | 1 | 11 | 0 | 1+11+0=12 | spine: `selectedConflictMembershipPackage`; support: pointwise miss membership facts |
| `Formal/AG/Research/SFT/ConwaySelectedMissScanner.lean` | 11 | 1 | 10 | 0 | 1+10+0=11 | spine: `selectedMissScannerPackage`; support: first-miss scanner soundness/completeness facts |
| `Formal/AG/Research/SFT/ConwayMissRepairCriterion.lean` | 9 | 1 | 8 | 0 | 1+8+0=9 | spine: `selectedMissRepairCriterionPackage`; support: negative-side repair criterion facts |
| `Formal/AG/Research/SFT/ConwayNoMissRepairCriterion.lean` | 5 | 1 | 4 | 0 | 1+4+0=5 | spine: `selectedNoMissRepairCriterionPackage`; support: positive no-miss criterion facts |
| `Formal/AG/Research/SFT/ConwayFirstMissNoMissBridge.lean` | 3 | 1 | 2 | 0 | 1+2+0=3 | spine: `selectedFirstMissNoMissBridgePackage`; support: first-miss / no-miss bridge facts |
