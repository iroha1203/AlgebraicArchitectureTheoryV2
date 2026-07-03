# 研究ループ Lean API 索引

この文書は、`Formal/AG/Research` と research / target-theorem loop で追加された
theorem package の public Lean API を追跡する分割索引である。研究成果は canonical
mathematical text ではなく、GOAL card、tracking Issue、report、最終 review の境界に
相対化して読む。分割全体の入口は
[Lean 定義・定理索引](lean_theorem_index.md) を参照する。

`proof_obligations_research.md` は研究ループ側の theorem status 詳細台帳として扱い、
この文書は同じ範囲の実装済み Lean API を確認する詳細索引として扱う。

## Research Target Theorem Packages

Research target theorem artifacts live under `Formal/AG/Research/` and remain
research evidence, not canonical mathematical text. The GOAL card and tracking
Issue define the theorem boundary; this index records the public Lean API needed
for review.

File: `Formal/AG/Research/QualitySurface/SemanticRepairGluingComplex.lean`.
Certificate surface: `Formal/AG/Research/QualitySurface/SemanticRepairAdequacyDischarge.lean`.
Additional target theorem files: `Formal/AG/Research/QualitySurface/SemanticRepairTrueSheafH1.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairSheafH1.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairCechGrounding.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairLawEquationRealization.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairLawEquationWitnessInstance.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairLawEquationGroundedPacket.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairLawEquationEndToEndInstance.lean`,
`Formal/AG/Research/QualitySurface/SemanticRepairLawEquationNonzeroClassInstance.lean`.
Tracking Issue: [#2476](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2476).
Report: [`research/reports/G-aat-quality-surface-02.md`](../../research/reports/G-aat-quality-surface-02.md).
Final review: `$math-lean-review` passed with four `No major findings` lanes for
theorem strength, premise discharge / anti-weakening, Lean integrity, and
ledger sync. Completion is relative to the explicit complete-support finite
atlas class / certificate-discharged range.

| Lean 名 | 種別 | 意味 | Status |
| --- | --- | --- | --- |
| `SemanticRepairGluingComplex.FiniteSemanticRepairGluingComplex` | `structure` | finite semantic repair atlas、explicit chart list、explicit overlap / transition witness list `overlapOrder`、finite `C0` / `C1` lists、restriction-difference `delta0`、selected residual を束ねる。 | `defined only` |
| `SemanticRepairGluingComplex.overlapOrder_complete` | `theorem` | 任意の overlap / transition witness が `overlapOrder` に現れることを読む accessor。 | `proved` |
| `SemanticRepairGluingComplex.delta0_support_exact` | `theorem` | `delta0` が overlap 上の left / right restriction symmetric difference と一致する。 | `proved` |
| `SemanticRepairGluingComplex.B1`, `ObstructionClassVanishes`, `ObstructionClassNonzero` | `def` | finite `B1` boundary predicate、selected residual の boundary vanishing、nonzero obstruction predicate。 | `defined only` |
| `SemanticRepairGluingComplex.GlobalSemanticRepairCoherent` | `def` | boundary primitive と semantic closure を持つ global semantic repair coherent certificate の存在。 | `defined only` |
| `SemanticRepairGluingComplex.SemanticFaithfulnessHypotheses` | `structure` | boundary primitive から residual component coverage と residual-component faithfulness を得る sufficiency 用 premise surface。 | `defined only` |
| `SemanticRepairGluingComplex.globalRepairCoherent_forces_obstructionVanishes` | `theorem` | global semantic repair coherence から finite obstruction vanish を得る necessity direction。 | `proved` |
| `SemanticRepairGluingComplex.no_globalRepairCoherent_of_nonzero_obstruction` | `theorem` | nonzero finite obstruction から global semantic repair coherence 不在を得る contrapositive direction。 | `proved` |
| `SemanticRepairGluingComplex.globalRepairCoherent_of_obstructionVanishes`, `finiteSemanticRepairGluingDescent_iff` | `theorem` | `SemanticFaithfulnessHypotheses` の下で obstruction vanish から global coherence、および同値を得る conditional sufficiency package。 | `proved under explicit premise` |
| `SemanticRepairGluingComplex.CompleteRepairSupportBoundaryComplex` | `structure` | complete refined semantic repair support を持つ explicit finite atlas class。faithfulness / vanish / global coherence は field として持たない。 | `defined only` |
| `SemanticRepairGluingComplex.completeRepairSupportBoundary_semanticFaithfulnessHypotheses` | `theorem` | complete-support finite atlas class では `SemanticFaithfulnessHypotheses` が放電される。 | `proved` |
| `SemanticRepairGluingComplex.finiteSemanticRepairGluingDescent_iff_of_completeRepairSupportBoundary` | `theorem` | complete-support finite atlas class に相対化した finite semantic repair-gluing descent equivalence。 | `proved` |
| `SemanticRepairGluingComplex.selectedVisibleLocalWitnessComplex`, `selectedVisibleLocalWitness_obstructionNonzero`, `selectedVisibleLocalWitness_noGlobalRepairCoherent` | `def` / `theorem` | visible / local / component clearance だけでは finite obstruction が消えない calibration witness。 | `defined only` / `proved` |
| `SemanticRepairGluingComplex.selectedFaithfulBoundaryComplex`, `selectedFaithfulBoundary_descent_iff` | `def` / `theorem` | complete-support boundary による faithful calibration witness と finite descent equivalence。 | `defined only` / `proved` |
| `SemanticRepairGluingComplex.finiteSemanticRepairGluingDescent_package_of_completeRepairSupportBoundary` | `theorem` | necessity、contrapositive、sufficiency、faithfulness discharge、bridge theorem、witness validation を束ねた complete-support finite-class package。 | `proved` |
| `SemanticRepairAdequacyDischarge.completeRepairSupportBoundary_boundarySemanticClosureCertificate` | `def` | complete-support finite class から boundary-local coverage / faithfulness / semantic-closure bridge を持つ finite boundary certificate を構成する。 | `proved construction` |
| `SemanticRepairAdequacyDischarge.completeRepairSupportBoundary_semanticFaithfulnessHypotheses_of_boundaryCertificate` | `theorem` | `SemanticFaithfulnessHypotheses` を material premise として受け取らず、finite boundary certificate から導く。 | `proved` |
| `SemanticRepairAdequacyDischarge.finiteSemanticRepairGluingDescent_package_of_completeRepairSupportBoundary_via_dischargePrism` | `theorem` | complete-support finite-class package を explicit certificate / discharge prism surface 経由で読む。 | `proved` |

Non-conclusions: この package は arbitrary finite atlas descent、true sheaf
`H^1`、nonabelian / stacky descent、universal obstruction assignment、source
extraction completeness、ArchMap validation、runtime repair synthesis、whole-codebase
quality を主張しない。`SemanticFaithfulnessHypotheses` を generic theorem argument
として残す theorem は checkpoint であり、completion claim は
`CompleteRepairSupportBoundaryComplex` のような explicit finite atlas class に
相対化された discharge theorem と一緒に読む。
