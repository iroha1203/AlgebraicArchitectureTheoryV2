import ResearchLean.AG.AtlasDefectComposition.HomologyConjugation
import Formal.Util.AssertStandardAxioms
/-! # 名付き計算の実生成比較への接続

全台の三成分同定正方形により、標準homology比較と標準錐の全次数を移す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
variable (M : TargetSupportedNerveMorphism q r h D E)
variable (laws : FiniteLawFamily Source) (hq : laws.Adequate q) (hr : laws.Adequate r)
variable (hD0 : ∀ c, D.chartSupport c = Set.univ) (hD1 : ∀ e, D.edgeSupport e = Set.univ)
variable (hD2 : ∀ f, D.faceSupport f = Set.univ)
variable (hE0 : ∀ c, E.chartSupport c = Set.univ) (hE1 : ∀ e, E.edgeSupport e = Set.univ)
variable (hE2 : ∀ f, E.faceSupport f = Set.univ) (label : LawValueLabel laws)
/-- 同じ原始入力の実block比較と名付き比較は全次数で同じ欠損を持つ。 -/
theorem fullBlockNamedHomology_defect (m : ℤ) :
    blockDefect (HomologicalComplex.homologyMap
      (zeroExtensionMap (M.generatedBlockComparisonHom laws hq hr label)) m).hom =
    blockDefect (HomologicalComplex.homologyMap
      (zeroExtensionMap (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label)) m).hom :=
  homologyConjugation_defect _ _
    (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label))
    (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label))
    (namedComparison_zeroExtension_square M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label) m
/-- 同じ実block比較の標準錐homologyは名付き計算と全次数で等次元である。 -/
theorem fullBlockNamedCone_homology_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone (M.generatedBlockComparisonHom laws hq hr label)).homology m) =
    Module.finrank ℚ ((comparisonCone
      (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label)).homology m) :=
  (HomologicalComplex.homologyMapIso
    (fullBlockNamedConeIso M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label) m).toLinearEquiv.finrank_eq
/-- 同じ実block比較の標準錐の空間も名付き計算と全次数で等次元である。 -/
theorem fullBlockNamedCone_degree_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone (M.generatedBlockComparisonHom laws hq hr label)).X m) =
    Module.finrank ℚ ((comparisonCone
      (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label)).X m) :=
  ((HomologicalComplex.eval _ _ m).mapIso
    (fullBlockNamedConeIso M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label)).toLinearEquiv.finrank_eq
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
