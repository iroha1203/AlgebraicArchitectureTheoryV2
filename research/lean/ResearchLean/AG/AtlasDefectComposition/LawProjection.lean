import ResearchLean.AG.AtlasDefectComposition.LawDefectDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawConeDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 実Law対象・実錐・実欠損を結ぶ同じprojection

Implementation notes: 全Law複体の同型から構成した実projectionを、比較正方形と標準錐へ通す。homology族の成分を同じ射へ同定し、短完全列の自然性に使う。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 実Law零延長から同じラベルblockへの実複体projection。 -/
def lawBlockZeroExtensionProjection (l : LawValueLabel laws) :
    zeroExtension (N.lawGeneratedComplex laws ha) ⟶ zeroExtension (N.lawValueBlockComplex laws ha l) :=
  (lawZeroExtensionIso N laws ha).hom ≫ FiniteComplexFamily.projection _ l
/-- 同じ実projectionは粗側・細側の独立生成比較と可換である。 -/
theorem lawBlockZeroExtensionProjection_natural (l : LawValueLabel laws) :
    zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫
      lawBlockZeroExtensionProjection E laws hr l =
    lawBlockZeroExtensionProjection N laws ha l ≫
      zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l) := by
  dsimp only [lawBlockZeroExtensionProjection]
  rw [← Category.assoc,lawZeroExtensionIso_natural,Category.assoc,
    FiniteComplexFamily.map_projection]
  simp only [Category.assoc]
/-- 全次数homologyのLaw同定の成分は同じ実projectionである。 -/
theorem lawStandardHomologyEquiv_component (m : ℤ)
    (x : (zeroExtension (N.lawGeneratedComplex laws ha)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv N laws ha m x l =
      homologyMap (lawBlockZeroExtensionProjection N laws ha l) m x := by
  exact lawStandardHomologyEquiv_component_family N laws ha m x l
/-- 同じprojection正方形から作る実Law錐のラベル射。 -/
def lawConeBlockProjection (l : LawValueLabel laws) :
    mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ⟶
      mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) :=
  mappingCone.map _ _ (lawBlockZeroExtensionProjection N laws ha l)
    (lawBlockZeroExtensionProjection E laws hr l)
      (lawBlockZeroExtensionProjection_natural N E laws ha M hr l)
/-- 実Law錐の族同型からのprojectionは標準錐正方形射そのものである。 -/
theorem lawConeFamilyIso_projection (l : LawValueLabel laws) :
    (lawConeFamilyIso N E laws ha M hr).hom ≫ FiniteComplexFamily.projection _ l =
      lawConeBlockProjection N E laws ha M hr l := by
  rw [lawConeFamilyIso_hom,Category.assoc]
  rw [FiniteConeFamily.iso_projection,coneMapIso_hom,← mappingCone.map_comp]
  rfl
/-- 全整数次数で実Law錐homologyの同定の成分は標準錐射である。 -/
theorem lawConeHomologyEquiv_component (m : ℤ)
    (x : (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m)
    (l : LawValueLabel laws) : lawConeHomologyEquiv N E laws ha M hr m x l =
      homologyMap (lawConeBlockProjection N E laws ha M hr l) m x := by
  rw [lawConeHomologyEquiv_component_family,lawConeFamilyIso_projection]
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
