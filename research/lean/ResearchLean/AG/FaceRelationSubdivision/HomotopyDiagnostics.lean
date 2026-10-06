import ResearchLean.AG.FaceRelationSubdivision.ThreeHomotopy
import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence
import ResearchLean.AG.UniformInvariance.DefectSemantics
import Formal.Util.AssertStandardAxioms

/-!
# 同じ標準射のホモトピーと実診断

## Implementation notes

一般補題の標準同値は方向入力で、基本操作への適用では原始表から生成する。
旧H1の同型の射を自然性で同定し、標準錐の実短完全列から全次数零性を導く。
有限次元や次元一致を錐零性の仮定とする方法は使用しない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open TwoPhase AtlasDefectComposition ResolutionInvariance
universe u
variable {C D : ThreeCochainComplex.{0,u} ℚ}

/-- 同じ標準ホモトピー同値を既存H1商の同型へ読み戻す。 -/
def homotopyOldH1Iso (E : HomotopyEquiv (zeroExtension C) (zeroExtension D)) :
    ModuleCat.of ℚ C.H1 ≅ ModuleCat.of ℚ D.H1 :=
  oldH1Iso C ≪≫ E.toHomologyIso 1 ≪≫ (oldH1Iso D).symm

/-- 読み戻した同型の射は、指定された同じ実Homのh1Mapである。 -/
theorem homotopyOldH1Iso_hom (E : HomotopyEquiv (zeroExtension C) (zeroExtension D))
    (f : ThreeCochainComplex.Hom C D) (hf : E.hom = zeroExtensionMap f) :
    (homotopyOldH1Iso E).hom = ModuleCat.ofHom f.h1Map := by
  change ((oldH1Iso C).hom ≫ HomologicalComplex.homologyMap E.hom 1) ≫ (oldH1Iso D).inv = _
  rw [hf, oldH1Iso_natural]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 読み戻した逆射も指定された同じ実Homのh1Mapである。 -/
theorem homotopyOldH1Iso_inv (E : HomotopyEquiv (zeroExtension C) (zeroExtension D))
    (g : ThreeCochainComplex.Hom D C) (hg : E.inv = zeroExtensionMap g) :
    (homotopyOldH1Iso E).inv = ModuleCat.ofHom g.h1Map := by
  change (oldH1Iso D).hom ≫ (HomologicalComplex.homologyMap E.inv 1 ≫ (oldH1Iso C).inv) = _
  rw [← Category.assoc, hg, oldH1Iso_natural]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 同じ実H1比較は標準同値により全単射となる。 -/
theorem homotopyH1_bijective (E : HomotopyEquiv (zeroExtension C) (zeroExtension D))
    (f : ThreeCochainComplex.Hom C D) (hf : E.hom = zeroExtensionMap f) :
    Function.Bijective f.h1Map := by
  have hb := (homotopyOldH1Iso E).toLinearEquiv.bijective
  have hfun : ⇑(homotopyOldH1Iso E).toLinearEquiv = ⇑f.h1Map := by
    funext x
    rw [Iso.toLinearEquiv_apply, homotopyOldH1Iso_hom E f hf]
    rfl
  rw [hfun] at hb
  exact hb

/-- 同じ実H1比較の核・余核の二成分はともに零。 -/
theorem homotopyH1_blockDefect_zero [FiniteDimensional ℚ C.H1] [FiniteDimensional ℚ D.H1]
    (E : HomotopyEquiv (zeroExtension C) (zeroExtension D))
    (f : ThreeCochainComplex.Hom C D) (hf : E.hom = zeroExtensionMap f) :
    blockDefect f.h1Map = (0, 0) :=
  (blockDefect_eq_zero_iff_bijective f.h1Map).mpr (homotopyH1_bijective E f hf)

/-- G133実短完全列に同じ比較の全次数全単射を渡すと標準錐のhomologyは零。 -/
theorem cone_homology_isZero_of_bijective
    {F G : CochainComplex (ModuleCat.{u} ℚ) ℤ} (φ : F ⟶ G)
    (hb : ∀ n, Function.Bijective (HomologicalComplex.homologyMap φ n).hom) (m : ℤ) :
    IsZero ((mappingCone φ).homology m) := by
  letI : Subsingleton (G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr (hb m).2)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  have hz : ∀ z : (mappingCone φ).homology m, z = 0 := by
    intro z
    have hp : coneKernelProjection φ m z = 0 := by
      apply Subtype.ext
      apply (hb (m+1)).1
      exact (coneKernelProjection φ m z).2.trans (map_zero _).symm
    obtain ⟨w, hw⟩ := (cone_short_function_exact φ m z).mp hp
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact (hz x).trans (hz y).symm

/-- 同じ標準ホモトピー同値の射の標準錐は全整数次数で零。 -/
theorem homotopyCone_isZero {F G : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (E : HomotopyEquiv F G) (m : ℤ) : IsZero ((mappingCone E.hom).homology m) := by
  apply cone_homology_isZero_of_bijective
  intro n
  exact (E.toHomologyIso n).toLinearEquiv.bijective

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
