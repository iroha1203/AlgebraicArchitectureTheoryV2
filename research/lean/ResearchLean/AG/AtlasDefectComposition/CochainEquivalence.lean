import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import ResearchLean.AG.UniformInvariance.UniformityReduction
import Formal.Util.AssertStandardAxioms
/-! # 既存三項同値の標準complexへの移送

G-107のCochainEquiv・toHom・symm・h1Equivを再利用し、
零延長の標準complex同型と既存商の同型を接続する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open TwoPhase ResolutionInvariance
universe w
variable {C D : ThreeCochainComplex.{0,w} ℚ}
/-- 既存成分同値の順逆Homは全三成分で恒等へ合成する。 -/
theorem cochainEquiv_hom_inv (e : ThreeCochainComplex.CochainEquiv C D) :
    cochainComp e.toHom e.symm.toHom = cochainId C := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro x <;>
    exact LinearEquiv.symm_apply_apply _ _
/-- 既存成分同値の逆順Homも全三成分で恒等へ合成する。 -/
theorem cochainEquiv_inv_hom (e : ThreeCochainComplex.CochainEquiv C D) :
    cochainComp e.symm.toHom e.toHom = cochainId D := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro x <;>
    exact LinearEquiv.apply_symm_apply _ _
/-- 既存G-107の全三成分同値から標準ℤ complex同型を構成する。 -/
def cochainEquivZeroExtensionIso (e : ThreeCochainComplex.CochainEquiv C D) :
    zeroExtension C ≅ zeroExtension D where
  hom := zeroExtensionMap e.toHom
  inv := zeroExtensionMap e.symm.toHom
  hom_inv_id := by rw [← zeroExtensionMap_comp,cochainEquiv_hom_inv,zeroExtensionMap_id]
  inv_hom_id := by rw [← zeroExtensionMap_comp,cochainEquiv_inv_hom,zeroExtensionMap_id]
/-- 零延長同型の順射は既存成分同値の実Homの零延長である。 -/
@[simp] theorem cochainEquivZeroExtensionIso_hom (e : ThreeCochainComplex.CochainEquiv C D) :
    (cochainEquivZeroExtensionIso e).hom = zeroExtensionMap e.toHom := rfl
/-- 標準homologyの同型は既存G-107のh1Equivと全類で同じ写像を読む。 -/
theorem cochainEquiv_h1_standard (e : ThreeCochainComplex.CochainEquiv C D) (x : C.H1) :
    oldH1Equiv D (e.h1Equiv x) =
      (HomologicalComplex.homologyMapIso (cochainEquivZeroExtensionIso e) 1).hom (oldH1Equiv C x) :=
  oldH1Equiv_natural e.toHom x
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
