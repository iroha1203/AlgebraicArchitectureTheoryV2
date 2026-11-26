import Formal.SHIGURE.Part2.Descent.ExtensionAlgebraTensor
import Formal.SHIGURE.Part2.Descent.FiniteLocallyFree
import Formal.SHIGURE.Part2.Schemes.AffineQuasiCoherentFiber

/-! # Finite local freeness under affine pullback -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory SHIGURE.CoefficientDescent TensorProduct

noncomputable section

universe u

variable {R S : CommRingCat.{u}}

/-- In B.5 the finite projective criterion transports finite local freeness
across an isomorphism of coefficient modules. -/
theorem finiteLocallyFree_of_moduleIso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (h : FiniteLocallyFree R M) : FiniteLocallyFree R N := by
  obtain ⟨finite, projective⟩ := finiteLocallyFree_iff_finite_projective.mp h
  exact finiteLocallyFree_iff_finite_projective.mpr
    ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv⟩

/-- For the B.3 affine pullback, the B.5 finite projective criterion is
preserved by extension along an arbitrary coordinate map. -/
theorem finiteLocallyFree_extendScalars (f : R ⟶ S) (M : ModuleCat.{u} R)
    (h : FiniteLocallyFree R M) :
    FiniteLocallyFree S ((ModuleCat.extendScalars f.hom).obj M) := by
  letI : Algebra R S := f.hom.toAlgebra
  obtain ⟨finite, projective⟩ := finiteLocallyFree_iff_finite_projective.mp h
  let N := ModuleCat.of S (S ⊗[R] M)
  have baseChange : FiniteLocallyFree S N := finiteLocallyFree_iff_finite_projective.mpr
    ⟨inferInstance, inferInstance⟩
  exact finiteLocallyFree_of_moduleIso (extendScalarsTensorIso (B := S) M).symm baseChange

/-- B.5 reflects finite presentation and flatness of the coefficient module
along a faithfully flat ring map, giving finite local freeness on the base. -/
theorem finiteLocallyFree_of_faithfullyFlat_extendScalars (f : R ⟶ S) (M : ModuleCat.{u} R)
    (faithfulFlat : letI : Algebra R S := f.hom.toAlgebra; Module.FaithfullyFlat R S)
    (h : FiniteLocallyFree S ((ModuleCat.extendScalars f.hom).obj M)) : FiniteLocallyFree R M := by
  letI : Algebra R S := f.hom.toAlgebra
  letI : Module.FaithfullyFlat R S := faithfulFlat
  let N := (ModuleCat.extendScalars f.hom).obj M
  let comparison : (S ⊗[R] M) ≃ₗ[S] N := (extendScalarsTensorIso (B := S) M).symm.toLinearEquiv
  letI : Module.FinitePresentation S N := h.finitePresentation
  letI : Module.Flat S N := h.flat
  letI : Module.FinitePresentation R M := finitePresentation_of_equiv_baseChange comparison
  letI : Module.Flat R M := flat_of_equiv_baseChange comparison
  exact finiteLocallyFree_of_finitePresentation_flat

end

end SHIGURE.SchemeDescent
