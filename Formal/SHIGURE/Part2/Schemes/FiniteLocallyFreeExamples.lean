import Formal.SHIGURE.Part2.Schemes.FiniteFreeAffinePullback
import Formal.SHIGURE.Part2.Schemes.FiniteLocallyFreeFppf

/-! # Affine finite locally free examples -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- The full affine chart of an associated sheaf is finite locally free
exactly when its coefficient module is finite locally free. -/
theorem affineTilde_on_top_finiteLocallyFree_iff (M : ModuleCat.{u} R) :
    HasFiniteLocallyFreeOn ((tilde.functor R).obj M) (isAffineOpen_top (Spec R)) ↔
      FiniteLocallyFree R M := by
  let X := Spec R
  let h := isAffineOpen_top X
  let N := (tilde.functor R).obj M
  let e := Scheme.ΓSpecIso R
  have fromSpec : h.fromSpec = Spec.map e.inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have inverse : Spec.map e.hom ≫ h.fromSpec = 𝟙 X := by
    rw [fromSpec, ← Spec.map_comp, e.inv_hom_id, Spec.map_id]
  constructor
  · rintro ⟨P, finite, ⟨k⟩⟩
    let equiv := ((tildeRestrictIso e.hom).app P).symm ≪≫ (restrictFunctor (Spec.map e.hom)).mapIso k ≪≫
      ((restrictFunctorComp (Spec.map e.hom) h.fromSpec).app N).symm ≪≫
      (restrictFunctorCongr inverse).app N ≪≫ (restrictFunctorId (X := X)).app N
    exact finiteLocallyFree_of_moduleIso ((tilde.fullyFaithfulFunctor (R := R)).preimageIso equiv)
      (finiteLocallyFree_extendScalars e.hom P finite)
  · intro finite
    refine ⟨(ModuleCat.extendScalars e.inv.hom).obj M, finiteLocallyFree_extendScalars e.inv M finite, ⟨?_⟩⟩
    exact ((tildeRestrictIso e.inv).app M).symm ≪≫ (restrictFunctorCongr fromSpec.symm).app N

/-- The associated module sheaf on a spectrum is finite locally free exactly
when its coefficient module is finite locally free. -/
theorem affineTilde_finiteLocallyFree_iff (M : ModuleCat.{u} R) :
    IsFiniteLocallyFreeModule ((tilde.functor R).obj M) ↔ FiniteLocallyFree R M := by
  rw [← affineTilde_on_top_finiteLocallyFree_iff M]
  constructor
  · intro finite
    exact isFiniteLocallyFreeModule_iff_on_affineOpens.mp finite ⟨⊤, isAffineOpen_top _⟩
  · intro finite
    exact ⟨ULift.{u} Unit, fun _ => ⟨⊤, isAffineOpen_top _⟩, by simp, fun _ => finite⟩

namespace Examples

/-- The trivial affine module has a finite locally free presentation on the
full affine chart, including in rank zero. -/
theorem finiteFreeAffine_on_top (R : CommRingCat.{u}) (n : ℕ) :
    HasFiniteLocallyFreeOn ((tilde.functor R).obj (finiteFreeModule R n)) (isAffineOpen_top (Spec R)) := by
  apply (affineTilde_on_top_finiteLocallyFree_iff _).2
  change FiniteLocallyFree R (Fin n → R)
  letI : Module.Free R (Fin n → R) := Module.Free.of_basis (Pi.basisFun R (Fin n))
  exact finiteLocallyFree_iff_finite_projective.mpr ⟨inferInstance, inferInstance⟩

/-- The trivial affine module sheaf is finite locally free. -/
theorem finiteFreeAffine_isFiniteLocallyFree (R : CommRingCat.{u}) (n : ℕ) :
    IsFiniteLocallyFreeModule ((tilde.functor R).obj (finiteFreeModule R n)) := by
  exact ⟨ULift.{u} Unit, fun _ => ⟨⊤, isAffineOpen_top _⟩, by simp, fun _ => finiteFreeAffine_on_top R n⟩

/-- The B.5 infinite rank counterexample as a rational coefficient module. -/
private abbrev rationalInfiniteFree := ModuleCat.of ℚ (ℕ →₀ ℚ)
/-- The affine base of the infinite rank example. -/
private abbrev rationalSpectrum := Spec (CommRingCat.of ℚ)
/-- The associated sheaf in the B.3 infinite rank counterexample. -/
private abbrev rationalInfiniteTilde := (tilde.functor (CommRingCat.of ℚ)).obj rationalInfiniteFree

/-- The infinite rank free rational module has no finite locally free
presentation on the full affine chart. -/
theorem rationalInfiniteTilde_not_on_top :
    ¬ HasFiniteLocallyFreeOn rationalInfiniteTilde (isAffineOpen_top rationalSpectrum) :=
  fun finite => by
    have comparison := affineTilde_on_top_finiteLocallyFree_iff (R := CommRingCat.of ℚ) rationalInfiniteFree
    have coefficients : FiniteLocallyFree ℚ (ℕ →₀ ℚ) := comparison.1 finite
    exact SHIGURE.CoefficientDescent.Examples.infinite_free_not_finiteLocallyFree coefficients

/-- The associated sheaf of the infinite rank rational module fails
finite local freeness. -/
theorem rationalInfiniteTilde_not_finiteLocallyFree : ¬ IsFiniteLocallyFreeModule rationalInfiniteTilde :=
  fun finite => rationalInfiniteTilde_not_on_top
    (isFiniteLocallyFreeModule_iff_on_affineOpens.mp finite ⟨⊤, isAffineOpen_top _⟩)

end Examples

end

end SHIGURE.SchemeDescent
