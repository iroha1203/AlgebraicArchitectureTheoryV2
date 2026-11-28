import Formal.SHIGURE.Part2.MinimalRing.RingDualObservation
import Mathlib.Algebra.Module.Projective

/-!
# Splitting finite-word observation

For a finite projective source, surjectivity of the dual of a linear map
produces a retraction of the original map.  This applies to the actual
finite-product observation map over the affine base.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped BigOperators

variable {R E Q : Type*} [CommRing R]
variable [AddCommGroup E] [Module R E] [Module.Finite R E] [Module.Projective R E]
variable [AddCommGroup Q] [Module R Q]

/-- A surjective dual of a map with finite projective source makes the
original map split injective. -/
theorem exists_retraction_of_dualMap_surjective (f : E →ₗ[R] Q)
    (h : Function.Surjective f.dualMap) :
    ∃ r : Q →ₗ[R] E, r.comp f = LinearMap.id := by
  obtain ⟨g, hg⟩ := f.dualMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr h)
  refine ⟨(Module.evalEquiv R E).symm.toLinearMap.comp
    (g.dualMap.comp (Module.Dual.eval R Q)), ?_⟩
  apply LinearMap.ext
  intro x
  change (Module.evalEquiv R E).symm (g.dualMap (Module.Dual.eval R Q (f x))) = x
  apply (Module.evalEquiv R E).injective
  simp only [LinearEquiv.apply_symm_apply, Module.evalEquiv_apply]
  apply LinearMap.ext
  intro φ
  change g φ (f x) = φ x
  exact LinearMap.congr_fun (LinearMap.congr_fun hg φ) x

section Observation

variable {S : Type*} [Fintype S] {Op : S → S → Type*} [∀ s t, Finite (Op s t)]
variable {States Inputs Outputs : S → Type*}
variable [∀ s, AddCommGroup (States s)] [∀ s, Module R (States s)]
variable [∀ s, AddCommGroup (Inputs s)] [∀ s, Module R (Inputs s)]
variable [∀ s, AddCommGroup (Outputs s)] [∀ s, Module R (Outputs s)]
variable [∀ s, Module.Finite R (States s)] [∀ s, Module.Projective R (States s)]

/-- A surjective finite-word observation dual gives a retraction of the
actual finite-word observation map. -/
theorem boundedObservationMap_split
    (A : LinearSystem (R := R) Op States Inputs) (observe : ∀ s, States s →ₗ[R] Outputs s)
    (s : S) (n : ℕ) (h : Function.Surjective (boundedObservationMap A observe s n).dualMap) :
    ∃ r : (∀ w : ShortOutputWord Op s n, Outputs w.1.1) →ₗ[R] States s,
      r.comp (boundedObservationMap A observe s n) = LinearMap.id :=
  exists_retraction_of_dualMap_surjective _ h

/-- All-word dual observation yields a global retraction of the N−1
observation map at each sort, and hence a local retraction on the affine base. -/
theorem allWordDualObservation_yields_bounded_split
    (A : LinearSystem (R := R) Op States Inputs) (observe : ∀ s, States s →ₗ[R] Outputs s)
    (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (States s) p = rank s)
    (hpositive : 0 < ∑ s, rank s)
    (hall : ∀ s, Function.Surjective (allWordDualObservationMap A observe s)) :
    ∀ s, ∃ r : (∀ w : ShortOutputWord Op s ((∑ t, rank t) - 1), Outputs w.1.1) →ₗ[R] States s,
      r.comp (boundedObservationMap A observe s ((∑ t, rank t) - 1)) = LinearMap.id := by
  have hbounded := (allWordDualObservationMap_iff_boundedObservation_dualMap
    A observe rank hrank hpositive).mp hall
  intro s
  exact boundedObservationMap_split A observe s _ (hbounded s)

end Observation
end SHIGURE.MinimalRing
