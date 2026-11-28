import Formal.SHIGURE.Part2.MinimalRing.ObservationBaseChange
import Formal.SHIGURE.Part2.MinimalRing.ObservationSplit

/-!
# Preservation under scalar extension

The actual all-word reachability and dual-observation conditions survive an
arbitrary change of commutative coefficient rings.  For observation, a
retraction of the finite-word map is extended along the coefficient map and
transported through the finite-product equivalence.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped BigOperators TensorProduct

variable {R T S : Type*} [CommRing R] [CommRing T] [Algebra R T] [Fintype S]
variable {Op : S → S → Type*} [∀ s t, Finite (Op s t)]
variable {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]

/-- A retraction of the actual finite observation map extends to a retraction
of the corresponding map of the scalar-extended system. -/
theorem boundedObservationMap_baseChange_split
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (s : S) (n : ℕ)
    (r : (∀ w : ShortOutputWord Op s n, O w.1.1) →ₗ[R] E s)
    (hr : r.comp (boundedObservationMap A observe s n) = LinearMap.id) :
    ∃ r' : (∀ w : ShortOutputWord Op s n, T ⊗[R] O w.1.1) →ₗ[T] (T ⊗[R] E s),
      r'.comp (boundedObservationMap
        (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (O := fun u => T ⊗[R] O u) (baseChangeSystem T A)
        (fun u => (observe u).baseChange T) s n) = LinearMap.id := by
  let e := observationProductEquiv (R := R) (T := T) (Op := Op) (O := O) s n
  refine ⟨(r.baseChange T).comp e.symm.toLinearMap, ?_⟩
  rw [boundedObservationMap_baseChange]
  have hsplit : (r.baseChange T).comp ((boundedObservationMap A observe s n).baseChange T) =
      LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  apply LinearMap.ext
  intro x
  change (r.baseChange T) (e.symm (e ((boundedObservationMap A observe s n).baseChange T x))) = x
  rw [e.symm_apply_apply]
  exact LinearMap.congr_fun hsplit x

variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]

/-- A split injection has surjective dual, over an arbitrary commutative ring. -/
theorem dualMap_surjective_of_retraction
    {M Q : Type*} [AddCommGroup M] [Module T M] [AddCommGroup Q] [Module T Q]
    (f : M →ₗ[T] Q) (r : Q →ₗ[T] M) (hr : r.comp f = LinearMap.id) :
    Function.Surjective f.dualMap := by
  intro φ
  refine ⟨r.dualMap φ, ?_⟩
  apply LinearMap.ext
  intro x
  change φ (r (f x)) = φ x
  have hx := LinearMap.congr_fun hr x
  change r (f x) = x at hx
  rw [hx]

/-- All-word reachability and all-word dual observation are preserved under
any scalar extension.  In particular this applies to finite free input and
output modules, without imposing their freeness as an extra requirement. -/
theorem allWord_minimality_baseChange
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (E s) p = rank s)
    (hpositive : 0 < ∑ s, rank s)
    (hreach : ∀ s, Function.Surjective (allWordReachMap A s))
    (hobserve : ∀ s, Function.Surjective (allWordDualObservationMap A observe s)) :
    (∀ s, Function.Surjective (allWordReachMap
      (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (baseChangeSystem T A) s)) ∧
    (∀ s, Function.Surjective (allWordDualObservationMap
      (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (O := fun u => T ⊗[R] O u) (baseChangeSystem T A)
      (fun u => (observe u).baseChange T) s)) := by
  constructor
  · intro s
    apply (allWordReachMap_baseChange_surjective_iff (T := T) A s).mp
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (LinearMap.lTensor_surjective T (hreach s))
  · letI : ∀ s, Module.Finite T (T ⊗[R] E s) := fun s => inferInstance
    letI : ∀ s, Module.Projective T (T ⊗[R] E s) := fun s => inferInstance
    have hrankT : ∀ s (p : PrimeSpectrum T),
        Module.rankAtStalk (T ⊗[R] E s) p = rank s := by
      intro s p
      exact (Module.rankAtStalk_baseChange (M := E s) p).trans
        (hrank s (p.comap (algebraMap R T)))
    apply (allWordDualObservationMap_iff_boundedObservation_dualMap
      (baseChangeSystem T A) (fun u => (observe u).baseChange T)
      rank hrankT hpositive).mpr
    intro s
    obtain ⟨r, hr⟩ := allWordDualObservation_yields_bounded_split
      A observe rank hrank hpositive hobserve s
    obtain ⟨r', hr'⟩ := boundedObservationMap_baseChange_split (T := T) A observe s _ r hr
    exact dualMap_surjective_of_retraction _ r' hr'

/-- The preservation theorem for explicitly finite free input and output
coordinates.  The extended coordinate modules are their tensor extensions. -/
theorem allWord_minimality_baseChange_finiteFree
    (inputRank outputRank : S → ℕ)
    (A : LinearSystem (R := R) Op E (fun s => Fin (inputRank s) → R))
    (observe : ∀ s, E s →ₗ[R] (Fin (outputRank s) → R))
    (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (E s) p = rank s)
    (hpositive : 0 < ∑ s, rank s)
    (hreach : ∀ s, Function.Surjective (allWordReachMap A s))
    (hobserve : ∀ s, Function.Surjective (allWordDualObservationMap A observe s)) :
    (∀ s, Function.Surjective (allWordReachMap
      (E := fun u => T ⊗[R] E u)
      (I := fun u => T ⊗[R] (Fin (inputRank u) → R)) (baseChangeSystem T A) s)) ∧
    (∀ s, Function.Surjective (allWordDualObservationMap
      (E := fun u => T ⊗[R] E u)
      (I := fun u => T ⊗[R] (Fin (inputRank u) → R))
      (O := fun u => T ⊗[R] (Fin (outputRank u) → R)) (baseChangeSystem T A)
      (fun u => (observe u).baseChange T) s)) :=
  allWord_minimality_baseChange (T := T) A observe rank hrank hpositive hreach hobserve

end SHIGURE.MinimalRing
