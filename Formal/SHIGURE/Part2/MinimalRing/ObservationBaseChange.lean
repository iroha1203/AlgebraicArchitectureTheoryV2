import Formal.SHIGURE.Part2.MinimalRing.Systems
import Formal.SHIGURE.Part2.MinimalRing.ProductBaseChange

/-!
# Scalar extension of finite-word observation

The actual finite-product observation map of the scalar-extended system is
the scalar extension of the original map, followed by the canonical
finite-product/tensor equivalence.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped TensorProduct

variable {R T S : Type*} [CommRing R] [CommRing T] [Algebra R T] [Finite S]
variable {Op : S → S → Type*} [∀ s t, Finite (Op s t)]
variable {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]

/-- The canonical product comparison for the outputs indexed by short words. -/
noncomputable def observationProductEquiv (s : S) (n : ℕ) :
    (T ⊗[R] (∀ w : ShortOutputWord Op s n, O w.1.1)) ≃ₗ[T]
      (∀ w : ShortOutputWord Op s n, T ⊗[R] O w.1.1) := by
  letI : Finite (ShortOutputWord Op s n) := finite_shortOutputWord s n
  exact scalarProductEquiv (R := R) (T := T) (M := fun w : ShortOutputWord Op s n => O w.1.1)

/-- The finite observation map of the scalar-extended system corresponds to
the actual scalar extension of the original observation map. -/
theorem boundedObservationMap_baseChange (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) :
    boundedObservationMap (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (O := fun u => T ⊗[R] O u) (baseChangeSystem (E := E) (I := I) T A)
        (fun u => (observe u).baseChange T) s n =
      (observationProductEquiv (R := R) (T := T) (Op := Op) (O := O) s n).toLinearMap.comp
        ((boundedObservationMap A observe s n).baseChange T) := by
  classical
  letI : Finite (ShortOutputWord Op s n) := finite_shortOutputWord s n
  let f : ∀ w : ShortOutputWord Op s n, E s →ₗ[R] O w.1.1 :=
    fun w => (observe w.1.1).comp (evaluate A w.1.2)
  have h := pi_baseChange (T := T) f
  symm
  simpa only [boundedObservationMap, observationProductEquiv, f, evaluate_baseChange,
    LinearMap.baseChange_comp] using h

end SHIGURE.MinimalRing
