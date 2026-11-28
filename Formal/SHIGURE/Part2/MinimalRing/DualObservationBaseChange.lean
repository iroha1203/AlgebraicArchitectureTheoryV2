import Formal.SHIGURE.Part2.MinimalRing.Systems
import Formal.SHIGURE.Part2.MinimalRing.DirectSumDualBaseChange

/-!
# Scalar extension of all-word dual observation

The actual all-word map commutes with scalar extension through the canonical
dual and direct-sum equivalences.  The type of all words need not be finite.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped DirectSum TensorProduct

variable {R T S : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]
variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]
variable [∀ s, Module.Finite R (O s)] [∀ s, Module.Projective R (O s)]

/-- The natural equivalence on the sources of the all-word dual maps. -/
noncomputable def allWordDualObservationBaseChangeEquiv (s : S) :
    (T ⊗[R] (⨁ w : OutputWord Op s, Module.Dual R (O w.1))) ≃ₗ[T]
      (⨁ w : OutputWord Op s, Module.Dual T (T ⊗[R] O w.1)) :=
  directSumDualBaseChangeEquiv (R := R) (T := T) (N := fun w : OutputWord Op s => O w.1)

/-- The actual all-word dual observation map commutes with scalar extension,
via the canonical equivalences on both source and target. -/
theorem allWordDualObservationMap_baseChange
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s) (s : S) :
    (dualBaseChangeEquiv (R := R) (T := T) (M := E s)).toLinearMap.comp
      ((allWordDualObservationMap A observe s).baseChange T) =
    (allWordDualObservationMap
      (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (O := fun u => T ⊗[R] O u) (baseChangeSystem T A)
      (fun u => (observe u).baseChange T) s).comp
        (allWordDualObservationBaseChangeEquiv (R := R) (T := T) (Op := Op) (O := O) s).toLinearMap := by
  classical
  let f : ∀ w : OutputWord Op s, E s →ₗ[R] O w.1 :=
    fun w => (observe w.1).comp (evaluate A w.2)
  have h := toModule_dual_baseChange (T := T) f
  simpa only [allWordDualObservationMap, allWordDualObservationBaseChangeEquiv, f,
    LinearMap.dualMap_comp_dualMap, evaluate_baseChange, LinearMap.baseChange_comp] using h

end SHIGURE.MinimalRing
