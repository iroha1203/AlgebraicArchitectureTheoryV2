import Formal.SHIGURE.Part2.MinimalRing.Systems
import Formal.SHIGURE.Part2.MinimalRing.DirectSumBaseChange

/-! Scalar extension of the actual all-word and bounded-word input maps. -/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped DirectSum TensorProduct

variable {R T S : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {Op : S → S → Type*} {E I : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]

/-- Extending the all-word reachability map agrees with constructing the
all-word map after extending every input and operation. -/
theorem allWordReachMap_baseChange (A : LinearSystem (R := R) Op E I) (s : S) :
    (allWordReachMap (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (baseChangeSystem (E := E) (I := I) T A) s).comp
      (scalarDirectSumEquiv (R := R) (T := T) (M := fun w : InputWord Op s => I w.1)).toLinearMap =
        (allWordReachMap A s).baseChange T := by
  classical
  let f : ∀ w : InputWord Op s, I w.1 →ₗ[R] E s :=
    fun w => (evaluate A w.2).comp (A.input w.1)
  have hi (u : S) : (baseChangeSystem (E := E) (I := I) T A).input u =
      (A.input u).baseChange T := rfl
  have h := toModule_baseChange (T := T) f
  rw [scalarDirectSumEquiv_eq_directSumRight]
  simpa only [allWordReachMap, f, evaluate_baseChange, hi,
    LinearMap.baseChange_comp] using h

/-- The same comparison for a fixed finite word-length bound. -/
theorem boundedWordReachMap_baseChange (A : LinearSystem (R := R) Op E I) (s : S) (n : ℕ) :
    (boundedWordReachMap (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (baseChangeSystem (E := E) (I := I) T A) s n).comp
      (scalarDirectSumEquiv (R := R) (T := T)
        (M := fun w : ShortInputWord Op s n => I w.1.1)).toLinearMap =
        (boundedWordReachMap A s n).baseChange T := by
  classical
  let f : ∀ w : ShortInputWord Op s n, I w.1.1 →ₗ[R] E s :=
    fun w => (evaluate A w.1.2).comp (A.input w.1.1)
  have hi (u : S) : (baseChangeSystem (E := E) (I := I) T A).input u =
      (A.input u).baseChange T := rfl
  have h := toModule_baseChange (T := T) f
  rw [scalarDirectSumEquiv_eq_directSumRight]
  simpa only [boundedWordReachMap, f, evaluate_baseChange, hi,
    LinearMap.baseChange_comp] using h

/-- Surjectivity of the extended all-word map is exactly surjectivity of the
all-word map of the extended system. -/
theorem allWordReachMap_baseChange_surjective_iff
    (A : LinearSystem (R := R) Op E I) (s : S) :
    Function.Surjective ((allWordReachMap A s).baseChange T) ↔
      Function.Surjective (allWordReachMap
        (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (baseChangeSystem (E := E) (I := I) T A) s) := by
  classical
  rw [← allWordReachMap_baseChange (T := T) A s]
  simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe] using
    (Function.Surjective.of_comp_iff
      (allWordReachMap (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (baseChangeSystem (E := E) (I := I) T A) s)
      (scalarDirectSumEquiv (R := R) (T := T) (M := fun w : InputWord Op s => I w.1)).surjective)

/-- Surjectivity of the extended bounded map is exactly surjectivity of the
bounded map of the extended system. -/
theorem boundedWordReachMap_baseChange_surjective_iff
    (A : LinearSystem (R := R) Op E I) (s : S) (n : ℕ) :
    Function.Surjective ((boundedWordReachMap A s n).baseChange T) ↔
      Function.Surjective (boundedWordReachMap
        (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (baseChangeSystem (E := E) (I := I) T A) s n) := by
  classical
  rw [← boundedWordReachMap_baseChange (T := T) A s n]
  simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe] using
    (Function.Surjective.of_comp_iff
      (boundedWordReachMap (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (baseChangeSystem (E := E) (I := I) T A) s n)
      (scalarDirectSumEquiv (R := R) (T := T)
        (M := fun w : ShortInputWord Op s n => I w.1.1)).surjective)

end SHIGURE.MinimalRing
