import Formal.SHIGURE.Part2.MinimalRing.Systems
import Formal.SHIGURE.Part2.Minimal.FiniteObservationComparison

/-!
# Comparison with the finite-dimensional field theorem

A commutative-ring system over a field has exactly the same word evaluations
and reachability and observation maps as the system used by the field theorem.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal

noncomputable section

variable {K S : Type*} [Field K]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module K (O s)]

/-- Regard the same input and operations as the system used in the field theorem. -/
def asFieldSystem (A : LinearSystem (R := K) Op E I) : Word.LinearSystem (K := K) Op E I where
  input := A.input
  operation := A.operation

/-- Both evaluators compose the same operations in the same order. -/
theorem evaluate_asFieldSystem (A : LinearSystem (R := K) Op E I)
    {s t : S} (w : Word Op s t) :
    Word.evaluate (asFieldSystem A) w = evaluate A w := by
  induction w with
  | nil => rfl
  | snoc w e ih =>
    change (A.operation e).comp (Word.evaluate (asFieldSystem A) w) =
      (A.operation e).comp (evaluate A w)
    rw [ih]

/-- The all-words maps agree under the identity comparison of source and target. -/
theorem allWordReachMap_asFieldSystem (A : LinearSystem (R := K) Op E I) (s : S) :
    allWordReachMap A s = SHIGURE.Minimal.allWordReachMap (asFieldSystem A) s := by
  classical
  unfold allWordReachMap SHIGURE.Minimal.allWordReachMap
  congr 1

/-- The bounded maps agree under the same comparison. -/
theorem boundedWordReachMap_asFieldSystem (A : LinearSystem (R := K) Op E I) (s : S) (n : ℕ) :
    boundedWordReachMap A s n = SHIGURE.Minimal.boundedWordReachMap (asFieldSystem A) s n := by
  classical
  unfold boundedWordReachMap SHIGURE.Minimal.boundedWordReachMap
  congr 1

/-- The finite-product observation maps agree over a field. -/
theorem boundedObservationMap_asFieldSystem (A : LinearSystem (R := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    boundedObservationMap A observe s n =
      SHIGURE.Minimal.boundedObservationMap (asFieldSystem A) observe s n := by
  apply LinearMap.ext
  intro x
  funext w
  change (observe w.1.1) (evaluate A w.1.2 x) =
    (observe w.1.1) (Word.evaluate (asFieldSystem A) w.1.2 x)
  rw [evaluate_asFieldSystem]

/-- The all-words dual observation maps agree over a field. -/
theorem allWordDualObservationMap_asFieldSystem (A : LinearSystem (R := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) :
    allWordDualObservationMap A observe s =
      SHIGURE.Minimal.allWordDualObservationMap (asFieldSystem A) observe s := by
  classical
  unfold allWordDualObservationMap SHIGURE.Minimal.allWordDualObservationMap
  congr 1

end
end SHIGURE.MinimalRing
