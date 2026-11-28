import Formal.SHIGURE.Part2.MinimalRing.RingDualObservation

/-! The combined all-word and finite-word minimality conditions. -/

namespace SHIGURE.MinimalRing

open scoped BigOperators

variable {R S : Type*} [CommRing R] [Fintype S]
variable {Op : S → S → Type*} [∀ s t, Finite (Op s t)]
variable {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]
variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]

/-- A system satisfies both all-word minimality conditions exactly when the
actual reachability and dual observation maps for words of length at most
the total state rank minus one are surjective at every sort. -/
theorem allWord_minimality_iff_bounded
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (E s) p = rank s)
    (hpositive : 0 < ∑ s, rank s) :
    ((∀ s, Function.Surjective (allWordReachMap A s)) ∧
      (∀ s, Function.Surjective (allWordDualObservationMap A observe s))) ↔
    ((∀ s, Function.Surjective (boundedWordReachMap A s ((∑ t, rank t) - 1))) ∧
      (∀ s, Function.Surjective
        (boundedObservationMap A observe s ((∑ t, rank t) - 1)).dualMap)) := by
  exact and_congr (allWordReachMap_iff_bounded A rank hrank hpositive)
    (allWordDualObservationMap_iff_boundedObservation_dualMap A observe rank hrank hpositive)

end SHIGURE.MinimalRing
