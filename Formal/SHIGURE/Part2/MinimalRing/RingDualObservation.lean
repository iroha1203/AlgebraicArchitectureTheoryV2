import Formal.SHIGURE.Part2.MinimalRing.ReverseRanges
import Formal.SHIGURE.Part2.MinimalRing.DualRank
import Formal.SHIGURE.Part2.MinimalRing.RingReachability

/-!
# Finite-word dual observation over a commutative ring

Word reversal turns the dual observations into the inputs of a reversed
system.  Finite projective duals have the same stalk ranks, so the proved
ring reachability theorem applies with the original word bound.  The final
statement uses the actual dual of the finite-product observation map.
-/

namespace SHIGURE.MinimalRing

open scoped BigOperators

variable {R S : Type*} [CommRing R] [Fintype S]
variable {Op : S → S → Type*} [∀ s t, Finite (Op s t)]
variable {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]
variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]

/-- All-word dual observation is surjective at every sort if and only if
the actual observation map for words of length at most N−1 has surjective
dual at every sort, where N is the total specified state rank. -/
theorem allWordDualObservationMap_iff_boundedObservation_dualMap
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (E s) p = rank s)
    (hpositive : 0 < ∑ s, rank s) :
    (∀ s, Function.Surjective (allWordDualObservationMap A observe s)) ↔
      (∀ s, Function.Surjective (boundedObservationMap A observe s ((∑ t, rank t) - 1)).dualMap) := by
  let B : LinearSystem (R := R) (fun s t => Op t s)
      (fun s => Module.Dual R (E s)) (fun s => Module.Dual R (O s)) :=
    reverseSystem (E := E) (I := I) (O := O) A observe
  have hrankDual : ∀ s (p : PrimeSpectrum R),
      Module.rankAtStalk (Module.Dual R (E s)) p = rank s := by
    intro s p
    exact (dual_rankAtStalk_eq (M := E s) p).trans (hrank s p)
  have hreach := allWordReachMap_iff_bounded
    (E := fun s => Module.Dual R (E s)) (I := fun s => Module.Dual R (O s))
    B rank hrankDual hpositive
  constructor
  · intro hall
    have hreverse : ∀ s, Function.Surjective (allWordReachMap B s) := by
      intro s
      apply LinearMap.range_eq_top.mp
      rw [← range_allWordDualObservationMap_eq_reverseReach A observe s]
      exact LinearMap.range_eq_top.mpr (hall s)
    have hbounded := hreach.mp hreverse
    intro s
    apply (boundedObservationMap_dualMap_surjective_iff A observe s _).mpr
    apply LinearMap.range_eq_top.mp
    rw [range_boundedWordDualObservationMap_eq_reverseReach A observe s]
    exact LinearMap.range_eq_top.mpr (hbounded s)
  · intro hbounded
    have hreverse : ∀ s, Function.Surjective
        (boundedWordReachMap B s ((∑ t, rank t) - 1)) := by
      intro s
      apply LinearMap.range_eq_top.mp
      rw [← range_boundedWordDualObservationMap_eq_reverseReach A observe s]
      exact LinearMap.range_eq_top.mpr
        ((boundedObservationMap_dualMap_surjective_iff A observe s _).mp (hbounded s))
    have hall := hreach.mpr hreverse
    intro s
    apply LinearMap.range_eq_top.mp
    rw [range_allWordDualObservationMap_eq_reverseReach A observe s]
    exact LinearMap.range_eq_top.mpr (hall s)

end SHIGURE.MinimalRing
