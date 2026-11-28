import Formal.SHIGURE.Part2.MinimalRing.FiberFieldReach
import Formal.SHIGURE.Part2.MinimalRing.FiberSurjectivity
import Formal.SHIGURE.Part2.MinimalRing.ReachBaseChange

/-!
# Finite-word reachability over a commutative ring

For finite projective state modules of specified constant ranks, the field
bound is applied on residue-field fibers and descended using the finite
cokernel criterion.  Both sides use the actual typed-word direct-sum maps.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped BigOperators TensorProduct

variable {R S : Type*} [CommRing R] [Fintype S]
variable {Op : S → S → Type*} {E I : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]

/-- The all-words reachability maps are surjective exactly when the maps for
words of length at most the total state rank minus one are surjective. -/
theorem allWordReachMap_iff_bounded
    (A : LinearSystem (R := R) Op E I) (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (E s) p = rank s)
    (hpositive : 0 < ∑ s, rank s) :
    (∀ s, Function.Surjective (allWordReachMap A s)) ↔
      (∀ s, Function.Surjective (boundedWordReachMap A s ((∑ t, rank t) - 1))) := by
  constructor
  · intro hall s
    apply (surjective_iff_residueField_lTensor_surjective
      (boundedWordReachMap A s ((∑ t, rank t) - 1))).mpr
    intro p
    let k := p.asIdeal.ResidueField
    have hallfiber : ∀ t, Function.Surjective (allWordReachMap
        (E := fun u => k ⊗[R] E u) (I := fun u => k ⊗[R] I u)
        (baseChangeSystem (E := E) (I := I) k A) t) := by
      intro t
      apply (allWordReachMap_baseChange_surjective_iff (T := k) A t).mp
      simpa only [LinearMap.baseChange_eq_ltensor] using
        (LinearMap.lTensor_surjective k (hall t))
    have hbounded := (fiber_allWordReachMap_iff_bounded A rank hrank hpositive p).mp hallfiber s
    have hbase := (boundedWordReachMap_baseChange_surjective_iff (T := k) A s
      ((∑ t, rank t) - 1)).mpr hbounded
    simpa only [LinearMap.baseChange_eq_ltensor] using hbase
  · intro hbounded s
    apply (surjective_iff_residueField_lTensor_surjective (allWordReachMap A s)).mpr
    intro p
    let k := p.asIdeal.ResidueField
    have hboundedfiber : ∀ t, Function.Surjective (boundedWordReachMap
        (E := fun u => k ⊗[R] E u) (I := fun u => k ⊗[R] I u)
        (baseChangeSystem (E := E) (I := I) k A) t ((∑ u, rank u) - 1)) := by
      intro t
      apply (boundedWordReachMap_baseChange_surjective_iff (T := k) A t
        ((∑ u, rank u) - 1)).mp
      simpa only [LinearMap.baseChange_eq_ltensor] using
        (LinearMap.lTensor_surjective k (hbounded t))
    have hall := (fiber_allWordReachMap_iff_bounded A rank hrank hpositive p).mpr hboundedfiber s
    have hbase := (allWordReachMap_baseChange_surjective_iff (T := k) A s).mpr hall
    simpa only [LinearMap.baseChange_eq_ltensor] using hbase

end SHIGURE.MinimalRing
