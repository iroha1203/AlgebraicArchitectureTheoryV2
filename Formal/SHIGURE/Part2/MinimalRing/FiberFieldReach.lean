import Formal.SHIGURE.Part2.MinimalRing.FieldBridge
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The finite-word field theorem on every residue-field fiber

The state module at each sort is finite projective of the specified constant
rank.  The field theorem is applied to the scalar extension of the actual
ring system, and the stalk-rank theorem identifies the word bound.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped BigOperators TensorProduct

variable {R S : Type*} [CommRing R] [Fintype S]
variable {Op : S → S → Type*} {E I : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]

/-- At any prime, the actual fiber system is reachable by all words exactly
when it is reachable by words of length at most the total rank minus one. -/
theorem fiber_allWordReachMap_iff_bounded
    (A : LinearSystem (R := R) Op E I) (rank : S → ℕ)
    (hrank : ∀ s (p : PrimeSpectrum R), Module.rankAtStalk (E s) p = rank s)
    (hpositive : 0 < ∑ s, rank s) (p : PrimeSpectrum R) :
    (∀ s, Function.Surjective (allWordReachMap
      (E := fun u => p.asIdeal.ResidueField ⊗[R] E u)
      (I := fun u => p.asIdeal.ResidueField ⊗[R] I u)
      (baseChangeSystem (E := E) (I := I) p.asIdeal.ResidueField A) s)) ↔
    (∀ s, Function.Surjective (boundedWordReachMap
      (E := fun u => p.asIdeal.ResidueField ⊗[R] E u)
      (I := fun u => p.asIdeal.ResidueField ⊗[R] I u)
      (baseChangeSystem (E := E) (I := I) p.asIdeal.ResidueField A) s ((∑ t, rank t) - 1))) := by
  let k := p.asIdeal.ResidueField
  let B : LinearSystem (R := k) Op (fun u => k ⊗[R] E u) (fun u => k ⊗[R] I u) :=
    baseChangeSystem k A
  have hdim : ∀ s, Module.finrank k (k ⊗[R] E s) = rank s := by
    intro s
    exact (Module.rankAtStalk_eq (M := E s) p).symm.trans (hrank s p)
  have hpositive' : 0 < ∑ s, Module.finrank k (k ⊗[R] E s) := by
    simpa only [hdim] using hpositive
  have hsum : (∑ s, Module.finrank k (k ⊗[R] E s)) = ∑ s, rank s := by
    apply Finset.sum_congr rfl
    intro s _
    exact hdim s
  have hfield := SHIGURE.Minimal.surjective_allWordReachMap_iff_bounded
    (asFieldSystem B) hpositive'
  simp only [← allWordReachMap_asFieldSystem B, ← boundedWordReachMap_asFieldSystem B] at hfield
  rw [hsum] at hfield
  exact hfield

end SHIGURE.MinimalRing
