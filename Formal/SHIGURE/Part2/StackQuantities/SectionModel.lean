import Formal.SHIGURE.Part2.StackQuantities.ResidualExamples
import Formal.SHIGURE.Part2.Quantities.FixedModels

/-! # A designated section as a written quantity Law

The fixed-input presentation uses the actual Chapter 5 quantity-model API.
Its unique input denotes the designated section, not a chosen frame vector.
-/

noncomputable section

universe u

namespace SHIGURE.StackQuantities

open SHIGURE.Quantities

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
variable {sig : SHIGURE.Signature.{u}} (A : SHIGURE.Structure sig)

/-- The written `q(c) = 1` Law at its one designated input. -/
def sectionPresentation : Presentation k A where
  Quantity := PUnit
  Domain _ := PUnit
  Law := PUnit
  Input _ := PUnit
  left _ _ := .quantity ⟨PUnit.unit, PUnit.unit⟩
  right _ _ := .scalar 1

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Read a linear quantity at the declared section as a Chapter 5 candidate. -/
def sectionCandidate (c : M) (q : M →ₗ[R] R) : (sectionPresentation (k := k) A).Candidate R :=
  fun _ _ => q c

/-- The model predicate for the original written Law is exactly `q(c) = 1`. -/
theorem sectionCandidate_holds_iff (c : M) (q : M →ₗ[R] R) :
    (sectionPresentation (k := k) A).Holds (sectionCandidate A c q) ↔ q c = 1 := by
  simp [Presentation.Holds, sectionPresentation, sectionCandidate, Expression.eval]

/-- A structure isomorphism preserving the section transports the actual
Chapter 5 model predicate in both directions. -/
theorem sectionCandidate_holds_transport (h : M ≃ₗ[R] N) (c : M) (c' : N)
    (hc : h c = c') (q' : N →ₗ[R] R) :
    (sectionPresentation (k := k) A).Holds (sectionCandidate A c (q'.comp h.toLinearMap)) ↔
      (sectionPresentation (k := k) A).Holds (sectionCandidate A c' q') := by
  rw [sectionCandidate_holds_iff, sectionCandidate_holds_iff]
  exact specifiedSection_preserved h c c' hc q'

/-- The identity linear quantity satisfies the designated-section Law. -/
theorem section_identity_holds :
    (sectionPresentation (k := k) A).Holds
      (sectionCandidate A (1 : k) (LinearMap.id : k →ₗ[k] k)) := by
  rw [sectionCandidate_holds_iff]
  rfl

/-- Over a nonzero ring, the zero linear quantity violates that same Law. -/
theorem section_zero_not_holds [Nontrivial k] :
    ¬ (sectionPresentation (k := k) A).Holds
      (sectionCandidate A (1 : k) (0 : k →ₗ[k] k)) := by
  rw [sectionCandidate_holds_iff]
  exact zero_ne_one

end SHIGURE.StackQuantities
end
