import ResearchLean.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses
import ResearchLean.AG.RelativeRepairComposition.W3UnrestrictedRestrictions
import ResearchLean.AG.RelativeRepairComposition.W3Classes
import ResearchLean.AG.RelativeRepairComposition.W3Automorphisms
import Mathlib.CategoryTheory.Discrete.Basic

/-! # W3's actual local π₀-first information loss

The ordinary pullback below uses the actual maps of whole original local
isomorphism quotients induced by the original restriction functors. It has
one point. Its discrete arrows lose the global classes and automorphisms.
-/
namespace AAT.AG.RelativeRepairComposition.W3Pi0Loss
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3ActualArrows
open W3LocalRepairs W3UnrestrictedLocalFunctors
attribute [local instance] actualAction localAction

/-- Every actual original U isomorphism class, before its overlap restriction. -/
abbrev LeftClasses (sheared : Bool) :=
  Quotient (isIsomorphicSetoid (LocalCategory sheared leftRegion candidates))
/-- Every actual original V isomorphism class, before its overlap restriction. -/
abbrev RightClasses (sheared : Bool) :=
  Quotient (isIsomorphicSetoid (LocalCategory sheared rightRegion candidates))
/-- Every actual original overlap isomorphism class. -/
abbrev OverlapClasses (sheared : Bool) :=
  Quotient (isIsomorphicSetoid (LocalCategory sheared overlap candidates))

/-- The original actual U restriction induces this map on its whole isomorphism quotient. -/
noncomputable def leftClassRestriction (sheared : Bool) : LeftClasses sheared → OverlapClasses sheared :=
  Quotient.map (W3UnrestrictedRestrictions.leftRestriction sheared).obj
    (fun _ _ h => ⟨(W3UnrestrictedRestrictions.leftRestriction sheared).mapIso h.some⟩)

/-- The original actual V restriction induces this map on its whole isomorphism quotient. -/
noncomputable def rightClassRestriction (sheared : Bool) : RightClasses sheared → OverlapClasses sheared :=
  Quotient.map (W3UnrestrictedRestrictions.rightRestriction sheared).obj
    (fun _ _ h => ⟨(W3UnrestrictedRestrictions.rightRestriction sheared).mapIso h.some⟩)

/-- Taking local π₀ first gives the ordinary pullback of these same original quotient maps. -/
def Pi0Pullback (sheared : Bool) :=
  {p : LeftClasses sheared × RightClasses sheared //
    leftClassRestriction sheared p.1 = rightClassRestriction sheared p.2}

/-- The same original unchanged local references give the actual compatible class pair. -/
noncomputable def referencePair (sheared : Bool) : Pi0Pullback sheared :=
  ⟨(Quotient.mk _ (leftReference sheared),Quotient.mk _ (rightReference sheared)),rfl⟩

/-- The entire actual local π₀ pullback has both inverse point coordinates. -/
noncomputable def pullbackEquiv (sheared : Bool) : Pi0Pullback sheared ≃ Unit where
  toFun _ := ()
  invFun _ := referencePair sheared
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply (W3UnrestrictedLocalClasses.leftClassEquiv sheared).injective
      exact Subsingleton.elim _ _
    · apply (W3UnrestrictedLocalClasses.rightClassEquiv sheared).injective
      exact Subsingleton.elim _ _
  right_inv _ := rfl

/-- Every actual class pair of the original local π₀ diagram is counted, with exactly one point. -/
theorem pullback_card (sheared : Bool) : Nat.card (Pi0Pullback sheared) = 1 := by
  rw [Nat.card_congr (pullbackEquiv sheared), Nat.card_eq_fintype_card]
  rfl

/-- Local π₀-first gluing cannot retain the whole original global class family for either full transport. -/
theorem global_class_count_lost (sheared : Bool) :
    Nat.card (Quotient (isIsomorphicSetoid (ActualCategory sheared candidates))) ≠
      Nat.card (Pi0Pullback sheared) := by
  intro h
  cases sheared
  · rw [W3Classes.identity_class_card,pullback_card] at h
    exact (by decide : (9 : Nat) ≠ 1) h
  · rw [W3Classes.shear_class_card,pullback_card] at h
    exact (by decide : (3 : Nat) ≠ 1) h

/-- Treating these π₀ points as discrete objects retains exactly one arrow at every object. -/
theorem pi0_aut_card (sheared : Bool) (p : Discrete (Pi0Pullback sheared)) : Nat.card (Aut p) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨?_,⟨Iso.refl p⟩⟩
  constructor
  intro f g
  apply Aut.ext
  exact Subsingleton.elim _ _

/-- Local π₀-first discrete gluing loses each full original global automorphism group. -/
theorem global_aut_count_lost (sheared : Bool) (R : ActualCategory sheared candidates)
    (p : Discrete (Pi0Pullback sheared)) : Nat.card (Aut R) ≠ Nat.card (Aut p) := by
  intro h
  cases sheared
  · rw [W3Automorphisms.identity_aut_card,pi0_aut_card] at h
    exact (by decide : (9 : Nat) ≠ 1) h
  · rw [W3Automorphisms.shear_aut_card,pi0_aut_card] at h
    exact (by decide : (3 : Nat) ≠ 1) h

end AAT.AG.RelativeRepairComposition.W3Pi0Loss
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3Pi0Loss
