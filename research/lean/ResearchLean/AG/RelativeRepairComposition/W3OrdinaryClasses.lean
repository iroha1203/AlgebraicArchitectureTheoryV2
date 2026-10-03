import ResearchLean.AG.RelativeRepairComposition.W3OrdinaryComparison
import ResearchLean.AG.RelativeRepairComposition.W3Automorphisms
import ResearchLean.AG.RelativeRepairComposition.W2OrdinaryClasses

/-! # Full W3 ordinary classes, automorphisms and restricted non-equivalence

The whole actual comparison transports the entire ordinary isomorphism
quotient and each full automorphism group. The restricted global category
has one class, while its same original ordinary diagram has three or nine.
-/
namespace AAT.AG.RelativeRepairComposition.W3OrdinaryClasses
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3ActualArrows
open W3Classes W3Automorphisms W3LocalRepairs W3RestrictionDiagram W3OrdinaryComparison
attribute [local instance] actualAction localAction

/-- Every actual shear ordinary isomorphism class has both inverse F3 coordinates. -/
noncomputable def shearOrdinaryClassEquiv :
    Quotient (isIsomorphicSetoid (Ordinary true)) ≃ ZMod 3 :=
  (W2OrdinaryClasses.equivalenceClasses (comparisonEquivalence true).symm).trans shearClassEquiv

/-- Every actual identity ordinary isomorphism class has both inverse full A coordinates. -/
noncomputable def identityOrdinaryClassEquiv :
    Quotient (isIsomorphicSetoid (Ordinary false)) ≃ A :=
  (W2OrdinaryClasses.equivalenceClasses (comparisonEquivalence false).symm).trans identityClassEquiv

/-- The entire actual ordinary shear diagram has exactly three isomorphism classes. -/
theorem ordinary_shear_class_card :
    Nat.card (Quotient (isIsomorphicSetoid (Ordinary true))) = 3 := by
  rw [Nat.card_congr shearOrdinaryClassEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The entire actual ordinary identity diagram has exactly nine isomorphism classes. -/
theorem ordinary_identity_class_card :
    Nat.card (Quotient (isIsomorphicSetoid (Ordinary false))) = 9 := by
  rw [Nat.card_congr identityOrdinaryClassEquiv]
  simp [A, Nat.card_eq_fintype_card]

/-- Every shear ordinary object's full automorphism group is the same original F3 fixed-vector group. -/
noncomputable def shearOrdinaryAutEquiv (D : Ordinary true) : Aut D ≃* Multiplicative (ZMod 3) :=
  ((comparisonEquivalence true).fullyFaithfulInverse.autMulEquivOfFullyFaithful D).trans
    (shearAutEquiv ((comparisonEquivalence true).inverse.obj D))

/-- Every identity ordinary object's full automorphism group is the same entire original A. -/
noncomputable def identityOrdinaryAutEquiv (D : Ordinary false) : Aut D ≃* Multiplicative A :=
  ((comparisonEquivalence false).fullyFaithfulInverse.autMulEquivOfFullyFaithful D).trans
    (identityAutEquiv ((comparisonEquivalence false).inverse.obj D))

/-- All actual ordinary shear stabilizers retain exactly three full arrows. -/
theorem ordinary_shear_aut_card (D : Ordinary true) : Nat.card (Aut D) = 3 := by
  rw [Nat.card_congr (shearOrdinaryAutEquiv D).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- All actual ordinary identity stabilizers retain exactly nine full arrows. -/
theorem ordinary_identity_aut_card (D : Ordinary false) : Nat.card (Aut D) = 9 := by
  rw [Nat.card_congr (identityOrdinaryAutEquiv D).toEquiv]
  simp [A, Nat.card_eq_fintype_card]

/-- Neither original restricted global groupoid is equivalent to its whole actual ordinary homotopy pullback. -/
theorem restricted_global_not_equivalent (sheared : Bool) :
    ¬ Nonempty (ActualCategory sheared ∅ ≌ Ordinary sheared) := by
  rintro ⟨e⟩
  have h := Nat.card_congr (W2OrdinaryClasses.equivalenceClasses e)
  cases sheared
  · rw [empty_class_card, ordinary_identity_class_card] at h
    exact (by decide : (1 : Nat) ≠ 9) h
  · rw [empty_class_card, ordinary_shear_class_card] at h
    exact (by decide : (1 : Nat) ≠ 3) h

end AAT.AG.RelativeRepairComposition.W3OrdinaryClasses
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3OrdinaryClasses
