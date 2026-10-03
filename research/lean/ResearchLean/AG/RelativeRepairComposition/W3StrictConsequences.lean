import ResearchLean.AG.RelativeRepairComposition.W3StrictLabels
import ResearchLean.AG.RelativeRepairComposition.W3StrictInverseChecks
import ResearchLean.AG.RelativeRepairComposition.W3Automorphisms
import ResearchLean.AG.RelativeRepairComposition.W3Classes
import ResearchLean.AG.RelativeRepairComposition.W2OrdinaryClasses

/-! # W3's full generated strict objects and automorphisms

The literal inverse functors retain every original operation and full label.
In particular empty permission gives one actual object while keeping its
entire nontrivial fixed-vector automorphism group for either loop transport.
-/
namespace AAT.AG.RelativeRepairComposition.W3StrictConsequences
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3ActualArrows
open W3GaugeLabels W3Automorphisms W3Classes W3StrictGeneratedCover W3StrictLabels
attribute [local instance] actualAction Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (sheared : Bool)

/-- Every full strict arrow restores its same entire original actual vertex label. -/
theorem actual_inverse_label (S : Set (EdgeName (K := geometry)))
    {R Q : W3StrictGeneratedCover.Groupoid sheared S} (f : R ⟶ Q) :
    ((actualEquivalence sheared S).inverse.map f).1.toAdd =
      (actualLabelEquiv sheared S).symm f.1.toAdd := rfl

/-- The whole generated empty-permission object family has both inverse actual point coordinates. -/
noncomputable def emptyObjectEquiv : Objects sheared ∅ ≃ Unit :=
  (actualObjectEquiv sheared ∅).symm.trans (W3ActualRepairs.emptyObjectEquiv sheared)

/-- Every complete generated empty-permission object is counted, with exactly one object. -/
theorem empty_object_card : Nat.card (Objects sheared ∅) = 1 := by
  rw [Nat.card_congr (emptyObjectEquiv sheared), Nat.card_eq_fintype_card]
  rfl

/-- The whole strict categorical isomorphism quotient has both inverse point coordinates. -/
noncomputable def emptyClassEquiv :
    Quotient (isIsomorphicSetoid (W3StrictGeneratedCover.Groupoid sheared ∅)) ≃ Unit :=
  (W2OrdinaryClasses.equivalenceClasses (actualEquivalence sheared ∅).symm).trans
    (W3Classes.emptyClassEquiv sheared)

/-- The whole generated strict empty-permission category has exactly one isomorphism class. -/
theorem empty_class_card :
    Nat.card (Quotient (isIsomorphicSetoid (W3StrictGeneratedCover.Groupoid sheared ∅))) = 1 := by
  rw [Nat.card_congr (emptyClassEquiv sheared), Nat.card_eq_fintype_card]
  rfl

/-- Each complete generated strict object's full automorphism group is the original fixed-vector group. -/
noncomputable def autFixedEquiv (S : Set (EdgeName (K := geometry)))
    (R : W3StrictGeneratedCover.Groupoid sheared S) : Aut R ≃* Multiplicative (FixedVectors sheared) :=
  ((actualEquivalence sheared S).fullyFaithfulInverse.autMulEquivOfFullyFaithful R).trans
    (W3Automorphisms.autFixedEquiv ((actualEquivalence sheared S).inverse.obj R))

/-- Every generated shear object's full automorphism group retains all original F3 labels. -/
noncomputable def shearAutEquiv (S : Set (EdgeName (K := geometry)))
    (R : W3StrictGeneratedCover.Groupoid true S) : Aut R ≃* Multiplicative (ZMod 3) :=
  (autFixedEquiv true S R).trans shearFixedEquiv.toMultiplicative

/-- Every generated identity object's full automorphism group retains the entire original A. -/
noncomputable def identityAutEquiv (S : Set (EdgeName (K := geometry)))
    (R : W3StrictGeneratedCover.Groupoid false S) : Aut R ≃* Multiplicative A :=
  (autFixedEquiv false S R).trans identityFixedEquiv.toMultiplicative

/-- Each full generated shear stabilizer has exactly three distinct original labels. -/
theorem shear_aut_card (S : Set (EdgeName (K := geometry)))
    (R : W3StrictGeneratedCover.Groupoid true S) : Nat.card (Aut R) = 3 := by
  rw [Nat.card_congr (shearAutEquiv S R).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- Each full generated identity stabilizer has exactly nine distinct original labels. -/
theorem identity_aut_card (S : Set (EdgeName (K := geometry)))
    (R : W3StrictGeneratedCover.Groupoid false S) : Nat.card (Aut R) = 9 := by
  rw [Nat.card_congr (identityAutEquiv S R).toEquiv]
  simp [A, Nat.card_eq_fintype_card]

end AAT.AG.RelativeRepairComposition.W3StrictConsequences
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3StrictConsequences
