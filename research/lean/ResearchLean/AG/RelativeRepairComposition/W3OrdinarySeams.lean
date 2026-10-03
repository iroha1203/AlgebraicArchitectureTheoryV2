import ResearchLean.AG.RelativeRepairComposition.W3RestrictionDiagram

/-! # Every W3 ordinary object's complete actual overlap seam

The original (s,t) label pair is read from the actual overlap arrow. Both
local objects are the independent unchanged reference repairs. The complete
comma-square equation keeps the actual U and V arrow coordinates.
-/
namespace AAT.AG.RelativeRepairComposition.W3OrdinarySeams
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3LocalRepairs W3LocalLabels W3RestrictionDiagram
attribute [local instance] localAction

/-- The ordinary seam is the entire original overlap (s,t) arrow label. -/
def seam {sheared : Bool} (D : Ordinary sheared) : A × A :=
  overlapLabelEquiv sheared ∅ D.hom.1.toAdd

/-- U's actual categorical reference object keeps its original full affine edge. -/
noncomputable def leftObject (sheared : Bool) : LocalCategory sheared leftRegion ∅ :=
  localReferenceRepair sheared leftRegion ∅
/-- V's actual categorical reference object keeps its original full affine edge and T. -/
noncomputable def rightObject (sheared : Bool) : LocalCategory sheared rightRegion ∅ :=
  localReferenceRepair sheared rightRegion ∅

/-- Every full original overlap label pair is an actual ordinary descent object. -/
noncomputable def seamObject (sheared : Bool) (p : A × A) : Ordinary sheared where
  left := leftObject sheared
  right := rightObject sheared
  hom := ⟨Multiplicative.ofAdd (overlapLabel sheared ∅ p.1 p.2), local_empty_unique sheared overlap _⟩

/-- Reading the constructed actual overlap arrow recovers both entire original vectors. -/
theorem seam_object (sheared : Bool) (p : A × A) : seam (seamObject sheared p) = p := rfl

/-- Every ordinary left categorical object is the unchanged independent U repair. -/
theorem left_object_eq {sheared : Bool} (D : Ordinary sheared) : D.left = leftObject sheared := by
  rcases D.left with ⟨u,R⟩
  cases u
  exact congrArg (fun R : LocalRepairs sheared leftRegion ∅ =>
    (R : LocalCategory sheared leftRegion ∅)) (local_empty_unique sheared leftRegion R)

/-- Every ordinary right categorical object is the unchanged independent V repair. -/
theorem right_object_eq {sheared : Bool} (D : Ordinary sheared) : D.right = rightObject sheared := by
  rcases D.right with ⟨u,R⟩
  cases u
  exact congrArg (fun R : LocalRepairs sheared rightRegion ∅ =>
    (R : LocalCategory sheared rightRegion ∅)) (local_empty_unique sheared rightRegion R)

/-- Both original local objects and the entire actual overlap arrow are restored exactly. -/
theorem seam_restore {sheared : Bool} (D : Ordinary sheared) : seamObject sheared (seam D) = D := by
  have hl := left_object_eq D
  have hr := right_object_eq D
  rcases D with ⟨l,r,h⟩
  dsimp only at hl hr
  subst l
  subst r
  apply congrArg (fun f : (leftRestriction sheared).obj (leftObject sheared) ⟶
      (rightRestriction sheared).obj (rightObject sheared) =>
    (⟨leftObject sheared,rightObject sheared,f⟩ : Ordinary sheared))
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  exact (overlapLabelEquiv sheared ∅).symm_apply_apply h.1.toAdd

/-- The entire actual ordinary object family has both inverse full A² seam coordinates. -/
noncomputable def objectEquiv (sheared : Bool) : Ordinary sheared ≃ (A × A) where
  toFun := seam
  invFun := seamObject sheared
  left_inv := seam_restore
  right_inv := seam_object sheared

/-- Every actual ordinary seam pair is counted, before any isomorphism quotient. -/
theorem ordinary_object_card (sheared : Bool) : Nat.card (Ordinary sheared) = 81 := by
  rw [Nat.card_congr (objectEquiv sheared)]
  simp [A, Nat.card_eq_fintype_card]

/-- Any full U label is an actual arrow between its uniquely fixed local objects. -/
noncomputable def leftArrow (sheared : Bool) {R Q : LocalCategory sheared leftRegion ∅}
    (b : LocalLabels sheared leftRegion ∅) : R ⟶ Q :=
  ⟨Multiplicative.ofAdd b, (local_empty_unique sheared leftRegion _).trans
    (local_empty_unique sheared leftRegion _).symm⟩

/-- Any full V label is an actual arrow between its uniquely fixed local objects. -/
noncomputable def rightArrow (sheared : Bool) {R Q : LocalCategory sheared rightRegion ∅}
    (b : LocalLabels sheared rightRegion ∅) : R ⟶ Q :=
  ⟨Multiplicative.ofAdd b, (local_empty_unique sheared rightRegion _).trans
    (local_empty_unique sheared rightRegion _).symm⟩

/-- The whole actual comma-square equation is precisely the original two-vector boundary equation. -/
theorem square_iff {sheared : Bool} (D E : Ordinary sheared) (b : D.left ⟶ E.left)
    (c : D.right ⟶ E.right) :
    (leftRestriction sheared).map b ≫ E.hom = D.hom ≫ (rightRestriction sheared).map c ↔
      seam E + (leftLabelEquiv sheared b.1.toAdd,leftLabelEquiv sheared b.1.toAdd) =
        (linearAction sheared (rightLabelEquiv sheared c.1.toAdd),
          rightLabelEquiv sheared c.1.toAdd) + seam D := by
  constructor
  · intro h
    exact congrArg (fun f => overlapLabelEquiv sheared ∅ f.1.toAdd) h
  · intro h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (overlapLabelEquiv sheared ∅).injective
    exact h

/-- Every full compatible ordinary arrow has the exact original boundary equation. -/
theorem hom_square {sheared : Bool} {D E : Ordinary sheared} (f : D ⟶ E) :
    seam E + (leftLabelEquiv sheared f.left.1.toAdd,leftLabelEquiv sheared f.left.1.toAdd) =
      (linearAction sheared (rightLabelEquiv sheared f.right.1.toAdd),
        rightLabelEquiv sheared f.right.1.toAdd) + seam D :=
  (square_iff D E f.left f.right).mp f.w

end AAT.AG.RelativeRepairComposition.W3OrdinarySeams
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3OrdinarySeams
