import ResearchLean.AG.RelativeRepairComposition.W1PermissionClassification
import ResearchLean.AG.RelativeRepairComposition.W1NativeLabels

/-!
# Cardinalities of all actual W1 repairs and native classes

## Implementation notes

Cardinalities are transported along equivalences of the entire independent
actual repair types. The private h is arbitrary even when both candidates are
forbidden. Class cardinalities use the proved full native hom classification,
rather than treating a coordinate family as a groupoid.
-/
namespace AAT.AG.RelativeRepairComposition.W1RepairCounts
open CategoryTheory TransportCoherence AbelianLiftingObstruction
open W1AffineInput W1Regions W1ActualRepairs W1PermissionClassification W1NativeLabels

/-- At zero obstruction the empty mask retains the full private h and forces both candidate values to zero. -/
noncomputable def negativeEmptyChoiceEquiv (d : ZMod 3) (hd : d = 0) :
    NegativeChoices ∅ d ≃ ZMod 3 where
  toFun q := q.1.1
  invFun h := ⟨(h, 0), by simp [hd]⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext rfl (q.2.1 (by simp)).symm
  right_inv _ := rfl

/-- Permitting only b retains the full private h and forces the original candidate value z=d. -/
noncomputable def negativeBChoiceEquiv (d : ZMod 3) :
    NegativeChoices {name edgeB} d ≃ ZMod 3 where
  toFun q := q.1.1
  invFun h := ⟨(h, d), by simp [geometry, name, edgeB, edgeC]⟩
  left_inv q := by
    apply Subtype.ext
    have hz := q.2.2 (by simp [geometry, name, edgeB, edgeC])
    exact Prod.ext rfl (sub_eq_zero.mp hz)
  right_inv _ := rfl

/-- Permitting only c retains the full private h and forces the original candidate b value to zero. -/
noncomputable def negativeCChoiceEquiv (d : ZMod 3) :
    NegativeChoices {name edgeC} d ≃ ZMod 3 where
  toFun q := q.1.1
  invFun h := ⟨(h, 0), by simp [geometry, name, edgeB, edgeC]⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext rfl (q.2.1 (by simp [geometry, name, edgeB, edgeC])).symm
  right_inv _ := rfl

/-- All actual empty-range repairs retain precisely the three private h values when d=0. -/
noncomputable def negativeEmptyActualEquiv (x y : ZMod 3) (hd : y - x = 0) :
    RealRepairs true x y ∅ ≃ ZMod 3 :=
  (negativeActualEquiv x y ∅).trans (negativeEmptyChoiceEquiv (y - x) hd)

/-- Every x,y has precisely the entire three-value actual b-only repair family. -/
noncomputable def negativeBActualEquiv (x y : ZMod 3) :
    RealRepairs true x y {name edgeB} ≃ ZMod 3 :=
  (negativeActualEquiv x y _).trans (negativeBChoiceEquiv (y - x))

/-- Every x,y has precisely the entire three-value actual c-only repair family. -/
noncomputable def negativeCActualEquiv (x y : ZMod 3) :
    RealRepairs true x y {name edgeC} ≃ ZMod 3 :=
  (negativeActualEquiv x y _).trans (negativeCChoiceEquiv (y - x))

/-- The entire actual empty-range repair set has three elements at d=0 and none at nonzero d. -/
theorem negative_empty_card (x y : ZMod 3) :
    Nat.card (RealRepairs true x y ∅) = if y - x = 0 then 3 else 0 := by
  classical
  by_cases hd : y - x = 0
  · rw [if_pos hd, Nat.card_congr (negativeEmptyActualEquiv x y hd),
      Nat.card_eq_fintype_card, ZMod.card]
  · rw [if_neg hd]
    letI : IsEmpty (RealRepairs true x y ∅) :=
      ⟨fun R => hd ((negative_empty_exists_iff x y).mp ⟨R⟩)⟩
    exact Nat.card_of_isEmpty

/-- All actual b-only repairs number three for every input pair. -/
theorem negative_b_card (x y : ZMod 3) : Nat.card (RealRepairs true x y {name edgeB}) = 3 := by
  rw [Nat.card_congr (negativeBActualEquiv x y), Nat.card_eq_fintype_card, ZMod.card]

/-- All actual c-only repairs number three for every input pair. -/
theorem negative_c_card (x y : ZMod 3) : Nat.card (RealRepairs true x y {name edgeC}) = 3 := by
  rw [Nat.card_congr (negativeCActualEquiv x y), Nat.card_eq_fintype_card, ZMod.card]

/-- Both permitted original candidates retain all nine complete actual h,z choices. -/
theorem negative_full_card (x y : ZMod 3) : Nat.card (RealRepairs true x y candidates) = 9 := by
  rw [Nat.card_congr (negativeFullEquiv x y), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- Empty-range actual isomorphism classes have the same three-or-zero count, on full native arrows. -/
theorem negative_empty_class_card (x y : ZMod 3) :
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory true x y ∅))) =
      if y - x = 0 then 3 else 0 := by
  rw [class_card_eq_actual_card, negative_empty_card]

/-- All b-only native actual isomorphism classes number three. -/
theorem negative_b_class_card (x y : ZMod 3) :
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory true x y {name edgeB}))) = 3 := by
  rw [class_card_eq_actual_card, negative_b_card]

/-- All c-only native actual isomorphism classes number three. -/
theorem negative_c_class_card (x y : ZMod 3) :
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory true x y {name edgeC}))) = 3 := by
  rw [class_card_eq_actual_card, negative_c_card]

/-- All fully permitted native actual isomorphism classes number nine. -/
theorem negative_full_class_card (x y : ZMod 3) :
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory true x y candidates))) = 9 := by
  rw [class_card_eq_actual_card, negative_full_card]

end AAT.AG.RelativeRepairComposition.W1RepairCounts
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1RepairCounts
