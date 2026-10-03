import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionRepairs

/-!
# All W1 subdivision isomorphism classes from the full native unit and counit

Classes use the actual Mathlib isomorphism setoid on the whole repair groupoid.
The original full affine repair classification and the genuine native equivalence
therefore preserve class counts while the independent new repair counts triple.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionClasses
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W1AffineInput W1Regions W1ActualRepairs W1NativeLabels W1RepairCounts W1SubdivisionRepairs

variable (x y : ZMod 3) (S : Set (EdgeName (K := geometry)))

/-- The complete actual native unit and counit induce the bijection of all new and old isomorphism classes. -/
noncomputable def classEquiv : Quotient (isIsomorphicSetoid (NewCategory x y S)) ≃
    Quotient (isIsomorphicSetoid (NativeCategory true x y S)) where
  toFun := Quotient.map (nativeEquivalence x y S).inverse.obj
    (fun _ _ h => ⟨(nativeEquivalence x y S).inverse.mapIso h.some⟩)
  invFun := Quotient.map (nativeEquivalence x y S).functor.obj
    (fun _ _ h => ⟨(nativeEquivalence x y S).functor.mapIso h.some⟩)
  left_inv R := Quotient.inductionOn R
    (fun R => Quotient.sound ⟨(nativeEquivalence x y S).counitIso.app R⟩)
  right_inv R := Quotient.inductionOn R
    (fun R => Quotient.sound ⟨((nativeEquivalence x y S).unitIso.app R).symm⟩)

/-- The whole new native isomorphism-class count equals the count of all original actual affine repairs, for every S. -/
theorem class_card : Nat.card (Quotient (isIsomorphicSetoid (NewCategory x y S))) =
    Nat.card (RealRepairs true x y S) := by
  rw [Nat.card_congr (classEquiv x y S), class_card_eq_actual_card]

/-- The entire empty-range new class count remains three at zero d and zero otherwise. -/
theorem empty_class_card : Nat.card (Quotient (isIsomorphicSetoid (NewCategory x y ∅))) =
    if y - x = 0 then 3 else 0 := by
  rw [class_card, negative_empty_card]

/-- The whole b-only new native groupoid has exactly three isomorphism classes. -/
theorem b_class_card : Nat.card (Quotient (isIsomorphicSetoid (NewCategory x y {name edgeB}))) = 3 := by
  rw [class_card, negative_b_card]

/-- The whole c-only new native groupoid also retains exactly three classes. -/
theorem c_class_card : Nat.card (Quotient (isIsomorphicSetoid (NewCategory x y {name edgeC}))) = 3 := by
  rw [class_card, negative_c_card]

/-- Allowing both unchanged original candidates retains all nine original classes despite twenty-seven new repairs. -/
theorem full_class_card : Nat.card (Quotient (isIsomorphicSetoid (NewCategory x y candidates))) = 9 := by
  rw [class_card, negative_full_card]

end AAT.AG.RelativeRepairComposition.W1SubdivisionClasses
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionClasses
