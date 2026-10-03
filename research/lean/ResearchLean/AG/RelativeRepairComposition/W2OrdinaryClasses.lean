import ResearchLean.AG.RelativeRepairComposition.W2OrdinarySeams
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.SetTheory.Cardinal.Finite

/-!
# W2's whole ordinary class count and actual non-equivalence

The quotients are Mathlib's isomorphism setoids of the original actual repair
and actual comma categories. The three-versus-one calculation follows from
their complete object and arrow comparisons, not a selected seam image.
-/
namespace AAT.AG.RelativeRepairComposition.W2OrdinaryClasses
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2GaugeLabels
open W2EmptyGroupoids W2RestrictionDiagram W2OrdinarySeams

/-- The global actual categorical object is the original unchanged affine edge pair. -/
noncomputable def globalObject : ActualCategory ∅ := referenceRepair ∅

/-- Every global actual categorical object is this same unchanged original edge pair. -/
theorem global_object_eq (R : ActualCategory ∅) : R = globalObject := by
  rcases R with ⟨u,R⟩
  cases u
  exact congrArg (fun R : RealRepairs ∅ => (R : ActualCategory ∅)) (empty_unique R)

/-- The complete actual global isomorphism quotient has mutually inverse point coordinates. -/
noncomputable def globalClassEquiv : Quotient (isIsomorphicSetoid (ActualCategory ∅)) ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => Quotient.mk _ globalObject
  left_inv q := Quotient.inductionOn q (fun R =>
    congrArg (Quotient.mk (isIsomorphicSetoid (ActualCategory ∅))) (global_object_eq R).symm)
  right_inv _ := rfl

/-- The actual ordinary isomorphism quotient is the entire original F3 seam family. -/
noncomputable def ordinaryClassEquiv : Quotient (isIsomorphicSetoid Ordinary) ≃ ZMod 3 where
  toFun := Quotient.lift seam (fun _ _ h => seam_equal_of_hom h.some.hom)
  invFun a := Quotient.mk _ (seamObject a)
  left_inv q := Quotient.inductionOn q (fun D =>
    congrArg (Quotient.mk (isIsomorphicSetoid Ordinary)) (seam_restore D))
  right_inv := seam_object

/-- The whole actual global repair category has exactly one isomorphism class. -/
theorem global_class_card : Nat.card (Quotient (isIsomorphicSetoid (ActualCategory ∅))) = 1 := by
  rw [Nat.card_congr globalClassEquiv, Nat.card_eq_fintype_card]
  rfl

/-- The whole actual ordinary homotopy pullback has exactly three isomorphism classes. -/
theorem ordinary_class_card : Nat.card (Quotient (isIsomorphicSetoid Ordinary)) = 3 := by
  rw [Nat.card_congr ordinaryClassEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- Every ordinary actual object is counted, including all three full overlap seam arrows. -/
theorem ordinary_object_card : Nat.card Ordinary = 3 := by
  rw [Nat.card_congr objectEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- A whole category equivalence preserves all isomorphism classes by its actual unit and counit. -/
noncomputable def equivalenceClasses {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) : Quotient (isIsomorphicSetoid C) ≃ Quotient (isIsomorphicSetoid D) where
  toFun := Quotient.map e.functor.obj (fun _ _ h => ⟨e.functor.mapIso h.some⟩)
  invFun := Quotient.map e.inverse.obj (fun _ _ h => ⟨e.inverse.mapIso h.some⟩)
  left_inv q := Quotient.inductionOn q (fun X => Quotient.sound ⟨(e.unitIso.app X).symm⟩)
  right_inv q := Quotient.inductionOn q (fun X => Quotient.sound ⟨e.counitIso.app X⟩)

/-- The original restricted global repair category is not equivalent to its actual ordinary homotopy pullback. -/
theorem global_not_equivalent : ¬ Nonempty (ActualCategory ∅ ≌ Ordinary) := by
  rintro ⟨e⟩
  have h := Nat.card_congr (equivalenceClasses e)
  rw [global_class_card, ordinary_class_card] at h
  exact (by decide : (1 : Nat) ≠ 3) h

/-- The actual zero and one seams are not isomorphic in the original ordinary diagram. -/
theorem zero_one_not_isomorphic : ¬ IsIsomorphic (seamObject 0) (seamObject 1) := by
  intro h
  have he := seam_equal_of_hom h.some.hom
  rw [seam_object, seam_object] at he
  exact zero_ne_one he

end AAT.AG.RelativeRepairComposition.W2OrdinaryClasses
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2OrdinaryClasses
