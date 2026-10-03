import ResearchLean.AG.RelativeRepairComposition.W2RestrictionDiagram
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# All actual W2 ordinary descent seams and compatible arrows

The seam reads the original w label of the actual overlap morphism. The two
local arrows have zero full labels, so a compatible comma arrow exists exactly
when the two original seam values agree. No overlap label is identified away.
-/
namespace AAT.AG.RelativeRepairComposition.W2OrdinarySeams
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2GaugeLabels
open W2EmptyGroupoids W2RestrictionDiagram
attribute [local instance] W2RestrictionDiagram.leftAction W2RestrictionDiagram.rightAction
  W2RestrictionDiagram.overlapAction

/-- The ordinary object's seam is its complete actual original overlap label at w. -/
def seam (D : Ordinary) : ZMod 3 := D.hom.1.toAdd.1 overlapW

/-- Restricting any whole left arrow produces the actual overlap identity arrow. -/
theorem left_map_identity {R Q : LocalCategory leftRegion ∅} (f : R ⟶ Q) :
    leftRestriction.map f = 𝟙 (leftRestriction.obj R) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change leftLabelRestriction f.1.toAdd = 0
  rw [left_empty_zero f.1.toAdd, map_zero]

/-- Restricting any whole right arrow produces the actual overlap identity arrow. -/
theorem right_map_identity {R Q : LocalCategory rightRegion ∅} (f : R ⟶ Q) :
    rightRestriction.map f = 𝟙 (rightRestriction.obj R) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change rightLabelRestriction f.1.toAdd = 0
  rw [right_empty_zero f.1.toAdd, map_zero]

/-- Every compatible actual comma arrow preserves the entire original seam value. -/
theorem seam_equal_of_hom {D E : Ordinary} (f : D ⟶ E) : seam D = seam E := by
  have h := f.w
  rw [left_map_identity f.left, right_map_identity f.right, Category.id_comp,
    Category.comp_id] at h
  exact congrArg (fun b => b.1.toAdd.1 overlapW) h.symm

/-- The original left actual point is its unchanged original e1 repair. -/
noncomputable def leftObject : LocalCategory leftRegion ∅ := localReferenceRepair leftRegion ∅
/-- The original right actual point is its unchanged original e2 repair. -/
noncomputable def rightObject : LocalCategory rightRegion ∅ := localReferenceRepair rightRegion ∅

/-- Every full seam a defines an actual ordinary descent object. -/
noncomputable def seamObject (a : ZMod 3) : Ordinary where
  left := leftObject
  right := rightObject
  hom := ⟨Multiplicative.ofAdd (overlapLabel a), local_empty_unique overlap _⟩

/-- The actual seam construction evaluates to the specified entire original F3 value. -/
theorem seam_object (a : ZMod 3) : seam (seamObject a) = a := rfl

/-- Every original left categorical object is the same unchanged full actual repair. -/
theorem left_object_eq (D : Ordinary) : D.left = leftObject := by
  rcases D.left with ⟨u,R⟩
  cases u
  exact congrArg (fun R : LocalRepairs leftRegion ∅ =>
    (R : LocalCategory leftRegion ∅)) (local_empty_unique leftRegion R)

/-- Every original right categorical object is the same unchanged full actual repair. -/
theorem right_object_eq (D : Ordinary) : D.right = rightObject := by
  rcases D.right with ⟨u,R⟩
  cases u
  exact congrArg (fun R : LocalRepairs rightRegion ∅ =>
    (R : LocalCategory rightRegion ∅)) (local_empty_unique rightRegion R)

/-- Restoring the actual seam restores both original local objects and the entire overlap arrow. -/
theorem seam_restore (D : Ordinary) : seamObject (seam D) = D := by
  have hl := left_object_eq D
  have hr := right_object_eq D
  rcases D with ⟨l,r,h⟩
  dsimp only at hl hr
  subst l
  subst r
  apply congrArg (fun f : leftRestriction.obj leftObject ⟶ rightRestriction.obj rightObject =>
    (⟨leftObject,rightObject,f⟩ : Ordinary))
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  exact overlapLabelEquiv.symm_apply_apply h.1.toAdd

/-- The entire actual comma object family, including its actual seam arrow, has both F3 coordinate inverses. -/
noncomputable def objectEquiv : Ordinary ≃ ZMod 3 where
  toFun := seam
  invFun := seamObject
  left_inv := seam_restore
  right_inv := seam_object

/-- Two actual comma objects have an arrow exactly when their complete original seam labels agree. -/
theorem hom_iff (D E : Ordinary) : Nonempty (D ⟶ E) ↔ seam D = seam E := by
  constructor
  · rintro ⟨f⟩; exact seam_equal_of_hom f
  · intro h
    have he : D = E := objectEquiv.injective h
    subst E
    exact ⟨𝟙 D⟩

/-- Every actual comma hom-set has exactly the original full compatible arrows, with at most one arrow. -/
theorem hom_unique {D E : Ordinary} (f g : D ⟶ E) : f = g := by
  apply Comma.hom_ext
  · apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [left_empty_zero f.left.1.toAdd, left_empty_zero g.left.1.toAdd]
  · apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [right_empty_zero f.right.1.toAdd, right_empty_zero g.right.1.toAdd]

/-- The complete actual ordinary diagram maps to discrete F3 by its original seam. -/
def seamFunctor : Ordinary ⥤ Discrete (ZMod 3) where
  obj D := Discrete.mk (seam D)
  map f := Discrete.eqToHom' (seam_equal_of_hom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The ordinary actual homotopy pullback is the whole discrete F3, on all objects and arrows. -/
noncomputable def discreteEquivalence : Ordinary ≌ Discrete (ZMod 3) := by
  let F := seamFunctor
  letI : F.Full := {
    map_surjective := by
      intro D E f
      exact ⟨((hom_iff D E).mpr (Discrete.eq_of_hom f)).some, Subsingleton.elim _ _⟩ }
  letI : F.Faithful := {
    map_injective := by
      intro D E f g _
      exact hom_unique f g }
  letI : F.EssSurj := {
    mem_essImage := by
      intro a
      refine ⟨seamObject a.as, ⟨?_⟩⟩
      exact eqToIso (by change Discrete.mk (seam (seamObject a.as)) = a; rw [seam_object]) }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end AAT.AG.RelativeRepairComposition.W2OrdinarySeams
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2OrdinarySeams
