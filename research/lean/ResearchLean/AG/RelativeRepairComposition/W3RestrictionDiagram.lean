import ResearchLean.AG.RelativeRepairComposition.W3LocalLabels
import ResearchLean.AG.RelativeRepairComposition.CommaCoordinates

/-! # W3's actual original restricted ordinary descent diagram

U and V each retain both original vertices. Their full-label restrictions
are (b,b) and (T c,c) on the same ordered original (s,t) overlap. The comma
category is defined from those actual restrictions before classification.
-/
namespace AAT.AG.RelativeRepairComposition.W3RestrictionDiagram
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3LocalRepairs W3LocalLabels
attribute [local instance] localAction

/-- U restriction keeps both actual original overlap vectors. -/
def leftLabelRestriction (sheared : Bool) :
    LocalLabels sheared leftRegion ∅ →+ LocalLabels sheared overlap ∅ where
  toFun b := overlapLabel sheared ∅ (b.1 leftS) (b.1 leftS)
  map_zero' := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v <;> rfl
  map_add' b c := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v <;> rfl

/-- V restriction keeps the original full T and both original overlap vectors. -/
def rightLabelRestriction (sheared : Bool) :
    LocalLabels sheared rightRegion ∅ →+ LocalLabels sheared overlap ∅ where
  toFun b := overlapLabel sheared ∅ (linearAction sheared (b.1 rightT)) (b.1 rightT)
  map_zero' := by
    apply Subtype.ext
    funext v
    change (if (v.1 : Fin 2).val = 0 then linearAction sheared 0 else 0) = 0
    rw [map_zero]
    split <;> rfl
  map_add' b c := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v
    · exact (linearAction sheared).map_add _ _
    · rfl

/-- The original U boundary is the full diagonal b↦(b,b). -/
theorem left_boundary (sheared : Bool) (b : LocalLabels sheared leftRegion ∅) :
    overlapLabelEquiv sheared ∅ (leftLabelRestriction sheared b) =
      (leftLabelEquiv sheared b, leftLabelEquiv sheared b) := rfl

/-- The original V boundary is the full map c↦(T c,c). -/
theorem right_boundary (sheared : Bool) (b : LocalLabels sheared rightRegion ∅) :
    overlapLabelEquiv sheared ∅ (rightLabelRestriction sheared b) =
      (linearAction sheared (rightLabelEquiv sheared b),rightLabelEquiv sheared b) := rfl

/-- U's restriction is literally evaluation at each same original overlap vertex. -/
theorem left_original_value (sheared : Bool) (b : LocalLabels sheared leftRegion ∅)
    (v : (ClosedRegion.presentation overlap).Vertex) :
    (leftLabelRestriction sheared b).1 v =
      b.1 ⟨v.1,(ClosedRegion.inter_left leftRegion rightRegion).vertices v.2⟩ := by
  rcases v with ⟨v,hv⟩
  fin_cases v
  · rfl
  · exact (left_relation sheared b).symm

/-- V's restriction is literally evaluation at each same original overlap vertex. -/
theorem right_original_value (sheared : Bool) (b : LocalLabels sheared rightRegion ∅)
    (v : (ClosedRegion.presentation overlap).Vertex) :
    (rightLabelRestriction sheared b).1 v =
      b.1 ⟨v.1,(ClosedRegion.inter_right leftRegion rightRegion).vertices v.2⟩ := by
  rcases v with ⟨v,hv⟩
  fin_cases v
  · exact (right_relation sheared b).symm
  · rfl

/-- The original actual U restriction retains all original full-label arrows. -/
noncomputable def leftRestriction (sheared : Bool) :
    LocalCategory sheared leftRegion ∅ ⥤ LocalCategory sheared overlap ∅ :=
  actionLabelFunctor (leftLabelRestriction sheared).toMultiplicative
    (fun _ => localReferenceRepair sheared overlap ∅)
    (fun _ _ => (local_empty_unique sheared overlap _).symm)

/-- The original actual V restriction retains all original full-label arrows. -/
noncomputable def rightRestriction (sheared : Bool) :
    LocalCategory sheared rightRegion ∅ ⥤ LocalCategory sheared overlap ∅ :=
  actionLabelFunctor (rightLabelRestriction sheared).toMultiplicative
    (fun _ => localReferenceRepair sheared overlap ∅)
    (fun _ _ => (local_empty_unique sheared overlap _).symm)

/-- Mapping any actual U arrow preserves its entire vector at each original overlap vertex. -/
theorem left_map_value (sheared : Bool) {R Q : LocalCategory sheared leftRegion ∅} (f : R ⟶ Q)
    (v : (ClosedRegion.presentation overlap).Vertex) :
    ((leftRestriction sheared).map f).1.toAdd.1 v =
      f.1.toAdd.1 ⟨v.1,(ClosedRegion.inter_left leftRegion rightRegion).vertices v.2⟩ :=
  left_original_value sheared f.1.toAdd v

/-- Mapping any actual V arrow preserves its entire vector at each original overlap vertex. -/
theorem right_map_value (sheared : Bool) {R Q : LocalCategory sheared rightRegion ∅} (f : R ⟶ Q)
    (v : (ClosedRegion.presentation overlap).Vertex) :
    ((rightRestriction sheared).map f).1.toAdd.1 v =
      f.1.toAdd.1 ⟨v.1,(ClosedRegion.inter_right leftRegion rightRegion).vertices v.2⟩ :=
  right_original_value sheared f.1.toAdd v

/-- The ordinary homotopy pullback is the whole actual comma of the original restrictions. -/
abbrev Ordinary (sheared : Bool) := Comma (leftRestriction sheared) (rightRestriction sheared)

/-- Every arrow of this actual ordinary comma is an isomorphism. -/
theorem ordinary_is_groupoid (sheared : Bool) : IsGroupoid (Ordinary sheared) :=
  CommaCoordinates.comma_is_groupoid (leftRestriction sheared) (rightRestriction sheared)

end AAT.AG.RelativeRepairComposition.W3RestrictionDiagram
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3RestrictionDiagram
