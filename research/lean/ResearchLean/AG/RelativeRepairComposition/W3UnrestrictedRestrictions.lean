import ResearchLean.AG.RelativeRepairComposition.W3LocalGauge

/-! # Original unrestricted W3 overlap restrictions

Each patch retains both original vertices and therefore restricts its two
entire label values to the same original (s,t) overlap. The actual overlap
object has no selected operation and is independently unique for every S.
-/
namespace AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3LocalRepairs W3LocalLabels W3LocalOperationCoordinates W3LocalFullLabels
attribute [local instance] localAction

/-- Original U-to-overlap restriction retains both full original label vectors. -/
noncomputable def leftLabelRestriction (sheared : Bool) :
    LocalLabels sheared leftRegion candidates →+ LocalLabels sheared overlap candidates :=
  ((overlapLabelEquiv sheared candidates).symm.toAddMonoidHom).comp
    (leftFullLabelEquiv sheared).toAddMonoidHom

/-- Original V-to-overlap restriction retains both full original label vectors. -/
noncomputable def rightLabelRestriction (sheared : Bool) :
    LocalLabels sheared rightRegion candidates →+ LocalLabels sheared overlap candidates :=
  ((overlapLabelEquiv sheared candidates).symm.toAddMonoidHom).comp
    (rightFullLabelEquiv sheared).toAddMonoidHom

/-- U restricts at the very same original vertex, for every full original label. -/
theorem left_original_value (sheared : Bool) (b : LocalLabels sheared leftRegion candidates)
    (v : (ClosedRegion.presentation overlap).Vertex) :
    (leftLabelRestriction sheared b).1 v =
      b.1 ⟨v.1,(ClosedRegion.inter_left leftRegion rightRegion).vertices v.2⟩ := by
  rcases v with ⟨v,hv⟩
  fin_cases v <;> rfl

/-- V restricts at the very same original vertex, for every full original label. -/
theorem right_original_value (sheared : Bool) (b : LocalLabels sheared rightRegion candidates)
    (v : (ClosedRegion.presentation overlap).Vertex) :
    (rightLabelRestriction sheared b).1 v =
      b.1 ⟨v.1,(ClosedRegion.inter_right leftRegion rightRegion).vertices v.2⟩ := by
  rcases v with ⟨v,hv⟩
  fin_cases v <;> rfl

/-- The whole original actual U restriction preserves all full labeled arrows. -/
noncomputable def leftRestriction (sheared : Bool) :
    LocalCategory sheared leftRegion candidates ⥤ LocalCategory sheared overlap candidates :=
  actionLabelFunctor (leftLabelRestriction sheared).toMultiplicative
    (fun _ => localReferenceRepair sheared overlap candidates)
    (fun _ _ => (overlap_unique sheared candidates _).symm)

/-- The whole original actual V restriction preserves all full labeled arrows. -/
noncomputable def rightRestriction (sheared : Bool) :
    LocalCategory sheared rightRegion candidates ⥤ LocalCategory sheared overlap candidates :=
  actionLabelFunctor (rightLabelRestriction sheared).toMultiplicative
    (fun _ => localReferenceRepair sheared overlap candidates)
    (fun _ _ => (overlap_unique sheared candidates _).symm)

/-- U arrow restriction evaluates to the same full original vertex value. -/
theorem left_map_value (sheared : Bool) {R Q : LocalCategory sheared leftRegion candidates}
    (f : R ⟶ Q) (v : (ClosedRegion.presentation overlap).Vertex) :
    ((leftRestriction sheared).map f).1.toAdd.1 v =
      f.1.toAdd.1 ⟨v.1,(ClosedRegion.inter_left leftRegion rightRegion).vertices v.2⟩ :=
  left_original_value sheared f.1.toAdd v

/-- V arrow restriction evaluates to the same full original vertex value. -/
theorem right_map_value (sheared : Bool) {R Q : LocalCategory sheared rightRegion candidates}
    (f : R ⟶ Q) (v : (ClosedRegion.presentation overlap).Vertex) :
    ((rightRestriction sheared).map f).1.toAdd.1 v =
      f.1.toAdd.1 ⟨v.1,(ClosedRegion.inter_right leftRegion rightRegion).vertices v.2⟩ :=
  right_original_value sheared f.1.toAdd v

end AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3UnrestrictedRestrictions
