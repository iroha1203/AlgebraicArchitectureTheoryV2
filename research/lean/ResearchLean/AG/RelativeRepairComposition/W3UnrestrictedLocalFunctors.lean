import ResearchLean.AG.RelativeRepairComposition.W3LocalGauge
import ResearchLean.AG.RelativeRepairComposition.W3EmptyGroupoids

/-! # Whole original BA functors to unrestricted W3 patches

Every entire A vector gives an actual original-vertex automorphism of the
unchanged reference. Fullness and essential surjectivity will compare these
arrows with all independent unrestricted local repairs and full labels.
-/
namespace AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3LocalRepairs W3LocalLabels W3LocalFullLabels W3LocalGauge W3EmptyGroupoids
attribute [local instance] localAction

/-- U's canonical object is its unchanged full original e operation under unrestricted permission. -/
noncomputable def leftReference (sheared : Bool) : LocalCategory sheared leftRegion candidates :=
  localReferenceRepair sheared leftRegion candidates

/-- V's canonical object is its unchanged full original f operation and T under unrestricted permission. -/
noncomputable def rightReference (sheared : Bool) : LocalCategory sheared rightRegion candidates :=
  localReferenceRepair sheared rightRegion candidates

/-- Every whole A vector gives an actual U reference automorphism labeled (a,a). -/
noncomputable def leftReferenceArrow (sheared : Bool) (a : A) :
    leftReference sheared ⟶ leftReference sheared :=
  ⟨Multiplicative.ofAdd (freeLabel sheared leftRegion a a), by
    apply (left_gauge_eq sheared candidates _ _ _).mpr
    change (localReferenceRepair sheared leftRegion candidates).operation leftEdge.2.2 0 +
      (freeLabel sheared leftRegion a a).1 leftT - (freeLabel sheared leftRegion a a).1 leftS =
        (localReferenceRepair sheared leftRegion candidates).operation leftEdge.2.2 0
    rw [local_reference_zero,left_source,left_target]
    simp⟩

/-- Every whole A vector gives an actual V reference automorphism labeled (T a,a). -/
noncomputable def rightReferenceArrow (sheared : Bool) (a : A) :
    rightReference sheared ⟶ rightReference sheared :=
  ⟨Multiplicative.ofAdd (freeLabel sheared rightRegion (linearAction sheared a) a), by
    apply (right_gauge_eq sheared candidates _ _ _).mpr
    change (localReferenceRepair sheared rightRegion candidates).operation rightEdge.2.2 0 +
      (freeLabel sheared rightRegion (linearAction sheared a) a).1 rightS -
        linearAction sheared ((freeLabel sheared rightRegion (linearAction sheared a) a).1 rightT) =
          (localReferenceRepair sheared rightRegion candidates).operation rightEdge.2.2 0
    rw [local_reference_zero,right_source,right_target]
    simp⟩

/-- BA sends every original vector label to the complete actual U reference arrow. -/
noncomputable def leftFunctor (sheared : Bool) : BA ⥤ LocalCategory sheared leftRegion candidates where
  obj _ := leftReference sheared
  map a := leftReferenceArrow sheared a.toAdd
  map_id _ := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (leftFullLabelEquiv sheared).injective
    exact Prod.ext rfl rfl
  map_comp _ _ := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (leftFullLabelEquiv sheared).injective
    exact Prod.ext rfl rfl

/-- BA sends every original vector label to the complete actual V reference arrow with full T. -/
noncomputable def rightFunctor (sheared : Bool) : BA ⥤ LocalCategory sheared rightRegion candidates where
  obj _ := rightReference sheared
  map a := rightReferenceArrow sheared a.toAdd
  map_id _ := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (rightFullLabelEquiv sheared).injective
    exact Prod.ext (linearAction sheared).map_zero rfl
  map_comp a b := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (rightFullLabelEquiv sheared).injective
    exact Prod.ext ((linearAction sheared).map_add b.toAdd a.toAdd) rfl

/-- Every arbitrary full U reference arrow retains equal original s,t vectors. -/
theorem left_reference_labels (sheared : Bool) (f : leftReference sheared ⟶ leftReference sheared) :
    f.1.toAdd.1 leftT = f.1.toAdd.1 leftS := by
  have h := (left_gauge_eq sheared candidates f.1.toAdd
    (leftReference sheared).back (leftReference sheared).back).mp f.2
  change (localReferenceRepair sheared leftRegion candidates).operation leftEdge.2.2 0 +
    f.1.toAdd.1 leftT - f.1.toAdd.1 leftS =
      (localReferenceRepair sheared leftRegion candidates).operation leftEdge.2.2 0 at h
  rw [local_reference_zero,zero_add] at h
  exact sub_eq_zero.mp h

/-- Every arbitrary full V reference arrow retains its original full T relation. -/
theorem right_reference_labels (sheared : Bool) (f : rightReference sheared ⟶ rightReference sheared) :
    f.1.toAdd.1 rightS = linearAction sheared (f.1.toAdd.1 rightT) := by
  have h := (right_gauge_eq sheared candidates f.1.toAdd
    (rightReference sheared).back (rightReference sheared).back).mp f.2
  change (localReferenceRepair sheared rightRegion candidates).operation rightEdge.2.2 0 +
    f.1.toAdd.1 rightS - linearAction sheared (f.1.toAdd.1 rightT) =
      (localReferenceRepair sheared rightRegion candidates).operation rightEdge.2.2 0 at h
  rw [local_reference_zero,zero_add] at h
  exact sub_eq_zero.mp h

end AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalFunctors
