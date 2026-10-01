import ResearchLean.AG.RelativeRepairComposition.SubdivisionHomLift

/-!
# Zero first-factor restoration and its entire actual vertex-label section

The canonical restored object has zero first correction. Its original label
extends with the full actual first-factor transport of its old source value,
which preserves zero first correction under every old gauge.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))

/-- Every restored actual supported solution has exactly its supplied full first-factor correction. -/
theorem firstCorrection_expandSupported (R : SupportedRepair T fixed)
    (r : Additive (Kernel p q F.middle)) :
    firstCorrection T chosen F (expandSupported T chosen F fixed R r).1 = r := by
  rw [firstCorrection_value,expandSupported_correction,expandCorrection_first]

/-- Extend every full old allowed label to the section preserving zero first-factor correction. -/
noncomputable def zeroSectionLabel : supportedC0 T vertices fixed →+
    supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) where
  toFun b := expandAllowedLabel T chosen F vertices fixed b (rho1AddEquiv T chosen F (b.1 chosen.1))
  map_zero' := by
    apply Subtype.ext
    funext v
    cases v with
    | inl _ => rfl
    | inr u =>
      cases u
      change rho1AddEquiv T chosen F 0 = 0
      exact map_zero _
  map_add' b c := by
    apply Subtype.ext
    funext v
    cases v with
    | inl _ => rfl
    | inr u =>
      cases u
      change rho1AddEquiv T chosen F (b.1 chosen.1 + c.1 chosen.1) =
        rho1AddEquiv T chosen F (b.1 chosen.1) + rho1AddEquiv T chosen F (c.1 chosen.1)
      exact map_add _ _ _

/-- Every old vertex label of the section is exactly its original full value. -/
theorem zeroSectionLabel_old (b : supportedC0 T vertices fixed) (v : K.Vertex) :
    (zeroSectionLabel T chosen F vertices fixed b).1 (.inl v) = b.1 v := rfl

/-- The section's new-vertex value is the full actual transported old source label. -/
theorem zeroSectionLabel_fresh (b : supportedC0 T vertices fixed) :
    (zeroSectionLabel T chosen F vertices fixed b).1 (.inr ()) = rho1AddEquiv T chosen F (b.1 chosen.1) := rfl

variable (hchosen : chosen ∉ fixed)

/-- Restriction of the section retains the complete original allowed label. -/
theorem collapse_zeroSectionLabel (b : supportedC0 T vertices fixed) :
    collapseAllowedLabel T chosen F vertices fixed hchosen (zeroSectionLabel T chosen F vertices fixed b) = b :=
  collapse_expand_allowed T chosen F vertices fixed hchosen b _

include hchosen in
/-- Every actual old gauge is an actual new gauge between the canonically restored actual repairs. -/
theorem zeroSectionLabel_gauge (b : supportedC0 T vertices fixed) (R Q : SupportedRepair T fixed)
    (hb : repairGauge T vertices fixed b R = Q) :
    repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)
      (zeroSectionLabel T chosen F vertices fixed b)
      (expandSupported T chosen F fixed R 0) = expandSupported T chosen F fixed Q 0 := by
  apply (gauge_equation_iff T chosen F vertices fixed hchosen _ _ _).mpr
  constructor
  · rw [collapse_zeroSectionLabel,collapse_expand_supported,collapse_expand_supported]
    exact hb
  · change firstCorrection T chosen F (expandSupported T chosen F fixed Q 0).1 =
      firstCorrection T chosen F (expandSupported T chosen F fixed R 0).1 +
        ((zeroSectionLabel T chosen F vertices fixed b).1 (.inr ()) -
          rho1AddEquiv T chosen F ((zeroSectionLabel T chosen F vertices fixed b).1 (.inl chosen.1)))
    rw [firstCorrection_expandSupported,firstCorrection_expandSupported,
      zeroSectionLabel_fresh,zeroSectionLabel_old]
    simp only [sub_self,add_zero]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
