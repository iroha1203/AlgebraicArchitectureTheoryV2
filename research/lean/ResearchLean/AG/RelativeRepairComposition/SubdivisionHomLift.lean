import ResearchLean.AG.RelativeRepairComposition.SubdivisionGaugeEquations

/-!
# Unique actual label over every original reidentification

The full first-factor correction is evaluated in the actual new-object kernel.
For arbitrary new repairs and an old gauge between their collapses, the unique
fresh label is the difference of their first corrections plus the actual
transported old source label. No label is restricted to an image subgroup.

## Implementation notes

The inverse acts on all morphisms between independently given new repairs. Their first corrections force a unique fresh label. Restricting to the image of the restoration functor would avoid this uniqueness obligation and would not prove full categorical equivalence.
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

/-- The raw full first-factor correction, at the actual fresh-object kernel. -/
noncomputable def firstCorrection (R : Solution (originalTower T chosen F)) :
    (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
  (originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen)

/-- This fresh-object value is exactly the raw original actual-kernel difference on the first factor. -/
theorem firstCorrection_value (R : Solution (originalTower T chosen F)) :
    firstCorrection T chosen F R =
      (originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen) := rfl

/-- Actual gauge action reads the entire fresh label and the same full transported source label. -/
theorem firstCorrection_gauge (b : C0 (originalTower T chosen F).toTower.localCoefficients)
    (R : Solution (originalTower T chosen F)) :
    firstCorrection T chosen F ((originalTower T chosen F).vertexGauge b R) =
      firstCorrection T chosen F R + (b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1))) :=
  vertexGauge_first T chosen F b R

variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
variable (hchosen : chosen ∉ fixed)

omit hchosen in
/-- The uniquely forced full fresh value above an arbitrary old label between arbitrary new repairs. -/
noncomputable def liftFreshValue
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed) :
    (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
  firstCorrection T chosen F Q.1 - firstCorrection T chosen F R.1 + rho1AddEquiv T chosen F (b.1 chosen.1)

omit hchosen in
/-- Extend the complete old label by the unique fresh value dictated by these actual repairs. -/
noncomputable def liftGaugeLabel
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed) :
    supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) :=
  expandAllowedLabel T chosen F vertices fixed b (liftFreshValue T chosen F vertices fixed R Q b)

/-- This full new label restricts to exactly the complete old label. -/
theorem liftGaugeLabel_collapse
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed) :
    collapseAllowedLabel T chosen F vertices fixed hchosen
      (liftGaugeLabel T chosen F vertices fixed R Q b) = b :=
  collapse_expand_allowed T chosen F vertices fixed hchosen b _

omit hchosen in
/-- Every retained original vertex value of the lifted label is its original old value. -/
theorem liftGaugeLabel_old
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed) (v : K.Vertex) :
    (liftGaugeLabel T chosen F vertices fixed R Q b).1 (.inl v) = b.1 v := rfl

omit hchosen in
/-- The actual new-vertex label is exactly the full forced value. -/
theorem liftGaugeLabel_fresh
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed) :
    (liftGaugeLabel T chosen F vertices fixed R Q b).1 (.inr ()) =
      liftFreshValue T chosen F vertices fixed R Q b := rfl

/-- Every old actual reidentification lifts to an actual reidentification of these full new repairs. -/
theorem liftGaugeLabel_gauge
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed)
    (hb : repairGauge T vertices fixed b (collapseSupported T chosen F fixed hchosen R) =
      collapseSupported T chosen F fixed hchosen Q) :
    repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)
      (liftGaugeLabel T chosen F vertices fixed R Q b) R = Q := by
  apply (gauge_equation_iff T chosen F vertices fixed hchosen _ R Q).mpr
  constructor
  · rw [liftGaugeLabel_collapse]
    exact hb
  · change firstCorrection T chosen F Q.1 = firstCorrection T chosen F R.1 +
      ((liftGaugeLabel T chosen F vertices fixed R Q b).1 (.inr ()) -
        rho1AddEquiv T chosen F ((liftGaugeLabel T chosen F vertices fixed R Q b).1 (.inl chosen.1)))
    rw [liftGaugeLabel_fresh,liftGaugeLabel_old]
    change firstCorrection T chosen F Q.1 = firstCorrection T chosen F R.1 +
      ((firstCorrection T chosen F Q.1 - firstCorrection T chosen F R.1 +
        rho1AddEquiv T chosen F (b.1 chosen.1)) - rho1AddEquiv T chosen F (b.1 chosen.1))
    abel

/-- No other full new vertex label lies above this old label between these actual repairs. -/
theorem liftGaugeLabel_unique
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (b : supportedC0 T vertices fixed)
    (c : supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (hc : collapseAllowedLabel T chosen F vertices fixed hchosen c = b)
    (hg : repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) c R = Q) :
    c = liftGaugeLabel T chosen F vertices fixed R Q b := by
  have hfirst := ((gauge_equation_iff T chosen F vertices fixed hchosen c R Q).mp hg).2
  have hs := congrArg (fun d : supportedC0 T vertices fixed => d.1 chosen.1) hc
  change c.1 (.inl chosen.1) = b.1 chosen.1 at hs
  rw [hs] at hfirst
  change firstCorrection T chosen F Q.1 = firstCorrection T chosen F R.1 +
    (c.1 (.inr ()) - rho1AddEquiv T chosen F (b.1 chosen.1)) at hfirst
  have hf : c.1 (.inr ()) = liftFreshValue T chosen F vertices fixed R Q b := by
    calc
      c.1 (.inr ()) =
          (firstCorrection T chosen F R.1 + (c.1 (.inr ()) - rho1AddEquiv T chosen F (b.1 chosen.1))) -
            firstCorrection T chosen F R.1 + rho1AddEquiv T chosen F (b.1 chosen.1) := by abel
      _ = firstCorrection T chosen F Q.1 - firstCorrection T chosen F R.1 +
            rho1AddEquiv T chosen F (b.1 chosen.1) := by rw [← hfirst]
      _ = _ := rfl
  rw [← expand_collapse_allowed T chosen F vertices fixed hchosen c,hc,hf]
  rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
