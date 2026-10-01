import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedLabels

/-!
# Collapse of actual gauge actions and the full fresh-label equation

Every original label value is retained. The first-factor correction changes by
the fresh label minus the actual transported old source label. These two facts
characterize the entire new gauge equation between arbitrary actual repairs.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The recovered full actual-kernel correction uniquely determines every original actual choice. -/
theorem solutionCorrection_injective : Function.Injective T.solutionCorrection := by
  intro R Q h
  apply Solution.ext
  intro i j e
  rw [← T.correctionChoice_solutionCorrection R e,
    ← T.correctionChoice_solutionCorrection Q e,h]

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)

/-- Restricting the full actual label commutes with collapse of the actual vertex reidentification. -/
theorem collapseSolution_gauge
    (b : C0 (originalTower T chosen F).toTower.localCoefficients)
    (R : Solution (originalTower T chosen F)) :
    collapseSolution T chosen F ((originalTower T chosen F).vertexGauge b R) =
      T.vertexGauge (collapseVertex T chosen F b) (collapseSolution T chosen F R) := by
  apply solutionCorrection_injective T
  rw [collapseSolution_correction,(originalTower T chosen F).vertexGauge_correction,
    collapseCorrection_add,collapse_d0,T.vertexGauge_correction,collapseSolution_correction]

/-- The full first-factor correction reads every actual fresh and original source label in its actual gauge formula. -/
theorem vertexGauge_first
    (b : C0 (originalTower T chosen F).toTower.localCoefficients)
    (R : Solution (originalTower T chosen F)) :
    (originalTower T chosen F).solutionCorrection ((originalTower T chosen F).vertexGauge b R)
      (firstEdgeName K chosen) =
    (let a : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
      (originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen);
      a + (b (.inr ()) - rho1AddEquiv T chosen F (b (.inl chosen.1)))) := by
  rw [(originalTower T chosen F).vertexGauge_correction]
  let a : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
    (originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen)
  change a +
    (b (.inr ()) - (originalTower T chosen F).toTower.localCoefficients.edge
      (firstEdge K chosen) (b (.inl chosen.1))) = _
  rw [coefficient_edge_first]
  rfl

variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
variable (hchosen : chosen ∉ fixed)

/-- Collapse of actual supported gauges retains the full original supported gauge and all its old labels. -/
theorem collapseSupported_gauge
    (b : supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    collapseSupported T chosen F fixed hchosen
      (repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) b R) =
    repairGauge T vertices fixed (collapseAllowedLabel T chosen F vertices fixed hchosen b)
      (collapseSupported T chosen F fixed hchosen R) :=
  Subtype.ext (collapseSolution_gauge T chosen F b.1 R.1)

/-- A full new actual gauge equation is precisely the old actual equation and its single forced full fresh value. -/
theorem gauge_equation_iff
    (b : supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (R Q : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) b R = Q ↔
      repairGauge T vertices fixed (collapseAllowedLabel T chosen F vertices fixed hchosen b)
          (collapseSupported T chosen F fixed hchosen R) = collapseSupported T chosen F fixed hchosen Q ∧
      (originalTower T chosen F).solutionCorrection Q.1 (firstEdgeName K chosen) =
        (let a : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
          (originalTower T chosen F).solutionCorrection R.1 (firstEdgeName K chosen);
          a + (b.1 (.inr ()) - rho1AddEquiv T chosen F (b.1 (.inl chosen.1)))) := by
  constructor
  · intro h
    constructor
    · exact (collapseSupported_gauge T chosen F vertices fixed hchosen b R).symm.trans
        (congrArg (collapseSupported T chosen F fixed hchosen) h)
    · have hv := congrArg (fun U => (originalTower T chosen F).solutionCorrection U.1
        (firstEdgeName K chosen)) h
      exact hv.symm.trans (vertexGauge_first T chosen F b.1 R.1)
  · rintro ⟨hc,hfirst⟩
    apply (supportedSolutionEquiv T chosen F fixed hchosen).injective
    apply Prod.ext
    · change collapseSupported T chosen F fixed hchosen
        (repairGauge (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) b R) = _
      exact (collapseSupported_gauge T chosen F vertices fixed hchosen b R).trans hc
    · change (originalTower T chosen F).solutionCorrection
        ((originalTower T chosen F).vertexGauge b.1 R.1) (firstEdgeName K chosen) = _
      exact (vertexGauge_first T chosen F b.1 R.1).trans hfirst.symm

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
