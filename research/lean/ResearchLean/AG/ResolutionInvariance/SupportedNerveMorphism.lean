import ResearchLean.AG.ResolutionInvariance.LawGeneratedComplex
import Formal.Util.AssertStandardAxioms

/-!
# Supported nerve morphisms for resolution invariance

This module fixes the comparison-geometry input required by
`G-104-aat-resolution-invariance`.  A morphism sends fine charts to coarse
charts and may declare an edge or face degenerate by returning `none`.
Degenerate edges lie in one chart fiber.  Degenerate faces are hereditary:
all three boundary edges must already be declared degenerate.

Only chart support compatibility with the canonical comparison factor is an
input field.  Compatibility of mapped edge and face supports is derived from
the K1 intersection definitions in `LawGeneratedComplex`; it is not supplied
as additional comparison data.  No cochain map, commutation law, cohomology
map, or isomorphism is part of this structure.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology

universe u

variable {Source : Type u}

/-! ## Hereditary comparison geometry -/

/--
A partial incidence morphism between K1-supported nerves over a coarse/fine
reading comparison.  Returning `none` declares a cell degenerate.  The three
`face_none_edge*` fields make that declaration hereditary from faces to their
boundary edges.
-/
structure TargetSupportedNerveMorphism
    (coarseReading fineReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (coarse : TargetSupportedNerve coarseReading)
    (fine : TargetSupportedNerve fineReading) where
  chartMap : fine.nerve.Chart → coarse.nerve.Chart
  edgeMap : fine.nerve.EdgeComponent → Option coarse.nerve.EdgeComponent
  faceMap : fine.nerve.FaceComponent → Option coarse.nerve.FaceComponent
  edge_some_left : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fine.nerve.edgeLeft fineEdge) =
        coarse.nerve.edgeLeft coarseEdge
  edge_some_right : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fine.nerve.edgeRight fineEdge) =
        coarse.nerve.edgeRight coarseEdge
  edge_none_fiber : ∀ fineEdge,
    edgeMap fineEdge = none →
      chartMap (fine.nerve.edgeLeft fineEdge) =
        chartMap (fine.nerve.edgeRight fineEdge)
  face_some_edge0 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.nerve.faceEdge0 fineFace) =
        some (coarse.nerve.faceEdge0 coarseFace)
  face_some_edge1 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.nerve.faceEdge1 fineFace) =
        some (coarse.nerve.faceEdge1 coarseFace)
  face_some_edge2 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.nerve.faceEdge2 fineFace) =
        some (coarse.nerve.faceEdge2 coarseFace)
  face_none_edge0 : ∀ fineFace,
    faceMap fineFace = none →
      edgeMap (fine.nerve.faceEdge0 fineFace) = none
  face_none_edge1 : ∀ fineFace,
    faceMap fineFace = none →
      edgeMap (fine.nerve.faceEdge1 fineFace) = none
  face_none_edge2 : ∀ fineFace,
    faceMap fineFace = none →
      edgeMap (fine.nerve.faceEdge2 fineFace) = none
  chartSupport_compatible : ∀ fineChart fineTarget,
    fineTarget ∈ fine.chartSupport fineChart →
      comparisonFactor coarseReading fineReading hcoarser fineTarget ∈
        coarse.chartSupport (chartMap fineChart)

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-! ## K1-derived support transport -/

/--
Mapped edge support compatibility follows from endpoint incidence, chart
support compatibility, and the K1 endpoint intersection.
-/
theorem edgeSupport_compatible
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {fineEdge : fine.nerve.EdgeComponent}
    {coarseEdge : coarse.nerve.EdgeComponent}
    (hmap : M.edgeMap fineEdge = some coarseEdge)
    {fineTarget : fineReading.Target}
    (htarget : fineTarget ∈ fine.edgeSupport fineEdge) :
    comparisonFactor coarseReading fineReading hcoarser fineTarget ∈
      coarse.edgeSupport coarseEdge := by
  rw [fine.mem_edgeSupport_iff] at htarget
  rw [coarse.mem_edgeSupport_iff]
  constructor
  · rw [← M.edge_some_left fineEdge coarseEdge hmap]
    exact M.chartSupport_compatible _ _ htarget.1
  · rw [← M.edge_some_right fineEdge coarseEdge hmap]
    exact M.chartSupport_compatible _ _ htarget.2

/--
Mapped face support compatibility follows from boundary incidence and the K1
intersection of the three already-derived edge supports.
-/
theorem faceSupport_compatible
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    {fineFace : fine.nerve.FaceComponent}
    {coarseFace : coarse.nerve.FaceComponent}
    (hmap : M.faceMap fineFace = some coarseFace)
    {fineTarget : fineReading.Target}
    (htarget : fineTarget ∈ fine.faceSupport fineFace) :
    comparisonFactor coarseReading fineReading hcoarser fineTarget ∈
      coarse.faceSupport coarseFace := by
  rw [fine.mem_faceSupport_iff] at htarget
  rw [coarse.mem_faceSupport_iff]
  exact ⟨
    M.edgeSupport_compatible
      (M.face_some_edge0 fineFace coarseFace hmap) htarget.1,
    M.edgeSupport_compatible
      (M.face_some_edge1 fineFace coarseFace hmap) htarget.2.1,
    M.edgeSupport_compatible
      (M.face_some_edge2 fineFace coarseFace hmap) htarget.2.2⟩

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
