import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFoldWitnesses

/-!
# Propagation for the lax diagnostic projector

This module fixes the G-117 propagation law on the reviewed finite axis-fold
datum.  It first records the noncommutative recursion for an arbitrary typed
pasting, then connects the two endpoint gauges, the raw cochain action, a
genuine two-face pasting, and the closed double-diamond obstruction on the
fixed nonidentity reselection.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteLaxProjectorAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Arbitrary typed pastings -/

/-- The empty typed pasting has trivial raw defect. -/
@[simp]
theorem pastingRawDefect_nil
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} (path : G.Path source target) :
    pastingRawDefect data reselection (.nil path) = 1 := by
  simp [pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator]

/--
The raw defect of a nonempty typed pasting is the tail defect followed by the
new oriented face defect conjugated by the tail's canonical comparator.
-/
theorem pastingRawDefect_cons
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex}
    {before middle finish : G.Path source target}
    (step : RewriteStep G.toFiniteTransportTwoPresentation before middle)
    (tail : RewritePasting G.toFiniteTransportTwoPresentation middle finish) :
    pastingRawDefect data reselection (.cons step tail) =
      pastingRawDefect data reselection tail *
        (canonicalPastingComparator data reselection tail *
          orientedFaceDefect data reselection step.face *
          (canonicalPastingComparator data reselection tail)⁻¹) := by
  simp only [pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator, orientedFaceDefect,
    orientedFaceAuthoredComparator, orientedFaceCanonicalComparator]
  simp [mul_assoc]

/-! ## Endpoint gauges on the fixed double diamond -/

/-- On a single edge, an arbitrary incremental reselection is its endpoint gauge. -/
theorem pathReselectionTransition_singleEdge_at
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleLiftData G U)
    (current increment : EdgeReselection data)
    {source target : G.Vertex} (edge : G.Edge source target) :
    pathReselectionTransition data current increment
        (.cons edge (.nil target)) =
      increment source target edge := by
  let path : G.Path source target := .cons edge (.nil target)
  letI : (packageProjection U).IsStronglyCocartesian
      (reselectedPathLift data current path).base
      (reselectedPathLift data current path) :=
    reselectedPathLift_isStronglyCocartesian data current path
  apply PackageFiberAut.ext_of_strong_fac
    (reselectedPathLift data current path)
  rw [pathReselectionTransition_fac]
  change reselectedEdgeLift data (increment * current) edge =
    (reselectedEdgeLift data current edge).comp
      (PackageFiberAut.hom (increment source target edge))
  exact reselectedEdgeLift_mul data increment current edge

/-- The left-path endpoint gauge is the left-edge increment. -/
theorem finiteAxisFold_leftTransition
    (current increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    pathReselectionTransition finiteAxisFoldTransportData.lift current increment
        (singleDiskLeftPath PUnit) =
      increment
        (SingleDiskVertex.source : SingleDiskVertex PUnit)
        (SingleDiskVertex.target : SingleDiskVertex PUnit)
        (SingleDiskEdge.left : SingleDiskEdge
          SingleDiskVertex.source SingleDiskVertex.target) := by
  exact pathReselectionTransition_singleEdge_at
    finiteAxisFoldTransportData.lift current increment SingleDiskEdge.left

/-- The right-path endpoint gauge is the right-edge increment. -/
theorem finiteAxisFold_rightTransition
    (current increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    pathReselectionTransition finiteAxisFoldTransportData.lift current increment
        (singleDiskRightPath PUnit) =
      increment
        (SingleDiskVertex.source : SingleDiskVertex PUnit)
        (SingleDiskVertex.target : SingleDiskVertex PUnit)
        (SingleDiskEdge.right : SingleDiskEdge
          SingleDiskVertex.source SingleDiskVertex.target) := by
  exact pathReselectionTransition_singleEdge_at
    finiteAxisFoldTransportData.lift current increment SingleDiskEdge.right

/-- The left-edge increment, presented in the firing cell's endpoint fiber. -/
noncomputable def finiteAxisFoldLeftIncrement
    (increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    PackageFiberAut (finiteAxisFoldTransportData.lift.package
      ((doubleDiamondPresentation PUnit).twoTarget
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit))) := by
  simpa [doubleDiamondPresentation, doubleDiamondTwoPresentation] using
    increment
      (SingleDiskVertex.source : SingleDiskVertex PUnit)
      (SingleDiskVertex.target : SingleDiskVertex PUnit)
      (SingleDiskEdge.left : SingleDiskEdge
        SingleDiskVertex.source SingleDiskVertex.target)

/-- The right-edge increment, presented in the firing cell's endpoint fiber. -/
noncomputable def finiteAxisFoldRightIncrement
    (increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    PackageFiberAut (finiteAxisFoldTransportData.lift.package
      ((doubleDiamondPresentation PUnit).twoTarget
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit))) := by
  simpa [doubleDiamondPresentation, doubleDiamondTwoPresentation] using
    increment
      (SingleDiskVertex.source : SingleDiskVertex PUnit)
      (SingleDiskVertex.target : SingleDiskVertex PUnit)
      (SingleDiskEdge.right : SingleDiskEdge
        SingleDiskVertex.source SingleDiskVertex.target)

/-- The left path formula, stated directly at the fixed firing cell. -/
theorem finiteAxisFold_leftTransition_atFiringCell
    (current increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    pathReselectionTransition finiteAxisFoldTransportData.lift current increment
        ((doubleDiamondPresentation PUnit).twoLeft
          (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit)) =
      finiteAxisFoldLeftIncrement increment := by
  simpa [finiteAxisFoldLeftIncrement, doubleDiamondPresentation,
    doubleDiamondTwoPresentation] using
    finiteAxisFold_leftTransition current increment

/-- The right path formula, stated directly at the fixed firing cell. -/
theorem finiteAxisFold_rightTransition_atFiringCell
    (current increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    pathReselectionTransition finiteAxisFoldTransportData.lift current increment
        ((doubleDiamondPresentation PUnit).twoRight
          (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit)) =
      finiteAxisFoldRightIncrement increment := by
  simpa [finiteAxisFoldRightIncrement, doubleDiamondPresentation,
    doubleDiamondTwoPresentation] using
    finiteAxisFold_rightTransition current increment

/--
The two computed endpoint gauges specialize the general coboundary formula at
the fixed firing cell.
-/
theorem finiteAxisFold_rawDefect_transition
    (current increment : EdgeReselection finiteAxisFoldTransportData.lift) :
    rawDefectCochain finiteAxisFoldTransportData (increment * current)
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) =
      (finiteAxisFoldTransportData.comparator
          (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) *
          finiteAxisFoldLeftIncrement increment *
          (finiteAxisFoldTransportData.comparator
            (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit))⁻¹) *
        rawDefectCochain finiteAxisFoldTransportData current
          (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) *
        (finiteAxisFoldRightIncrement increment)⁻¹ := by
  change rawTwoCellDefect finiteAxisFoldTransportData (increment * current)
      (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) = _
  rw [rawTwoCellDefect_transition,
    finiteAxisFold_leftTransition_atFiringCell,
    finiteAxisFold_rightTransition_atFiringCell]
  rfl

/-! ## The fixed nonidentity action -/

/-- The named second-face reselection is not the identity edge coordinate. -/
theorem finiteAxisFoldSecondFaceReselection_ne_one :
    finiteAxisFoldSecondFaceReselection ≠
      (1 : EdgeReselection finiteAxisFoldTransportData.lift) := by
  intro equality
  have rightEquality := congrArg
    (fun reselection : EdgeReselection finiteAxisFoldTransportData.lift =>
      reselection
        (SingleDiskVertex.source : SingleDiskVertex PUnit)
        (SingleDiskVertex.target : SingleDiskVertex PUnit)
        (SingleDiskEdge.right : SingleDiskEdge
          SingleDiskVertex.source SingleDiskVertex.target)) equality
  exact finiteAxisFoldSwap_ne_one rightEquality

/-- The fixed increment has trivial left endpoint gauge at baseline. -/
theorem finiteAxisFold_fixed_leftTransition :
    pathReselectionTransition finiteAxisFoldTransportData.lift 1
        finiteAxisFoldSecondFaceReselection (singleDiskLeftPath PUnit) = 1 := by
  rw [finiteAxisFold_leftTransition]
  rfl

/-- The fixed increment has the adjacent swap as its right endpoint gauge. -/
theorem finiteAxisFold_fixed_rightTransition :
    pathReselectionTransition finiteAxisFoldTransportData.lift 1
        finiteAxisFoldSecondFaceReselection (singleDiskRightPath PUnit) =
      finiteAxisFoldSwap := by
  rw [finiteAxisFold_rightTransition]
  rfl

@[simp]
theorem finiteAxisFold_fixed_leftIncrement :
    finiteAxisFoldLeftIncrement finiteAxisFoldSecondFaceReselection = 1 := by
  rfl

@[simp]
theorem finiteAxisFold_fixed_rightIncrement :
    finiteAxisFoldRightIncrement finiteAxisFoldSecondFaceReselection =
      finiteAxisFoldSwap := by
  rfl

/-- The endpoint-gauge formula computes the shifted firing-cell defect. -/
theorem finiteAxisFold_fixed_rawDefect_transition :
    rawDefectCochain finiteAxisFoldTransportData
        (finiteAxisFoldSecondFaceReselection * 1)
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) = 1 := by
  rw [finiteAxisFold_rawDefect_transition]
  simp only [finiteAxisFold_fixed_leftIncrement,
    finiteAxisFold_fixed_rightIncrement]
  rw [show finiteAxisFoldTransportData.comparator
    (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) =
      finiteAxisFoldSwap by rfl]
  rw [show rawDefectCochain finiteAxisFoldTransportData 1
    (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) =
      finiteAxisFoldSwap from finiteAxisFold_initialRawDefect_second]
  simp

/-! ## A genuine two-face typed pasting -/

/-- The second double-diamond face used in the backward direction. -/
def doubleDiamondBackwardFace (Marker : Type u)
    (cell : DoubleDiamondTwoCell Marker) :
    WhiskeredFace (doubleDiamondTwoPresentation Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) where
  cell := cell
  incoming := .nil SingleDiskVertex.source
  outgoing := .nil SingleDiskVertex.target
  orientation := .backward

/-- The backward face is a typed step from the right path to the left path. -/
def doubleDiamondBackwardStep (Marker : Type u)
    (cell : DoubleDiamondTwoCell Marker) :
    RewriteStep (doubleDiamondTwoPresentation Marker)
      (singleDiskRightPath Marker) (singleDiskLeftPath Marker) where
  face := doubleDiamondBackwardFace Marker cell
  before_eq := by
    simp [doubleDiamondBackwardFace, WhiskeredFace.before,
      WhiskeredFace.localBefore, doubleDiamondTwoPresentation,
      PresentedPath.append]
  after_eq := by
    simp [doubleDiamondBackwardFace, WhiskeredFace.after,
      WhiskeredFace.localAfter, doubleDiamondTwoPresentation,
      PresentedPath.append]

/-- Forward along the first face, then backward along the second face. -/
def finiteAxisFoldTwoFacePasting :
    RewritePasting (doubleDiamondTwoPresentation PUnit)
      (singleDiskLeftPath PUnit) (singleDiskLeftPath PUnit) :=
  .cons (doubleDiamondStep PUnit DoubleDiamondTwoCell.first)
    (.cons (doubleDiamondBackwardStep PUnit DoubleDiamondTwoCell.second)
      (@RewritePasting.nil (doubleDiamondTwoPresentation PUnit)
        (SingleDiskVertex.source : SingleDiskVertex PUnit)
        (SingleDiskVertex.target : SingleDiskVertex PUnit)
        (singleDiskLeftPath PUnit)))

/-- Empty outgoing whiskering is literal on the fixed lift data. -/
@[simp]
theorem finiteAxisFold_whiskerFiberAut_nil
    (reselection : EdgeReselection finiteAxisFoldTransportData.lift)
    (automorphism : PackageFiberAut
      (finiteAxisFoldTransportData.lift.package
        (SingleDiskVertex.target : SingleDiskVertex PUnit))) :
    whiskerFiberAut finiteAxisFoldTransportData.lift reselection automorphism
        (.nil (SingleDiskVertex.target : SingleDiskVertex PUnit)) =
      automorphism := by
  exact whiskerFiberAut_nil finiteAxisFoldTransportData.lift reselection
    automorphism

@[simp]
theorem finiteAxisFold_authoredComparator_first :
    finiteAxisFoldTransportData.comparator
        (DoubleDiamondTwoCell.first : DoubleDiamondTwoCell PUnit) = 1 := by
  rfl

@[simp]
theorem finiteAxisFold_authoredComparator_second :
    finiteAxisFoldTransportData.comparator
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) =
      finiteAxisFoldSwap := by
  rfl

/-- The adjacent swap is its own inverse. -/
@[simp]
theorem finiteAxisFoldSwap_inv : finiteAxisFoldSwap⁻¹ = finiteAxisFoldSwap := by
  apply Subtype.ext
  apply Iso.ext
  rfl

@[simp]
theorem finiteAxisFold_canonicalComparator_first_baseline :
    canonicalTwoCellComparator finiteAxisFoldTransportData 1
        (DoubleDiamondTwoCell.first : DoubleDiamondTwoCell PUnit) = 1 := by
  rw [finiteAxisFold_canonicalComparator_faces_eq]
  exact finiteAxisFold_canonicalComparator_second_eq_one

@[simp]
theorem finiteAxisFold_canonicalComparator_second_shifted :
    canonicalTwoCellComparator finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) =
      finiteAxisFoldSwap := by
  rw [← finiteAxisFold_secondComparator_eq_canonical]
  rfl

@[simp]
theorem finiteAxisFold_canonicalComparator_first_shifted :
    canonicalTwoCellComparator finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection
        (DoubleDiamondTwoCell.first : DoubleDiamondTwoCell PUnit) =
      finiteAxisFoldSwap := by
  rw [finiteAxisFold_canonicalComparator_faces_eq]
  exact finiteAxisFold_canonicalComparator_second_shifted

/-- The two-face pasting has the adjacent swap as raw defect at baseline. -/
theorem finiteAxisFold_twoFacePasting_baseline :
    pastingRawDefect finiteAxisFoldTransportData 1
        finiteAxisFoldTwoFacePasting = finiteAxisFoldSwap := by
  change pastingRawDefect finiteAxisFoldTransportData 1
    (.cons (doubleDiamondStep PUnit DoubleDiamondTwoCell.first)
      (.cons (doubleDiamondBackwardStep PUnit DoubleDiamondTwoCell.second)
        (@RewritePasting.nil (doubleDiamondTwoPresentation PUnit)
          (SingleDiskVertex.source : SingleDiskVertex PUnit)
          (SingleDiskVertex.target : SingleDiskVertex PUnit)
          (singleDiskLeftPath PUnit)))) = finiteAxisFoldSwap
  rw [pastingRawDefect_cons, pastingRawDefect_cons]
  simp [doubleDiamondBackwardStep,
    doubleDiamondBackwardFace, doubleDiamondStep, doubleDiamondFace,
    pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator,
    orientedFaceDefect, orientedFaceAuthoredComparator,
    orientedFaceCanonicalComparator, orientedFaceComparator,
    authoredComparatorFamily, canonicalComparatorFamily,
    finiteAxisFold_canonicalComparator_second_eq_one]
  rw [finiteAxisFoldSwap_inv]

/-- The fixed nonidentity reselection preserves the two-face raw defect. -/
theorem finiteAxisFold_twoFacePasting_shifted :
    pastingRawDefect finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection finiteAxisFoldTwoFacePasting =
      finiteAxisFoldSwap := by
  change pastingRawDefect finiteAxisFoldTransportData
    finiteAxisFoldSecondFaceReselection
    (.cons (doubleDiamondStep PUnit DoubleDiamondTwoCell.first)
      (.cons (doubleDiamondBackwardStep PUnit DoubleDiamondTwoCell.second)
        (@RewritePasting.nil (doubleDiamondTwoPresentation PUnit)
          (SingleDiskVertex.source : SingleDiskVertex PUnit)
          (SingleDiskVertex.target : SingleDiskVertex PUnit)
          (singleDiskLeftPath PUnit)))) = finiteAxisFoldSwap
  rw [pastingRawDefect_cons, pastingRawDefect_cons]
  simp [doubleDiamondBackwardStep,
    doubleDiamondBackwardFace, doubleDiamondStep, doubleDiamondFace,
    pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator,
    orientedFaceDefect, orientedFaceAuthoredComparator,
    orientedFaceCanonicalComparator, orientedFaceComparator,
    authoredComparatorFamily, canonicalComparatorFamily,
    finiteAxisFold_canonicalComparator_faces_eq]
  rw [finiteAxisFoldSwap_inv]

/-! ## Closed double-diamond obstruction -/

/-- The closed double-diamond obstruction is the swap at baseline. -/
theorem finiteAxisFold_closedObstruction_baseline :
    closedPastingRawObstruction finiteAxisFoldTransportData 1
        DoubleDiamondThreeCell.comparison = finiteAxisFoldSwap := by
  simp [closedPastingRawObstruction, doubleDiamondPresentation,
    doubleDiamondPasting, doubleDiamondStep, doubleDiamondFace,
    pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator, orientedFaceComparator,
    authoredComparatorFamily, canonicalComparatorFamily,
    finiteAxisFold_canonicalComparator_second_eq_one,
    finiteAxisFold_canonicalComparator_faces_eq]
  rw [finiteAxisFoldSwap_inv]

/-- The fixed nonidentity reselection preserves the closed obstruction. -/
theorem finiteAxisFold_closedObstruction_shifted :
    closedPastingRawObstruction finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection
        DoubleDiamondThreeCell.comparison = finiteAxisFoldSwap := by
  simp [closedPastingRawObstruction, doubleDiamondPresentation,
    doubleDiamondPasting, doubleDiamondStep, doubleDiamondFace,
    pastingRawDefect, authoredPastingComparator,
    canonicalPastingComparator, pastingComparator, orientedFaceComparator,
    authoredComparatorFamily, canonicalComparatorFamily,
    finiteAxisFold_canonicalComparator_faces_eq]
  rw [finiteAxisFoldSwap_inv]

/-!
## Fixed-fixture propagation decision

The following theorem keeps the authored input equality in the proof term and
collects the nonidentity action, actual cochain change, both endpoint gauges,
the raw transition, the length-two pasting decision, and the closed comparison
decision.  Thus the result is not a specialization of one predecessor lemma.
-/

theorem finiteAxisFold_propagation_decision :
    finiteAxisFoldBCDatumSquare.toTransportData =
        finiteAxisFoldTransportData ∧
    finiteAxisFoldSecondFaceReselection ≠
        (1 : EdgeReselection finiteAxisFoldTransportData.lift) ∧
    rawDefectCochain finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection ≠
      initialRawDefectCochain finiteAxisFoldTransportData ∧
    pathReselectionTransition finiteAxisFoldTransportData.lift 1
        finiteAxisFoldSecondFaceReselection (singleDiskLeftPath PUnit) = 1 ∧
    pathReselectionTransition finiteAxisFoldTransportData.lift 1
        finiteAxisFoldSecondFaceReselection (singleDiskRightPath PUnit) =
      finiteAxisFoldSwap ∧
    rawDefectCochain finiteAxisFoldTransportData
        (finiteAxisFoldSecondFaceReselection * 1)
        (DoubleDiamondTwoCell.second : DoubleDiamondTwoCell PUnit) = 1 ∧
    pastingRawDefect finiteAxisFoldTransportData 1
        finiteAxisFoldTwoFacePasting = finiteAxisFoldSwap ∧
    pastingRawDefect finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection finiteAxisFoldTwoFacePasting =
      finiteAxisFoldSwap ∧
    closedPastingRawObstruction finiteAxisFoldTransportData 1
        DoubleDiamondThreeCell.comparison = finiteAxisFoldSwap ∧
    closedPastingRawObstruction finiteAxisFoldTransportData
        finiteAxisFoldSecondFaceReselection
        DoubleDiamondThreeCell.comparison = finiteAxisFoldSwap := by
  exact ⟨finiteAxisFold_toTransportData,
    finiteAxisFoldSecondFaceReselection_ne_one,
    finiteAxisFold_shiftedCochain_ne_initial,
    finiteAxisFold_fixed_leftTransition,
    finiteAxisFold_fixed_rightTransition,
    finiteAxisFold_fixed_rawDefect_transition,
    finiteAxisFold_twoFacePasting_baseline,
    finiteAxisFold_twoFacePasting_shifted,
    finiteAxisFold_closedObstruction_baseline,
    finiteAxisFold_closedObstruction_shifted⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
