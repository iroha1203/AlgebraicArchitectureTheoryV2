import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonBijectivity
import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceFiringCondition
import Formal.Util.AssertStandardAxioms

/-!
# Nondegenerate firing witness for resolution invariance

This module closes the final positive witness required by
`G-104-aat-resolution-invariance`.  It uses exactly the finite data and
Condition C proof fixed in the two preceding firing modules.

The coarse cocycle is supported on one edge of the directed two-edge cycle.
The sum of its values on the two opposite directed edges vanishes on every
actual coboundary, while the displayed cocycle has unit sum.  This gives a
nonzero class in the actual G-102 quotient.  The fine class is its image under
the actual generated comparison map, and the already proved general
bijectivity theorem makes that image nonzero.  No inverse, chosen preimage, or
cohomology certificate is stored as data.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace ResolutionInvarianceFiringWitness

/-! ## A nonzero class in the actual coarse complex -/

/-- Sum of a coarse one-cochain on the two oppositely directed value-zero edges. -/
def coarseDirectedPeriod (cochain : coarseComplex.C1) : ℚ :=
  cochain (coarseZeroEdgeCoordinate 0).1 +
    cochain (coarseZeroEdgeCoordinate 1).1

/-- Every actual coarse coboundary has zero directed two-edge period. -/
theorem coarseDirectedPeriod_boundary_zero (cochain : coarseComplex.C0) :
    coarseDirectedPeriod (coarseComplex.d0 cochain) = 0 := by
  change
    (cochain
          (coarseSupported.edgeRightCoordinate laws coarse_adequate
            (coarseZeroEdgeCoordinate 0).1) -
        cochain
          (coarseSupported.edgeLeftCoordinate laws coarse_adequate
            (coarseZeroEdgeCoordinate 0).1)) +
      (cochain
          (coarseSupported.edgeRightCoordinate laws coarse_adequate
            (coarseZeroEdgeCoordinate 1).1) -
        cochain
          (coarseSupported.edgeLeftCoordinate laws coarse_adequate
            (coarseZeroEdgeCoordinate 1).1)) = 0
  have hrightLeft :
      coarseSupported.edgeRightCoordinate laws coarse_adequate
          (coarseZeroEdgeCoordinate 0).1 =
        coarseSupported.edgeLeftCoordinate laws coarse_adequate
          (coarseZeroEdgeCoordinate 1).1 := by
    apply CellCoordinate.ext
    · rfl
    · rfl
    · rfl
  have hleftRight :
      coarseSupported.edgeLeftCoordinate laws coarse_adequate
          (coarseZeroEdgeCoordinate 0).1 =
        coarseSupported.edgeRightCoordinate laws coarse_adequate
          (coarseZeroEdgeCoordinate 1).1 := by
    apply CellCoordinate.ext
    · rfl
    · rfl
    · rfl
  rw [hrightLeft, hleftRight]
  ring

/-- The actual coarse one-cochain supported on directed edge zero. -/
def coarseFiringCochain : coarseComplex.C1 := fun coordinate =>
  if coordinate.cell = 0 then 1 else 0

/-- The selected coarse one-cochain is an actual cocycle. -/
theorem coarseFiringCochain_cocycle :
    coarseComplex.d1 coarseFiringCochain = 0 := by
  funext coordinate
  change
    coarseFiringCochain
          (coarseSupported.faceEdge0Coordinate laws coarse_adequate coordinate) -
        coarseFiringCochain
          (coarseSupported.faceEdge1Coordinate laws coarse_adequate coordinate) +
      coarseFiringCochain
        (coarseSupported.faceEdge2Coordinate laws coarse_adequate coordinate) = 0
  simp [coarseFiringCochain, coarseNerve]

/-- The selected coarse cocycle as an element of the actual kernel. -/
def coarseFiringCycle : LinearMap.ker coarseComplex.d1 :=
  ⟨coarseFiringCochain, coarseFiringCochain_cocycle⟩

/-- The actual G-102 quotient class of the selected coarse cocycle. -/
def coarseFiringClass : coarseComplex.H1 :=
  (LinearMap.range coarseComplex.boundaryToCycles).mkQ coarseFiringCycle

/-- The selected coarse cocycle has unit directed period. -/
theorem coarseDirectedPeriod_firing :
    coarseDirectedPeriod coarseFiringCycle.1 = 1 := by
  simp [coarseDirectedPeriod, coarseFiringCycle, coarseFiringCochain]

/-- The actual coarse firing class is nonzero. -/
theorem coarseFiringClass_ne_zero : coarseFiringClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker coarseComplex.d1 =>
      coarseDirectedPeriod cycle.1) hcochain
  change coarseDirectedPeriod (coarseComplex.d0 cochain) =
    coarseDirectedPeriod coarseFiringCycle.1 at hperiod
  rw [coarseDirectedPeriod_boundary_zero, coarseDirectedPeriod_firing] at hperiod
  exact zero_ne_one hperiod

/-! ## The actual canonical image and its nonvanishing -/

/-- The actual generated comparison map on the two firing complexes. -/
def firingComparisonH1Map : coarseComplex.H1 →ₗ[ℚ] fineComplex.H1 :=
  nerveMorphism.generatedComparisonH1Map laws coarse_adequate fine_adequate

/-- Fixed Condition C makes the actual firing comparison map bijective. -/
theorem firingComparisonH1Map_bijective :
    Function.Bijective firingComparisonH1Map := by
  simpa only [firingComparisonH1Map] using
    nerveMorphism.generatedComparisonH1Map_bijective laws coarse_adequate
      fine_adequate fixed_firing_conditionC

/-- The fine firing class is the actual canonical image of the coarse class. -/
def fineFiringClass : fineComplex.H1 :=
  firingComparisonH1Map coarseFiringClass

/-- The fine canonical image is nonzero by actual comparison injectivity. -/
theorem fineFiringClass_ne_zero : fineFiringClass ≠ 0 := by
  intro hzero
  apply coarseFiringClass_ne_zero
  apply firingComparisonH1Map_bijective.1
  simpa only [fineFiringClass, map_zero] using hzero

/--
The actual value-zero coordinate fiber is nontrivial, and declared edge three
realizes its nonempty C1 adjacency.
-/
theorem zero_coordinate_fiber_nontrivial :
    fineZeroChartCoordinate 0 ≠ fineZeroChartCoordinate 1 ∧
      nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
        zeroLabel (coarseZeroChartCoordinate 0) (fineZeroChartCoordinate 0)
          (fineZeroChartCoordinate 1) := by
  constructor
  · intro heq
    exact zero_ne_one (fineZeroChartCoordinate_inj.mp heq)
  · exact zero_fiberAdjacent_zero_one

/-! ## Final fixed firing witness -/

/--
G-104 claim (v): one closed fixture simultaneously fires the proper comparison,
law-derived coefficient distribution, all nonvacuity conditions, fixed
Condition C, nonzero cohomology on both sides, and bijectivity of the actual
canonical comparison map.
-/
theorem fixed_claim_v :
    (laws.Adequate coarseReading ∧
      laws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∃ law left right,
        laws.eval law left ≠ laws.eval law right) ∧
      zeroLabel ≠ oneLabel ∧
      (∃ left right : fineNerve.Chart,
        left ≠ right ∧ chartMap left = 0 ∧ chartMap right = 0) ∧
      (∃ fineFace coarseFace,
        faceMap fineFace = some coarseFace) ∧
      (edgeMap 3 = none ∧
        fineNerve.edgeLeft 3 ≠ fineNerve.edgeRight 3 ∧
        chartMap (fineNerve.edgeLeft 3) =
          chartMap (fineNerve.edgeRight 3)) ∧
      (faceMap 1 = none ∧
        edgeMap (fineNerve.faceEdge0 1) = none ∧
        edgeMap (fineNerve.faceEdge1 1) = none ∧
        edgeMap (fineNerve.faceEdge2 1) = none) ∧
      (edgeMap 2 = some 2 ∧
        coarseNerve.edgeLeft 2 = coarseNerve.edgeRight 2 ∧
        fineNerve.edgeLeft 2 = fineNerve.edgeRight 2) ∧
      fineDegenerateFaceBlockCoordinate.1.cell = 1 ∧
      (∃ coordinate :
          (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
            oneLabel).Chart,
        fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
          oneLabel coordinate = 0) ∧
      (¬ Function.Surjective
        (fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
          oneLabel)) ∧
      ∀ cochain : coarseComplex.C1,
        nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
              (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate = 0 ∧
          fineComplex.d1
              (nerveMorphism.generatedPullback1 laws coarse_adequate
                fine_adequate cochain) fineDegenerateFaceCoordinate = 0 ∧
          nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
              (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate =
            fineComplex.d1
              (nerveMorphism.generatedPullback1 laws coarse_adequate
                fine_adequate cochain) fineDegenerateFaceCoordinate) ∧
      nerveMorphism.ConditionC laws coarse_adequate fine_adequate ∧
      fineZeroChartCoordinate 0 ≠ fineZeroChartCoordinate 1 ∧
      nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate
        zeroLabel (coarseZeroChartCoordinate 0) (fineZeroChartCoordinate 0)
          (fineZeroChartCoordinate 1) ∧
      coarseFiringClass ≠ 0 ∧
      fineFiringClass ≠ 0 ∧
      nerveMorphism.generatedComparisonH1Map laws coarse_adequate fine_adequate
          coarseFiringClass = fineFiringClass ∧
      Function.Bijective
        (nerveMorphism.generatedComparisonH1Map laws coarse_adequate
          fine_adequate) := by
  exact ⟨fixed_firing_input_nonvacuity, fixed_firing_conditionC,
    zero_coordinate_fiber_nontrivial.1, zero_coordinate_fiber_nontrivial.2,
    coarseFiringClass_ne_zero, fineFiringClass_ne_zero, rfl,
    firingComparisonH1Map_bijective⟩

end ResolutionInvarianceFiringWitness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.ResolutionInvarianceFiringWitness
