import ResearchLean.AG.ObstructionDiagnosticBridge.IntegralReflection
import ResearchLean.AG.ObstructionDiagnosticBridge.SpecifiedAffineObstruction
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Formal.Util.AssertStandardAxioms

/-!
# Reflection of specified diagnostic zero classes

This module lifts the integral-flooring kernel to the actual Cech complex used
by G-125.  Full chart support supplies one canonical diagnostic coordinate for
every chart and source-generated Law-value label.  If a specified diagnostic
class vanishes, its rational degree-zero witness is read at those coordinates
and floored blockwise.  The resulting integral presentation cochain has the
original actual mismatch as its coboundary.

The reflection premise is the structural generator condition `R_q`; neither
H1 injectivity nor a zero-class certificate is stored in the input data.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution Cohomology ResolutionInvariance TwoPhase

universe u

namespace GeneratorPresentation

variable {Source : Type u} [Fintype Source]
variable {q : Reading Source} {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent]

/-- Every reading target is visible on every selected diagnostic chart. -/
def FullChartSupport (D : TargetSupportedNerve q) : Prop :=
  ∀ chart target, target ∈ D.chartSupport chart

namespace FullChartSupportFixtures

/-- A two-point reading used to show that full chart support is a genuine premise. -/
abbrev partialReading : Reading Bool where
  Target := Bool
  read := id
  surjective := Function.surjective_id

/-- A one-chart nerve whose support can be chosen strictly smaller than the target. -/
abbrev partialNerve : CoverNerve where
  Chart := PUnit
  EdgeComponent := Empty
  FaceComponent := Empty
  edgeLeft := isEmptyElim
  edgeRight := isEmptyElim
  faceEdge0 := isEmptyElim
  faceEdge1 := isEmptyElim
  faceEdge2 := isEmptyElim
  edgeOverlapComponent := isEmptyElim
  faceTripleOverlapComponent := isEmptyElim
  edgeOverlapComponent_holds := isEmptyElim
  faceTripleOverlapComponent_holds := isEmptyElim

/-- A supported nerve that sees `false` but omits `true`. -/
def partialSupportedNerve : TargetSupportedNerve partialReading where
  nerve := partialNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport _ := {false}
  chartSupport_nonempty _ := ⟨false, by simp⟩
  faceEdge0_left := isEmptyElim
  faceEdge0_right := isEmptyElim
  faceEdge1_right := isEmptyElim

/-- Full chart support fails when an actual target value is omitted. -/
theorem partial_not_full : ¬ FullChartSupport partialSupportedNerve := by
  intro hfull
  have htrue := hfull PUnit.unit true
  simp [partialSupportedNerve] at htrue

end FullChartSupportFixtures

namespace FullChartSupport

variable (hfull : FullChartSupport D)
variable (hadequate : laws.Adequate q)

/-- Canonical chart coordinate carrying a requested source-generated label. -/
def chartCoordinate (chart : D.nerve.Chart) (label : LawValueLabel laws) :
    D.ChartCoordinate laws hadequate := by
  let source := Classical.choose label.generated
  have hsource := Classical.choose_spec label.generated
  exact ⟨chart, label.law, label.value,
    q.read source, hfull chart (q.read source),
      (lawDescend_commutes laws q hadequate label.law source).trans hsource⟩

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- The canonical chart coordinate carries exactly the requested label. -/
@[simp]
theorem chartCoordinate_lawValueLabel
    (chart : D.nerve.Chart) (label : LawValueLabel laws) :
    (FullChartSupport.chartCoordinate hfull hadequate chart label).lawValueLabel laws q hadequate
        D.nerve.Chart D.chartSupport = label := by
  apply LawValueLabel.ext laws
  · rfl
  · rfl

/-- Canonical edge coordinate carrying a requested source-generated label. -/
def edgeCoordinate (edge : D.nerve.EdgeComponent) (label : LawValueLabel laws) :
    D.EdgeCoordinate laws hadequate := by
  let source := Classical.choose label.generated
  have hsource := Classical.choose_spec label.generated
  refine ⟨edge, label.law, label.value, q.read source, ?_, ?_⟩
  · exact (D.mem_edgeSupport_iff edge (q.read source)).2
      ⟨hfull _ _, hfull _ _⟩
  · exact (lawDescend_commutes laws q hadequate label.law source).trans hsource

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- The canonical edge coordinate carries exactly the requested label. -/
@[simp]
theorem edgeCoordinate_lawValueLabel
    (edge : D.nerve.EdgeComponent) (label : LawValueLabel laws) :
    (FullChartSupport.edgeCoordinate hfull hadequate edge label).lawValueLabel laws q hadequate
        D.nerve.EdgeComponent D.edgeSupport = label := by
  apply LawValueLabel.ext laws
  · rfl
  · rfl

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- The left endpoint of the canonical edge coordinate is the canonical left chart coordinate. -/
theorem edgeLeftCoordinate_eq
    (edge : D.nerve.EdgeComponent) (label : LawValueLabel laws) :
    D.edgeLeftCoordinate laws hadequate
        (FullChartSupport.edgeCoordinate hfull hadequate edge label) =
      FullChartSupport.chartCoordinate hfull hadequate
        (D.nerve.edgeLeft edge) label := by
  apply CellCoordinate.ext
  · rfl
  · rfl
  · exact HEq.rfl

omit [Fintype Source] [IsEmpty D.nerve.FaceComponent] in
/-- The right endpoint of the canonical edge coordinate is the canonical right chart coordinate. -/
theorem edgeRightCoordinate_eq
    (edge : D.nerve.EdgeComponent) (label : LawValueLabel laws) :
    D.edgeRightCoordinate laws hadequate
        (FullChartSupport.edgeCoordinate hfull hadequate edge label) =
      FullChartSupport.chartCoordinate hfull hadequate
        (D.nerve.edgeRight edge) label := by
  apply CellCoordinate.ext
  · rfl
  · rfl
  · exact HEq.rfl

end FullChartSupport

namespace ActualCechAffineLocalData

variable {P : GeneratorPresentation laws} {C : FaceEmptyAATCechCover D G}

/-- Read a rational diagnostic zero-cochain by chart and generated label. -/
def rationalChartWitness (hfull : FullChartSupport D)
    (hadequate : laws.Adequate q)
    (b : D.ChartCoordinate laws hadequate → ℚ) :
    D.nerve.Chart → LawValueLabel laws → ℚ :=
  fun chart label => b
    (FullChartSupport.chartCoordinate hfull hadequate chart label)

/-- The actual mismatch in normalized presentation coordinates. -/
def normalizedActualMismatch (x : ActualCechAffineLocalData P C) :
    P.PresentationCochain1 D :=
  P.faceEmptyCechCochain1Equiv C x.actualMismatch

/-- Integral block coefficient of the normalized actual mismatch. -/
def normalizedActualBlockCoefficient (x : ActualCechAffineLocalData P C)
    (edge : D.nerve.EdgeComponent) (block : P.Block) : ℤ :=
  FreeAbelianGroup.coeff block
    (P.presentationToBlocks (x.normalizedActualMismatch edge))

/-- Floor a diagnostic zero-cochain and return an actual degree-zero correction. -/
def integralCorrection (hfull : FullChartSupport D) (hadequate : laws.Adequate q)
    (b : D.ChartCoordinate laws hadequate → ℚ) :
    (P.faceEmptyCechComplex C).Cn 0 :=
  (P.faceEmptyCechCochain0Equiv C).symm fun chart =>
    P.blocksToPresentation <|
      (FreeAbelianGroup.equivFinsupp P.Block).symm <|
        Finsupp.equivFunOnFinite.symm <|
          P.blockFloorCorrection (rationalChartWitness hfull hadequate b) chart

/-- The actual correction normalizes to the floored presentation cochain. -/
@[simp]
theorem faceEmptyCechCochain0Equiv_integralCorrection
    (hfull : FullChartSupport D) (hadequate : laws.Adequate q)
    (b : D.ChartCoordinate laws hadequate → ℚ) :
    P.faceEmptyCechCochain0Equiv C (integralCorrection (P := P) (C := C)
      hfull hadequate b) =
      fun chart => P.blocksToPresentation
        ((FreeAbelianGroup.equivFinsupp P.Block).symm
          (Finsupp.equivFunOnFinite.symm
            (P.blockFloorCorrection (rationalChartWitness hfull hadequate b) chart))) :=
  (P.faceEmptyCechCochain0Equiv C).apply_symm_apply _

omit [Fintype Source] in
/-- A diagnostic boundary witness has the exact integral edge differences needed for flooring. -/
theorem rational_chart_witness_edge_difference
    (x : ActualCechAffineLocalData P C)
    (hfull : FullChartSupport D) (hadequate : laws.Adequate q)
    (hReflection : P.ReflectionCondition)
    (b : D.ChartCoordinate laws hadequate → ℚ)
    (hboundary : x.diagnosticMismatch hadequate =
      D.lawGeneratedD0 laws hadequate b)
    (edge : D.nerve.EdgeComponent) (block : P.Block) :
    rationalChartWitness hfull hadequate b (D.nerve.edgeRight edge)
          (P.blockLabel block) -
        rationalChartWitness hfull hadequate b (D.nerve.edgeLeft edge)
          (P.blockLabel block) =
      (x.normalizedActualBlockCoefficient edge block : ℚ) := by
  let coordinate := FullChartSupport.edgeCoordinate hfull hadequate edge
    (P.blockLabel block)
  have hvalue := congrFun hboundary coordinate
  rw [D.lawGeneratedD0_apply] at hvalue
  rw [FullChartSupport.edgeRightCoordinate_eq hfull hadequate edge
      (P.blockLabel block),
    FullChartSupport.edgeLeftCoordinate_eq hfull hadequate edge
      (P.blockLabel block)] at hvalue
  rw [← x.actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch hadequate]
    at hvalue
  change
    P.coefficientComparison (x.normalizedActualMismatch edge)
        (P.blockLabel block) = _ at hvalue
  rw [coefficientComparison, AddMonoidHom.comp_apply,
    P.blockToLawCoefficients_apply_blockLabel hReflection] at hvalue
  exact hvalue.symm

/-- The floored actual correction has the specified actual mismatch as its coboundary. -/
theorem actual_mismatch_eq_d_integralCorrection
    (x : ActualCechAffineLocalData P C)
    (hfull : FullChartSupport D) (hadequate : laws.Adequate q)
    (hReflection : P.ReflectionCondition)
    (b : D.ChartCoordinate laws hadequate → ℚ)
    (hboundary : x.diagnosticMismatch hadequate =
      D.lawGeneratedD0 laws hadequate b) :
    x.actualMismatch =
      (P.faceEmptyCechComplex C).d 0
        (integralCorrection (P := P) (C := C) hfull hadequate b) := by
  let correctionBlocks : D.nerve.Chart → FreeAbelianGroup P.Block :=
    fun chart =>
      (FreeAbelianGroup.equivFinsupp P.Block).symm
        (Finsupp.equivFunOnFinite.symm
          (P.blockFloorCorrection (rationalChartWitness hfull hadequate b) chart))
  have hnormalizes :
      P.faceEmptyCechCochain0Equiv C
          (integralCorrection (P := P) (C := C) hfull hadequate b) =
        fun chart => P.blocksToPresentation (correctionBlocks chart) := by
    exact faceEmptyCechCochain0Equiv_integralCorrection
      (P := P) (C := C) hfull hadequate b
  apply (P.faceEmptyCechCochain1Equiv C).injective
  rw [P.faceEmptyCech_d0_normalizes]
  change x.normalizedActualMismatch =
    P.presentationD0 D
      (P.faceEmptyCechCochain0Equiv C
        (integralCorrection (P := P) (C := C) hfull hadequate b))
  rw [hnormalizes]
  apply funext
  intro edge
  change x.normalizedActualMismatch edge =
    P.blocksToPresentation (correctionBlocks (D.nerve.edgeRight edge)) -
      P.blocksToPresentation (correctionBlocks (D.nerve.edgeLeft edge))
  apply P.presentationGroupEquivBlocks.injective
  change P.presentationToBlocks (x.normalizedActualMismatch edge) =
    P.presentationToBlocks
      (P.blocksToPresentation (correctionBlocks (D.nerve.edgeRight edge)) -
        P.blocksToPresentation (correctionBlocks (D.nerve.edgeLeft edge)))
  rw [map_sub]
  have hright :
      P.presentationToBlocks
          (P.blocksToPresentation (correctionBlocks (D.nerve.edgeRight edge))) =
        correctionBlocks (D.nerve.edgeRight edge) := by
    exact congrArg (fun f => f (correctionBlocks (D.nerve.edgeRight edge)))
      P.presentationToBlocks_comp_blocksToPresentation
  have hleft :
      P.presentationToBlocks
          (P.blocksToPresentation (correctionBlocks (D.nerve.edgeLeft edge))) =
        correctionBlocks (D.nerve.edgeLeft edge) := by
    exact congrArg (fun f => f (correctionBlocks (D.nerve.edgeLeft edge)))
      P.presentationToBlocks_comp_blocksToPresentation
  rw [hright, hleft]
  apply (FreeAbelianGroup.equivFinsupp P.Block).injective
  ext block
  rw [map_sub]
  simp only [Finsupp.sub_apply]
  simp only [correctionBlocks, AddEquiv.apply_symm_apply]
  change x.normalizedActualBlockCoefficient edge block =
    P.blockFloorCorrection (rationalChartWitness hfull hadequate b)
        (D.nerve.edgeRight edge) block -
      P.blockFloorCorrection (rationalChartWitness hfull hadequate b)
        (D.nerve.edgeLeft edge) block
  exact (P.blockFloorCorrection_edgeDifference D.nerve.edgeLeft D.nerve.edgeRight
    x.normalizedActualBlockCoefficient
    (rationalChartWitness hfull hadequate b)
    (x.rational_chart_witness_edge_difference hfull hadequate hReflection b hboundary)
    edge block).symm

/-- G-125(B2): diagnostic vanishing reflects to the specified actual obstruction class. -/
theorem actual_class_eq_zero_of_diagnostic_class_eq_zero
    (x : ActualCechAffineLocalData P C)
    (hfull : FullChartSupport D) (hadequate : laws.Adequate q)
    (hReflection : P.ReflectionCondition)
    (hzero : x.diagnosticClass hadequate = 0) :
    x.actualClass = 0 := by
  rw [actualClass, (P.faceEmptyCechComplex C).additiveH1Class_eq_zero_iff]
  have hrange := (Submodule.Quotient.mk_eq_zero _).1 hzero
  rcases hrange with ⟨b, hb⟩
  refine ⟨integralCorrection (P := P) (C := C) hfull hadequate b, ?_⟩
  apply x.actual_mismatch_eq_d_integralCorrection hfull hadequate hReflection b
  exact (congrArg Subtype.val hb).symm

/-- G-125(B2): under structural reflection, specified actual and diagnostic classes vanish together. -/
theorem diagnostic_class_eq_zero_iff_actual_class_eq_zero
    (x : ActualCechAffineLocalData P C)
    (hfull : FullChartSupport D) (hadequate : laws.Adequate q)
    (hReflection : P.ReflectionCondition) :
    x.diagnosticClass hadequate = 0 ↔ x.actualClass = 0 :=
  ⟨x.actual_class_eq_zero_of_diagnostic_class_eq_zero
      hfull hadequate hReflection,
    x.diagnostic_class_eq_zero_of_actual_class_eq_zero hadequate⟩

end ActualCechAffineLocalData

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.FullChartSupport
#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData
#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.FullChartSupportFixtures

end GeneratorPresentation
end AAT.AG.ObstructionDiagnosticBridge
