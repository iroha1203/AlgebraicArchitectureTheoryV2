import ResearchLean.AG.VisibleCycleReflection.ActualCover
import ResearchLean.AG.VisibleCycleReflection.IntegralLabelCoordinates
import ResearchLean.AG.VisibleCycleReflection.VisibleCoordinates
import ResearchLean.AG.ObstructionDiagnosticBridge.ExistingObstructionBridge
import Formal.Util.AssertStandardAxioms

/-! # Actual Cech cochains in integral graph coordinates and visible Law coordinates -/
noncomputable section
namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge Cohomology
universe u
variable {Source : Type u} [Fintype Source] {laws : FiniteLawFamily Source} {q : Reading Source}

/-- A: the ordinary graph differential with integral label coefficients. -/
def integralGraphD0 (N : CoverNerve.{u}) (Label : Type u) :
    (N.Chart → Label → ℤ) →+ (N.EdgeComponent → Label → ℤ) where
  toFun c edge label := c (N.edgeRight edge) label - c (N.edgeLeft edge) label
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

/-- Public evaluation of the integer graph differential. -/
@[simp]
theorem integralGraphD0_apply (N : CoverNerve.{u}) (Label : Type u)
    (c : N.Chart → Label → ℤ) (edge : N.EdgeComponent) (label : Label) :
    integralGraphD0 N Label c edge label =
      c (N.edgeRight edge) label - c (N.edgeLeft edge) label := rfl

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent]
variable (P : GeneratorPresentation laws) (C : GeneratorPresentation.FaceEmptyAATCechCover D G)

/-- A: actual chart sections identified with all integral label coordinates. -/
def actualIntegralCochain0Equiv (hR : P.ReflectionCondition) :
    (P.faceEmptyCechComplex C).Cn 0 ≃+ (D.nerve.Chart → LawValueLabel laws → ℤ) :=
  (P.faceEmptyCechCochain0Equiv C).trans
    (AddEquiv.piCongrRight (fun _ => integralLabelEquiv P hR))

/-- A: actual overlap sections identified with all integral label coordinates. -/
def actualIntegralCochain1Equiv (hR : P.ReflectionCondition) :
    (P.faceEmptyCechComplex C).Cn 1 ≃+ (D.nerve.EdgeComponent → LawValueLabel laws → ℤ) :=
  (P.faceEmptyCechCochain1Equiv C).trans
    (AddEquiv.piCongrRight (fun _ => integralLabelEquiv P hR))

/-- A: degree two is the empty product on both the actual and ordinary graph sides. -/
def actualIntegralCochain2Equiv : (P.faceEmptyCechComplex C).Cn 2 ≃+
    (D.nerve.FaceComponent → LawValueLabel laws → ℤ) where
  toFun _ face := isEmptyElim face
  invFun _ face := isEmptyElim face
  left_inv _ := by funext face; exact isEmptyElim face
  right_inv _ := by ext face; exact isEmptyElim face
  map_add' _ _ := by ext face; exact isEmptyElim face

omit [Fintype Source] in
/-- A: the actual degree-one differential corresponds to the zero graph differential. -/
theorem actualIntegral_d1 (c : (P.faceEmptyCechComplex C).Cn 1) :
    actualIntegralCochain2Equiv P C ((P.faceEmptyCechComplex C).d 1 c) = 0 := by
  rw [P.faceEmptyCech_d1_eq_zero C]
  exact map_zero _

omit [Fintype Source] in
/-- A: the existing degree-two comparison is uniquely zero on the complete empty face index. -/
theorem actualCoefficient2_eq_zero (hadequate : laws.Adequate q) :
    P.actualCechCoefficientCochain2 C hadequate = 0 := by
  ext c coordinate
  exact isEmptyElim coordinate.cell

/-- Public evaluation of the actual chart coordinate equivalence. -/
@[simp]
theorem actualIntegralCochain0Equiv_apply (hR : P.ReflectionCondition)
    (c : (P.faceEmptyCechComplex C).Cn 0) (chart : D.nerve.Chart) :
    actualIntegralCochain0Equiv P C hR c chart =
      integralLabelEquiv P hR (P.faceEmptyCechCochain0Equiv C c chart) := rfl

/-- Public evaluation of the actual overlap coordinate equivalence. -/
@[simp]
theorem actualIntegralCochain1Equiv_apply (hR : P.ReflectionCondition)
    (c : (P.faceEmptyCechComplex C).Cn 1) (edge : D.nerve.EdgeComponent) :
    actualIntegralCochain1Equiv P C hR c edge =
      integralLabelEquiv P hR (P.faceEmptyCechCochain1Equiv C c edge) := rfl

/-- A: the actual restriction differential becomes the ordinary integral graph differential. -/
theorem actualIntegral_d0 (hR : P.ReflectionCondition)
    (c : (P.faceEmptyCechComplex C).Cn 0) :
    actualIntegralCochain1Equiv P C hR ((P.faceEmptyCechComplex C).d 0 c) =
      integralGraphD0 D.nerve (LawValueLabel laws) (actualIntegralCochain0Equiv P C hR c) := by
  ext edge label
  change integralLabelEquiv P hR
    (P.faceEmptyCechCochain1Equiv C ((P.faceEmptyCechComplex C).d 0 c) edge) label = _
  rw [P.faceEmptyCech_d0_normalizes C]
  change integralLabelEquiv P hR
    (P.faceEmptyCechCochain0Equiv C c (D.nerve.edgeRight edge) -
      P.faceEmptyCechCochain0Equiv C c (D.nerve.edgeLeft edge)) label = _
  rw [map_sub]
  rfl

/-- A: existing degree-zero comparison evaluates the same integer coordinate, cast to Q. -/
theorem actualCoefficient0_apply (hR : P.ReflectionCondition)
    (hadequate : laws.Adequate q) (c : (P.faceEmptyCechComplex C).Cn 0)
    (coordinate : D.ChartCoordinate laws hadequate) :
    P.actualCechCoefficientCochain0 C hadequate c coordinate =
      (actualIntegralCochain0Equiv P C hR c coordinate.cell
        (coordinate.lawValueLabel laws q hadequate D.nerve.Chart D.chartSupport) : ℚ) :=
  coefficientComparison_eq_cast P hR _ _

/-- A: existing degree-one comparison evaluates the same integer coordinate, cast to Q. -/
theorem actualCoefficient1_apply (hR : P.ReflectionCondition)
    (hadequate : laws.Adequate q) (c : (P.faceEmptyCechComplex C).Cn 1)
    (coordinate : D.EdgeCoordinate laws hadequate) :
    P.actualCechCoefficientCochain1 C hadequate c coordinate =
      (actualIntegralCochain1Equiv P C hR c coordinate.cell
        (coordinate.lawValueLabel laws q hadequate D.nerve.EdgeComponent D.edgeSupport) : ℚ) :=
  coefficientComparison_eq_cast P hR _ _

/-- A: the comparison in a visible vertex component is coefficient change and restriction. -/
theorem actualCoefficient0_visible (hR : P.ReflectionCondition)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (c : (P.faceEmptyCechComplex C).Cn 0) (vertex : VisibleVertex D hadequate label) :
    visibleCochain0Equiv D hadequate label
      (fun coordinate => P.actualCechCoefficientCochain0 C hadequate c coordinate.1) vertex =
      (actualIntegralCochain0Equiv P C hR c vertex.1 label : ℚ) := by
  rw [visibleCochain0Equiv_apply, actualCoefficient0_apply P C hR]
  rw [((visibleVertexEquiv D hadequate label).symm vertex).2]
  rw [visibleVertexEquiv_symm_cell]

/-- A: the comparison in a visible edge component is coefficient change and restriction. -/
theorem actualCoefficient1_visible (hR : P.ReflectionCondition)
    (hadequate : laws.Adequate q) (label : LawValueLabel laws)
    (c : (P.faceEmptyCechComplex C).Cn 1) (edge : VisibleEdge D hadequate label) :
    visibleCochain1Equiv D hadequate label
      (fun coordinate => P.actualCechCoefficientCochain1 C hadequate c coordinate.1) edge =
      (actualIntegralCochain1Equiv P C hR c edge.1 label : ℚ) := by
  rw [visibleCochain1Equiv_apply, actualCoefficient1_apply P C hR]
  rw [((visibleEdgeEquiv D hadequate label).symm edge).2]
  rw [visibleEdgeEquiv_symm_cell]

/-- A: the specified mismatch representative is transition plus the ordinary vertex difference. -/
theorem actualMismatch_normalized (hR : P.ReflectionCondition)
    (x : GeneratorPresentation.ActualCechAffineLocalData P C) :
    actualIntegralCochain1Equiv P C hR x.actualMismatch =
      actualIntegralCochain1Equiv P C hR x.transition +
        integralGraphD0 D.nerve (LawValueLabel laws)
          (actualIntegralCochain0Equiv P C hR x.localState) := by
  change actualIntegralCochain1Equiv P C hR
    (x.transition + (P.faceEmptyCechComplex C).d 0 x.localState) = _
  rw [map_add, actualIntegral_d0]

/-- A: the independent existing diagnostic is the comparison of the existing descent class. -/
theorem existingDescent_comparison (hadequate : laws.Adequate q)
    (x : GeneratorPresentation.ActualCechAffineLocalData P C) :
    P.actualCechDiagnosticH1Map C hadequate x.existingDescentAdditiveClass =
      x.diagnosticClass hadequate := by
  rw [x.existingDescentAdditiveClass_eq_actualClass]
  exact x.h1_map_actual_class_eq_diagnostic_class hadequate

end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
