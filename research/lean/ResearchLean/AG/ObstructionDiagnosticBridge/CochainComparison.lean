import ResearchLean.AG.ObstructionDiagnosticBridge.CoefficientComparison
import ResearchLean.AG.ResolutionInvariance.LawGeneratedComplex
import Formal.Util.AssertStandardAxioms

/-!
# Cellwise comparison with the law-generated diagnostic complex

This module lifts G-125's coefficient map `ε_R` cellwise over an existing
`TargetSupportedNerve`.  The source is the normalized presentation-coefficient
complex on the same chart, edge, and face sets.  The target is not a copied
diagnostic complex: it is the existing K0/K1-generated coordinate surface and
the actual `lawGeneratedD0` and `lawGeneratedD1` differentials.

Endpoint and face-coordinate label preservation proves both cochain squares.
This supplies the normalized degree-zero-through-two comparison kernel.  The
remaining A1 obligation is to identify these source cochains with the selected
cover-relative complex of the constructed obstruction sheaf.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution ResolutionInvariance

universe u

namespace GeneratorPresentation

variable {Source : Type u} {q : Reading Source}
variable {laws : FiniteLawFamily Source}

/-- Presentation-valued degree-zero cochains on the selected diagnostic nerve. -/
abbrev PresentationCochain0 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) := D.nerve.Chart → P.PresentationGroup

/-- Presentation-valued degree-one cochains on the selected diagnostic nerve. -/
abbrev PresentationCochain1 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) := D.nerve.EdgeComponent → P.PresentationGroup

/-- Presentation-valued degree-two cochains on the selected diagnostic nerve. -/
abbrev PresentationCochain2 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) := D.nerve.FaceComponent → P.PresentationGroup

/-- The normalized right-minus-left presentation differential. -/
def presentationD0 (P : GeneratorPresentation laws) (D : TargetSupportedNerve q) :
    P.PresentationCochain0 D →+ P.PresentationCochain1 D where
  toFun c edge := c (D.nerve.edgeRight edge) - c (D.nerve.edgeLeft edge)
  map_zero' := by ext; simp
  map_add' left right := by ext; simp; abel

/-- The normalized alternating face presentation differential. -/
def presentationD1 (P : GeneratorPresentation laws) (D : TargetSupportedNerve q) :
    P.PresentationCochain1 D →+ P.PresentationCochain2 D where
  toFun c face := c (D.nerve.faceEdge0 face) - c (D.nerve.faceEdge1 face) +
    c (D.nerve.faceEdge2 face)
  map_zero' := by ext; simp
  map_add' left right := by ext; simp; abel

/-- The normalized presentation differentials compose to zero by nerve endpoint coherence. -/
theorem presentation_d1_comp_d0 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (c : P.PresentationCochain0 D) :
    P.presentationD1 D (P.presentationD0 D c) = 0 := by
  funext face
  change
    (c (D.nerve.edgeRight (D.nerve.faceEdge0 face)) -
      c (D.nerve.edgeLeft (D.nerve.faceEdge0 face))) -
    (c (D.nerve.edgeRight (D.nerve.faceEdge1 face)) -
      c (D.nerve.edgeLeft (D.nerve.faceEdge1 face))) +
    (c (D.nerve.edgeRight (D.nerve.faceEdge2 face)) -
      c (D.nerve.edgeLeft (D.nerve.faceEdge2 face))) = 0
  rw [D.faceEdge0_left face, D.faceEdge0_right face, D.faceEdge1_right face]
  abel

/-- Apply `ε_R` to each chart at the exact generated label of a diagnostic coordinate. -/
def coefficientCochain0 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q) :
    P.PresentationCochain0 D →+
      (D.ChartCoordinate laws hadequate → ℚ) where
  toFun c coordinate :=
    P.coefficientComparison (c coordinate.cell)
      (coordinate.lawValueLabel laws q hadequate D.nerve.Chart D.chartSupport)
  map_zero' := by ext; simp
  map_add' left right := by ext; simp

/-- Apply `ε_R` to each edge at the exact generated label of a diagnostic coordinate. -/
def coefficientCochain1 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q) :
    P.PresentationCochain1 D →+
      (D.EdgeCoordinate laws hadequate → ℚ) where
  toFun c coordinate :=
    P.coefficientComparison (c coordinate.cell)
      (coordinate.lawValueLabel laws q hadequate D.nerve.EdgeComponent D.edgeSupport)
  map_zero' := by ext; simp
  map_add' left right := by ext; simp

/-- Apply `ε_R` to each face at the exact generated label of a diagnostic coordinate. -/
def coefficientCochain2 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q) :
    P.PresentationCochain2 D →+
      (D.FaceCoordinate laws hadequate → ℚ) where
  toFun c coordinate :=
    P.coefficientComparison (c coordinate.cell)
      (coordinate.lawValueLabel laws q hadequate D.nerve.FaceComponent D.faceSupport)
  map_zero' := by ext; simp
  map_add' left right := by ext; simp

/-- The degree-zero square commutes with the actual generated diagnostic differential. -/
theorem coefficientCochain_comm0 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q)
    (c : P.PresentationCochain0 D) :
    P.coefficientCochain1 D hadequate (P.presentationD0 D c) =
      D.lawGeneratedD0 laws hadequate (P.coefficientCochain0 D hadequate c) := by
  funext coordinate
  change P.coefficientComparison
      (c (D.nerve.edgeRight coordinate.cell) - c (D.nerve.edgeLeft coordinate.cell))
      (coordinate.lawValueLabel laws q hadequate D.nerve.EdgeComponent D.edgeSupport) =
    P.coefficientComparison (c (D.nerve.edgeRight coordinate.cell))
        ((D.edgeRightCoordinate laws hadequate coordinate).lawValueLabel laws q
          hadequate D.nerve.Chart D.chartSupport) -
      P.coefficientComparison (c (D.nerve.edgeLeft coordinate.cell))
        ((D.edgeLeftCoordinate laws hadequate coordinate).lawValueLabel laws q
          hadequate D.nerve.Chart D.chartSupport)
  rw [map_sub, Pi.sub_apply, D.edgeRightCoordinate_lawValueLabel laws hadequate,
    D.edgeLeftCoordinate_lawValueLabel laws hadequate]

/-- The degree-one square commutes with the actual generated diagnostic differential. -/
theorem coefficientCochain_comm1 (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q)
    (c : P.PresentationCochain1 D) :
    P.coefficientCochain2 D hadequate (P.presentationD1 D c) =
      D.lawGeneratedD1 laws hadequate (P.coefficientCochain1 D hadequate c) := by
  funext coordinate
  change P.coefficientComparison
      (c (D.nerve.faceEdge0 coordinate.cell) -
          c (D.nerve.faceEdge1 coordinate.cell) +
        c (D.nerve.faceEdge2 coordinate.cell))
      (coordinate.lawValueLabel laws q hadequate D.nerve.FaceComponent D.faceSupport) =
    P.coefficientComparison (c (D.nerve.faceEdge0 coordinate.cell))
        ((D.faceEdge0Coordinate laws hadequate coordinate).lawValueLabel laws q
          hadequate D.nerve.EdgeComponent D.edgeSupport) -
      P.coefficientComparison (c (D.nerve.faceEdge1 coordinate.cell))
        ((D.faceEdge1Coordinate laws hadequate coordinate).lawValueLabel laws q
          hadequate D.nerve.EdgeComponent D.edgeSupport) +
      P.coefficientComparison (c (D.nerve.faceEdge2 coordinate.cell))
        ((D.faceEdge2Coordinate laws hadequate coordinate).lawValueLabel laws q
          hadequate D.nerve.EdgeComponent D.edgeSupport)
  rw [map_add, Pi.add_apply, map_sub, Pi.sub_apply,
    D.faceEdge0Coordinate_lawValueLabel laws hadequate,
    D.faceEdge1Coordinate_lawValueLabel laws hadequate,
    D.faceEdge2Coordinate_lawValueLabel laws hadequate]

/-- Mixed additive cochain-map package from presentation cochains to the generated complex. -/
structure PresentationDiagnosticCochainMap (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q) where
  f0 : P.PresentationCochain0 D →+
    (D.ChartCoordinate laws hadequate → ℚ)
  f1 : P.PresentationCochain1 D →+
    (D.EdgeCoordinate laws hadequate → ℚ)
  f2 : P.PresentationCochain2 D →+
    (D.FaceCoordinate laws hadequate → ℚ)
  comm0 : ∀ c, f1 (P.presentationD0 D c) =
    D.lawGeneratedD0 laws hadequate (f0 c)
  comm1 : ∀ c, f2 (P.presentationD1 D c) =
    D.lawGeneratedD1 laws hadequate (f1 c)

/-- G-125(A)'s normalized degree-zero-through-two coefficient cochain map. -/
def coefficientCochainMap (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) (hadequate : laws.Adequate q) :
    PresentationDiagnosticCochainMap P D hadequate where
  f0 := P.coefficientCochain0 D hadequate
  f1 := P.coefficientCochain1 D hadequate
  f2 := P.coefficientCochain2 D hadequate
  comm0 := P.coefficientCochain_comm0 D hadequate
  comm1 := P.coefficientCochain_comm1 D hadequate

end GeneratorPresentation

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge

end AAT.AG.ObstructionDiagnosticBridge
