import ResearchLean.AG.ObstructionDiagnosticBridge.AATLocallyConstantObstruction
import ResearchLean.AG.ObstructionDiagnosticBridge.CochainComparison
import Formal.AG.Cohomology.CechComplex
import Formal.Util.AssertStandardAxioms

/-!
# Selected face-index-empty Cech normalization

This module constructs the actual `CoverRelativeCechCover` and
`CoverRelativeCechComplex` attached to a supplied diagnostic nerve whose
selected `FaceComponent` index is empty.  Degree zero consists of chart
contexts, degree one of edge-overlap contexts, and degree two is the empty
selected face-index type.  The actual
obstruction-sheaf restriction maps define `d⁰`; all later differentials land
in an empty product and are zero.

On nonempty preconnected chart and edge supports, Cycle 7's evaluation
coordinates identify the actual Cech groups with the normalized presentation
cochains.  Under these coordinates, actual `d⁰` is the right-minus-left
presentation differential, while `C²` and `d¹` are zero because the selected
face type is empty.

This module does not prove that all geometric triple intersections are empty,
or that `FaceComponent` lists every nonempty triple-overlap component.  Those
provenance and completeness obligations belong to the later selected finite
geometry realization.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution ResolutionInvariance

universe u v

namespace GeneratorPresentation

variable {Source : Type u} {q : Reading Source}
variable {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-- Simplices of the selected face-index-empty Cech cover. -/
def FaceEmptySimplex (D : TargetSupportedNerve q) : Nat → Type u
  | 0 => D.nerve.Chart
  | 1 => D.nerve.EdgeComponent
  | 2 => D.nerve.FaceComponent
  | _ + 3 => PEmpty

/-- Dependent elimination for every simplex degree at least two. -/
def faceEmptyHigherSimplexElim (D : TargetSupportedNerve q)
    [IsEmpty D.nerve.FaceComponent]
    {motive : ∀ n, FaceEmptySimplex D (n + 2) → Sort v} :
    ∀ n (simplex : FaceEmptySimplex D (n + 2)), motive n simplex
  | 0, face => isEmptyElim (show D.nerve.FaceComponent from face)
  | _ + 1, simplex => PEmpty.elim (show PEmpty from simplex)

instance faceEmptyHigherSimplexIsEmpty (D : TargetSupportedNerve q)
    [IsEmpty D.nerve.FaceComponent] (n : Nat) :
    IsEmpty (FaceEmptySimplex D (n + 2)) where
  false simplex := faceEmptyHigherSimplexElim
    (motive := fun _ _ => False) D n simplex

/--
Actual AAT contexts and restriction maps attached to a diagnostic nerve whose
supplied face-index type is empty.  This package does not assert completeness
of that face index for geometric triple intersections.  Connectedness
assumptions are restricted to the chart and edge supports used in degrees zero
and one.
-/
structure FaceEmptyAATCechCover (D : TargetSupportedNerve q)
    (G : ContextOpenSupport S) [IsEmpty D.nerve.FaceComponent] where
  base : S.category
  chartContext : D.nerve.Chart → S.category
  edgeContext : D.nerve.EdgeComponent → S.category
  inclusion : ∀ chart, chartContext chart ⟶ base
  edgeLeftRestriction : ∀ edge,
    edgeContext edge ⟶ chartContext (D.nerve.edgeLeft edge)
  edgeRightRestriction : ∀ edge,
    edgeContext edge ⟶ chartContext (D.nerve.edgeRight edge)
  chartSupportNonempty : ∀ chart, Nonempty (G.support.obj (chartContext chart))
  chartSupportPreconnected : ∀ chart,
    PreconnectedSpace (G.support.obj (chartContext chart))
  edgeSupportNonempty : ∀ edge, Nonempty (G.support.obj (edgeContext edge))
  edgeSupportPreconnected : ∀ edge,
    PreconnectedSpace (G.support.obj (edgeContext edge))

namespace FaceEmptyAATCechCover

variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent]

/-- Context attached to each simplex of the selected face-index-empty nerve. -/
def overlap (C : FaceEmptyAATCechCover D G) :
    ∀ n, FaceEmptySimplex D n → S.category
  | 0, chart => C.chartContext chart
  | 1, edge => C.edgeContext edge
  | 2, face => isEmptyElim (show D.nerve.FaceComponent from face)
  | _ + 3, simplex => PEmpty.elim (show PEmpty from simplex)

/-- Ordered face map; degree zero uses left then right endpoint. -/
def face (_C : FaceEmptyAATCechCover D G) :
    ∀ n, Fin (n + 2) → FaceEmptySimplex D (n + 1) → FaceEmptySimplex D n
  | 0, i, edge =>
      by
        by_cases h : i = 0
        · exact D.nerve.edgeLeft edge
        · exact D.nerve.edgeRight edge
  | 1, _, face => isEmptyElim (show D.nerve.FaceComponent from face)
  | _ + 2, _, simplex => PEmpty.elim (show PEmpty from simplex)

/-- Actual AAT restriction attached to each face map. -/
def faceRestriction (C : FaceEmptyAATCechCover D G) :
    ∀ (n : Nat) (i : Fin (n + 2)) (σ : FaceEmptySimplex D (n + 1)),
      C.overlap (n + 1) σ ⟶ C.overlap n (C.face n i σ)
  | 0, i, edge =>
      by
        by_cases h : i = 0
        · subst i
          exact C.edgeLeftRestriction edge
        · have hi : i = 1 := Fin.eq_one_of_ne_zero i h
          subst i
          exact C.edgeRightRestriction edge
  | 1, _, face => isEmptyElim (show D.nerve.FaceComponent from face)
  | _ + 2, _, simplex => PEmpty.elim (show PEmpty from simplex)

/-- The selected data as the existing actual cover-relative Cech cover. -/
def toCoverRelativeCechCover (C : FaceEmptyAATCechCover D G) :
    Cohomology.CoverRelativeCechCover S where
  base := C.base
  Index := D.nerve.Chart
  chart := C.chartContext
  inclusion := C.inclusion
  simplex := FaceEmptySimplex D
  overlap := C.overlap
  face := C.face
  faceRestriction := C.faceRestriction

end FaceEmptyAATCechCover

variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent]

instance coverRelativeHigherSimplexIsEmpty
    (C : FaceEmptyAATCechCover D G) (n : Nat) :
    IsEmpty (C.toCoverRelativeCechCover.simplex (n + 2)) := by
  change IsEmpty (FaceEmptySimplex D (n + 2))
  infer_instance

instance faceEmptyCechCochainAddCommGroup (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (n : Nat) :
    AddCommGroup
      (Cohomology.CoverRelativeCechCochain C.toCoverRelativeCechCover
        (P.aatLocallyConstantObstructionSheaf G) n) := by
  dsimp [Cohomology.CoverRelativeCechCochain]
  infer_instance

/--
The actual Cech package of the pulled-back locally constant obstruction sheaf
relative to the supplied face-index-empty nerve.
-/
def faceEmptyCechComplex (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) :
    Cohomology.CoverRelativeCechComplex C.toCoverRelativeCechCover
      (P.aatLocallyConstantObstructionSheaf G) where
  cochainAddCommGroup n := P.faceEmptyCechCochainAddCommGroup C n
  alternatingFaceCombination
    | 0 => fun terms edge => terms edge 1 - terms edge 0
    | _ + 1 => fun _ simplex => isEmptyElim simplex
  differential
    | 0 => {
        toFun := fun c edge =>
          (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
              (C.edgeRightRestriction edge).op (c (D.nerve.edgeRight edge)) -
            (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
              (C.edgeLeftRestriction edge).op (c (D.nerve.edgeLeft edge))
        map_zero' := by
          funext edge
          change
            (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                (C.edgeRightRestriction edge).op 0 -
              (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                (C.edgeLeftRestriction edge).op 0 = 0
          rw [(P.aatLocallyConstantObstructionSheaf G).map_zero,
            (P.aatLocallyConstantObstructionSheaf G).map_zero]
          exact sub_self 0
        map_add' := by
          intro left right
          funext edge
          change
            (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                (C.edgeRightRestriction edge).op
                  (left (D.nerve.edgeRight edge) +
                    right (D.nerve.edgeRight edge)) -
              (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                (C.edgeLeftRestriction edge).op
                  (left (D.nerve.edgeLeft edge) +
                    right (D.nerve.edgeLeft edge)) =
              ((P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                    (C.edgeRightRestriction edge).op
                      (left (D.nerve.edgeRight edge)) -
                (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                    (C.edgeLeftRestriction edge).op
                      (left (D.nerve.edgeLeft edge))) +
              ((P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                    (C.edgeRightRestriction edge).op
                      (right (D.nerve.edgeRight edge)) -
                (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
                    (C.edgeLeftRestriction edge).op
                      (right (D.nerve.edgeLeft edge)))
          rw [(P.aatLocallyConstantObstructionSheaf G).map_add,
            (P.aatLocallyConstantObstructionSheaf G).map_add]
          abel
      }
    | _ + 1 => 0
  differential_eq_alternatingFaceCombination
    | 0, _ => by
        funext edge
        rfl
    | _ + 1, _ => by
        funext simplex
        exact isEmptyElim simplex
  differential_comp
    | 0, _ => rfl
    | _ + 1, _ => rfl

/-- Degree-zero actual Cech cochains evaluated in presentation coordinates. -/
def faceEmptyCechCochain0Equiv (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) :
    (P.faceEmptyCechComplex C).Cn 0 ≃+ P.PresentationCochain0 D where
  toFun c chart := by
    letI := C.chartSupportNonempty chart
    letI := C.chartSupportPreconnected chart
    exact P.aatLocallyConstantObstructionSectionEquiv G (C.chartContext chart)
      (c chart)
  invFun c chart := by
    letI := C.chartSupportNonempty chart
    letI := C.chartSupportPreconnected chart
    exact (P.aatLocallyConstantObstructionSectionEquiv G
      (C.chartContext chart)).symm (c chart)
  left_inv c := by
    funext chart
    letI := C.chartSupportNonempty chart
    letI := C.chartSupportPreconnected chart
    exact (P.aatLocallyConstantObstructionSectionEquiv G
      (C.chartContext chart)).left_inv (c chart)
  right_inv c := by
    funext chart
    letI := C.chartSupportNonempty chart
    letI := C.chartSupportPreconnected chart
    exact (P.aatLocallyConstantObstructionSectionEquiv G
      (C.chartContext chart)).right_inv (c chart)
  map_add' left right := by
    funext chart
    letI := C.chartSupportNonempty chart
    letI := C.chartSupportPreconnected chart
    exact map_add _ _ _

/-- Degree-one actual Cech cochains evaluated in presentation coordinates. -/
def faceEmptyCechCochain1Equiv (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) :
    (P.faceEmptyCechComplex C).Cn 1 ≃+ P.PresentationCochain1 D where
  toFun c edge := by
    letI := C.edgeSupportNonempty edge
    letI := C.edgeSupportPreconnected edge
    exact P.aatLocallyConstantObstructionSectionEquiv G (C.edgeContext edge)
      (c edge)
  invFun c edge := by
    letI := C.edgeSupportNonempty edge
    letI := C.edgeSupportPreconnected edge
    exact (P.aatLocallyConstantObstructionSectionEquiv G
      (C.edgeContext edge)).symm (c edge)
  left_inv c := by
    funext edge
    letI := C.edgeSupportNonempty edge
    letI := C.edgeSupportPreconnected edge
    exact (P.aatLocallyConstantObstructionSectionEquiv G
      (C.edgeContext edge)).left_inv (c edge)
  right_inv c := by
    funext edge
    letI := C.edgeSupportNonempty edge
    letI := C.edgeSupportPreconnected edge
    exact (P.aatLocallyConstantObstructionSectionEquiv G
      (C.edgeContext edge)).right_inv (c edge)
  map_add' left right := by
    funext edge
    letI := C.edgeSupportNonempty edge
    letI := C.edgeSupportPreconnected edge
    exact map_add _ _ _

/-- Degree two is the empty product on both the actual and normalized sides. -/
def faceEmptyCechCochain2Equiv (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) :
    (P.faceEmptyCechComplex C).Cn 2 ≃+ P.PresentationCochain2 D where
  toFun _ face := isEmptyElim face
  invFun _ face := isEmptyElim face
  left_inv c := by funext face; exact isEmptyElim face
  right_inv c := by funext face; exact isEmptyElim face
  map_add' _ _ := by funext face; exact isEmptyElim face

/-- Actual `d⁰` is right-minus-left in connected-support coordinates. -/
theorem faceEmptyCech_d0_normalizes (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G)
    (c : (P.faceEmptyCechComplex C).Cn 0) :
    P.faceEmptyCechCochain1Equiv C ((P.faceEmptyCechComplex C).d 0 c) =
      P.presentationD0 D (P.faceEmptyCechCochain0Equiv C c) := by
  funext edge
  letI := C.chartSupportNonempty (D.nerve.edgeRight edge)
  letI := C.chartSupportPreconnected (D.nerve.edgeRight edge)
  letI := C.chartSupportNonempty (D.nerve.edgeLeft edge)
  letI := C.chartSupportPreconnected (D.nerve.edgeLeft edge)
  letI := C.edgeSupportNonempty edge
  letI := C.edgeSupportPreconnected edge
  change
    P.aatLocallyConstantObstructionSectionEquiv G (C.edgeContext edge)
        ((P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
            (C.edgeRightRestriction edge).op
              (c (D.nerve.edgeRight edge)) -
          (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map
            (C.edgeLeftRestriction edge).op
              (c (D.nerve.edgeLeft edge))) = _
  rw [map_sub]
  rw [P.aatLocallyConstantObstructionSectionEquiv_restriction G
    (C.edgeContext edge) (C.chartContext (D.nerve.edgeRight edge))
    (C.edgeRightRestriction edge) (c (D.nerve.edgeRight edge))]
  rw [P.aatLocallyConstantObstructionSectionEquiv_restriction G
    (C.edgeContext edge) (C.chartContext (D.nerve.edgeLeft edge))
    (C.edgeLeftRestriction edge) (c (D.nerve.edgeLeft edge))]
  rfl

/-- The actual degree-one differential is zero for the supplied empty face index. -/
theorem faceEmptyCech_d1_eq_zero (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) :
    (P.faceEmptyCechComplex C).d 1 = 0 := by
  apply AddMonoidHom.ext
  intro c
  funext face
  exact isEmptyElim face

/-- The normalized presentation degree-one differential is also zero. -/
theorem presentationD1_eq_zero_of_faceEmpty (P : GeneratorPresentation laws)
    (D : TargetSupportedNerve q) [IsEmpty D.nerve.FaceComponent] :
    P.presentationD1 D = 0 := by
  ext c face
  exact isEmptyElim face

/-- Degree-zero comparison from the actual Cech complex to diagnostic coefficients. -/
def actualCechCoefficientCochain0 (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) :
    (P.faceEmptyCechComplex C).Cn 0 →+
      (D.ChartCoordinate laws hadequate → ℚ) :=
  (P.coefficientCochain0 D hadequate).comp
    (P.faceEmptyCechCochain0Equiv C).toAddMonoidHom

/-- Degree-one comparison from the actual Cech complex to diagnostic coefficients. -/
def actualCechCoefficientCochain1 (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) :
    (P.faceEmptyCechComplex C).Cn 1 →+
      (D.EdgeCoordinate laws hadequate → ℚ) :=
  (P.coefficientCochain1 D hadequate).comp
    (P.faceEmptyCechCochain1Equiv C).toAddMonoidHom

/-- Degree-two comparison from the actual Cech complex to diagnostic coefficients. -/
def actualCechCoefficientCochain2 (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) :
    (P.faceEmptyCechComplex C).Cn 2 →+
      (D.FaceCoordinate laws hadequate → ℚ) :=
  (P.coefficientCochain2 D hadequate).comp
    (P.faceEmptyCechCochain2Equiv C).toAddMonoidHom

/-- The degree-zero square now starts at the actual obstruction Cech complex. -/
theorem actualCechCoefficient_comm0 (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q)
    (c : (P.faceEmptyCechComplex C).Cn 0) :
    P.actualCechCoefficientCochain1 C hadequate
        ((P.faceEmptyCechComplex C).d 0 c) =
      D.lawGeneratedD0 laws hadequate
        (P.actualCechCoefficientCochain0 C hadequate c) := by
  change
    P.coefficientCochain1 D hadequate
        (P.faceEmptyCechCochain1Equiv C
          ((P.faceEmptyCechComplex C).d 0 c)) =
      D.lawGeneratedD0 laws hadequate
        (P.coefficientCochain0 D hadequate
          (P.faceEmptyCechCochain0Equiv C c))
  rw [P.faceEmptyCech_d0_normalizes C]
  exact P.coefficientCochain_comm0 D hadequate
    (P.faceEmptyCechCochain0Equiv C c)

/-- The degree-one square holds on the selected face-index-empty input. -/
theorem actualCechCoefficient_comm1 (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q)
    (c : (P.faceEmptyCechComplex C).Cn 1) :
    P.actualCechCoefficientCochain2 C hadequate
        ((P.faceEmptyCechComplex C).d 1 c) =
      D.lawGeneratedD1 laws hadequate
        (P.actualCechCoefficientCochain1 C hadequate c) := by
  change
    P.coefficientCochain2 D hadequate
        (P.faceEmptyCechCochain2Equiv C
          ((P.faceEmptyCechComplex C).d 1 c)) =
      D.lawGeneratedD1 laws hadequate
        (P.coefficientCochain1 D hadequate
          (P.faceEmptyCechCochain1Equiv C c))
  rw [P.faceEmptyCech_d1_eq_zero C]
  simp only [AddMonoidHom.zero_apply, map_zero]
  rw [← P.coefficientCochain_comm1 D hadequate]
  rw [P.presentationD1_eq_zero_of_faceEmpty D]
  rfl

/-- Actual degree-zero-through-two Cech-to-diagnostic cochain map package. -/
structure ActualCechDiagnosticCochainMap (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) where
  f0 : (P.faceEmptyCechComplex C).Cn 0 →+
    (D.ChartCoordinate laws hadequate → ℚ)
  f1 : (P.faceEmptyCechComplex C).Cn 1 →+
    (D.EdgeCoordinate laws hadequate → ℚ)
  f2 : (P.faceEmptyCechComplex C).Cn 2 →+
    (D.FaceCoordinate laws hadequate → ℚ)
  comm0 : ∀ c, f1 ((P.faceEmptyCechComplex C).d 0 c) =
    D.lawGeneratedD0 laws hadequate (f0 c)
  comm1 : ∀ c, f2 ((P.faceEmptyCechComplex C).d 1 c) =
    D.lawGeneratedD1 laws hadequate (f1 c)

/-- G-125(A1)'s cochain map with the actual obstruction Cech source. -/
def actualCechCoefficientCochainMap (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) :
    ActualCechDiagnosticCochainMap P C hadequate where
  f0 := P.actualCechCoefficientCochain0 C hadequate
  f1 := P.actualCechCoefficientCochain1 C hadequate
  f2 := P.actualCechCoefficientCochain2 C hadequate
  comm0 := P.actualCechCoefficient_comm0 C hadequate
  comm1 := P.actualCechCoefficient_comm1 C hadequate

end GeneratorPresentation

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge

end AAT.AG.ObstructionDiagnosticBridge
