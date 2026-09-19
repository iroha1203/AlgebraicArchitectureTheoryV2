import ResearchLean.AG.ObstructionDiagnosticBridge.ActualCechH1Comparison
import ResearchLean.AG.ResolutionInvariance.GeneratedComparisonMap
import ResearchLean.AG.ResolutionInvariance.LawValueBlockDecomposition
import Formal.Util.AssertStandardAxioms

/-!
# Actual Cech comparison along a reading refinement

For a supported-nerve morphism, presentation-valued cochains pull back by
precomposing chart values, copying mapped edge values, and inserting zero on
contracted edges.  Endpoint preservation proves the degree-zero cochain
square.  Conjugating this map through the connected-section coordinate
equivalences gives an additive map between the two actual obstruction Cech
complexes and hence a map on additive H1.

The construction uses the actual Cech covers on both sides.  It does not use
the diagnostic comparison, a cohomology inverse, or a vanishing certificate.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution Cohomology ResolutionInvariance TwoPhase

universe u

namespace GeneratorPresentation

variable {Source : Type u} [Fintype Source]
variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {laws : FiniteLawFamily Source}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {G : ContextOpenSupport S}
variable [IsEmpty coarse.nerve.FaceComponent]
variable [IsEmpty fine.nerve.FaceComponent]

/-- Degree-zero presentation pullback along the chart map. -/
def presentationPullback0 (P : GeneratorPresentation laws)
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    P.PresentationCochain0 coarse →+ P.PresentationCochain0 fine where
  toFun cochain fineChart := cochain (M.chartMap fineChart)
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- Degree-one presentation pullback, with zero on contracted fine edges. -/
def presentationPullback1 (P : GeneratorPresentation laws)
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    P.PresentationCochain1 coarse →+ P.PresentationCochain1 fine where
  toFun cochain fineEdge := (M.edgeMap fineEdge).elim 0 cochain
  map_zero' := by
    funext fineEdge
    cases M.edgeMap fineEdge <;> rfl
  map_add' left right := by
    funext fineEdge
    generalize hmap : M.edgeMap fineEdge = mapped
    cases mapped <;> simp [hmap]

omit [Fintype Source] [IsEmpty coarse.nerve.FaceComponent]
    [IsEmpty fine.nerve.FaceComponent] in
/-- Presentation pullback commutes with the normalized degree-zero differential. -/
theorem presentationPullback_comm0 (P : GeneratorPresentation laws)
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (cochain : P.PresentationCochain0 coarse) :
    P.presentationPullback1 M (P.presentationD0 coarse cochain) =
      P.presentationD0 fine (P.presentationPullback0 M cochain) := by
  funext fineEdge
  generalize hmap : M.edgeMap fineEdge = mapped
  cases mapped with
  | none =>
      have hfiber := M.edge_none_fiber fineEdge hmap
      simp [presentationPullback1, presentationPullback0, presentationD0,
        hmap, hfiber]
  | some coarseEdge =>
      have hleft := M.edge_some_left fineEdge coarseEdge hmap
      have hright := M.edge_some_right fineEdge coarseEdge hmap
      simp [presentationPullback1, presentationPullback0, presentationD0,
        hmap, hleft, hright]

omit [Fintype Source] [IsEmpty coarse.nerve.FaceComponent]
    [IsEmpty fine.nerve.FaceComponent] in
/-- Coefficient evaluation is natural under the chart pullback. -/
theorem coefficientCochain0_presentationPullback (P : GeneratorPresentation laws)
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : P.PresentationCochain0 coarse) :
    P.coefficientCochain0 fine hfine (P.presentationPullback0 M cochain) =
      M.generatedPullback0 laws hcoarse hfine
        (P.coefficientCochain0 coarse hcoarse cochain) := by
  funext coordinate
  change
    P.coefficientComparison (cochain (M.chartMap coordinate.cell))
        (coordinate.lawValueLabel laws fineReading hfine fine.nerve.Chart
          fine.chartSupport) =
      P.coefficientComparison (cochain (M.chartMap coordinate.cell))
        ((M.chartCoordinateMap laws hcoarse hfine coordinate).lawValueLabel laws
          coarseReading hcoarse coarse.nerve.Chart coarse.chartSupport)
  rw [M.chartCoordinateMap_lawValueLabel laws hcoarse hfine coordinate]

omit [Fintype Source] [IsEmpty coarse.nerve.FaceComponent]
    [IsEmpty fine.nerve.FaceComponent] in
/-- Coefficient evaluation is natural under mapped or contracted edge pullback. -/
theorem coefficientCochain1_presentationPullback (P : GeneratorPresentation laws)
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : P.PresentationCochain1 coarse) :
    P.coefficientCochain1 fine hfine (P.presentationPullback1 M cochain) =
      M.generatedPullback1 laws hcoarse hfine
        (P.coefficientCochain1 coarse hcoarse cochain) := by
  funext coordinate
  generalize hmap : M.edgeMap coordinate.cell = mapped
  cases mapped with
  | none =>
      rw [M.generatedPullback1_apply,
        M.edgeCoordinateMapOption_eq_none laws hcoarse hfine coordinate hmap]
      change
        P.coefficientComparison ((M.edgeMap coordinate.cell).elim 0 cochain)
            (coordinate.lawValueLabel laws fineReading hfine
              fine.nerve.EdgeComponent fine.edgeSupport) = 0
      rw [hmap]
      change
        P.coefficientComparison (0 : P.PresentationGroup)
            (coordinate.lawValueLabel laws fineReading hfine
              fine.nerve.EdgeComponent fine.edgeSupport) = 0
      rw [map_zero]
      rfl
  | some coarseEdge =>
      rw [M.generatedPullback1_apply,
        M.edgeCoordinateMapOption_eq_some laws hcoarse hfine coordinate
          coarseEdge hmap]
      change
        P.coefficientComparison ((M.edgeMap coordinate.cell).elim 0 cochain)
            (coordinate.lawValueLabel laws fineReading hfine
              fine.nerve.EdgeComponent fine.edgeSupport) =
          P.coefficientComparison (cochain coarseEdge)
            ((M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap).lawValueLabel
              laws coarseReading hcoarse
                coarse.nerve.EdgeComponent coarse.edgeSupport)
      rw [hmap]
      change
        P.coefficientComparison (cochain coarseEdge)
            (coordinate.lawValueLabel laws fineReading hfine
              fine.nerve.EdgeComponent fine.edgeSupport) =
          P.coefficientComparison (cochain coarseEdge)
            ((M.edgeCoordinateMap laws hcoarse hfine coordinate coarseEdge hmap).lawValueLabel
              laws coarseReading hcoarse
                coarse.nerve.EdgeComponent coarse.edgeSupport)
      rw [M.edgeCoordinateMap_lawValueLabel laws hcoarse hfine coordinate
        coarseEdge hmap]

variable {P : GeneratorPresentation laws}
variable {coarseCover : FaceEmptyAATCechCover coarse G}
variable {fineCover : FaceEmptyAATCechCover fine G}

/-- Degree-zero pullback on the actual obstruction Cech cochains. -/
def actualCechPullback0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    (P.faceEmptyCechComplex coarseCover).Cn 0 →+
      (P.faceEmptyCechComplex fineCover).Cn 0 :=
  (P.faceEmptyCechCochain0Equiv fineCover).symm.toAddMonoidHom.comp
    ((P.presentationPullback0 M).comp
      (P.faceEmptyCechCochain0Equiv coarseCover).toAddMonoidHom)

/-- Degree-one pullback on the actual obstruction Cech cochains. -/
def actualCechPullback1
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    (P.faceEmptyCechComplex coarseCover).Cn 1 →+
      (P.faceEmptyCechComplex fineCover).Cn 1 :=
  (P.faceEmptyCechCochain1Equiv fineCover).symm.toAddMonoidHom.comp
    ((P.presentationPullback1 M).comp
      (P.faceEmptyCechCochain1Equiv coarseCover).toAddMonoidHom)

omit [Fintype Source] in
/-- Actual Cech pullback commutes with `d⁰`. -/
theorem actualCechPullback_comm0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (cochain : (P.faceEmptyCechComplex coarseCover).Cn 0) :
    P.actualCechPullback1 M ((P.faceEmptyCechComplex coarseCover).d 0 cochain) =
      (P.faceEmptyCechComplex fineCover).d 0 (P.actualCechPullback0 M cochain) := by
  apply (P.faceEmptyCechCochain1Equiv fineCover).injective
  change
    P.presentationPullback1 M
        (P.faceEmptyCechCochain1Equiv coarseCover
          ((P.faceEmptyCechComplex coarseCover).d 0 cochain)) =
      P.faceEmptyCechCochain1Equiv fineCover
        ((P.faceEmptyCechComplex fineCover).d 0
          ((P.faceEmptyCechCochain0Equiv fineCover).symm
            (P.presentationPullback0 M
              (P.faceEmptyCechCochain0Equiv coarseCover cochain))))
  rw [P.faceEmptyCech_d0_normalizes coarseCover,
    P.faceEmptyCech_d0_normalizes fineCover]
  simp only [AddEquiv.apply_symm_apply]
  exact P.presentationPullback_comm0 M
    (P.faceEmptyCechCochain0Equiv coarseCover cochain)

omit [Fintype Source] in
/-- The actual degree-one coefficient comparison is natural under refinement. -/
theorem actualCechCoefficient1_pullback_naturality
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (cochain : (P.faceEmptyCechComplex coarseCover).Cn 1) :
    P.actualCechCoefficientCochain1 fineCover hfine
        (P.actualCechPullback1 M cochain) =
      M.generatedPullback1 laws hcoarse hfine
        (P.actualCechCoefficientCochain1 coarseCover hcoarse cochain) := by
  change
    P.coefficientCochain1 fine hfine
        ((P.faceEmptyCechCochain1Equiv fineCover)
          ((P.faceEmptyCechCochain1Equiv fineCover).symm
            (P.presentationPullback1 M
              (P.faceEmptyCechCochain1Equiv coarseCover cochain)))) = _
  rw [AddEquiv.apply_symm_apply]
  exact P.coefficientCochain1_presentationPullback M hcoarse hfine
    (P.faceEmptyCechCochain1Equiv coarseCover cochain)

/-- Degree-one actual cocycles pulled back along the selected refinement. -/
def actualCechPullbackCycles
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    (P.faceEmptyCechComplex coarseCover).CechCocycleSubgroup 1 →+
      (P.faceEmptyCechComplex fineCover).CechCocycleSubgroup 1 where
  toFun cocycle := ⟨P.actualCechPullback1 M cocycle.1, by
    change (P.faceEmptyCechComplex fineCover).d 1
      (P.actualCechPullback1 M cocycle.1) = 0
    rw [P.faceEmptyCech_d1_eq_zero fineCover]
    rfl⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' left right := by
    apply Subtype.ext
    exact map_add _ left.1 right.1

/-- The actual coarse-to-fine map on additive Cech H1. -/
def actualCechRefinementH1Map
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    (P.faceEmptyCechComplex coarseCover).AdditiveCechH1 →+
      (P.faceEmptyCechComplex fineCover).AdditiveCechH1 :=
  QuotientAddGroup.lift
    ((P.faceEmptyCechComplex coarseCover).CechCoboundarySubgroupSucc 0)
    ((QuotientAddGroup.mk'
        ((P.faceEmptyCechComplex fineCover).CechCoboundarySubgroupSucc 0)).comp
      (P.actualCechPullbackCycles M))
    (by
      intro cocycle hcocycle
      rcases hcocycle with ⟨cochain, rfl⟩
      apply (QuotientAddGroup.eq_zero_iff _).2
      refine ⟨P.actualCechPullback0 M cochain, ?_⟩
      apply Subtype.ext
      change
        P.actualCechPullback1 M
            ((P.faceEmptyCechComplex coarseCover).d 0 cochain) =
          (P.faceEmptyCechComplex fineCover).d 0
            (P.actualCechPullback0 M cochain)
      exact P.actualCechPullback_comm0 M cochain)

/-- G-125(C1): actual and generated diagnostic H1 comparisons commute. -/
theorem actualCechDiagnosticH1_naturality
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading) :
    (P.actualCechDiagnosticH1Map fineCover hfine).comp
        (P.actualCechRefinementH1Map M) =
      (M.generatedComparisonH1Map laws hcoarse hfine).toAddMonoidHom.comp
        (P.actualCechDiagnosticH1Map coarseCover hcoarse) := by
  apply AddMonoidHom.ext
  intro coarseClass
  refine Quotient.inductionOn' coarseClass ?_
  intro cocycle
  change
    (LinearMap.range
      (fine.lawGeneratedComplex laws hfine).boundaryToCycles).mkQ
        (P.actualCechDiagnosticCyclesMap fineCover hfine
          (P.actualCechPullbackCycles M cocycle)) =
    (M.generatedComparisonHom laws hcoarse hfine).h1Map
      ((LinearMap.range
        (coarse.lawGeneratedComplex laws hcoarse).boundaryToCycles).mkQ
          (P.actualCechDiagnosticCyclesMap coarseCover hcoarse cocycle))
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  apply congrArg
  apply Subtype.ext
  exact P.actualCechCoefficient1_pullback_naturality M hcoarse hfine cocycle.1

omit [Fintype Source] in
/-- The actual H1 map sends a represented coarse cocycle to its pullback. -/
@[simp]
theorem actualCechRefinementH1Map_additiveH1Class
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (cocycle : (P.faceEmptyCechComplex coarseCover).CechCocycle 1) :
    P.actualCechRefinementH1Map M
        ((P.faceEmptyCechComplex coarseCover).additiveH1Class cocycle) =
      (P.faceEmptyCechComplex fineCover).additiveH1Class
        ⟨P.actualCechPullback1 M cocycle.1, by
          rw [P.faceEmptyCech_d1_eq_zero fineCover]
          rfl⟩ :=
  rfl

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation

end GeneratorPresentation
end AAT.AG.ObstructionDiagnosticBridge
