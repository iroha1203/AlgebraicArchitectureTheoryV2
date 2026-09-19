import ResearchLean.AG.ObstructionDiagnosticBridge.FaceEmptyCechNormalization
import ResearchLean.AG.TwoPhase.CohomologyComparison
import Formal.Util.AssertStandardAxioms

/-!
# H1 map from the actual obstruction Cech complex to diagnostics

The degree-zero-through-two additive cochain map constructed for a face-empty
actual Cech source is restricted to degree-one cocycles and then descended
through degree-zero coboundaries.  The target is the existing law-generated
`ThreeCochainComplex` and its standard `H1` quotient.

## Implementation notes

The source coefficients are the integral presentation group while the target
coefficients are rational diagnostic coordinates.  The induced H1 comparison
is therefore an additive homomorphism, not a falsely asserted rational-linear
map.  A direct quotient lift is used instead of copying either H1 definition:
`actualCechCoefficient_comm1` proves preservation of cocycles and
`actualCechCoefficient_comm0` proves that source boundaries map to target
boundaries.
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

/-- Actual degree-one cocycles mapped to law-generated diagnostic cocycles. -/
def actualCechDiagnosticCyclesMap (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) :
    (P.faceEmptyCechComplex C).CechCocycleSubgroup 1 →+
      LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1 where
  toFun cocycle := ⟨P.actualCechCoefficientCochain1 C hadequate cocycle.1, by
    change D.lawGeneratedD1 laws hadequate
        (P.actualCechCoefficientCochain1 C hadequate cocycle.1) = 0
    rw [← P.actualCechCoefficient_comm1 C hadequate cocycle.1, cocycle.2]
    exact map_zero _⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' left right := by
    apply Subtype.ext
    exact map_add _ left.1 right.1

/-- A source degree-zero coboundary maps to zero in diagnostic H1. -/
theorem actualCechDiagnostic_boundary_to_zero
    (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q)
    (cochain : (P.faceEmptyCechComplex C).Cn 0) :
    (LinearMap.range
        (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ
      (P.actualCechDiagnosticCyclesMap C hadequate
        ((P.faceEmptyCechComplex C).coboundaryCocycle 0 cochain)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨P.actualCechCoefficientCochain0 C hadequate cochain, ?_⟩
  apply Subtype.ext
  exact (P.actualCechCoefficient_comm0 C hadequate cochain).symm

/-- Additive H1 map induced by the actual Cech-to-diagnostic cochain map. -/
def actualCechDiagnosticH1Map (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q) :
    (P.faceEmptyCechComplex C).AdditiveCechH1 →+
      (D.lawGeneratedComplex laws hadequate).H1 :=
  QuotientAddGroup.lift
    ((P.faceEmptyCechComplex C).CechCoboundarySubgroupSucc 0)
    ((LinearMap.range
        (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ.toAddMonoidHom.comp
      (P.actualCechDiagnosticCyclesMap C hadequate))
    (by
      intro cocycle hcocycle
      rcases hcocycle with ⟨cochain, rfl⟩
      exact P.actualCechDiagnostic_boundary_to_zero C hadequate cochain)

/-- The induced H1 map is represented by the degree-one comparison on cocycles.

The simp normal form exposes the target quotient representative.
-/
@[simp]
theorem actualCechDiagnosticH1Map_additiveH1Class
    (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) (hadequate : laws.Adequate q)
    (cocycle : (P.faceEmptyCechComplex C).CechCocycle 1) :
    P.actualCechDiagnosticH1Map C hadequate
        ((P.faceEmptyCechComplex C).additiveH1Class cocycle) =
      (LinearMap.range
          (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ
        (P.actualCechDiagnosticCyclesMap C hadequate ⟨cocycle.1, cocycle.2⟩) :=
  rfl

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation

end GeneratorPresentation
end AAT.AG.ObstructionDiagnosticBridge
