import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDefectComparison
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.TransportCoherence.VanishingCoherence

/-!
# Finite firing of the defect-induced authored comparison

The existing nonempty identity-square fixture has one actual authored cell and
identity edge lifts.  Its authored comparator satisfies the independent G-106
path-factorization equation at the initial coordinate.  Consequently the raw
defect is identity and the generated authored comparison agrees with the
canonical Beck--Chevalley mate.

This is the strict positive half only.  The required lax negative fixture must
retain nonvanishing over its entire genuine reselection orbit and is not
claimed here.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteAuthoredDefectAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The identity diagnostic datum satisfies its authored path equation initially. -/
theorem finiteAuthoredSupport_coherentAt_identity :
    CoherentAt finiteAuthoredSupportTransportData 1 := by
  intro face
  cases face
  simp only [finiteAuthoredSupportTransportData,
    finiteAuthoredSupportLiftData, reselectedPathLift,
    AdmissibleLiftData.pathLift,
    finiteBCDiagnosticGeometry, finiteBCDiagnosticTwoPresentation]
  change (PackageTotalHom.id finiteAuthoredSupportPackage).comp
      (PackageFiberAut.hom
        (1 : PackageFiberAut finiteAuthoredSupportPackage)) =
    (PackageTotalHom.id finiteAuthoredSupportPackage).comp
      (PackageTotalHom.id finiteAuthoredSupportPackage)
  rw [show PackageFiberAut.hom
      (1 : PackageFiberAut finiteAuthoredSupportPackage) =
    PackageTotalHom.id finiteAuthoredSupportPackage by rfl]

/-- Hence the independent initial G-106 raw cochain is the identity cochain. -/
theorem finiteAuthoredSupport_initialRawDefect_eq_identity :
    initialRawDefectCochain finiteAuthoredSupportTransportData =
      identityDefectCochain finiteAuthoredSupportTransportData := by
  exact (coherentAt_iff_rawDefectCochain_eq_identity
    finiteAuthoredSupportTransportData 1).1
      finiteAuthoredSupport_coherentAt_identity

/-- Reconstructing the authored datum preserves the exact G-106 transport data. -/
theorem finiteAuthoredBCDatumSquare_toTransportData :
    finiteAuthoredBCDatumSquare.toTransportData =
      finiteAuthoredSupportTransportData := by
  rfl

/-- The public relative relation fires on the existing nonempty strict fixture. -/
theorem finiteAuthoredBCDatumSquare_mateCoherentRel :
    MateCoherentRel FiniteModel.carrier finiteAuthoredBCDatumSquare := by
  apply mateCoherentRel_of_initialRawDefect_eq_identity
  simpa [finiteAuthoredBCDatumSquare_toTransportData] using
    finiteAuthoredSupport_initialRawDefect_eq_identity

/-- The same fixture still exposes an actual support object. -/
theorem finiteAuthoredDefectComparison_nonempty_support :
    Nonempty finiteAuthoredBCDatumSquare.context.Category :=
  finiteAuthoredSupport_nonempty

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
