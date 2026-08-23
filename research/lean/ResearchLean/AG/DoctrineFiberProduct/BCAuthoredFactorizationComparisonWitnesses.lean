import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredFactorizationComparison
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses

/-!
# Finite firing of the universally factorized authored comparison

The existing nonempty identity-square fixture proves `CoherentAt` from its
actual path equations.  The reviewed G-106 equivalence converts that fact to
identity of the initial raw cochain, so the independently generated counit
factor and the resulting Beck--Chevalley family specialize to the canonical
mate.  No raw-defect identity certificate is stored in the fixture.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteAuthoredFactorizationAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The strict fixture satisfies the authored path equation at identity reselection. -/
theorem finiteAuthoredFactorization_coherentAt_identity :
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

/-- The reviewed G-106 theorem derives identity of the initial raw cochain. -/
theorem finiteAuthoredFactorization_initialRawDefect_eq_identity :
    initialRawDefectCochain finiteAuthoredSupportTransportData =
      identityDefectCochain finiteAuthoredSupportTransportData := by
  exact (coherentAt_iff_rawDefectCochain_eq_identity
    finiteAuthoredSupportTransportData 1).1
      finiteAuthoredFactorization_coherentAt_identity

/-- The reconstructed authored datum is the same reviewed G-106 datum. -/
theorem finiteAuthoredFactorization_toTransportData :
    finiteAuthoredBCDatumSquare.toTransportData =
      finiteAuthoredSupportTransportData := by
  rfl

/-- The attempted factorization relation fires on an actual strict authored cell. -/
theorem finiteAuthoredBCDatumSquare_attemptedFactorizationMateCoherentRel :
    AttemptedFactorizationMateCoherentRel FiniteModel.carrier
      finiteAuthoredBCDatumSquare := by
  apply attemptedFactorizationMateCoherentRel_of_initialRawDefect_eq_identity
  simpa [finiteAuthoredFactorization_toTransportData] using
    finiteAuthoredFactorization_initialRawDefect_eq_identity

/-- The strict firing has a genuine authored support object. -/
theorem finiteAuthoredFactorization_nonempty_support :
    Nonempty finiteAuthoredBCDatumSquare.context.Category :=
  finiteAuthoredSupport_nonempty

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
