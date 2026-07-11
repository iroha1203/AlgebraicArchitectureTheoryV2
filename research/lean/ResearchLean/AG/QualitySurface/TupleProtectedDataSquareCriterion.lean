import ResearchLean.AG.QualitySurface.FiniteSquareCriterion
import ResearchLean.AG.QualitySurface.ProfileTupleIntegration

/-!
Cycle 18 evidence for `G-aat-quality-surface-01`.

This file instantiates the generic finite-square criterion with the central
profile tuple's protected data. The square is selected and finite: its tuple
edge transports follow the underlying `ProfileGridHolonomy` path transports and
only then choose the tuple fields carried by the finite witness. It does not
assert a global tuple transport, global flatness, source extraction
completeness, ArchMap correctness, or whole-codebase traceability.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace TupleProtectedDataSquareCriterion

/-! ## A selected tuple square over the finite grid -/

abbrev TupleProtectedEndpoint :=
  ProfileTupleIntegration.TupleCertificateAt
    ProfileTupleIntegration.endpointProfile

/-- The selected lower-left tuple seed of the finite grid. -/
def tupleSeed :
    ProfileTupleIntegration.TupleCertificateAt ProfileGridHolonomy.lowCoarse where
  gridCertificate := ProfileGridHolonomy.seedAt
  sigma := 0
  omega := StateSeparation.ObligationKind.none
  selectedSupport := TraceLocus.selectedSupport
  repairFrontier := fun _ => False
  nu := StateSeparation.StateVerdict.acceptable
  traceField := TraceLocus.fullTraceField

/-- Tuple law-first branch transport to the high/middle grid vertex. -/
def tupleLawFirstTransport :
    FiniteSquareCriterion.SquareEdgeTransport
      ProfileTupleIntegration.TupleCertificateAt
      ProfileGridHolonomy.lowCoarse ProfileGridHolonomy.highMiddle where
  map := fun c =>
    { gridCertificate :=
        ProfileGridHolonomy.lawFirstBeforeEndpoint c.gridCertificate
      sigma := 3
      omega := StateSeparation.ObligationKind.none
      selectedSupport := TraceLocus.selectedSupport
      repairFrontier := fun _ => False
      nu := StateSeparation.StateVerdict.acceptable
      traceField := TraceLocus.fullTraceField }

/-- Tuple law-first endpoint transport to the high/fine grid vertex. -/
def tupleLawFirstEndpointTransport :
    FiniteSquareCriterion.SquareEdgeTransport
      ProfileTupleIntegration.TupleCertificateAt
      ProfileGridHolonomy.highMiddle ProfileGridHolonomy.highFine where
  map := fun c =>
    { gridCertificate :=
        ProfileGridHolonomy.transportCoverMiddleToFineAfterLaw.map
          c.gridCertificate
      sigma := 4
      omega := StateSeparation.ObligationKind.none
      selectedSupport := TraceLocus.selectedSupport
      repairFrontier := fun _ => False
      nu := StateSeparation.StateVerdict.acceptable
      traceField := TraceLocus.fullTraceField }

/-- Tuple cover-first branch transport to the mid/fine grid vertex. -/
def tupleCoverFirstTransport :
    FiniteSquareCriterion.SquareEdgeTransport
      ProfileTupleIntegration.TupleCertificateAt
      ProfileGridHolonomy.lowCoarse ProfileGridHolonomy.midFine where
  map := fun c =>
    { gridCertificate :=
        ProfileGridHolonomy.coverFirstBeforeEndpoint c.gridCertificate
      sigma := 3
      omega := StateSeparation.ObligationKind.none
      selectedSupport := TraceLocus.selectedSupport
      repairFrontier := fun _ => False
      nu := StateSeparation.StateVerdict.acceptable
      traceField := TraceLocus.fullTraceField }

/-- Tuple cover-first endpoint transport to the high/fine grid vertex. -/
def tupleCoverFirstEndpointTransport :
    FiniteSquareCriterion.SquareEdgeTransport
      ProfileTupleIntegration.TupleCertificateAt
      ProfileGridHolonomy.midFine ProfileGridHolonomy.highFine where
  map := fun c =>
    { gridCertificate :=
        ProfileGridHolonomy.transportLawMiddleToHighAfterCover.map
          c.gridCertificate
      sigma := 4
      omega := StateSeparation.ObligationKind.provideTrace
      selectedSupport := TraceLocus.selectedSupport
      repairFrontier := TraceLocus.databaseRepairFrontier
      nu := StateSeparation.StateVerdict.acceptable
      traceField := TraceLocus.partialTraceField }

/-- The selected finite square whose endpoints are the two tuple witnesses. -/
def tupleProtectedDataSquare :
    FiniteSquareCriterion.FiniteSquare
      ProfileTupleIntegration.TupleProfile
      ProfileTupleIntegration.TupleCertificateAt where
  lowerLeft := ProfileGridHolonomy.lowCoarse
  lowerRight := ProfileGridHolonomy.highMiddle
  upperLeft := ProfileGridHolonomy.midFine
  upperRight := ProfileGridHolonomy.highFine
  seed := tupleSeed
  lawBottom := tupleLawFirstTransport
  coverRight := tupleLawFirstEndpointTransport
  coverLeft := tupleCoverFirstTransport
  lawTop := tupleCoverFirstEndpointTransport

/-- The named endpoint pair of the selected tuple square. -/
def tupleProtectedDataEndpointPair :
    FiniteSquareCriterion.EndpointPair TupleProtectedEndpoint where
  lawFirst := ProfileTupleIntegration.fullEndpointTuple
  coverFirst := ProfileTupleIntegration.traceMissingEndpointTuple

/-- Generic finite-square endpoints agree with the named tuple endpoints. -/
theorem tupleProtectedData_endpointPairOfSquare :
    (FiniteSquareCriterion.endpointPairOfSquare
        tupleProtectedDataSquare).lawFirst =
        tupleProtectedDataEndpointPair.lawFirst ∧
      (FiniteSquareCriterion.endpointPairOfSquare
        tupleProtectedDataSquare).coverFirst =
        tupleProtectedDataEndpointPair.coverFirst :=
  ⟨rfl, rfl⟩

/--
The selected tuple square follows the underlying `ProfileGridHolonomy` path
transports on its grid-certificate component.
-/
theorem tupleProtectedData_square_gridCompatible :
    (tupleProtectedDataSquare.lawBottom.map
        tupleProtectedDataSquare.seed).gridCertificate =
        ProfileGridHolonomy.lawFirstBeforeEndpoint
          ProfileGridHolonomy.seedAt ∧
      (tupleProtectedDataSquare.coverRight.map
        (tupleProtectedDataSquare.lawBottom.map
          tupleProtectedDataSquare.seed)).gridCertificate =
        ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt ∧
      (tupleProtectedDataSquare.coverLeft.map
        tupleProtectedDataSquare.seed).gridCertificate =
        ProfileGridHolonomy.coverFirstBeforeEndpoint
          ProfileGridHolonomy.seedAt ∧
      (tupleProtectedDataSquare.lawTop.map
        (tupleProtectedDataSquare.coverLeft.map
          tupleProtectedDataSquare.seed)).gridCertificate =
        ProfileGridHolonomy.coverFirstPath ProfileGridHolonomy.seedAt :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Tuple visible surface and protected-data reading -/

/-- Visible tuple surface: scalar, verdict, and selected support. -/
def SameTupleVisibleSurfaceReading
    (left right : TupleProtectedEndpoint) : Prop :=
  ProfileTupleIntegration.SameTupleVisibleSurface left right

/-- Protected tuple data: obstruction/obligation, repair frontier, and trace field. -/
def SameTupleProtectedDataInvariant
    (left right : TupleProtectedEndpoint) : Prop :=
  ProfileTupleIntegration.SameTupleProtectedData left right

/-- Square reading that hides tuple protected data behind the visible surface. -/
def tupleProtectedDataSquareReading :
    FiniteSquareCriterion.SquareReading TupleProtectedEndpoint where
  VisibleEquivalent := SameTupleVisibleSurfaceReading
  SameProtectedInvariant := SameTupleProtectedDataInvariant

/-- The two selected endpoints agree on the visible tuple surface. -/
theorem tupleProtectedData_visibleFlat :
    FiniteSquareCriterion.VisibleFlat
      tupleProtectedDataSquareReading tupleProtectedDataEndpointPair :=
  ProfileTupleIntegration.endpointTuple_visibleAgreement

/-- The selected square is visibly flat for the tuple surface reading. -/
theorem tupleProtectedData_square_visibleFlat :
    FiniteSquareCriterion.VisibleFlat
      tupleProtectedDataSquareReading
      (FiniteSquareCriterion.endpointPairOfSquare tupleProtectedDataSquare) :=
  ProfileTupleIntegration.endpointTuple_visibleAgreement

/-- The two endpoints differ in the obligation component of protected tuple data. -/
theorem tupleProtectedData_omega_discrepancy :
    tupleProtectedDataEndpointPair.lawFirst.omega ≠
      tupleProtectedDataEndpointPair.coverFirst.omega :=
  ProfileTupleIntegration.endpointTuple_omega_diff

/-- The two endpoints differ in the repair-frontier component. -/
theorem tupleProtectedData_repairFrontier_discrepancy :
    ¬ ProfileTupleIntegration.SameTupleRepairFrontier
      tupleProtectedDataEndpointPair.lawFirst
      tupleProtectedDataEndpointPair.coverFirst :=
  ProfileTupleIntegration.endpointTuple_repairFrontier_diff

/-- The two endpoints differ in the trace-field component. -/
theorem tupleProtectedData_traceField_discrepancy :
    ¬ ProfileTupleIntegration.SameTupleTraceField
      tupleProtectedDataEndpointPair.lawFirst
      tupleProtectedDataEndpointPair.coverFirst :=
  ProfileTupleIntegration.endpointTuple_traceField_diff

/-- The two selected endpoints differ in protected tuple data. -/
theorem tupleProtectedData_discrepancy :
    ¬ FiniteSquareCriterion.ProtectedInvariantFlat
      tupleProtectedDataSquareReading tupleProtectedDataEndpointPair :=
  ProfileTupleIntegration.endpointTuple_protectedData_diff

/-- The selected square differs in protected tuple data. -/
theorem tupleProtectedData_square_discrepancy :
    ¬ FiniteSquareCriterion.ProtectedInvariantFlat
      tupleProtectedDataSquareReading
      (FiniteSquareCriterion.endpointPairOfSquare tupleProtectedDataSquare) :=
  ProfileTupleIntegration.endpointTuple_protectedData_diff

/--
The selected tuple square instantiates the generic finite-square
protected-data curvature criterion.
-/
theorem tupleProtectedData_instantiates_finiteSquareCriterion :
    FiniteSquareCriterion.ReadingCurved
      tupleProtectedDataSquareReading
      (FiniteSquareCriterion.endpointPairOfSquare tupleProtectedDataSquare) :=
  FiniteSquareCriterion.finiteSquare_curvature_of_square_visible_protected_discrepancy
    tupleProtectedDataSquare
    tupleProtectedDataSquareReading
    tupleProtectedData_square_visibleFlat
    tupleProtectedData_square_discrepancy

/-- The visible tuple surface is not faithful to protected tuple data. -/
theorem tupleProtectedData_no_visibleFaithfulness :
    ¬ FiniteSquareCriterion.VisibleFaithfulToProtected
      tupleProtectedDataSquareReading :=
  FiniteSquareCriterion.finiteSquare_not_faithful_of_curvature
    tupleProtectedDataSquareReading
    (FiniteSquareCriterion.endpointPairOfSquare tupleProtectedDataSquare)
    tupleProtectedData_instantiates_finiteSquareCriterion

/--
Cycle-18 theorem package: the selected tuple square is visibly flat for the
tuple surface, follows the underlying grid transports, but is curved for
protected tuple data.
-/
theorem same_tuple_surface_but_protectedDataSquare_curved :
    FiniteSquareCriterion.VisibleFlat
        tupleProtectedDataSquareReading
        (FiniteSquareCriterion.endpointPairOfSquare tupleProtectedDataSquare) ∧
      (tupleProtectedDataSquare.lawBottom.map
          tupleProtectedDataSquare.seed).gridCertificate =
          ProfileGridHolonomy.lawFirstBeforeEndpoint
            ProfileGridHolonomy.seedAt ∧
      (tupleProtectedDataSquare.coverRight.map
        (tupleProtectedDataSquare.lawBottom.map
          tupleProtectedDataSquare.seed)).gridCertificate =
          ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt ∧
      (tupleProtectedDataSquare.coverLeft.map
          tupleProtectedDataSquare.seed).gridCertificate =
          ProfileGridHolonomy.coverFirstBeforeEndpoint
            ProfileGridHolonomy.seedAt ∧
      (tupleProtectedDataSquare.lawTop.map
        (tupleProtectedDataSquare.coverLeft.map
          tupleProtectedDataSquare.seed)).gridCertificate =
          ProfileGridHolonomy.coverFirstPath ProfileGridHolonomy.seedAt ∧
      tupleProtectedDataEndpointPair.lawFirst.omega ≠
        tupleProtectedDataEndpointPair.coverFirst.omega ∧
      ¬ ProfileTupleIntegration.SameTupleRepairFrontier
        tupleProtectedDataEndpointPair.lawFirst
        tupleProtectedDataEndpointPair.coverFirst ∧
      ¬ ProfileTupleIntegration.SameTupleTraceField
        tupleProtectedDataEndpointPair.lawFirst
        tupleProtectedDataEndpointPair.coverFirst ∧
      FiniteSquareCriterion.ReadingCurved
        tupleProtectedDataSquareReading
        (FiniteSquareCriterion.endpointPairOfSquare tupleProtectedDataSquare) ∧
      ¬ FiniteSquareCriterion.VisibleFaithfulToProtected
        tupleProtectedDataSquareReading :=
  by
    exact ⟨tupleProtectedData_square_visibleFlat,
    tupleProtectedData_square_gridCompatible.1,
    tupleProtectedData_square_gridCompatible.2.1,
    tupleProtectedData_square_gridCompatible.2.2.1,
    tupleProtectedData_square_gridCompatible.2.2.2,
    tupleProtectedData_omega_discrepancy,
    tupleProtectedData_repairFrontier_discrepancy,
    tupleProtectedData_traceField_discrepancy,
    tupleProtectedData_instantiates_finiteSquareCriterion,
    tupleProtectedData_no_visibleFaithfulness⟩

end TupleProtectedDataSquareCriterion
end QualitySurface
end ResearchLean.AG
