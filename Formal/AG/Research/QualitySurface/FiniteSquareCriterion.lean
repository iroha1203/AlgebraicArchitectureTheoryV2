import Formal.AG.Research.QualitySurface.ProfileTupleIntegration

/-!
Cycle 12 evidence for `G-aat-quality-surface-01`.

This file extracts a finite-square reading criterion from the earlier
profile-curvature witnesses. The criterion is relative to a chosen visible
reading and a chosen protected invariant; it does not assert global flatness or
source-observation completeness.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace FiniteSquareCriterion

open TraceLocus

universe u v

/-! ## Generic finite-square path composites -/

/-- A typed edge transport between two profile vertices. -/
structure SquareEdgeTransport {Profile : Type u}
    (CertificateAt : Profile -> Type v) (source target : Profile) where
  map : CertificateAt source -> CertificateAt target

/-- A finite square with four typed edge transports and one selected seed. -/
structure FiniteSquare (Profile : Type u)
    (CertificateAt : Profile -> Type v) where
  lowerLeft : Profile
  lowerRight : Profile
  upperLeft : Profile
  upperRight : Profile
  seed : CertificateAt lowerLeft
  lawBottom : SquareEdgeTransport CertificateAt lowerLeft lowerRight
  coverRight : SquareEdgeTransport CertificateAt lowerRight upperRight
  coverLeft : SquareEdgeTransport CertificateAt lowerLeft upperLeft
  lawTop : SquareEdgeTransport CertificateAt upperLeft upperRight

/-- A finite square remembers only the two typed path-composite endpoints. -/
structure EndpointPair (Endpoint : Type u) where
  lawFirst : Endpoint
  coverFirst : Endpoint

/-- The endpoint pair induced by the two path composites of a finite square. -/
def endpointPairOfSquare {Profile : Type u} {CertificateAt : Profile -> Type v}
    (square : FiniteSquare Profile CertificateAt) :
    EndpointPair (CertificateAt square.upperRight) where
  lawFirst := square.coverRight.map (square.lawBottom.map square.seed)
  coverFirst := square.lawTop.map (square.coverLeft.map square.seed)

/-- A visible reading and protected invariant chosen for one endpoint type. -/
structure SquareReading (Endpoint : Type u) where
  VisibleEquivalent : Endpoint -> Endpoint -> Prop
  SameProtectedInvariant : Endpoint -> Endpoint -> Prop

/-- The two endpoints are visibly flat for the selected reading. -/
def VisibleFlat {Endpoint : Type u}
    (reading : SquareReading Endpoint) (pair : EndpointPair Endpoint) : Prop :=
  reading.VisibleEquivalent pair.lawFirst pair.coverFirst

/-- The two endpoints have no holonomy for the selected protected invariant. -/
def ProtectedInvariantFlat {Endpoint : Type u}
    (reading : SquareReading Endpoint) (pair : EndpointPair Endpoint) : Prop :=
  reading.SameProtectedInvariant pair.lawFirst pair.coverFirst

/--
Reading-curvature for a chosen protected invariant: the visible endpoint pair
is flat, but the protected invariant is not.
-/
def ReadingCurved {Endpoint : Type u}
    (reading : SquareReading Endpoint) (pair : EndpointPair Endpoint) : Prop :=
  VisibleFlat reading pair ∧ ¬ ProtectedInvariantFlat reading pair

/-- The visible reading is faithful to the chosen protected invariant. -/
def VisibleFaithfulToProtected {Endpoint : Type u}
    (reading : SquareReading Endpoint) : Prop :=
  ∀ left right,
    reading.VisibleEquivalent left right ->
      reading.SameProtectedInvariant left right

/-- A protected discrepancy together with visible flatness yields reading-curvature. -/
theorem finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    {Endpoint : Type u} (reading : SquareReading Endpoint)
    (pair : EndpointPair Endpoint)
    (hvisible : VisibleFlat reading pair)
    (hprotected : ¬ ProtectedInvariantFlat reading pair) :
    ReadingCurved reading pair :=
  ⟨hvisible, hprotected⟩

/-- If the visible reading is faithful, visible flatness rules out holonomy. -/
theorem finiteSquare_no_holonomy_of_faithful_reading
    {Endpoint : Type u} (reading : SquareReading Endpoint)
    (hfaithful : VisibleFaithfulToProtected reading)
    (pair : EndpointPair Endpoint)
    (hvisible : VisibleFlat reading pair) :
    ProtectedInvariantFlat reading pair :=
  hfaithful pair.lawFirst pair.coverFirst hvisible

/-- A visibly flat square with protected discrepancy refutes visible faithfulness. -/
theorem finiteSquare_not_faithful_of_curvature
    {Endpoint : Type u} (reading : SquareReading Endpoint)
    (pair : EndpointPair Endpoint)
    (hcurved : ReadingCurved reading pair) :
    ¬ VisibleFaithfulToProtected reading := by
  intro hfaithful
  exact hcurved.2
    (finiteSquare_no_holonomy_of_faithful_reading
      reading hfaithful pair hcurved.1)

/-- The square-level version of the selected reading-curvature criterion. -/
theorem finiteSquare_curvature_of_square_visible_protected_discrepancy
    {Profile : Type u} {CertificateAt : Profile -> Type v}
    (square : FiniteSquare Profile CertificateAt)
    (reading : SquareReading (CertificateAt square.upperRight))
    (hvisible : VisibleFlat reading (endpointPairOfSquare square))
    (hprotected : ¬ ProtectedInvariantFlat reading (endpointPairOfSquare square)) :
    ReadingCurved reading (endpointPairOfSquare square) :=
  finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    reading (endpointPairOfSquare square) hvisible hprotected

/-- For a faithful reading, a finite square has no protected holonomy. -/
theorem finiteSquare_no_holonomy_of_square_faithful_reading
    {Profile : Type u} {CertificateAt : Profile -> Type v}
    (square : FiniteSquare Profile CertificateAt)
    (reading : SquareReading (CertificateAt square.upperRight))
    (hfaithful : VisibleFaithfulToProtected reading)
    (hvisible : VisibleFlat reading (endpointPairOfSquare square)) :
    ProtectedInvariantFlat reading (endpointPairOfSquare square) :=
  finiteSquare_no_holonomy_of_faithful_reading
    reading hfaithful (endpointPairOfSquare square) hvisible

/-! ## Trace-curvature square as an instance -/

abbrev TraceUpperRightEndpoint :=
  TraceCurvature.CertificateAt TraceCurvature.TraceProfile.upperRight

/-- The cycle-7 trace square as a generic finite square with typed transports. -/
def traceCurvatureSquare :
    FiniteSquare TraceCurvature.TraceProfile TraceCurvature.CertificateAt where
  lowerLeft := TraceCurvature.TraceProfile.lowerLeft
  lowerRight := TraceCurvature.TraceProfile.lowerRight
  upperLeft := TraceCurvature.TraceProfile.upperLeft
  upperRight := TraceCurvature.TraceProfile.upperRight
  seed := TraceCurvature.seedAt
  lawBottom := ⟨TraceCurvature.transportLawBottom.map⟩
  coverRight := ⟨TraceCurvature.transportCoverRight.map⟩
  coverLeft := ⟨TraceCurvature.transportCoverLeft.map⟩
  lawTop := ⟨TraceCurvature.transportLawTop.map⟩

/-- The two path-composite endpoints of the cycle-7 trace square. -/
def traceCurvatureEndpointPair : EndpointPair TraceUpperRightEndpoint where
  lawFirst := TraceCurvature.lawThenCover TraceCurvature.seedAt
  coverFirst := TraceCurvature.coverThenLaw TraceCurvature.seedAt

/-- The generic finite-square endpoints agree with the named trace path composites. -/
theorem traceCurvature_endpointPairOfSquare :
    (endpointPairOfSquare traceCurvatureSquare).lawFirst =
        traceCurvatureEndpointPair.lawFirst ∧
      (endpointPairOfSquare traceCurvatureSquare).coverFirst =
        traceCurvatureEndpointPair.coverFirst :=
  ⟨rfl, rfl⟩

/-- Visible upper-right trace surface: scalar, verdict, and support. -/
def SameTraceVisibleSurface
    (left right : TraceUpperRightEndpoint) : Prop :=
  TraceCurvature.scalarReading left.val =
      TraceCurvature.scalarReading right.val ∧
    TraceCurvature.verdict left.val =
      TraceCurvature.verdict right.val ∧
    TraceCurvature.support left.val =
      TraceCurvature.support right.val

/-- Same path-ordered trace missing locus. -/
def SameTraceMissingInvariant
    (left right : TraceUpperRightEndpoint) : Prop :=
  ∀ atom,
    TraceCurvature.traceMissingLocus left.val atom ↔
      TraceCurvature.traceMissingLocus right.val atom

/-- Same path-ordered repair frontier. -/
def SameTraceRepairInvariant
    (left right : TraceUpperRightEndpoint) : Prop :=
  ∀ atom,
    TraceCurvature.repairFrontier left.val atom ↔
      TraceCurvature.repairFrontier right.val atom

/-- Trace square reading with trace missing locus as protected invariant. -/
def traceMissingSquareReading :
    SquareReading TraceUpperRightEndpoint where
  VisibleEquivalent := SameTraceVisibleSurface
  SameProtectedInvariant := SameTraceMissingInvariant

/-- Trace square reading with repair frontier as protected invariant. -/
def traceRepairSquareReading :
    SquareReading TraceUpperRightEndpoint where
  VisibleEquivalent := SameTraceVisibleSurface
  SameProtectedInvariant := SameTraceRepairInvariant

/-- The two trace-square endpoints agree on the visible reading. -/
theorem traceCurvature_visibleFlat :
    VisibleFlat traceMissingSquareReading traceCurvatureEndpointPair :=
  ⟨TraceCurvature.same_scalar_after_trace_paths,
    TraceCurvature.same_verdict_after_trace_paths,
    TraceCurvature.same_support_after_trace_paths⟩

/-- The repair-frontier reading has the same visible-flat endpoint pair. -/
theorem traceCurvature_repair_visibleFlat :
    VisibleFlat traceRepairSquareReading traceCurvatureEndpointPair :=
  traceCurvature_visibleFlat

/-- The trace-square endpoints differ in trace missing locus. -/
theorem traceCurvature_traceMissing_discrepancy :
    ¬ ProtectedInvariantFlat
      traceMissingSquareReading traceCurvatureEndpointPair := by
  intro hsame
  have hmissingLaw :
      TraceCurvature.traceMissingLocus
        (TraceCurvature.lawThenCover TraceCurvature.seedAt).val
        LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      TraceLocus.partialTrace_database_missing_locus
  exact TraceLocus.fullTrace_has_no_missing_locus
    ⟨LocusAtom.database, hmissingLaw⟩

/-- The trace-square endpoints differ in repair frontier. -/
theorem traceCurvature_repairFrontier_discrepancy :
    ¬ ProtectedInvariantFlat
      traceRepairSquareReading traceCurvatureEndpointPair := by
  intro hsame
  have hrepairLaw :
      TraceCurvature.repairFrontier
        (TraceCurvature.lawThenCover TraceCurvature.seedAt).val
        LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      TraceCurvature.coverThenLaw_forces_database_repair
  exact TraceCurvature.lawThenCover_no_database_repair hrepairLaw

/-- Cycle-7 trace square instantiates the trace-missing criterion. -/
theorem traceCurvature_instantiates_traceMissingCriterion :
    ReadingCurved traceMissingSquareReading traceCurvatureEndpointPair :=
  finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    traceMissingSquareReading traceCurvatureEndpointPair
    traceCurvature_visibleFlat traceCurvature_traceMissing_discrepancy

/-- Cycle-7 trace square instantiates the repair-frontier criterion. -/
theorem traceCurvature_instantiates_repairFrontierCriterion :
    ReadingCurved traceRepairSquareReading traceCurvatureEndpointPair :=
  finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    traceRepairSquareReading traceCurvatureEndpointPair
    traceCurvature_repair_visibleFlat
    traceCurvature_repairFrontier_discrepancy

/--
The trace square is visibly flat but reading-curved for both trace missing
locus and repair frontier.
-/
theorem same_trace_surface_but_finiteSquareCriterion_curved :
    VisibleFlat traceMissingSquareReading traceCurvatureEndpointPair ∧
      ReadingCurved traceMissingSquareReading traceCurvatureEndpointPair ∧
      ReadingCurved traceRepairSquareReading traceCurvatureEndpointPair ∧
      ¬ VisibleFaithfulToProtected traceMissingSquareReading ∧
      ¬ VisibleFaithfulToProtected traceRepairSquareReading := by
  exact ⟨traceCurvature_visibleFlat,
    traceCurvature_instantiates_traceMissingCriterion,
    traceCurvature_instantiates_repairFrontierCriterion,
    finiteSquare_not_faithful_of_curvature
      traceMissingSquareReading traceCurvatureEndpointPair
      traceCurvature_instantiates_traceMissingCriterion,
    finiteSquare_not_faithful_of_curvature
      traceRepairSquareReading traceCurvatureEndpointPair
      traceCurvature_instantiates_repairFrontierCriterion⟩

end FiniteSquareCriterion
end QualitySurface
end Formal.AG.Research
