import Formal.AG.Research.QualitySurface.TraceCurvature

/-!
Cycle 10 evidence for `G-aat-quality-surface-01`.

This file records a finite `P_law x P_cover` 3x3 profile-grid witness. It does
not claim a global flatness criterion. It only fixes one localized
trace-curvature cell whose path-ordered trace / repair frontier survives as an
endpoint holonomy discrepancy.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace ProfileGridHolonomy

open TraceLocus

/-! ## The finite 3x3 profile grid -/

/-- Law-coordinate levels in the finite profile grid. -/
inductive LawLevel where
  | low
  | mid
  | high
  deriving DecidableEq, Fintype

/-- Cover-coordinate levels in the finite profile grid. -/
inductive CoverLevel where
  | coarse
  | middle
  | fine
  deriving DecidableEq, Fintype

open LawLevel CoverLevel

/-- A profile vertex in the `P_law x P_cover` grid. -/
abbrev GridProfile :=
  LawLevel × CoverLevel

def lowCoarse : GridProfile := (low, coarse)
def midCoarse : GridProfile := (mid, coarse)
def midMiddle : GridProfile := (mid, middle)
def highMiddle : GridProfile := (high, middle)
def midFine : GridProfile := (mid, fine)
def highFine : GridProfile := (high, fine)

/-! ## Certificates carried by the two length-4 paths -/

/--
Named certificates on the finite grid.

The two paths share the first two stages and then cross the localized upper
right elementary cell in opposite orders.
-/
inductive GridCertificateName where
  | seed
  | sharedLawStage
  | sharedCenter
  | lawFirstHighMiddle
  | coverFirstMidFine
  | lawFirstEndpoint
  | coverFirstEndpoint
  deriving DecidableEq, Fintype

open GridCertificateName

/-- The common support used by every grid certificate. -/
def gridSupport : Set LocusAtom :=
  selectedSupport

/-- Trace-complete field used outside the localized curvature endpoint. -/
def gridFullTraceField : LocusAtom -> Option LocusTraceToken :=
  fullTraceField

/-- Trace-missing field used at the cover-first endpoint. -/
def gridCurvedTraceField : LocusAtom -> Option LocusTraceToken :=
  partialTraceField

/-- The empty repair frontier for trace-complete certificates. -/
def gridEmptyRepairFrontier : Set LocusAtom :=
  fun _ => False

/-- The database repair frontier for the path-ordered trace gap. -/
def gridDatabaseRepairFrontier : Set LocusAtom :=
  databaseRepairFrontier

/-- Certificate tuple carried by a grid node on a selected path. -/
structure GridTraceCertificate where
  visibleScalarReading : Nat
  verdict : StateSeparation.StateVerdict
  support : Set LocusAtom
  traceField : LocusAtom -> Option LocusTraceToken
  repairFrontier : Set LocusAtom

/-- The lower-left seed certificate. -/
def seedTuple : GridTraceCertificate where
  visibleScalarReading := 0
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridFullTraceField
  repairFrontier := gridEmptyRepairFrontier

/-- The first shared law step, still trace complete. -/
def sharedLawStageTuple : GridTraceCertificate where
  visibleScalarReading := 1
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridFullTraceField
  repairFrontier := gridEmptyRepairFrontier

/-- The shared center of the 3x3 grid, still trace complete. -/
def sharedCenterTuple : GridTraceCertificate where
  visibleScalarReading := 2
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridFullTraceField
  repairFrontier := gridEmptyRepairFrontier

/-- Law-first side of the localized upper-right cell. -/
def lawFirstHighMiddleTuple : GridTraceCertificate where
  visibleScalarReading := 3
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridFullTraceField
  repairFrontier := gridEmptyRepairFrontier

/-- Cover-first side of the localized upper-right cell. -/
def coverFirstMidFineTuple : GridTraceCertificate where
  visibleScalarReading := 3
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridFullTraceField
  repairFrontier := gridEmptyRepairFrontier

/-- Endpoint reached by taking law before cover in the localized cell. -/
def lawFirstEndpointTuple : GridTraceCertificate where
  visibleScalarReading := 4
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridFullTraceField
  repairFrontier := gridEmptyRepairFrontier

/-- Endpoint reached by taking cover before law in the localized cell. -/
def coverFirstEndpointTuple : GridTraceCertificate where
  visibleScalarReading := 4
  verdict := StateSeparation.StateVerdict.acceptable
  support := gridSupport
  traceField := gridCurvedTraceField
  repairFrontier := gridDatabaseRepairFrontier

/-- Read the tuple carried by a named grid certificate. -/
def gridTuple : GridCertificateName -> GridTraceCertificate
  | seed => seedTuple
  | sharedLawStage => sharedLawStageTuple
  | sharedCenter => sharedCenterTuple
  | lawFirstHighMiddle => lawFirstHighMiddleTuple
  | coverFirstMidFine => coverFirstMidFineTuple
  | lawFirstEndpoint => lawFirstEndpointTuple
  | coverFirstEndpoint => coverFirstEndpointTuple

/-- The grid vertex where each named certificate lives. -/
def profileOf : GridCertificateName -> GridProfile
  | seed => lowCoarse
  | sharedLawStage => midCoarse
  | sharedCenter => midMiddle
  | lawFirstHighMiddle => highMiddle
  | coverFirstMidFine => midFine
  | lawFirstEndpoint => highFine
  | coverFirstEndpoint => highFine

/-- Certificates typed by the grid profile where they live. -/
def CertificateAt (p : GridProfile) : Type :=
  { c : GridCertificateName // profileOf c = p }

/-- The selected lower-left certificate. -/
def seedAt : CertificateAt lowCoarse :=
  ⟨seed, rfl⟩

/-! ## Typed grid edge transports and two length-4 paths -/

/-- A typed edge transport on the finite grid. -/
structure EdgeTransport (source target : GridProfile) where
  map : CertificateAt source -> CertificateAt target

/-- First common step: increase law from low to mid at coarse cover. -/
def transportLawLowToMid :
    EdgeTransport lowCoarse midCoarse where
  map := fun _ => ⟨sharedLawStage, rfl⟩

/-- Second common step: refine cover from coarse to middle at mid law. -/
def transportCoverCoarseToMiddle :
    EdgeTransport midCoarse midMiddle where
  map := fun _ => ⟨sharedCenter, rfl⟩

/-- Localized cell, law-first branch: increase law from mid to high. -/
def transportLawMiddleToHigh :
    EdgeTransport midMiddle highMiddle where
  map := fun _ => ⟨lawFirstHighMiddle, rfl⟩

/-- Localized cell, law-first branch: refine cover from middle to fine. -/
def transportCoverMiddleToFineAfterLaw :
    EdgeTransport highMiddle highFine where
  map := fun _ => ⟨lawFirstEndpoint, rfl⟩

/-- Localized cell, cover-first branch: refine cover from middle to fine. -/
def transportCoverMiddleToFine :
    EdgeTransport midMiddle midFine where
  map := fun _ => ⟨coverFirstMidFine, rfl⟩

/-- Localized cell, cover-first branch: increase law from mid to high. -/
def transportLawMiddleToHighAfterCover :
    EdgeTransport midFine highFine where
  map := fun _ => ⟨coverFirstEndpoint, rfl⟩

/-- The first shared intermediate vertex on both paths. -/
def commonLawStage
    (c : CertificateAt lowCoarse) : CertificateAt midCoarse :=
  transportLawLowToMid.map c

/-- The shared center vertex on both paths. -/
def commonCenter
    (c : CertificateAt lowCoarse) : CertificateAt midMiddle :=
  transportCoverCoarseToMiddle.map (commonLawStage c)

/-- The law-first path's fourth vertex, before the endpoint. -/
def lawFirstBeforeEndpoint
    (c : CertificateAt lowCoarse) : CertificateAt highMiddle :=
  transportLawMiddleToHigh.map (commonCenter c)

/-- The cover-first path's fourth vertex, before the endpoint. -/
def coverFirstBeforeEndpoint
    (c : CertificateAt lowCoarse) : CertificateAt midFine :=
  transportCoverMiddleToFine.map (commonCenter c)

/-- The length-4 path that takes law before cover in the localized cell. -/
def lawFirstPath
    (c : CertificateAt lowCoarse) : CertificateAt highFine :=
  transportCoverMiddleToFineAfterLaw.map (lawFirstBeforeEndpoint c)

/-- The length-4 path that takes cover before law in the localized cell. -/
def coverFirstPath
    (c : CertificateAt lowCoarse) : CertificateAt highFine :=
  transportLawMiddleToHighAfterCover.map (coverFirstBeforeEndpoint c)

/-- The law-first path uses the shared middle grid vertices and the high-middle vertex. -/
theorem lawFirst_uses_middle_grid_vertices :
    (commonLawStage seedAt).val = sharedLawStage ∧
      (commonCenter seedAt).val = sharedCenter ∧
      (lawFirstBeforeEndpoint seedAt).val = lawFirstHighMiddle ∧
      (lawFirstPath seedAt).val = lawFirstEndpoint :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The cover-first path uses the shared middle grid vertices and the mid-fine vertex. -/
theorem coverFirst_uses_middle_grid_vertices :
    (commonLawStage seedAt).val = sharedLawStage ∧
      (commonCenter seedAt).val = sharedCenter ∧
      (coverFirstBeforeEndpoint seedAt).val = coverFirstMidFine ∧
      (coverFirstPath seedAt).val = coverFirstEndpoint :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The law-first path reaches the high/fine endpoint. -/
theorem lawFirst_path_endpoint :
    (lawFirstPath seedAt).property = rfl :=
  rfl

/-- The cover-first path reaches the high/fine endpoint. -/
theorem coverFirst_path_endpoint :
    (coverFirstPath seedAt).property = rfl :=
  rfl

/-! ## Endpoint readings, trace loci, and repair frontiers -/

/-- Visible scalar reading of a grid certificate. -/
def scalarReading (c : GridCertificateName) : Nat :=
  (gridTuple c).visibleScalarReading

/-- Selected verdict of a grid certificate. -/
def verdict (c : GridCertificateName) : StateSeparation.StateVerdict :=
  (gridTuple c).verdict

/-- Selected support of a grid certificate. -/
def support (c : GridCertificateName) : Set LocusAtom :=
  (gridTuple c).support

/-- Trace missing locus of a grid certificate. -/
def traceMissingLocus (c : GridCertificateName) : Set LocusAtom :=
  fun atom => support c atom ∧ (gridTuple c).traceField atom = none

/-- Repair frontier of a grid certificate. -/
def repairFrontier (c : GridCertificateName) : Set LocusAtom :=
  (gridTuple c).repairFrontier

/-- Endpoint scalar, verdict, and support agree along the two length-4 paths. -/
theorem gridHolonomy_visibleAgreement :
    scalarReading (lawFirstPath seedAt).val =
        scalarReading (coverFirstPath seedAt).val ∧
      verdict (lawFirstPath seedAt).val =
        verdict (coverFirstPath seedAt).val ∧
      support (lawFirstPath seedAt).val =
        support (coverFirstPath seedAt).val :=
  ⟨rfl, rfl, rfl⟩

/-- The law-first endpoint remains trace complete. -/
theorem lawFirst_trace_available_at_endpoint :
    TraceTransport.TraceAvailableOn
      (support (lawFirstPath seedAt).val)
      (gridTuple (lawFirstPath seedAt).val).traceField :=
  TraceLocus.fullTrace_available_on_support

/-- The cover-first endpoint has a missing database trace. -/
theorem coverFirst_trace_missing_at_endpoint :
    TraceTransport.TraceMissingOn
      (support (coverFirstPath seedAt).val)
      (gridTuple (coverFirstPath seedAt).val).traceField :=
  TraceLocus.partialTrace_missing_on_support

/-- The law-first endpoint has no database repair frontier. -/
theorem lawFirst_no_database_repair_at_endpoint :
    ¬ repairFrontier (lawFirstPath seedAt).val LocusAtom.database :=
  TraceLocus.fullTrace_repair_frontier_excludes_database

/-- The cover-first endpoint forces the database repair frontier. -/
theorem coverFirst_forces_database_repair_at_endpoint :
    repairFrontier (coverFirstPath seedAt).val LocusAtom.database :=
  TraceLocus.partialTrace_forces_database_repair

/-- The cover-first endpoint repair frontier is exactly its missing trace locus. -/
theorem coverFirst_repair_frontier_matches_missing_locus :
    ∀ atom,
      repairFrontier (coverFirstPath seedAt).val atom ↔
        traceMissingLocus (coverFirstPath seedAt).val atom :=
  TraceLocus.partialTrace_repair_frontier_matches_missing_locus

/-! ## Localized curvature and surrounding preservation -/

/--
Surrounding steps in the 3x3 grid preserve the trace frontier; the trace gap is
not introduced by the common prefix or by either branch before the endpoint.
-/
theorem surrounding_steps_preserve_trace_frontier :
    TraceTransport.TraceAvailableOn
        (support (commonLawStage seedAt).val)
        (gridTuple (commonLawStage seedAt).val).traceField ∧
      TraceTransport.TraceAvailableOn
        (support (commonCenter seedAt).val)
        (gridTuple (commonCenter seedAt).val).traceField ∧
      TraceTransport.TraceAvailableOn
        (support (lawFirstBeforeEndpoint seedAt).val)
        (gridTuple (lawFirstBeforeEndpoint seedAt).val).traceField ∧
      TraceTransport.TraceAvailableOn
        (support (coverFirstBeforeEndpoint seedAt).val)
        (gridTuple (coverFirstBeforeEndpoint seedAt).val).traceField ∧
      TraceTransport.TraceAvailableOn
        (support (lawFirstPath seedAt).val)
        (gridTuple (lawFirstPath seedAt).val).traceField ∧
      ¬ repairFrontier (commonLawStage seedAt).val LocusAtom.database ∧
      ¬ repairFrontier (commonCenter seedAt).val LocusAtom.database ∧
      ¬ repairFrontier (lawFirstBeforeEndpoint seedAt).val LocusAtom.database ∧
      ¬ repairFrontier (coverFirstBeforeEndpoint seedAt).val LocusAtom.database ∧
      ¬ repairFrontier (lawFirstPath seedAt).val LocusAtom.database := by
  exact ⟨TraceLocus.fullTrace_available_on_support,
    TraceLocus.fullTrace_available_on_support,
    TraceLocus.fullTrace_available_on_support,
    TraceLocus.fullTrace_available_on_support,
    lawFirst_trace_available_at_endpoint,
    TraceLocus.fullTrace_repair_frontier_excludes_database,
    TraceLocus.fullTrace_repair_frontier_excludes_database,
    TraceLocus.fullTrace_repair_frontier_excludes_database,
    TraceLocus.fullTrace_repair_frontier_excludes_database,
    lawFirst_no_database_repair_at_endpoint⟩

/-- The localized upper-right elementary cell is trace-curved. -/
def LocalizedCurvatureCell : Prop :=
  scalarReading (lawFirstPath seedAt).val =
      scalarReading (coverFirstPath seedAt).val ∧
    verdict (lawFirstPath seedAt).val =
      verdict (coverFirstPath seedAt).val ∧
    support (lawFirstPath seedAt).val =
      support (coverFirstPath seedAt).val ∧
    TraceTransport.TraceAvailableOn
      (support (lawFirstPath seedAt).val)
      (gridTuple (lawFirstPath seedAt).val).traceField ∧
    TraceTransport.TraceMissingOn
      (support (coverFirstPath seedAt).val)
      (gridTuple (coverFirstPath seedAt).val).traceField ∧
    ¬ repairFrontier (lawFirstPath seedAt).val LocusAtom.database ∧
    repairFrontier (coverFirstPath seedAt).val LocusAtom.database ∧
    (∀ atom,
      repairFrontier (coverFirstPath seedAt).val atom ↔
        traceMissingLocus (coverFirstPath seedAt).val atom)

/-- The localized upper-right cell generates the path-ordered trace discrepancy. -/
theorem localized_curvature_cell :
    LocalizedCurvatureCell := by
  exact ⟨gridHolonomy_visibleAgreement.1,
    gridHolonomy_visibleAgreement.2.1,
    gridHolonomy_visibleAgreement.2.2,
    lawFirst_trace_available_at_endpoint,
    coverFirst_trace_missing_at_endpoint,
    lawFirst_no_database_repair_at_endpoint,
    coverFirst_forces_database_repair_at_endpoint,
    coverFirst_repair_frontier_matches_missing_locus⟩

/-! ## Endpoint-only reading is not path-holonomy faithful -/

/-- Endpoint-surface faithfulness to the path-ordered trace missing locus. -/
def EndpointSurfaceFaithfulToTraceLocus : Prop :=
  ∀ c₁ c₂ : CertificateAt highFine,
    scalarReading c₁.val = scalarReading c₂.val ->
      verdict c₁.val = verdict c₂.val ->
        support c₁.val = support c₂.val ->
          ∀ atom,
            traceMissingLocus c₁.val atom ↔ traceMissingLocus c₂.val atom

/-- Endpoint-surface faithfulness to the path-ordered repair frontier. -/
def EndpointSurfaceFaithfulToGridRepairFrontier : Prop :=
  ∀ c₁ c₂ : CertificateAt highFine,
    scalarReading c₁.val = scalarReading c₂.val ->
      verdict c₁.val = verdict c₂.val ->
        support c₁.val = support c₂.val ->
          ∀ atom,
            repairFrontier c₁.val atom ↔ repairFrontier c₂.val atom

/-- Endpoint-only reading cannot recover the path-ordered trace locus. -/
theorem endpointSurface_not_faithful_to_gridTraceLocus :
    ¬ EndpointSurfaceFaithfulToTraceLocus := by
  intro hfaithful
  have hiff :=
    hfaithful (lawFirstPath seedAt) (coverFirstPath seedAt)
      rfl rfl rfl LocusAtom.database
  have hmissingLawFirst :
      traceMissingLocus (lawFirstPath seedAt).val LocusAtom.database :=
    hiff.mpr TraceLocus.partialTrace_database_missing_locus
  exact TraceLocus.fullTrace_has_no_missing_locus
    ⟨LocusAtom.database, hmissingLawFirst⟩

/-- Endpoint-only reading cannot recover the path-ordered repair frontier. -/
theorem endpointSurface_not_faithful_to_gridRepairFrontier :
    ¬ EndpointSurfaceFaithfulToGridRepairFrontier := by
  intro hfaithful
  have hiff :=
    hfaithful (lawFirstPath seedAt) (coverFirstPath seedAt)
      rfl rfl rfl LocusAtom.database
  have hrepairLawFirst :
      repairFrontier (lawFirstPath seedAt).val LocusAtom.database :=
    hiff.mpr coverFirst_forces_database_repair_at_endpoint
  exact lawFirst_no_database_repair_at_endpoint hrepairLawFirst

/--
Cycle-10 witness: a localized trace-curvature cell in a 3x3 grid survives as
endpoint path holonomy, even though endpoint scalar, verdict, and support agree.
-/
theorem same_grid_surface_but_path_ordered_frontier_diff :
    (commonLawStage seedAt).val = sharedLawStage ∧
      (commonCenter seedAt).val = sharedCenter ∧
      (lawFirstBeforeEndpoint seedAt).val = lawFirstHighMiddle ∧
      (coverFirstBeforeEndpoint seedAt).val = coverFirstMidFine ∧
      (lawFirstPath seedAt).val = lawFirstEndpoint ∧
      (coverFirstPath seedAt).val = coverFirstEndpoint ∧
      scalarReading (lawFirstPath seedAt).val =
        scalarReading (coverFirstPath seedAt).val ∧
      verdict (lawFirstPath seedAt).val =
        verdict (coverFirstPath seedAt).val ∧
      support (lawFirstPath seedAt).val =
        support (coverFirstPath seedAt).val ∧
      LocalizedCurvatureCell ∧
      ¬ repairFrontier (lawFirstPath seedAt).val LocusAtom.database ∧
      repairFrontier (coverFirstPath seedAt).val LocusAtom.database ∧
      (∀ atom,
        repairFrontier (coverFirstPath seedAt).val atom ↔
          traceMissingLocus (coverFirstPath seedAt).val atom) ∧
      ¬ EndpointSurfaceFaithfulToTraceLocus ∧
      ¬ EndpointSurfaceFaithfulToGridRepairFrontier := by
  exact ⟨lawFirst_uses_middle_grid_vertices.1,
    lawFirst_uses_middle_grid_vertices.2.1,
    lawFirst_uses_middle_grid_vertices.2.2.1,
    coverFirst_uses_middle_grid_vertices.2.2.1,
    lawFirst_uses_middle_grid_vertices.2.2.2,
    coverFirst_uses_middle_grid_vertices.2.2.2,
    gridHolonomy_visibleAgreement.1,
    gridHolonomy_visibleAgreement.2.1,
    gridHolonomy_visibleAgreement.2.2,
    localized_curvature_cell,
    lawFirst_no_database_repair_at_endpoint,
    coverFirst_forces_database_repair_at_endpoint,
    coverFirst_repair_frontier_matches_missing_locus,
    endpointSurface_not_faithful_to_gridTraceLocus,
    endpointSurface_not_faithful_to_gridRepairFrontier⟩

end ProfileGridHolonomy
end QualitySurface
end Formal.AG.Research
