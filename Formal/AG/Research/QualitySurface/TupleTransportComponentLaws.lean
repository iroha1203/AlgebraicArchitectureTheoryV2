import Formal.AG.Research.QualitySurface.TupleTransportExactness

/-!
Cycle 19 evidence for `G-aat-quality-surface-01`.

This file gives finite independence witnesses for tuple-transport component
laws. The witnesses are relative to supplied finite tuple transports. They do
not assert a global minimality classification, canonical tuple transport,
source extraction completeness, ArchMap correctness, or whole-codebase
traceability.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace TupleTransportComponentLaws

open TraceLocus
open StateSeparation
open TupleTransportExactness

abbrev EndpointTuple :=
  ProfileTupleIntegration.TupleCertificateAt
    ProfileTupleIntegration.endpointProfile

/-! ## Readings preserved by the finite witnesses -/

/-- Same scalar and verdict, without selected-support equality. -/
def SameTupleScalarVerdict (left right : EndpointTuple) : Prop :=
  left.sigma = right.sigma ∧ left.nu = right.nu

/-- A transport preserves the full visible tuple surface. -/
def PreservesVisibleTupleSurface
    (τ : TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile) : Prop :=
  ∀ c, ProfileTupleIntegration.SameTupleVisibleSurface c (τ.map c)

/-- A transport preserves only scalar and verdict. -/
def PreservesScalarVerdict
    (τ : TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile) : Prop :=
  ∀ c, SameTupleScalarVerdict c (τ.map c)

/-! ## Component-editing transports -/

/-- Erase the database trace token while leaving the other atoms unchanged. -/
def eraseDatabaseTrace
    (field : LocusAtom -> Option LocusTraceToken) :
    LocusAtom -> Option LocusTraceToken
  | LocusAtom.api => field LocusAtom.api
  | LocusAtom.database => none
  | LocusAtom.queue => field LocusAtom.queue

/-- Fill the database trace token while leaving the other atoms unchanged. -/
def fillDatabaseTrace
    (field : LocusAtom -> Option LocusTraceToken) :
    LocusAtom -> Option LocusTraceToken
  | LocusAtom.api => field LocusAtom.api
  | LocusAtom.database => some LocusTraceToken.refDatabase
  | LocusAtom.queue => field LocusAtom.queue

/-- Transport that creates an extra missing trace at the database atom. -/
def traceErasingTransport :
    TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile where
  map := fun c =>
    { gridCertificate := c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := c.selectedSupport
      repairFrontier := c.repairFrontier
      nu := c.nu
      traceField := eraseDatabaseTrace c.traceField }

/-- Transport that fills a missing database trace token. -/
def traceCreatingTransport :
    TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile where
  map := fun c =>
    { gridCertificate := c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := c.selectedSupport
      repairFrontier := c.repairFrontier
      nu := c.nu
      traceField := fillDatabaseTrace c.traceField }

/-- Transport that removes every repair frontier atom. -/
def repairErasingTransport :
    TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile where
  map := fun c =>
    { gridCertificate := c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := c.selectedSupport
      repairFrontier := fun _ => False
      nu := c.nu
      traceField := c.traceField }

/-- Transport that adds the database atom to the repair frontier. -/
def repairCreatingTransport :
    TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile where
  map := fun c =>
    { gridCertificate := c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := c.selectedSupport
      repairFrontier := fun atom =>
        c.repairFrontier atom ∨ atom = LocusAtom.database
      nu := c.nu
      traceField := c.traceField }

/-- Transport that drops the selected support entirely. -/
def supportDroppingTransport :
    TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile where
  map := fun c =>
    { gridCertificate := c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := fun _ => False
      repairFrontier := c.repairFrontier
      nu := c.nu
      traceField := c.traceField }

/-- Transport that expands the selected support to every finite locus atom. -/
def supportExpandingTransport :
    TupleTransport
      ProfileTupleIntegration.endpointProfile
      ProfileTupleIntegration.endpointProfile where
  map := fun c =>
    { gridCertificate := c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := fun _ => True
      repairFrontier := c.repairFrontier
      nu := c.nu
      traceField := c.traceField }

/-- Endpoint tuple with empty support and a partial trace field. -/
def emptySupportPartialEndpointTuple : EndpointTuple where
  gridCertificate := ProfileGridHolonomy.coverFirstPath
    ProfileGridHolonomy.seedAt
  sigma := 4
  omega := ObligationKind.none
  selectedSupport := fun _ => False
  repairFrontier := fun _ => False
  nu := StateVerdict.acceptable
  traceField := partialTraceField

/-! ## Positive component laws retained by the witnesses -/

theorem traceErasing_preserves_visibleTupleSurface :
    PreservesVisibleTupleSurface traceErasingTransport := by
  intro c
  exact ⟨rfl, rfl, by
    intro atom
    rfl⟩

theorem traceCreating_preserves_visibleTupleSurface :
    PreservesVisibleTupleSurface traceCreatingTransport := by
  intro c
  exact ⟨rfl, rfl, by
    intro atom
    rfl⟩

theorem repairErasing_preserves_visibleTupleSurface :
    PreservesVisibleTupleSurface repairErasingTransport := by
  intro c
  exact ⟨rfl, rfl, by
    intro atom
    rfl⟩

theorem repairCreating_preserves_visibleTupleSurface :
    PreservesVisibleTupleSurface repairCreatingTransport := by
  intro c
  exact ⟨rfl, rfl, by
    intro atom
    rfl⟩

theorem supportDropping_preserves_scalarVerdict :
    PreservesScalarVerdict supportDroppingTransport := by
  intro c
  exact ⟨rfl, rfl⟩

theorem supportExpanding_preserves_scalarVerdict :
    PreservesScalarVerdict supportExpandingTransport := by
  intro c
  exact ⟨rfl, rfl⟩

theorem traceErasing_support_laws :
    PreservesTupleSupport traceErasingTransport ∧
      ReflectsTupleSupport traceErasingTransport := by
  exact ⟨by
    intro c atom hsupport
    exact hsupport,
    by
      intro c atom hsupport
      exact hsupport⟩

theorem traceCreating_support_laws :
    PreservesTupleSupport traceCreatingTransport ∧
      ReflectsTupleSupport traceCreatingTransport := by
  exact ⟨by
    intro c atom hsupport
    exact hsupport,
    by
      intro c atom hsupport
      exact hsupport⟩

theorem repairErasing_support_laws :
    PreservesTupleSupport repairErasingTransport ∧
      ReflectsTupleSupport repairErasingTransport := by
  exact ⟨by
    intro c atom hsupport
    exact hsupport,
    by
      intro c atom hsupport
      exact hsupport⟩

theorem repairCreating_support_laws :
    PreservesTupleSupport repairCreatingTransport ∧
      ReflectsTupleSupport repairCreatingTransport := by
  exact ⟨by
    intro c atom hsupport
    exact hsupport,
    by
      intro c atom hsupport
      exact hsupport⟩

theorem traceErasing_preserves_traceNone :
    PreservesTupleTraceNone traceErasingTransport := by
  intro c atom htrace
  cases atom with
  | api => exact htrace
  | database => rfl
  | queue => exact htrace

theorem traceCreating_reflects_traceNone :
    ReflectsTupleTraceNone traceCreatingTransport := by
  intro c atom htrace
  cases atom with
  | api => exact htrace
  | database => cases htrace
  | queue => exact htrace

theorem repairErasing_trace_laws :
    PreservesTupleTraceNone repairErasingTransport ∧
      ReflectsTupleTraceNone repairErasingTransport := by
  exact ⟨by
    intro c atom htrace
    exact htrace,
    by
      intro c atom htrace
      exact htrace⟩

theorem repairCreating_trace_laws :
    PreservesTupleTraceNone repairCreatingTransport ∧
      ReflectsTupleTraceNone repairCreatingTransport := by
  exact ⟨by
    intro c atom htrace
    exact htrace,
    by
      intro c atom htrace
      exact htrace⟩

theorem supportDropping_trace_laws :
    PreservesTupleTraceNone supportDroppingTransport ∧
      ReflectsTupleTraceNone supportDroppingTransport := by
  exact ⟨by
    intro c atom htrace
    exact htrace,
    by
      intro c atom htrace
      exact htrace⟩

theorem supportExpanding_trace_laws :
    PreservesTupleTraceNone supportExpandingTransport ∧
      ReflectsTupleTraceNone supportExpandingTransport := by
  exact ⟨by
    intro c atom htrace
    exact htrace,
    by
      intro c atom htrace
      exact htrace⟩

theorem traceErasing_repair_laws :
    PreservesTupleRepairFrontier traceErasingTransport ∧
      ReflectsTupleRepairFrontier traceErasingTransport := by
  exact ⟨by
    intro c atom hrepair
    exact hrepair,
    by
      intro c atom hrepair
      exact hrepair⟩

theorem traceCreating_repair_laws :
    PreservesTupleRepairFrontier traceCreatingTransport ∧
      ReflectsTupleRepairFrontier traceCreatingTransport := by
  exact ⟨by
    intro c atom hrepair
    exact hrepair,
    by
      intro c atom hrepair
      exact hrepair⟩

theorem repairErasing_reflects_repairFrontier :
    ReflectsTupleRepairFrontier repairErasingTransport := by
  intro c atom hrepair
  exact False.elim hrepair

theorem repairCreating_preserves_repairFrontier :
    PreservesTupleRepairFrontier repairCreatingTransport := by
  intro c atom hrepair
  exact Or.inl hrepair

theorem supportDropping_repair_laws :
    PreservesTupleRepairFrontier supportDroppingTransport ∧
      ReflectsTupleRepairFrontier supportDroppingTransport := by
  exact ⟨by
    intro c atom hrepair
    exact hrepair,
    by
      intro c atom hrepair
      exact hrepair⟩

theorem supportExpanding_repair_laws :
    PreservesTupleRepairFrontier supportExpandingTransport ∧
      ReflectsTupleRepairFrontier supportExpandingTransport := by
  exact ⟨by
    intro c atom hrepair
    exact hrepair,
    by
      intro c atom hrepair
      exact hrepair⟩

theorem supportDropping_reflects_support :
    ReflectsTupleSupport supportDroppingTransport := by
  intro c atom hsupport
  exact False.elim hsupport

theorem supportExpanding_preserves_support :
    PreservesTupleSupport supportExpandingTransport := by
  intro c atom _hsupport
  trivial

/-! ## Component-law failures and exactness obstructions -/

theorem traceNoneReflection_failure_obstructs_missingLocus_reflection :
    ¬ ReflectsTupleTraceNone traceErasingTransport ∧
      ¬ ReflectsTupleTraceMissingLocus traceErasingTransport := by
  constructor
  · intro hreflect
    have htarget :
        (traceErasingTransport.map
          ProfileTupleIntegration.fullEndpointTuple).traceField
          LocusAtom.database = none :=
      rfl
    have hsource :=
      hreflect ProfileTupleIntegration.fullEndpointTuple
        LocusAtom.database htarget
    cases hsource
  · intro hreflect
    have htarget :
        ProfileTupleIntegration.TupleTraceMissingLocus
          (traceErasingTransport.map
            ProfileTupleIntegration.fullEndpointTuple)
          LocusAtom.database :=
      ⟨trivial, rfl⟩
    have hsource :=
      hreflect ProfileTupleIntegration.fullEndpointTuple
        LocusAtom.database htarget
    exact ProfileTupleIntegration.fullEndpoint_has_no_missing_locus
      ⟨LocusAtom.database, hsource⟩

theorem traceNonePreservation_failure_obstructs_missingLocus_preservation :
    ¬ PreservesTupleTraceNone traceCreatingTransport ∧
      ¬ PreservesTupleTraceMissingLocus traceCreatingTransport := by
  constructor
  · intro hpreserve
    have htarget :=
      hpreserve ProfileTupleIntegration.traceMissingEndpointTuple
        LocusAtom.database rfl
    cases htarget
  · intro hpreserve
    have hsource :
        ProfileTupleIntegration.TupleTraceMissingLocus
          ProfileTupleIntegration.traceMissingEndpointTuple
          LocusAtom.database :=
      ProfileTupleIntegration.traceMissingEndpoint_database_missing_locus
    have htarget :=
      hpreserve ProfileTupleIntegration.traceMissingEndpointTuple
        LocusAtom.database hsource
    cases htarget.2

theorem repairPreservation_failure_obstructs_exactRepair_preservation :
    ¬ PreservesTupleRepairFrontier repairErasingTransport ∧
      ¬ (∀ c : EndpointTuple,
        ProfileTupleIntegration.TupleRepairFrontierExact c ->
          ProfileTupleIntegration.TupleRepairFrontierExact
            (repairErasingTransport.map c)) := by
  constructor
  · intro hpreserve
    have htarget :=
      hpreserve ProfileTupleIntegration.traceMissingEndpointTuple
        LocusAtom.database
        ProfileTupleIntegration.traceMissingEndpoint_forces_database_repair
    exact htarget
  · intro hpreserveExact
    have htargetExact :=
      hpreserveExact ProfileTupleIntegration.traceMissingEndpointTuple
        ProfileTupleIntegration.traceMissingEndpoint_repairFrontierExact
    have hrepair :=
      (htargetExact LocusAtom.database).mpr
        ProfileTupleIntegration.traceMissingEndpoint_database_missing_locus
    exact hrepair

theorem repairReflection_failure_obstructs_exactRepair_preservation :
    ¬ ReflectsTupleRepairFrontier repairCreatingTransport ∧
      ¬ (∀ c : EndpointTuple,
        ProfileTupleIntegration.TupleRepairFrontierExact c ->
          ProfileTupleIntegration.TupleRepairFrontierExact
            (repairCreatingTransport.map c)) := by
  constructor
  · intro hreflect
    have hsource :=
      hreflect ProfileTupleIntegration.fullEndpointTuple
        LocusAtom.database (Or.inr rfl)
    exact ProfileTupleIntegration.fullEndpoint_no_database_repair hsource
  · intro hpreserveExact
    have htargetExact :=
      hpreserveExact ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.fullEndpoint_repairFrontierExact
    have hmissingTarget :
        ProfileTupleIntegration.TupleTraceMissingLocus
          (repairCreatingTransport.map ProfileTupleIntegration.fullEndpointTuple)
          LocusAtom.database :=
      (htargetExact LocusAtom.database).mp (Or.inr rfl)
    cases hmissingTarget.2

theorem supportPreservation_failure_obstructs_missingLocus_preservation :
    ¬ PreservesTupleSupport supportDroppingTransport ∧
      ¬ PreservesTupleTraceMissingLocus supportDroppingTransport := by
  constructor
  · intro hpreserve
    have htarget :=
      hpreserve ProfileTupleIntegration.fullEndpointTuple
        LocusAtom.database trivial
    exact htarget
  · intro hpreserve
    have htarget :=
      hpreserve ProfileTupleIntegration.traceMissingEndpointTuple
        LocusAtom.database
        ProfileTupleIntegration.traceMissingEndpoint_database_missing_locus
    exact htarget.1

theorem emptySupportPartial_repairFrontierExact :
    ProfileTupleIntegration.TupleRepairFrontierExact
      emptySupportPartialEndpointTuple := by
  intro atom
  constructor
  · intro hrepair
    exact False.elim hrepair
  · intro hmissing
    exact False.elim hmissing.1

theorem supportReflection_failure_obstructs_missingLocus_reflection :
    ¬ ReflectsTupleSupport supportExpandingTransport ∧
      ¬ ReflectsTupleTraceMissingLocus supportExpandingTransport := by
  constructor
  · intro hreflect
    have hsource :=
      hreflect emptySupportPartialEndpointTuple
        LocusAtom.database trivial
    exact hsource
  · intro hreflectMissing
    have htarget :
        ProfileTupleIntegration.TupleTraceMissingLocus
          (supportExpandingTransport.map emptySupportPartialEndpointTuple)
          LocusAtom.database :=
      ⟨trivial, rfl⟩
    have hsource :=
      hreflectMissing emptySupportPartialEndpointTuple
        LocusAtom.database htarget
    exact hsource.1

/--
Cycle-19 package: finite component-law failures are witnessed by supplied tuple
transports. Trace and repair witnesses preserve the full visible tuple surface;
support witnesses preserve only scalar/verdict because selected support is the
law being varied.
-/
theorem tupleTransport_componentLaws_independence_package :
    PreservesVisibleTupleSurface traceErasingTransport ∧
      PreservesVisibleTupleSurface traceCreatingTransport ∧
      PreservesVisibleTupleSurface repairErasingTransport ∧
      PreservesVisibleTupleSurface repairCreatingTransport ∧
      PreservesScalarVerdict supportDroppingTransport ∧
      PreservesScalarVerdict supportExpandingTransport ∧
      ¬ ReflectsTupleTraceNone traceErasingTransport ∧
      ¬ ReflectsTupleTraceMissingLocus traceErasingTransport ∧
      ¬ PreservesTupleTraceNone traceCreatingTransport ∧
      ¬ PreservesTupleTraceMissingLocus traceCreatingTransport ∧
      ¬ PreservesTupleRepairFrontier repairErasingTransport ∧
      ¬ (∀ c : EndpointTuple,
        ProfileTupleIntegration.TupleRepairFrontierExact c ->
          ProfileTupleIntegration.TupleRepairFrontierExact
            (repairErasingTransport.map c)) ∧
      ¬ ReflectsTupleRepairFrontier repairCreatingTransport ∧
      ¬ (∀ c : EndpointTuple,
        ProfileTupleIntegration.TupleRepairFrontierExact c ->
          ProfileTupleIntegration.TupleRepairFrontierExact
            (repairCreatingTransport.map c)) ∧
      ¬ PreservesTupleSupport supportDroppingTransport ∧
      ¬ PreservesTupleTraceMissingLocus supportDroppingTransport ∧
      ¬ ReflectsTupleSupport supportExpandingTransport ∧
      ¬ ReflectsTupleTraceMissingLocus supportExpandingTransport := by
  exact ⟨traceErasing_preserves_visibleTupleSurface,
    traceCreating_preserves_visibleTupleSurface,
    repairErasing_preserves_visibleTupleSurface,
    repairCreating_preserves_visibleTupleSurface,
    supportDropping_preserves_scalarVerdict,
    supportExpanding_preserves_scalarVerdict,
    traceNoneReflection_failure_obstructs_missingLocus_reflection.1,
    traceNoneReflection_failure_obstructs_missingLocus_reflection.2,
    traceNonePreservation_failure_obstructs_missingLocus_preservation.1,
    traceNonePreservation_failure_obstructs_missingLocus_preservation.2,
    repairPreservation_failure_obstructs_exactRepair_preservation.1,
    repairPreservation_failure_obstructs_exactRepair_preservation.2,
    repairReflection_failure_obstructs_exactRepair_preservation.1,
    repairReflection_failure_obstructs_exactRepair_preservation.2,
    supportPreservation_failure_obstructs_missingLocus_preservation.1,
    supportPreservation_failure_obstructs_missingLocus_preservation.2,
    supportReflection_failure_obstructs_missingLocus_reflection.1,
    supportReflection_failure_obstructs_missingLocus_reflection.2⟩

end TupleTransportComponentLaws
end QualitySurface
end Formal.AG.Research
