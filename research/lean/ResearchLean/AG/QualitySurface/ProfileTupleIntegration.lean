import ResearchLean.AG.QualitySurface.CodebaseTracePacket
import ResearchLean.AG.QualitySurface.ProfileGridHolonomy

/-!
Cycle 11 evidence for `G-aat-quality-surface-01`.

This file fixes a finite profile-typed version of the central quality
certificate tuple

`Cert_A(p) = (sigma_p, omega_p, S_p, R_p, nu_p, T_p)`.

The result is intentionally finite and relative to supplied trace data. It does
not claim source extraction completeness, global quality, or a canonical
promotion into `Formal/AG` proper.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ProfileTupleIntegration

open TraceLocus
open StateSeparation

abbrev TupleProfile :=
  ProfileGridHolonomy.GridProfile

abbrev endpointProfile : TupleProfile :=
  ProfileGridHolonomy.highFine

/-! ## Profile-typed certificate tuples -/

/--
A finite profile-typed certificate tuple.

The field order follows the intended quality tuple:
`(sigma_p, omega_p, S_p, R_p, nu_p, T_p)`.
-/
structure TupleCertificateAt (p : TupleProfile) where
  gridCertificate : ProfileGridHolonomy.CertificateAt p
  sigma : Nat
  omega : ObligationKind
  selectedSupport : Set LocusAtom
  repairFrontier : Set LocusAtom
  nu : StateVerdict
  traceField : LocusAtom -> Option LocusTraceToken

/-- Trace-locus projection of a profile-typed tuple. -/
def toTraceLocusCertificate {p : TupleProfile}
    (c : TupleCertificateAt p) : TraceLocusCertificate where
  visibleScalarReading := c.sigma
  verdict := c.nu
  selectedSupport := c.selectedSupport
  traceField := c.traceField
  repairFrontier := c.repairFrontier
  obligation := c.omega

/-- Missing trace locus of a profile-typed tuple. -/
def TupleTraceMissingLocus {p : TupleProfile}
    (c : TupleCertificateAt p) : Set LocusAtom :=
  fun atom => c.selectedSupport atom ∧ c.traceField atom = none

/-- Exact repair regime for profile-typed tuples. -/
def TupleRepairFrontierExact {p : TupleProfile}
    (c : TupleCertificateAt p) : Prop :=
  ∀ atom, c.repairFrontier atom ↔ TupleTraceMissingLocus c atom

/-! ## Endpoint tuple witnesses -/

/-- Endpoint tuple with complete trace coverage and no repair obligation. -/
def fullEndpointTuple : TupleCertificateAt endpointProfile where
  gridCertificate := ProfileGridHolonomy.lawFirstPath
    ProfileGridHolonomy.seedAt
  sigma := 4
  omega := ObligationKind.none
  selectedSupport := selectedSupport
  repairFrontier := fun _ => False
  nu := StateVerdict.acceptable
  traceField := fullTraceField

/-- Endpoint tuple with the same visible surface and a missing database trace. -/
def traceMissingEndpointTuple : TupleCertificateAt endpointProfile where
  gridCertificate := ProfileGridHolonomy.coverFirstPath
    ProfileGridHolonomy.seedAt
  sigma := 4
  omega := ObligationKind.provideTrace
  selectedSupport := selectedSupport
  repairFrontier := databaseRepairFrontier
  nu := StateVerdict.acceptable
  traceField := partialTraceField

/-! ## Projection and exactness -/

/-- Tuple missing locus projects exactly to the trace-locus certificate. -/
theorem tuple_missing_locus_projects_to_trace_missing
    {p : TupleProfile} (c : TupleCertificateAt p) :
    ∀ atom,
      TraceMissingLocus (toTraceLocusCertificate c) atom ↔
        TupleTraceMissingLocus c atom := by
  intro atom
  rfl

/-- Tuple repair-frontier membership projects pointwise. -/
theorem tuple_repair_projects_to_trace_repair
    {p : TupleProfile} (c : TupleCertificateAt p) :
    ∀ atom,
      (toTraceLocusCertificate c).repairFrontier atom ↔
        c.repairFrontier atom := by
  intro atom
  rfl

/--
Exact tuple repair frontier is preserved by projection to
`TraceLocusCertificate`.
-/
theorem tupleExactRepair_projects_to_trace_exactRepair
    {p : TupleProfile} (c : TupleCertificateAt p)
    (hexact : TupleRepairFrontierExact c) :
    ∀ atom,
      (toTraceLocusCertificate c).repairFrontier atom ↔
        TraceMissingLocus (toTraceLocusCertificate c) atom := by
  intro atom
  constructor
  · intro hrepair
    have hmissingTuple : TupleTraceMissingLocus c atom :=
      (hexact atom).mp hrepair
    exact (tuple_missing_locus_projects_to_trace_missing c atom).mpr
      hmissingTuple
  · intro hmissingTrace
    have hmissingTuple : TupleTraceMissingLocus c atom :=
      (tuple_missing_locus_projects_to_trace_missing c atom).mp
        hmissingTrace
    exact (hexact atom).mpr hmissingTuple

/-! ## Readings of tuple certificates -/

/-- Same selected support, stated pointwise to avoid extensionality assumptions. -/
def SameTupleSupport {p : TupleProfile}
    (c₁ c₂ : TupleCertificateAt p) : Prop :=
  ∀ atom, c₁.selectedSupport atom ↔ c₂.selectedSupport atom

/-- Same visible tuple surface: scalar, verdict, and selected support. -/
def SameTupleVisibleSurface {p : TupleProfile}
    (c₁ c₂ : TupleCertificateAt p) : Prop :=
  c₁.sigma = c₂.sigma ∧ c₁.nu = c₂.nu ∧ SameTupleSupport c₁ c₂

/-- Same tuple trace missing locus. -/
def SameTupleTraceMissingLocus {p : TupleProfile}
    (c₁ c₂ : TupleCertificateAt p) : Prop :=
  ∀ atom, TupleTraceMissingLocus c₁ atom ↔ TupleTraceMissingLocus c₂ atom

/-- Same tuple repair frontier. -/
def SameTupleRepairFrontier {p : TupleProfile}
    (c₁ c₂ : TupleCertificateAt p) : Prop :=
  ∀ atom, c₁.repairFrontier atom ↔ c₂.repairFrontier atom

/-- Same pointwise trace field before projection to a trace-locus certificate. -/
def SameTupleTraceField {p : TupleProfile}
    (c₁ c₂ : TupleCertificateAt p) : Prop :=
  ∀ atom, c₁.traceField atom = c₂.traceField atom

/-- Same protected tuple data before any trace-locus projection. -/
def SameTupleProtectedData {p : TupleProfile}
    (c₁ c₂ : TupleCertificateAt p) : Prop :=
  c₁.omega = c₂.omega ∧
    SameTupleRepairFrontier c₁ c₂ ∧
    SameTupleTraceField c₁ c₂

/-- Reading that keeps only the tuple visible surface. -/
def visibleTupleSurfaceReading (p : TupleProfile) :
    ReadingAdequacy.Reading (TupleCertificateAt p) where
  Equivalent := fun c₁ c₂ => SameTupleVisibleSurface c₁ c₂

/-- Reading that also keeps the tuple trace missing locus. -/
def traceAwareTupleReading (p : TupleProfile) :
    ReadingAdequacy.Reading (TupleCertificateAt p) where
  Equivalent := fun c₁ c₂ =>
    (visibleTupleSurfaceReading p).Equivalent c₁ c₂ ∧
      SameTupleTraceMissingLocus c₁ c₂

/-- Visible tuple agreement projects to the trace-locus support surface. -/
theorem tuple_projects_visible_surface
    {p : TupleProfile} {c₁ c₂ : TupleCertificateAt p}
    (heq : SameTupleVisibleSurface c₁ c₂) :
    ReadingAdequacy.supportSurfaceReading.Equivalent
      (toTraceLocusCertificate c₁) (toTraceLocusCertificate c₂) := by
  constructor
  · exact ⟨heq.1, heq.2.1⟩
  · exact heq.2.2

/-- Trace-aware tuple agreement projects to trace-aware certificate agreement. -/
theorem tuple_traceAware_projects_to_traceAware
    {p : TupleProfile} {c₁ c₂ : TupleCertificateAt p}
    (heq : (traceAwareTupleReading p).Equivalent c₁ c₂) :
    ReadingAdequacy.traceLocusAwareReading.Equivalent
      (toTraceLocusCertificate c₁) (toTraceLocusCertificate c₂) := by
  constructor
  · exact tuple_projects_visible_surface heq.1
  · intro atom
    exact Iff.trans
      (tuple_missing_locus_projects_to_trace_missing c₁ atom)
      (Iff.trans (heq.2 atom)
        (Iff.symm
          (tuple_missing_locus_projects_to_trace_missing c₂ atom)))

/-! ## Endpoint facts -/

/-- The endpoint tuples share the same visible tuple surface. -/
theorem endpointTuple_visibleAgreement :
    (visibleTupleSurfaceReading endpointProfile).Equivalent
      fullEndpointTuple traceMissingEndpointTuple := by
  constructor
  · rfl
  constructor
  · rfl
  · intro atom
    constructor <;> intro _ <;> trivial

/-- The endpoint tuples carry distinct typed grid certificates at the same profile. -/
theorem endpointTuple_gridWitness_diff :
    fullEndpointTuple.gridCertificate.val ≠
      traceMissingEndpointTuple.gridCertificate.val := by
  intro h
  cases h

/-- The complete endpoint tuple has trace coverage on selected support. -/
theorem fullEndpoint_tuple_trace_available :
    TraceTransport.TraceAvailableOn
      fullEndpointTuple.selectedSupport fullEndpointTuple.traceField :=
  fullTrace_available_on_support

/-- The trace-missing endpoint tuple has a missing trace on selected support. -/
theorem traceMissingEndpoint_tuple_trace_missing :
    TraceTransport.TraceMissingOn
      traceMissingEndpointTuple.selectedSupport
      traceMissingEndpointTuple.traceField :=
  partialTrace_missing_on_support

/-- The complete endpoint tuple has no missing trace locus. -/
theorem fullEndpoint_has_no_missing_locus :
    ¬ ∃ atom, TupleTraceMissingLocus fullEndpointTuple atom :=
  fullTrace_has_no_missing_locus

/-- The trace-missing endpoint has the database atom in its missing locus. -/
theorem traceMissingEndpoint_database_missing_locus :
    TupleTraceMissingLocus traceMissingEndpointTuple LocusAtom.database :=
  partialTrace_database_missing_locus

/-- The trace-missing endpoint repair frontier is exactly its missing locus. -/
theorem traceMissingEndpoint_repair_frontier_matches_missing_locus :
    ∀ atom,
      traceMissingEndpointTuple.repairFrontier atom ↔
        TupleTraceMissingLocus traceMissingEndpointTuple atom :=
  partialTrace_repair_frontier_matches_missing_locus

/-- The complete endpoint has exact repair frontier. -/
theorem fullEndpoint_repairFrontierExact :
    TupleRepairFrontierExact fullEndpointTuple := by
  intro atom
  constructor
  · intro hrepair
    exact False.elim hrepair
  · intro hmissing
    exact fullEndpoint_has_no_missing_locus ⟨atom, hmissing⟩

/-- The trace-missing endpoint has exact repair frontier. -/
theorem traceMissingEndpoint_repairFrontierExact :
    TupleRepairFrontierExact traceMissingEndpointTuple :=
  traceMissingEndpoint_repair_frontier_matches_missing_locus

/-- The complete endpoint does not put the database atom in its repair frontier. -/
theorem fullEndpoint_no_database_repair :
    ¬ fullEndpointTuple.repairFrontier LocusAtom.database :=
  fullTrace_repair_frontier_excludes_database

/-- The trace-missing endpoint forces the database repair frontier. -/
theorem traceMissingEndpoint_forces_database_repair :
    traceMissingEndpointTuple.repairFrontier LocusAtom.database :=
  partialTrace_forces_database_repair

/-- The endpoint tuples differ in the obstruction / obligation component. -/
theorem endpointTuple_omega_diff :
    fullEndpointTuple.omega ≠ traceMissingEndpointTuple.omega := by
  intro h
  cases h

/-- The endpoint tuples do not have the same trace field before projection. -/
theorem endpointTuple_traceField_diff :
    ¬ SameTupleTraceField
      fullEndpointTuple traceMissingEndpointTuple := by
  intro hsame
  have hdatabase := hsame LocusAtom.database
  cases hdatabase

/-- The endpoint tuples do not have the same protected tuple data. -/
theorem endpointTuple_protectedData_diff :
    ¬ SameTupleProtectedData
      fullEndpointTuple traceMissingEndpointTuple := by
  intro hsame
  exact endpointTuple_omega_diff hsame.1

/-- The endpoint tuples do not have the same trace missing locus. -/
theorem endpointTuple_traceMissingLocus_diff :
    ¬ SameTupleTraceMissingLocus
      fullEndpointTuple traceMissingEndpointTuple := by
  intro hsame
  have hmissingFull : TupleTraceMissingLocus
      fullEndpointTuple LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      traceMissingEndpoint_database_missing_locus
  exact fullEndpoint_has_no_missing_locus
    ⟨LocusAtom.database, hmissingFull⟩

/-- The endpoint tuples do not have the same repair frontier. -/
theorem endpointTuple_repairFrontier_diff :
    ¬ SameTupleRepairFrontier
      fullEndpointTuple traceMissingEndpointTuple := by
  intro hsame
  have hrepairFull :
      fullEndpointTuple.repairFrontier LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      traceMissingEndpoint_forces_database_repair
  exact fullEndpoint_no_database_repair hrepairFull

/-! ## Tuple surface nonfaithfulness and exact trace-aware sufficiency -/

/-- Visible tuple surface does not recover the tuple trace missing locus. -/
theorem visibleTupleSurface_not_faithful_to_traceMissingLocus :
    ¬ ReadingAdequacy.FaithfulToInvariant
      (visibleTupleSurfaceReading endpointProfile)
      (@SameTupleTraceMissingLocus endpointProfile) := by
  intro hfaithful
  have hsame :=
    hfaithful fullEndpointTuple traceMissingEndpointTuple
      endpointTuple_visibleAgreement
  have hmissingFull : TupleTraceMissingLocus
      fullEndpointTuple LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      traceMissingEndpoint_database_missing_locus
  exact fullEndpoint_has_no_missing_locus
    ⟨LocusAtom.database, hmissingFull⟩

/-- Visible tuple surface does not recover the tuple repair frontier. -/
theorem visibleTupleSurface_not_faithful_to_repairFrontier :
    ¬ ReadingAdequacy.FaithfulToInvariant
      (visibleTupleSurfaceReading endpointProfile)
      (@SameTupleRepairFrontier endpointProfile) := by
  intro hfaithful
  have hsame :=
    hfaithful fullEndpointTuple traceMissingEndpointTuple
      endpointTuple_visibleAgreement
  have hrepairFull :
      fullEndpointTuple.repairFrontier LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      traceMissingEndpoint_forces_database_repair
  exact fullEndpoint_no_database_repair hrepairFull

/--
In the exact trace-repair regime, a trace-aware tuple reading is faithful to
the tuple repair frontier.
-/
theorem traceAwareTupleReading_faithful_to_repair_of_exact
    (p : TupleProfile) :
    ReadingAdequacy.FaithfulToInvariantOn
      (@TupleRepairFrontierExact p)
      (traceAwareTupleReading p)
      (@SameTupleRepairFrontier p) := by
  intro c₁ c₂ hexact₁ hexact₂ heq atom
  have hmissingSame := heq.2 atom
  constructor
  · intro hrepair₁
    have hmissing₁ : TupleTraceMissingLocus c₁ atom :=
      (hexact₁ atom).mp hrepair₁
    have hmissing₂ : TupleTraceMissingLocus c₂ atom :=
      hmissingSame.mp hmissing₁
    exact (hexact₂ atom).mpr hmissing₂
  · intro hrepair₂
    have hmissing₂ : TupleTraceMissingLocus c₂ atom :=
      (hexact₂ atom).mp hrepair₂
    have hmissing₁ : TupleTraceMissingLocus c₁ atom :=
      hmissingSame.mpr hmissing₂
    exact (hexact₁ atom).mpr hmissing₁

/--
Cycle-11 integrated witness: the same endpoint profile and visible tuple
surface can hide different obstruction / trace / repair data. Projection to
the earlier trace-locus certificate preserves the missing locus and exact
repair frontier, while exact trace-aware tuple readings are repair-faithful.
-/
theorem same_surface_but_profile_tuple_diff :
    (visibleTupleSurfaceReading endpointProfile).Equivalent
      fullEndpointTuple traceMissingEndpointTuple ∧
      fullEndpointTuple.gridCertificate.val ≠
        traceMissingEndpointTuple.gridCertificate.val ∧
      fullEndpointTuple.omega ≠ traceMissingEndpointTuple.omega ∧
      ¬ SameTupleTraceField
        fullEndpointTuple traceMissingEndpointTuple ∧
      ¬ SameTupleProtectedData
        fullEndpointTuple traceMissingEndpointTuple ∧
      ¬ SameTupleTraceMissingLocus
        fullEndpointTuple traceMissingEndpointTuple ∧
      ¬ SameTupleRepairFrontier
        fullEndpointTuple traceMissingEndpointTuple ∧
      TupleRepairFrontierExact fullEndpointTuple ∧
      TupleRepairFrontierExact traceMissingEndpointTuple ∧
      (∀ atom,
        (toTraceLocusCertificate traceMissingEndpointTuple).repairFrontier
            atom ↔
          TraceMissingLocus
            (toTraceLocusCertificate traceMissingEndpointTuple) atom) ∧
      TraceMissingLocus
        (toTraceLocusCertificate traceMissingEndpointTuple)
        LocusAtom.database ∧
      ¬ TraceMissingLocus
        (toTraceLocusCertificate fullEndpointTuple)
        LocusAtom.database ∧
      ¬ ReadingAdequacy.FaithfulToInvariant
        (visibleTupleSurfaceReading endpointProfile)
        (@SameTupleTraceMissingLocus endpointProfile) ∧
      ¬ ReadingAdequacy.FaithfulToInvariant
        (visibleTupleSurfaceReading endpointProfile)
        (@SameTupleRepairFrontier endpointProfile) ∧
      ReadingAdequacy.FaithfulToInvariantOn
        (@TupleRepairFrontierExact endpointProfile)
        (traceAwareTupleReading endpointProfile)
        (@SameTupleRepairFrontier endpointProfile) := by
  exact ⟨endpointTuple_visibleAgreement,
    endpointTuple_gridWitness_diff,
    endpointTuple_omega_diff,
    endpointTuple_traceField_diff,
    endpointTuple_protectedData_diff,
    endpointTuple_traceMissingLocus_diff,
    endpointTuple_repairFrontier_diff,
    fullEndpoint_repairFrontierExact,
    traceMissingEndpoint_repairFrontierExact,
    tupleExactRepair_projects_to_trace_exactRepair
      traceMissingEndpointTuple traceMissingEndpoint_repairFrontierExact,
    (tuple_missing_locus_projects_to_trace_missing
      traceMissingEndpointTuple LocusAtom.database).mpr
      traceMissingEndpoint_database_missing_locus,
    by
      intro hmissingTrace
      have hmissingTuple : TupleTraceMissingLocus
          fullEndpointTuple LocusAtom.database :=
        (tuple_missing_locus_projects_to_trace_missing
          fullEndpointTuple LocusAtom.database).mp hmissingTrace
      exact fullEndpoint_has_no_missing_locus
        ⟨LocusAtom.database, hmissingTuple⟩,
    visibleTupleSurface_not_faithful_to_traceMissingLocus,
    visibleTupleSurface_not_faithful_to_repairFrontier,
    traceAwareTupleReading_faithful_to_repair_of_exact endpointProfile⟩

end ProfileTupleIntegration
end QualitySurface
end ResearchLean.AG
