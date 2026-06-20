import Formal.AG.Research.QualitySurface.ReadingAdequacy

/-!
Cycle 9 evidence for `G-aat-quality-surface-01`.

This file records a supplied finite source-reference packet as protected
quality-surface data. The source references are opaque tokens: the result is
relative to the supplied table and does not assert source extraction
completeness or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace CodebaseTracePacket

/-! ## Supplied source-reference packets -/

/-- Code atoms in the finite source-reference packet. -/
inductive CodeAtom where
  | endpoint
  | storage
  | worker
  deriving DecidableEq, Fintype

/-- Opaque source-reference tokens supplied by an observation artifact. -/
inductive SourceRefToken where
  | endpointRef
  | storageRef
  | workerRef
  deriving DecidableEq

open CodeAtom SourceRefToken

/-- Every code atom is selected in the finite packet witness. -/
def codebaseSupport : Set CodeAtom :=
  fun _ => True

/-- The supplied source-reference table with full coverage on the support. -/
def fullSourceRefTable : CodeAtom -> Option SourceRefToken
  | endpoint => some endpointRef
  | storage => some storageRef
  | worker => some workerRef

/-- A supplied source-reference table with the storage token missing. -/
def partialSourceRefTable : CodeAtom -> Option SourceRefToken
  | endpoint => some endpointRef
  | storage => none
  | worker => some workerRef

/-- The exact repair frontier for the missing storage reference. -/
def storageRepairFrontier : Set CodeAtom :=
  fun atom => atom = storage

/--
A finite source-reference packet.

The visible scalar, verdict, and support are the surface data. The supplied
source-reference table and repair frontier are protected drill-down data.
-/
structure SourceRefPacket where
  visibleScalarReading : Nat
  verdict : StateSeparation.StateVerdict
  codeSupport : Set CodeAtom
  sourceRefTable : CodeAtom -> Option SourceRefToken
  repairFrontier : Set CodeAtom
  obligation : StateSeparation.ObligationKind

/-- Packet whose selected support has full source-reference coverage. -/
def fullPacket : SourceRefPacket where
  visibleScalarReading := 0
  verdict := StateSeparation.StateVerdict.acceptable
  codeSupport := codebaseSupport
  sourceRefTable := fullSourceRefTable
  repairFrontier := fun _ => False
  obligation := StateSeparation.ObligationKind.none

/-- Packet with the same visible surface but a missing storage source reference. -/
def partialPacket : SourceRefPacket where
  visibleScalarReading := 0
  verdict := StateSeparation.StateVerdict.acceptable
  codeSupport := codebaseSupport
  sourceRefTable := partialSourceRefTable
  repairFrontier := storageRepairFrontier
  obligation := StateSeparation.ObligationKind.provideTrace

/-- Atoms in the support where a source-reference token is supplied. -/
def SourceRefAvailableLocus (p : SourceRefPacket) : Set CodeAtom :=
  fun atom => p.codeSupport atom ∧ ∃ token, p.sourceRefTable atom = some token

/-- Atoms in the support where a source-reference token is missing. -/
def SourceRefMissingLocus (p : SourceRefPacket) : Set CodeAtom :=
  fun atom => p.codeSupport atom ∧ p.sourceRefTable atom = none

/-- Source-reference coverage on a declared code support. -/
def SourceRefAvailableOn
    (support : Set CodeAtom) (table : CodeAtom -> Option SourceRefToken) : Prop :=
  ∀ atom, support atom -> ∃ token, table atom = some token

/-- A missing source reference on a declared code support. -/
def SourceRefMissingOn
    (support : Set CodeAtom) (table : CodeAtom -> Option SourceRefToken) : Prop :=
  ∃ atom, support atom ∧ table atom = none

/-- A packet whose repair frontier is exactly its missing source-reference locus. -/
def RepairFrontierExact (p : SourceRefPacket) : Prop :=
  ∀ atom, p.repairFrontier atom ↔ SourceRefMissingLocus p atom

/-! ## Projection to the earlier trace-locus certificate -/

/-- The code atom seen as the corresponding finite trace-locus atom. -/
def toLocusAtom : CodeAtom -> TraceLocus.LocusAtom
  | endpoint => TraceLocus.LocusAtom.api
  | storage => TraceLocus.LocusAtom.database
  | worker => TraceLocus.LocusAtom.queue

/-- The inverse coordinate used when projecting a source-ref packet to trace-locus data. -/
def fromLocusAtom : TraceLocus.LocusAtom -> CodeAtom
  | TraceLocus.LocusAtom.api => endpoint
  | TraceLocus.LocusAtom.database => storage
  | TraceLocus.LocusAtom.queue => worker

/-- Source-reference tokens projected to the earlier finite trace-token vocabulary. -/
def sourceRefToTraceToken : SourceRefToken -> TraceLocus.LocusTraceToken
  | endpointRef => TraceLocus.LocusTraceToken.refApi
  | storageRef => TraceLocus.LocusTraceToken.refDatabase
  | workerRef => TraceLocus.LocusTraceToken.refQueue

/-- Projected support of a source-reference packet. -/
def projectedSupport (p : SourceRefPacket) : Set TraceLocus.LocusAtom :=
  fun atom => p.codeSupport (fromLocusAtom atom)

/-- Projected trace-token field of a source-reference packet. -/
def projectedTraceField
    (p : SourceRefPacket) : TraceLocus.LocusAtom -> Option TraceLocus.LocusTraceToken :=
  fun atom => Option.map sourceRefToTraceToken
    (p.sourceRefTable (fromLocusAtom atom))

/-- Projected repair frontier of a source-reference packet. -/
def projectedRepairFrontier (p : SourceRefPacket) : Set TraceLocus.LocusAtom :=
  fun atom => p.repairFrontier (fromLocusAtom atom)

/-- The trace-locus certificate induced by a supplied source-reference packet. -/
def toTraceLocusCertificate
    (p : SourceRefPacket) : TraceLocus.TraceLocusCertificate where
  visibleScalarReading := p.visibleScalarReading
  verdict := p.verdict
  selectedSupport := projectedSupport p
  traceField := projectedTraceField p
  repairFrontier := projectedRepairFrontier p
  obligation := p.obligation

/-! ## Source-reference locus decomposition -/

/--
Every selected support atom lies either in the source-reference available locus
or in the missing locus, relative to the supplied table.
-/
theorem sourceRef_locus_partition (p : SourceRefPacket) :
    ∀ atom, p.codeSupport atom ->
      SourceRefAvailableLocus p atom ∨ SourceRefMissingLocus p atom := by
  intro atom hsupport
  cases hsource : p.sourceRefTable atom with
  | none =>
      exact Or.inr ⟨hsupport, hsource⟩
  | some token =>
      exact Or.inl ⟨hsupport, token, hsource⟩

/-- Available and missing source-reference loci are disjoint. -/
theorem sourceRef_available_missing_disjoint (p : SourceRefPacket) :
    ∀ atom,
      ¬ (SourceRefAvailableLocus p atom ∧ SourceRefMissingLocus p atom) := by
  intro atom hloci
  rcases hloci with ⟨havailable, hmissing⟩
  rcases havailable with ⟨_hsupportAvailable, token, hsome⟩
  rcases hmissing with ⟨_hsupportMissing, hnone⟩
  rw [hsome] at hnone
  cases hnone

/-- The full packet has source-reference coverage on its code support. -/
theorem fullTrace_available_on_codebaseSupport :
    SourceRefAvailableOn fullPacket.codeSupport fullPacket.sourceRefTable := by
  intro atom _hsupport
  cases atom with
  | endpoint => exact ⟨endpointRef, rfl⟩
  | storage => exact ⟨storageRef, rfl⟩
  | worker => exact ⟨workerRef, rfl⟩

/-- The partial packet has a missing storage source reference on its code support. -/
theorem partialTrace_missing_on_codebaseSupport :
    SourceRefMissingOn partialPacket.codeSupport partialPacket.sourceRefTable :=
  ⟨storage, trivial, rfl⟩

/-- The full packet has no missing source-reference atom. -/
theorem fullTrace_has_no_missing_sourceRef_locus :
    ¬ ∃ atom, SourceRefMissingLocus fullPacket atom := by
  intro hmissing
  rcases hmissing with ⟨atom, _hsupport, hsource⟩
  cases atom <;> cases hsource

/-- The storage atom lies in the partial packet's missing source-reference locus. -/
theorem partialTrace_storage_missing_locus :
    SourceRefMissingLocus partialPacket storage :=
  ⟨trivial, rfl⟩

/-- The partial packet's missing source-reference locus is exactly storage. -/
theorem partialTrace_missing_locus_exact_storage :
    ∀ atom, SourceRefMissingLocus partialPacket atom ↔ atom = storage := by
  intro atom
  constructor
  · intro hmissing
    rcases hmissing with ⟨_hsupport, hsource⟩
    cases atom with
    | endpoint => cases hsource
    | storage => rfl
    | worker => cases hsource
  · intro hstorage
    cases hstorage
    exact partialTrace_storage_missing_locus

/-- The partial packet's repair frontier covers all missing source-reference atoms. -/
theorem partialTrace_repair_covers_missingRefs :
    ∀ atom, SourceRefMissingLocus partialPacket atom ->
      partialPacket.repairFrontier atom := by
  intro atom hmissing
  change atom = storage
  exact (partialTrace_missing_locus_exact_storage atom).mp hmissing

/-- The storage repair frontier is forced by the partial packet's missing reference. -/
theorem partialTrace_forces_storage_repair :
    partialPacket.repairFrontier storage :=
  partialTrace_repair_covers_missingRefs storage
    partialTrace_storage_missing_locus

/-- The full packet does not put storage in its repair frontier. -/
theorem fullTrace_repair_frontier_excludes_storage :
    ¬ fullPacket.repairFrontier storage := by
  intro hrepair
  exact hrepair

/-- The partial packet's repair frontier matches its missing source-reference locus. -/
theorem partialTrace_repair_frontier_matches_missingRefs :
    ∀ atom,
      partialPacket.repairFrontier atom ↔
        SourceRefMissingLocus partialPacket atom := by
  intro atom
  constructor
  · intro hrepair
    change atom = storage at hrepair
    cases hrepair
    exact partialTrace_storage_missing_locus
  · intro hmissing
    change atom = storage
    exact (partialTrace_missing_locus_exact_storage atom).mp hmissing

/-- The full packet has exact repair frontier: no missing reference, no repair. -/
theorem fullTrace_repairFrontierExact :
    RepairFrontierExact fullPacket := by
  intro atom
  constructor
  · intro hrepair
    exact False.elim hrepair
  · intro hmissing
    exact fullTrace_has_no_missing_sourceRef_locus ⟨atom, hmissing⟩

/-- The partial packet has exact repair frontier at the missing source-ref locus. -/
theorem partialTrace_repairFrontierExact :
    RepairFrontierExact partialPacket :=
  partialTrace_repair_frontier_matches_missingRefs

/-! ## Projection preserves the relative exactness claim -/

/-- Missing source references project to missing trace-locus atoms. -/
theorem sourceRef_missing_projects_to_trace_missing
    (p : SourceRefPacket) :
    ∀ atom,
      TraceLocus.TraceMissingLocus (toTraceLocusCertificate p) atom ↔
        SourceRefMissingLocus p (fromLocusAtom atom) := by
  intro atom
  constructor
  · intro hmissing
    rcases hmissing with ⟨hsupport, htrace⟩
    constructor
    · exact hsupport
    · cases hsource : p.sourceRefTable (fromLocusAtom atom) with
      | none => rfl
      | some token =>
          change Option.map sourceRefToTraceToken
            (p.sourceRefTable (fromLocusAtom atom)) = none at htrace
          rw [hsource] at htrace
          cases htrace
  · intro hmissing
    rcases hmissing with ⟨hsupport, hsource⟩
    constructor
    · exact hsupport
    · change Option.map sourceRefToTraceToken
        (p.sourceRefTable (fromLocusAtom atom)) = none
      rw [hsource]
      rfl

/-- Repair-frontier membership projects pointwise to the trace-locus certificate. -/
theorem sourceRef_repair_projects_to_trace_repair
    (p : SourceRefPacket) :
    ∀ atom,
      (toTraceLocusCertificate p).repairFrontier atom ↔
        p.repairFrontier (fromLocusAtom atom) := by
  intro atom
  rfl

/--
If a source-reference packet has exact repair frontier, then its projected
trace-locus certificate also has exact repair frontier.
-/
theorem exact_packet_projects_to_exact_trace_repair
    (p : SourceRefPacket) (hexact : RepairFrontierExact p) :
    ∀ atom,
      (toTraceLocusCertificate p).repairFrontier atom ↔
        TraceLocus.TraceMissingLocus (toTraceLocusCertificate p) atom := by
  intro atom
  constructor
  · intro hrepair
    change p.repairFrontier (fromLocusAtom atom) at hrepair
    have hmissingSource :
        SourceRefMissingLocus p (fromLocusAtom atom) :=
      (hexact (fromLocusAtom atom)).mp hrepair
    exact (sourceRef_missing_projects_to_trace_missing p atom).mpr
      hmissingSource
  · intro hmissingTrace
    have hmissingSource :
        SourceRefMissingLocus p (fromLocusAtom atom) :=
      (sourceRef_missing_projects_to_trace_missing p atom).mp
        hmissingTrace
    change p.repairFrontier (fromLocusAtom atom)
    exact (hexact (fromLocusAtom atom)).mpr hmissingSource

/-- The full source-ref packet projects to a trace certificate with no database gap. -/
theorem fullPacket_projection_has_no_missing_database :
    ¬ TraceLocus.TraceMissingLocus
      (toTraceLocusCertificate fullPacket) TraceLocus.LocusAtom.database := by
  intro hmissing
  have hmissingSource :
      SourceRefMissingLocus fullPacket storage :=
    (sourceRef_missing_projects_to_trace_missing
      fullPacket TraceLocus.LocusAtom.database).mp hmissing
  exact fullTrace_has_no_missing_sourceRef_locus
    ⟨storage, hmissingSource⟩

/-- The partial source-ref packet projects to a database trace gap. -/
theorem partialPacket_projection_has_missing_database :
    TraceLocus.TraceMissingLocus
      (toTraceLocusCertificate partialPacket) TraceLocus.LocusAtom.database :=
  (sourceRef_missing_projects_to_trace_missing
    partialPacket TraceLocus.LocusAtom.database).mpr
    partialTrace_storage_missing_locus

/-- The partial projected trace certificate has exact repair frontier. -/
theorem partialPacket_projection_repairFrontierExact :
    ∀ atom,
      (toTraceLocusCertificate partialPacket).repairFrontier atom ↔
        TraceLocus.TraceMissingLocus
          (toTraceLocusCertificate partialPacket) atom :=
  exact_packet_projects_to_exact_trace_repair
    partialPacket partialTrace_repairFrontierExact

/-! ## Reading loss at the packet surface -/

/-- Same visible scalar and selected verdict for source-ref packets. -/
def SameVisibleSurface (p q : SourceRefPacket) : Prop :=
  p.visibleScalarReading = q.visibleScalarReading ∧ p.verdict = q.verdict

/-- Same code support, stated pointwise to avoid extensionality assumptions. -/
def SameCodeSupport (p q : SourceRefPacket) : Prop :=
  ∀ atom, p.codeSupport atom ↔ q.codeSupport atom

/-- Same missing source-reference locus. -/
def SameSourceRefMissingLocus (p q : SourceRefPacket) : Prop :=
  ∀ atom, SourceRefMissingLocus p atom ↔ SourceRefMissingLocus q atom

/-- Same repair frontier on code atoms. -/
def SameCodebaseRepairFrontier (p q : SourceRefPacket) : Prop :=
  ∀ atom, p.repairFrontier atom ↔ q.repairFrontier atom

/-- Reading that keeps only scalar, verdict, and selected code support. -/
def supportSurfaceReading :
    ReadingAdequacy.Reading SourceRefPacket where
  Equivalent := fun p q =>
    SameVisibleSurface p q ∧ SameCodeSupport p q

/-- Reading that also keeps the missing source-reference locus. -/
def sourceRefLocusAwareReading :
    ReadingAdequacy.Reading SourceRefPacket where
  Equivalent := fun p q =>
    supportSurfaceReading.Equivalent p q ∧ SameSourceRefMissingLocus p q

/-- The full and partial packets agree at the support-surface reading. -/
theorem full_partial_supportSurface_equivalent :
    supportSurfaceReading.Equivalent fullPacket partialPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro _ <;> trivial

/-- Support-surface reading does not recover the source-ref missing locus. -/
theorem supportSurface_not_faithful_to_sourceRefMissingLocus :
    ¬ ReadingAdequacy.FaithfulToInvariant
      supportSurfaceReading SameSourceRefMissingLocus := by
  intro hfaithful
  have hsame :=
    hfaithful fullPacket partialPacket
      full_partial_supportSurface_equivalent
  have hmissingFull : SourceRefMissingLocus fullPacket storage :=
    (hsame storage).mpr partialTrace_storage_missing_locus
  exact fullTrace_has_no_missing_sourceRef_locus
    ⟨storage, hmissingFull⟩

/-- Support-surface reading does not recover the exact codebase repair frontier. -/
theorem surfaceReading_not_faithful_to_codebaseTraceFrontier :
    ¬ ReadingAdequacy.FaithfulToInvariant
      supportSurfaceReading SameCodebaseRepairFrontier := by
  intro hfaithful
  have hsame :=
    hfaithful fullPacket partialPacket
      full_partial_supportSurface_equivalent
  have hrepairFull : fullPacket.repairFrontier storage :=
    (hsame storage).mpr partialTrace_forces_storage_repair
  exact fullTrace_repair_frontier_excludes_storage hrepairFull

/--
Inside the exact source-ref repair regime, the source-ref-locus-aware reading
is faithful to the codebase repair frontier.
-/
theorem sourceRefLocusAware_faithful_to_repairFrontier_of_exact :
    ReadingAdequacy.FaithfulToInvariantOn RepairFrontierExact
      sourceRefLocusAwareReading SameCodebaseRepairFrontier := by
  intro p q hexactP hexactQ heq atom
  have hmissingSame := heq.2 atom
  constructor
  · intro hrepairP
    have hmissingP : SourceRefMissingLocus p atom :=
      (hexactP atom).mp hrepairP
    have hmissingQ : SourceRefMissingLocus q atom :=
      hmissingSame.mp hmissingP
    exact (hexactQ atom).mpr hmissingQ
  · intro hrepairQ
    have hmissingQ : SourceRefMissingLocus q atom :=
      (hexactQ atom).mp hrepairQ
    have hmissingP : SourceRefMissingLocus p atom :=
      hmissingSame.mpr hmissingQ
    exact (hexactP atom).mpr hmissingP

/--
Cycle-9 finite witness: two supplied source-ref packets share the same visible
surface and code support, while source-ref trace locus and exact repair frontier
differ. The difference is preserved by projection to `TraceLocusCertificate`.
-/
theorem same_surface_support_but_codebase_trace_frontier_diff :
    supportSurfaceReading.Equivalent fullPacket partialPacket ∧
      SourceRefAvailableOn fullPacket.codeSupport
        fullPacket.sourceRefTable ∧
      SourceRefMissingOn partialPacket.codeSupport
        partialPacket.sourceRefTable ∧
      RepairFrontierExact fullPacket ∧
      RepairFrontierExact partialPacket ∧
      TraceLocus.TraceMissingLocus
        (toTraceLocusCertificate partialPacket)
        TraceLocus.LocusAtom.database ∧
      ¬ TraceLocus.TraceMissingLocus
        (toTraceLocusCertificate fullPacket)
        TraceLocus.LocusAtom.database ∧
      ¬ SameSourceRefMissingLocus fullPacket partialPacket ∧
      ¬ SameCodebaseRepairFrontier fullPacket partialPacket ∧
      (∀ atom,
        (toTraceLocusCertificate partialPacket).repairFrontier atom ↔
          TraceLocus.TraceMissingLocus
            (toTraceLocusCertificate partialPacket) atom) ∧
      ¬ ReadingAdequacy.FaithfulToInvariant
        supportSurfaceReading SameSourceRefMissingLocus ∧
      ¬ ReadingAdequacy.FaithfulToInvariant
        supportSurfaceReading SameCodebaseRepairFrontier := by
  exact ⟨full_partial_supportSurface_equivalent,
    fullTrace_available_on_codebaseSupport,
    partialTrace_missing_on_codebaseSupport,
    fullTrace_repairFrontierExact,
    partialTrace_repairFrontierExact,
    partialPacket_projection_has_missing_database,
    fullPacket_projection_has_no_missing_database,
    by
      intro hsame
      have hmissingFull : SourceRefMissingLocus fullPacket storage :=
        (hsame storage).mpr partialTrace_storage_missing_locus
      exact fullTrace_has_no_missing_sourceRef_locus
        ⟨storage, hmissingFull⟩,
    by
      intro hsame
      have hrepairFull : fullPacket.repairFrontier storage :=
        (hsame storage).mpr partialTrace_forces_storage_repair
      exact fullTrace_repair_frontier_excludes_storage hrepairFull,
    partialPacket_projection_repairFrontierExact,
    supportSurface_not_faithful_to_sourceRefMissingLocus,
    surfaceReading_not_faithful_to_codebaseTraceFrontier⟩

end CodebaseTracePacket
end QualitySurface
end Formal.AG.Research
