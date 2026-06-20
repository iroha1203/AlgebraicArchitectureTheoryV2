import Formal.AG.Research.QualitySurface.StateSeparation

/-!
Cycle 6 evidence for `G-aat-quality-surface-01`.

This file refines the trace-missing state into a finite trace-locus certificate:
two certificates can share the same visible scalar, verdict, and selected
support while differing in the locus of missing trace tokens and the repair
frontier forced by that locus.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace TraceLocus

/-! ## Finite trace-locus certificates -/

/-- Support atoms in the finite trace-locus example. -/
inductive LocusAtom where
  | api
  | database
  | queue
  deriving DecidableEq, Fintype

/-- Trace tokens available for support atoms. -/
inductive LocusTraceToken where
  | refApi
  | refDatabase
  | refQueue
  deriving DecidableEq

open LocusAtom LocusTraceToken

/-- Every atom belongs to the selected support in this finite witness. -/
def selectedSupport : Set LocusAtom :=
  fun _ => True

/-- Trace field with full trace coverage on the selected support. -/
def fullTraceField : LocusAtom -> Option LocusTraceToken
  | api => some refApi
  | database => some refDatabase
  | queue => some refQueue

/-- Trace field with one missing token on the selected support. -/
def partialTraceField : LocusAtom -> Option LocusTraceToken
  | api => some refApi
  | database => none
  | queue => some refQueue

/-- Repair frontier that covers exactly the database trace gap. -/
def databaseRepairFrontier : Set LocusAtom :=
  fun atom => atom = database

/--
Finite certificate carrying the visible surface and the trace locus beneath it.

The selected support is part of the visible certificate context, while the trace
field and repair frontier are the protected drill-down data.
-/
structure TraceLocusCertificate where
  visibleScalarReading : Nat
  verdict : StateSeparation.StateVerdict
  selectedSupport : Set LocusAtom
  traceField : LocusAtom -> Option LocusTraceToken
  repairFrontier : Set LocusAtom
  obligation : StateSeparation.ObligationKind

/-- Certificate whose selected support is fully traced. -/
def fullTraceCert : TraceLocusCertificate where
  visibleScalarReading := 0
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := selectedSupport
  traceField := fullTraceField
  repairFrontier := fun _ => False
  obligation := StateSeparation.ObligationKind.none

/-- Certificate with the same visible surface but a missing database trace. -/
def partialTraceCert : TraceLocusCertificate where
  visibleScalarReading := 0
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := selectedSupport
  traceField := partialTraceField
  repairFrontier := databaseRepairFrontier
  obligation := StateSeparation.ObligationKind.provideTrace

/-- Atoms in the selected support where a trace token is available. -/
def TraceAvailableLocus (c : TraceLocusCertificate) : Set LocusAtom :=
  fun atom => c.selectedSupport atom ∧ ∃ token, c.traceField atom = some token

/-- Atoms in the selected support where the trace token is missing. -/
def TraceMissingLocus (c : TraceLocusCertificate) : Set LocusAtom :=
  fun atom => c.selectedSupport atom ∧ c.traceField atom = none

/-- A repair frontier covers all missing trace atoms. -/
def RepairCoversMissingTrace (c : TraceLocusCertificate) : Prop :=
  ∀ atom, TraceMissingLocus c atom -> c.repairFrontier atom

/-! ## Locus decomposition -/

/-- Every selected support atom lies either in the available trace locus or the missing trace locus. -/
theorem trace_locus_partition (c : TraceLocusCertificate) :
    ∀ atom, c.selectedSupport atom ->
      TraceAvailableLocus c atom ∨ TraceMissingLocus c atom := by
  intro atom hsupport
  cases htrace : c.traceField atom with
  | none =>
      exact Or.inr ⟨hsupport, htrace⟩
  | some token =>
      exact Or.inl ⟨hsupport, token, htrace⟩

/-- Available and missing trace loci are disjoint. -/
theorem trace_available_missing_disjoint (c : TraceLocusCertificate) :
    ∀ atom, ¬ (TraceAvailableLocus c atom ∧ TraceMissingLocus c atom) := by
  intro atom hloci
  rcases hloci with ⟨havailable, hmissing⟩
  rcases havailable with ⟨_hsupportAvailable, token, hsome⟩
  rcases hmissing with ⟨_hsupportMissing, hnone⟩
  rw [hsome] at hnone
  cases hnone

/-- The full certificate has trace coverage on the selected support. -/
theorem fullTrace_available_on_support :
    TraceTransport.TraceAvailableOn fullTraceCert.selectedSupport
      fullTraceCert.traceField := by
  intro atom _hsupport
  cases atom with
  | api => exact ⟨refApi, rfl⟩
  | database => exact ⟨refDatabase, rfl⟩
  | queue => exact ⟨refQueue, rfl⟩

/-- The partial certificate has a missing database trace on the selected support. -/
theorem partialTrace_missing_on_support :
    TraceTransport.TraceMissingOn partialTraceCert.selectedSupport
      partialTraceCert.traceField :=
  ⟨database, trivial, rfl⟩

/-- `TraceMissingOn` is exactly nonempty missing trace locus for these certificates. -/
theorem traceMissingOn_iff_missingLocus_nonempty
    (c : TraceLocusCertificate) :
    TraceTransport.TraceMissingOn c.selectedSupport c.traceField ↔
      ∃ atom, TraceMissingLocus c atom := by
  rfl

/-- The full certificate has no missing trace atom. -/
theorem fullTrace_has_no_missing_locus :
    ¬ ∃ atom, TraceMissingLocus fullTraceCert atom := by
  intro hmissing
  rcases hmissing with ⟨atom, _hsupport, htrace⟩
  cases atom <;> cases htrace

/-- The partial certificate's database atom lies in the missing trace locus. -/
theorem partialTrace_database_missing_locus :
    TraceMissingLocus partialTraceCert database :=
  ⟨trivial, rfl⟩

/-- The partial certificate's missing trace locus is exactly the database atom. -/
theorem partialTrace_missing_locus_exact_database :
    ∀ atom, TraceMissingLocus partialTraceCert atom ↔ atom = database := by
  intro atom
  constructor
  · intro hmissing
    rcases hmissing with ⟨_hsupport, htrace⟩
    cases atom with
    | api => cases htrace
    | database => rfl
    | queue => cases htrace
  · intro hdatabase
    cases hdatabase
    exact partialTrace_database_missing_locus

/-- The partial certificate's missing trace locus is covered by its repair frontier. -/
theorem partialTrace_repair_covers_missing :
    RepairCoversMissingTrace partialTraceCert := by
  intro atom hmissing
  change atom = database
  exact (partialTrace_missing_locus_exact_database atom).mp hmissing

/-- The database repair frontier is forced by the partial certificate's missing trace. -/
theorem partialTrace_forces_database_repair :
    partialTraceCert.repairFrontier database :=
  partialTrace_repair_covers_missing database
    partialTrace_database_missing_locus

/-- The full certificate does not put the database atom in its repair frontier. -/
theorem fullTrace_repair_frontier_excludes_database :
    ¬ fullTraceCert.repairFrontier database := by
  intro hrepair
  exact hrepair

/-- The partial certificate's repair frontier matches its missing trace locus. -/
theorem partialTrace_repair_frontier_matches_missing_locus :
    ∀ atom,
      partialTraceCert.repairFrontier atom ↔
        TraceMissingLocus partialTraceCert atom := by
  intro atom
  constructor
  · intro hrepair
    change atom = database at hrepair
    cases hrepair
    exact partialTrace_database_missing_locus
  · intro hmissing
    change atom = database
    exact (partialTrace_missing_locus_exact_database atom).mp hmissing

/-- The two certificates have different repair frontier behavior at the database atom. -/
theorem repair_frontier_differs_on_database :
    ¬ (fullTraceCert.repairFrontier database ↔
      partialTraceCert.repairFrontier database) := by
  intro hiff
  exact fullTrace_repair_frontier_excludes_database
    (hiff.mpr partialTrace_forces_database_repair)

/-- The two certificates share the same visible scalar, verdict, and selected support. -/
theorem same_visible_surface_and_support :
    fullTraceCert.visibleScalarReading =
        partialTraceCert.visibleScalarReading ∧
      fullTraceCert.verdict = partialTraceCert.verdict ∧
      fullTraceCert.selectedSupport = partialTraceCert.selectedSupport :=
  And.intro rfl (And.intro rfl rfl)

/-- Faithfulness of the visible surface and support to the missing trace locus. -/
def SurfaceSupportFaithfulToMissingLocus
    (r : TraceLocusCertificate -> Nat)
    (v : TraceLocusCertificate -> StateSeparation.StateVerdict)
    (s : TraceLocusCertificate -> Set LocusAtom) : Prop :=
  ∀ c₁ c₂ : TraceLocusCertificate,
    r c₁ = r c₂ ->
      v c₁ = v c₂ ->
        s c₁ = s c₂ ->
          ∀ atom,
            (TraceMissingLocus c₁ atom ↔ TraceMissingLocus c₂ atom)

/-- Faithfulness of the visible surface and support to the repair frontier. -/
def SurfaceSupportFaithfulToRepairFrontier
    (r : TraceLocusCertificate -> Nat)
    (v : TraceLocusCertificate -> StateSeparation.StateVerdict)
    (s : TraceLocusCertificate -> Set LocusAtom) : Prop :=
  ∀ c₁ c₂ : TraceLocusCertificate,
    r c₁ = r c₂ ->
      v c₁ = v c₂ ->
        s c₁ = s c₂ ->
          ∀ atom,
            (c₁.repairFrontier atom ↔ c₂.repairFrontier atom)

/--
The visible scalar, verdict, and selected support do not recover the missing
trace locus.
-/
theorem surfaceSupport_not_faithful_to_missing_locus :
    ¬ SurfaceSupportFaithfulToMissingLocus
      (fun c => c.visibleScalarReading)
      (fun c => c.verdict)
      (fun c => c.selectedSupport) := by
  intro hfaithful
  have hiff :=
    hfaithful fullTraceCert partialTraceCert rfl rfl rfl database
  have hmissingFull : TraceMissingLocus fullTraceCert database :=
    hiff.mpr partialTrace_database_missing_locus
  exact fullTrace_has_no_missing_locus ⟨database, hmissingFull⟩

/--
The visible scalar, verdict, and selected support also do not recover the
repair frontier forced by the missing trace locus.
-/
theorem surfaceSupport_not_faithful_to_repair_frontier :
    ¬ SurfaceSupportFaithfulToRepairFrontier
      (fun c => c.visibleScalarReading)
      (fun c => c.verdict)
      (fun c => c.selectedSupport) := by
  intro hfaithful
  have hiff :=
    hfaithful fullTraceCert partialTraceCert rfl rfl rfl database
  have hrepairFull : fullTraceCert.repairFrontier database :=
    hiff.mpr partialTrace_forces_database_repair
  exact fullTrace_repair_frontier_excludes_database hrepairFull

/--
The cycle-6 finite witness: two certificates can have the same visible surface
and selected support while the protected trace locus and repair frontier differ.
-/
theorem same_surface_support_but_trace_locus_diff :
    fullTraceCert.visibleScalarReading =
        partialTraceCert.visibleScalarReading ∧
      fullTraceCert.verdict = partialTraceCert.verdict ∧
      fullTraceCert.selectedSupport = partialTraceCert.selectedSupport ∧
      TraceTransport.TraceAvailableOn fullTraceCert.selectedSupport
        fullTraceCert.traceField ∧
      TraceTransport.TraceMissingOn partialTraceCert.selectedSupport
        partialTraceCert.traceField ∧
      RepairCoversMissingTrace partialTraceCert ∧
      partialTraceCert.repairFrontier database ∧
      ¬ fullTraceCert.repairFrontier database ∧
      (∀ atom,
        partialTraceCert.repairFrontier atom ↔
          TraceMissingLocus partialTraceCert atom) ∧
      ¬ SurfaceSupportFaithfulToMissingLocus
        (fun c => c.visibleScalarReading)
        (fun c => c.verdict)
        (fun c => c.selectedSupport) ∧
      ¬ SurfaceSupportFaithfulToRepairFrontier
        (fun c => c.visibleScalarReading)
        (fun c => c.verdict)
        (fun c => c.selectedSupport) := by
  exact ⟨rfl, rfl, rfl, fullTrace_available_on_support,
    partialTrace_missing_on_support, partialTrace_repair_covers_missing,
    partialTrace_forces_database_repair,
    fullTrace_repair_frontier_excludes_database,
    partialTrace_repair_frontier_matches_missing_locus,
    surfaceSupport_not_faithful_to_missing_locus,
    surfaceSupport_not_faithful_to_repair_frontier⟩

end TraceLocus
end QualitySurface
end Formal.AG.Research
