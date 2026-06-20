import Formal.AG.Research.QualitySurface.CodebaseTracePacket

/-!
Cycle 21 evidence for `G-aat-quality-surface-01`.

This file turns the supplied finite source-reference packet witness into a
bounded repair trajectory.  The claim is relative to the supplied packet family
and a declared pointwise repair action; it does not assert whole-codebase repair
reachability, source extraction completeness, ArchMap correctness, arbitrary
repair planning, or tooling completeness.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace CodebaseTraceRepairTrajectory

open CodebaseTracePacket

/-! ## Pointwise source-ref repair actions -/

/-- A pointwise repair action over the finite source-reference packet. -/
structure SourceRefRepairAction where
  repairSupport : Set CodeAtom
  repairedSourceRefTable : CodeAtom -> Option SourceRefToken
  repairedObligation : StateSeparation.ObligationKind

/-- The action preserves every source-reference entry that was already present. -/
def PreservesNonMissingSourceRefs
    (action : SourceRefRepairAction) (packet : SourceRefPacket) : Prop :=
  ∀ atom token,
    packet.sourceRefTable atom = some token ->
      action.repairedSourceRefTable atom = some token

/--
The action fills exactly the missing source-ref locus: its repair support is
the pre-repair missing locus, it supplies a token there, and it preserves
non-missing source references.
-/
structure FillsExactlyMissingSourceRefs
    (action : SourceRefRepairAction) (packet : SourceRefPacket) : Prop where
  support_eq_missing :
    ∀ atom, action.repairSupport atom ↔ CodebaseTracePacket.SourceRefMissingLocus packet atom
  fillsMissing :
    ∀ atom, CodebaseTracePacket.SourceRefMissingLocus packet atom ->
      ∃ token, action.repairedSourceRefTable atom = some token
  preservesNonMissing : PreservesNonMissingSourceRefs action packet

/--
Apply a declared repair action.  The visible scalar, verdict, and code support
are preserved; the protected source-ref table and obligation are updated; the
post-repair frontier is recomputed as the post-repair missing locus.
-/
def repairPacket
    (action : SourceRefRepairAction) (packet : SourceRefPacket) :
    SourceRefPacket where
  visibleScalarReading := packet.visibleScalarReading
  verdict := packet.verdict
  codeSupport := packet.codeSupport
  sourceRefTable := action.repairedSourceRefTable
  repairFrontier := fun atom =>
    packet.codeSupport atom ∧ action.repairedSourceRefTable atom = none
  obligation := action.repairedObligation

/-- The recomputed post-repair frontier is exact by construction. -/
theorem repairPacket_repairFrontierExact
    (action : SourceRefRepairAction) (packet : SourceRefPacket) :
    CodebaseTracePacket.RepairFrontierExact (repairPacket action packet) := by
  intro atom
  rfl

/-! ## The storage repair action -/

/-- The storage repair action fills the missing storage source reference. -/
def storageRepairAction : SourceRefRepairAction where
  repairSupport := CodebaseTracePacket.storageRepairFrontier
  repairedSourceRefTable := CodebaseTracePacket.fullSourceRefTable
  repairedObligation := StateSeparation.ObligationKind.none

/-- The finite post-state obtained by applying the storage repair action. -/
def storageRepairPacket : SourceRefPacket :=
  repairPacket storageRepairAction CodebaseTracePacket.partialPacket

/-- The storage action preserves endpoint and worker source references. -/
theorem storageRepairAction_preserves_nonMissingRefs :
    PreservesNonMissingSourceRefs
      storageRepairAction CodebaseTracePacket.partialPacket := by
  intro atom token hsome
  cases atom with
  | endpoint =>
      cases hsome
      rfl
  | storage =>
      cases hsome
  | worker =>
      cases hsome
      rfl

/-- The storage action fills exactly the pre-repair missing storage locus. -/
theorem storageRepairAction_exactly_fills_missingRefs :
    FillsExactlyMissingSourceRefs
      storageRepairAction CodebaseTracePacket.partialPacket where
  support_eq_missing := by
    intro atom
    change atom = CodeAtom.storage ↔
      CodebaseTracePacket.SourceRefMissingLocus CodebaseTracePacket.partialPacket atom
    exact Iff.symm (CodebaseTracePacket.partialTrace_missing_locus_exact_storage atom)
  fillsMissing := by
    intro atom hmissing
    have hstorage :
        atom = CodeAtom.storage :=
      (CodebaseTracePacket.partialTrace_missing_locus_exact_storage atom).mp hmissing
    cases hstorage
    exact ⟨SourceRefToken.storageRef, rfl⟩
  preservesNonMissing := storageRepairAction_preserves_nonMissingRefs

/-! ## Trajectory properties -/

/-- The storage repair trajectory preserves the visible packet surface. -/
theorem repairTrajectory_visibleSurface_preserved :
    CodebaseTracePacket.supportSurfaceReading.Equivalent
      CodebaseTracePacket.partialPacket storageRepairPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro hsupport <;> exact hsupport

/-- After the storage repair, the source-ref missing locus is empty. -/
theorem repairTrajectory_missingLocus_collapses :
    ¬ ∃ atom, CodebaseTracePacket.SourceRefMissingLocus storageRepairPacket atom := by
  intro hmissing
  rcases hmissing with ⟨atom, _hsupport, htable⟩
  cases atom <;> cases htable

/-- After the storage repair, the repair frontier is empty. -/
theorem repairTrajectory_repairFrontier_collapses :
    ¬ ∃ atom, storageRepairPacket.repairFrontier atom := by
  intro hrepair
  rcases hrepair with ⟨atom, hfrontier⟩
  exact repairTrajectory_missingLocus_collapses ⟨atom, hfrontier⟩

/-- The repaired packet remains in the exact repair-frontier regime. -/
theorem repairTrajectory_repairFrontierExact :
    CodebaseTracePacket.RepairFrontierExact storageRepairPacket :=
  repairPacket_repairFrontierExact storageRepairAction CodebaseTracePacket.partialPacket

/-- The repaired packet has full source-ref coverage on the selected support. -/
theorem repairTrajectory_available_on_support :
    CodebaseTracePacket.SourceRefAvailableOn
      storageRepairPacket.codeSupport storageRepairPacket.sourceRefTable := by
  intro atom _hsupport
  cases atom with
  | endpoint => exact ⟨SourceRefToken.endpointRef, rfl⟩
  | storage => exact ⟨SourceRefToken.storageRef, rfl⟩
  | worker => exact ⟨SourceRefToken.workerRef, rfl⟩

/-- The protected source-ref missing locus changes along the trajectory. -/
theorem repairTrajectory_sourceRefMissing_changed :
    ¬ CodebaseTracePacket.SameSourceRefMissingLocus
      CodebaseTracePacket.partialPacket storageRepairPacket := by
  intro hsame
  have hmissingPost :
      CodebaseTracePacket.SourceRefMissingLocus storageRepairPacket CodeAtom.storage :=
    (hsame CodeAtom.storage).mp CodebaseTracePacket.partialTrace_storage_missing_locus
  exact repairTrajectory_missingLocus_collapses
    ⟨CodeAtom.storage, hmissingPost⟩

/-- The protected source-ref repair frontier changes along the trajectory. -/
theorem repairTrajectory_repairFrontier_changed :
    ¬ CodebaseTracePacket.SameCodebaseRepairFrontier
      CodebaseTracePacket.partialPacket storageRepairPacket := by
  intro hsame
  have hrepairPost :
      storageRepairPacket.repairFrontier CodeAtom.storage :=
    (hsame CodeAtom.storage).mp CodebaseTracePacket.partialTrace_forces_storage_repair
  exact repairTrajectory_repairFrontier_collapses
    ⟨CodeAtom.storage, hrepairPost⟩

/-- The source-ref-aware reading detects the repair progress. -/
theorem repairTrajectory_protectedReading_detects_progress :
    ¬ CodebaseTracePacket.sourceRefLocusAwareReading.Equivalent
      CodebaseTracePacket.partialPacket storageRepairPacket := by
  intro heq
  exact repairTrajectory_sourceRefMissing_changed heq.2

/--
The visible surface hides the repair progress, while protected source-ref data
detects it.
-/
theorem repairTrajectory_visibleSurface_not_faithful :
    CodebaseTracePacket.supportSurfaceReading.Equivalent
        CodebaseTracePacket.partialPacket storageRepairPacket ∧
      ¬ CodebaseTracePacket.SameSourceRefMissingLocus
        CodebaseTracePacket.partialPacket storageRepairPacket ∧
      ¬ CodebaseTracePacket.SameCodebaseRepairFrontier
        CodebaseTracePacket.partialPacket storageRepairPacket ∧
      ¬ CodebaseTracePacket.sourceRefLocusAwareReading.Equivalent
        CodebaseTracePacket.partialPacket storageRepairPacket := by
  exact ⟨repairTrajectory_visibleSurface_preserved,
    repairTrajectory_sourceRefMissing_changed,
    repairTrajectory_repairFrontier_changed,
    repairTrajectory_protectedReading_detects_progress⟩

/--
Cycle-21 theorem package: the storage repair action exactly fills the supplied
missing source-ref locus, recomputes an exact empty post-repair frontier, keeps
the visible surface fixed, and exposes repair progress only through protected
source-ref data.
-/
theorem codebaseTraceRepairTrajectory_package :
    FillsExactlyMissingSourceRefs
        storageRepairAction CodebaseTracePacket.partialPacket ∧
      CodebaseTracePacket.supportSurfaceReading.Equivalent
        CodebaseTracePacket.partialPacket storageRepairPacket ∧
      (¬ ∃ atom,
        CodebaseTracePacket.SourceRefMissingLocus storageRepairPacket atom) ∧
      (¬ ∃ atom, storageRepairPacket.repairFrontier atom) ∧
      CodebaseTracePacket.RepairFrontierExact storageRepairPacket ∧
      CodebaseTracePacket.SourceRefAvailableOn
        storageRepairPacket.codeSupport storageRepairPacket.sourceRefTable ∧
      ¬ CodebaseTracePacket.SameSourceRefMissingLocus
        CodebaseTracePacket.partialPacket storageRepairPacket ∧
      ¬ CodebaseTracePacket.SameCodebaseRepairFrontier
        CodebaseTracePacket.partialPacket storageRepairPacket ∧
      ¬ CodebaseTracePacket.sourceRefLocusAwareReading.Equivalent
        CodebaseTracePacket.partialPacket storageRepairPacket := by
  exact ⟨storageRepairAction_exactly_fills_missingRefs,
    repairTrajectory_visibleSurface_preserved,
    repairTrajectory_missingLocus_collapses,
    repairTrajectory_repairFrontier_collapses,
    repairTrajectory_repairFrontierExact,
    repairTrajectory_available_on_support,
    repairTrajectory_sourceRefMissing_changed,
    repairTrajectory_repairFrontier_changed,
    repairTrajectory_protectedReading_detects_progress⟩

end CodebaseTraceRepairTrajectory
end QualitySurface
end Formal.AG.Research
