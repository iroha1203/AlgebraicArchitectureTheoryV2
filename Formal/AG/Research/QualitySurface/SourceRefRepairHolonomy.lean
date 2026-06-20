import Formal.AG.Research.QualitySurface.CodebaseTraceRepairTrajectory
import Formal.AG.Research.QualitySurface.SourceRefExactVisualization

/-!
Cycle 25 evidence for `G-aat-quality-surface-01`.

This file reads the supplied exact source-ref repair action as a finite
holonomy-annihilation step: before repair, the visible packet-to-tuple surface
is flat but source-ref exactness fails; after the declared exact fill, the
repaired packet agrees with the full packet on protected source-ref data, so
packet holonomy, tuple holonomy, and source-ref exact visualization are
restored.  The claim is relative to the supplied finite packet family, the
declared repair action, and the explicit packet-to-tuple bridge.  It does not
assert arbitrary repair reachability, source extraction completeness, ArchMap
correctness, a canonical extractor, a global transport law, or whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SourceRefRepairHolonomyAnnihilation

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion

/-! ## Post-repair protected-data agreement -/

/-- The full packet and repaired storage packet have the same visible surface. -/
theorem full_storageRepair_supportSurface_equivalent :
    supportSurfaceReading.Equivalent fullPacket storageRepairPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro _hsupport <;> trivial

/--
After the exact storage repair, the repaired packet agrees with the full packet
on obligation, repair frontier, and source-ref table.
-/
theorem storageRepairPacket_sameProtectedData_fullPacket :
    SameSourceRefPacketProtectedData fullPacket storageRepairPacket := by
  constructor
  · rfl
  constructor
  · intro atom
    constructor
    · intro hfrontier
      exact False.elim hfrontier
    · intro hfrontier
      change codebaseSupport atom ∧ fullSourceRefTable atom = none at hfrontier
      rcases hfrontier with ⟨_hsupport, htable⟩
      cases atom <;> cases htable
  · intro atom
    cases atom <;> rfl

/-- The exact storage repair annihilates packet-level source-ref holonomy. -/
theorem storageRepairPacket_noPacketHolonomy_fullPacket :
    NoSourceRefPacketHolonomyDefect fullPacket storageRepairPacket :=
  storageRepairPacket_sameProtectedData_fullPacket

/-! ## Packet-to-tuple exact visualization after repair -/

/-- Post-repair packets induce the same visible tuple visualization. -/
theorem storageRepairPacket_tupleVisible_equivalent :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket storageRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    full_storageRepair_supportSurface_equivalent

/-- Packet zero holonomy after repair induces tuple zero holonomy. -/
theorem storageRepairPacket_noTupleHolonomy_fullPacket :
    TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate fullPacket)
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate storageRepairPacket) :=
  noPacketHolonomy_projects_to_noTupleHolonomy
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    storageRepairPacket_noPacketHolonomy_fullPacket

/-- The repaired packet pair is source-ref exact at the packet-to-tuple view. -/
theorem storageRepairPacket_sourceRefExactVisualization :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket storageRepairPacket :=
  ⟨storageRepairPacket_tupleVisible_equivalent,
    storageRepairPacket_noTupleHolonomy_fullPacket⟩

/-! ## Before/after contrast -/

/--
The selected repair step turns a lossy full/partial visualization into a
source-ref exact full/repaired visualization.
-/
theorem repairRestores_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket storageRepairPacket :=
  ⟨full_partial_packetTuple_not_sourceRefExact,
    storageRepairPacket_sourceRefExactVisualization⟩

/--
The exact fill repair kills the protected packet holonomy visible in the
full/partial packet pair.
-/
theorem repairAnnihilates_packetHolonomy :
    HasSourceRefPacketHolonomyDefect fullPacket partialPacket ∧
      NoSourceRefPacketHolonomyDefect fullPacket storageRepairPacket :=
  ⟨full_partial_packet_hasHolonomyDefect,
    storageRepairPacket_noPacketHolonomy_fullPacket⟩

/--
The visible surface alone does not see the holonomy-annihilation step: the
partial and repaired packets have the same support-surface reading, while the
full/partial pair is non-exact and the full/repaired pair is exact.
-/
theorem repairHolonomy_before_after_contrast :
    supportSurfaceReading.Equivalent partialPacket storageRepairPacket ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket storageRepairPacket ∧
      HasSourceRefPacketHolonomyDefect fullPacket partialPacket ∧
      NoSourceRefPacketHolonomyDefect fullPacket storageRepairPacket :=
  ⟨repairTrajectory_visibleSurface_preserved,
    full_partial_packetTuple_lossyVisualization,
    full_partial_packetTuple_not_sourceRefExact,
    storageRepairPacket_sourceRefExactVisualization,
    full_partial_packet_hasHolonomyDefect,
    storageRepairPacket_noPacketHolonomy_fullPacket⟩

/-! ## Theorem package -/

/--
Cycle-25 theorem package: the supplied exact storage repair action annihilates
the finite source-ref packet holonomy and restores source-ref exact
visualization, even though the visible surface by itself does not expose the
protected before/after change.
-/
theorem sourceRefRepairHolonomyAnnihilation_package :
    FillsExactlyMissingSourceRefs storageRepairAction partialPacket ∧
      supportSurfaceReading.Equivalent partialPacket storageRepairPacket ∧
      (¬ ∃ atom, SourceRefMissingLocus storageRepairPacket atom) ∧
      (¬ ∃ atom, storageRepairPacket.repairFrontier atom) ∧
      RepairFrontierExact storageRepairPacket ∧
      SourceRefAvailableOn storageRepairPacket.codeSupport
        storageRepairPacket.sourceRefTable ∧
      SameSourceRefPacketProtectedData fullPacket storageRepairPacket ∧
      NoSourceRefPacketHolonomyDefect fullPacket storageRepairPacket ∧
      TupleHolonomyDefectInvariant.NoTupleHolonomyDefect
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate fullPacket)
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate storageRepairPacket) ∧
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket storageRepairPacket ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      HasSourceRefPacketHolonomyDefect fullPacket partialPacket :=
  ⟨storageRepairAction_exactly_fills_missingRefs,
    repairTrajectory_visibleSurface_preserved,
    repairTrajectory_missingLocus_collapses,
    repairTrajectory_repairFrontier_collapses,
    repairTrajectory_repairFrontierExact,
    repairTrajectory_available_on_support,
    storageRepairPacket_sameProtectedData_fullPacket,
    storageRepairPacket_noPacketHolonomy_fullPacket,
    storageRepairPacket_noTupleHolonomy_fullPacket,
    storageRepairPacket_sourceRefExactVisualization,
    full_partial_packetTuple_lossyVisualization,
    full_partial_packetTuple_not_sourceRefExact,
    full_partial_packet_hasHolonomyDefect⟩

end SourceRefRepairHolonomyAnnihilation
end QualitySurface
end Formal.AG.Research
