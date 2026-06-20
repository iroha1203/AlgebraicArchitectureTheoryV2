import Formal.AG.Research.QualitySurface.SupportLocalRepairFrontier
import Formal.AG.Research.QualitySurface.SourceRefExactVisualization

/-!
Cycle 33 evidence for `G-aat-quality-surface-01`.

This file gives a finite supported-token mismatch obstruction: a declared
support-local repair action can satisfy the Cycle-31 frontier restriction and
collapse the post-repair frontier while still writing the wrong source-ref token
inside the repaired support.  The visible packet-to-tuple surface is flat, but
source-ref exact visualization fails because protected token identity is wrong.
The claim is relative to supplied finite source-ref packets and declared repair
actions; it does not assert canonical repair planning, source extraction
completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SupportedTokenMismatchObstruction

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open SupportLocalRepairFrontier

/-! ## Wrong-token repair action -/

/--
A storage repair action that fills the declared support but writes the worker
source-ref token at storage.  This is enough to clear the missing frontier but
not enough to restore source-ref exactness against the supplied full packet.
-/
def supportedTokenMismatchRepairAction : SourceRefRepairAction where
  repairSupport := storageRepairFrontier
  repairedSourceRefTable
    | CodeAtom.endpoint => some SourceRefToken.endpointRef
    | CodeAtom.storage => some SourceRefToken.workerRef
    | CodeAtom.worker => some SourceRefToken.workerRef
  repairedObligation := StateSeparation.ObligationKind.none

/-- The finite packet obtained by applying the supported-token mismatch repair. -/
def supportedTokenMismatchRepairPacket : SourceRefPacket :=
  repairPacket supportedTokenMismatchRepairAction partialPacket

/--
The wrong-token action is still support-local in the Cycle-31 sense: it supplies
some token on the declared support and preserves the source-ref table outside
that support.
-/
theorem supportedTokenMismatch_supportLocal :
    SupportLocalSourceRefRepair
      supportedTokenMismatchRepairAction partialPacket where
  fillsSupportedAtoms := by
    intro atom _hsupport hrepair
    change atom = CodeAtom.storage at hrepair
    cases hrepair
    exact ⟨SourceRefToken.workerRef, rfl⟩
  preservesOutsideSupport := by
    intro atom hout
    change ¬ atom = CodeAtom.storage at hout
    cases atom with
    | endpoint => rfl
    | storage => exact False.elim (hout rfl)
    | worker => rfl

/-! ## Frontier success -/

/-- The Cycle-31 frontier restriction formula holds for the wrong-token action. -/
theorem supportedTokenMismatch_frontierRestriction_holds
    (atom : CodeAtom) :
    supportedTokenMismatchRepairPacket.repairFrontier atom ↔
      partialPacket.repairFrontier atom ∧
        ¬ supportedTokenMismatchRepairAction.repairSupport atom :=
  supportLocalRepair_frontier_eq_preFrontier_diff_support
    supportedTokenMismatch_supportLocal partialTrace_repairFrontierExact atom

/-- The wrong-token repair clears the post-repair frontier. -/
theorem supportedTokenMismatch_postFrontier_empty :
    ¬ ∃ atom, supportedTokenMismatchRepairPacket.repairFrontier atom := by
  intro hfrontier
  rcases hfrontier with ⟨atom, hpost⟩
  have hformula := supportedTokenMismatch_frontierRestriction_holds atom
  have hright := hformula.mp hpost
  exact hright.2 hright.1

/-! ## Visible flatness and protected token mismatch -/

/-- The full packet and wrong-token repaired packet agree at the visible surface. -/
theorem supportedTokenMismatch_visiblePacketSurface :
    supportSurfaceReading.Equivalent
      fullPacket supportedTokenMismatchRepairPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro _hsupport <;> trivial

/-- The visible packet agreement projects to visible tuple agreement. -/
theorem supportedTokenMismatch_visibleTupleSurface :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket supportedTokenMismatchRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    supportedTokenMismatch_visiblePacketSurface

/-- The wrong-token repair leaves a storage source-ref table component defect. -/
theorem supportedTokenMismatch_storageSourceRefTableDefect :
    SourceRefTableDefectAt
      fullPacket supportedTokenMismatchRepairPacket CodeAtom.storage := by
  intro hsame
  change some SourceRefToken.storageRef =
    some SourceRefToken.workerRef at hsame
  cases hsame

/-- The storage source-ref table mismatch is a component-indexed packet defect. -/
theorem supportedTokenMismatch_storageSourceRefTableComponentDefect :
    SourceRefPacketHolonomyDefect
      fullPacket supportedTokenMismatchRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) :=
  supportedTokenMismatch_storageSourceRefTableDefect

/-- The wrong-token repair creates nonzero packet holonomy. -/
theorem supportedTokenMismatch_hasPacketHolonomyDefect :
    HasSourceRefPacketHolonomyDefect
      fullPacket supportedTokenMismatchRepairPacket :=
  sourceRefTableDefect_obstructs_noPacketHolonomy
    supportedTokenMismatch_storageSourceRefTableDefect

/--
The wrong-token repair is visibly flat after packet-to-tuple projection, but
protected packet holonomy is nonzero.
-/
theorem supportedTokenMismatch_lossyPacketToTupleVisualization :
    LossyPacketToTupleVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket supportedTokenMismatchRepairPacket :=
  ⟨supportedTokenMismatch_visibleTupleSurface,
    supportedTokenMismatch_hasPacketHolonomyDefect⟩

/-- The storage table defect obstructs source-ref exact visualization. -/
theorem supportedTokenMismatch_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket supportedTokenMismatchRepairPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    supportedTokenMismatch_storageSourceRefTableComponentDefect

/-! ## Theorem package -/

/--
Cycle-33 theorem package: frontier success is not source-ref exactness.  The
wrong-token action is support-local and clears the post frontier, but the
repaired packet remains visibly flat and source-ref lossy relative to the full
packet because storage carries the wrong source-ref token.
-/
theorem supportedTokenMismatchObstruction_package :
    SupportLocalSourceRefRepair
        supportedTokenMismatchRepairAction partialPacket ∧
      (∀ atom,
        supportedTokenMismatchRepairPacket.repairFrontier atom ↔
          partialPacket.repairFrontier atom ∧
            ¬ supportedTokenMismatchRepairAction.repairSupport atom) ∧
      (¬ ∃ atom, supportedTokenMismatchRepairPacket.repairFrontier atom) ∧
      supportSurfaceReading.Equivalent
        fullPacket supportedTokenMismatchRepairPacket ∧
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket supportedTokenMismatchRepairPacket ∧
      SourceRefPacketHolonomyDefect
        fullPacket supportedTokenMismatchRepairPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      HasSourceRefPacketHolonomyDefect
        fullPacket supportedTokenMismatchRepairPacket ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket supportedTokenMismatchRepairPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket supportedTokenMismatchRepairPacket := by
  exact ⟨supportedTokenMismatch_supportLocal,
    supportedTokenMismatch_frontierRestriction_holds,
    supportedTokenMismatch_postFrontier_empty,
    supportedTokenMismatch_visiblePacketSurface,
    supportedTokenMismatch_visibleTupleSurface,
    supportedTokenMismatch_storageSourceRefTableComponentDefect,
    supportedTokenMismatch_hasPacketHolonomyDefect,
    supportedTokenMismatch_lossyPacketToTupleVisualization,
    supportedTokenMismatch_not_sourceRefExactVisualization⟩

end SupportedTokenMismatchObstruction
end QualitySurface
end Formal.AG.Research
