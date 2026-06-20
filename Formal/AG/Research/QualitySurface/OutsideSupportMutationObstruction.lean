import Formal.AG.Research.QualitySurface.SupportLocalRepairFrontier
import Formal.AG.Research.QualitySurface.SourceRefExactVisualization

/-!
Cycle 32 evidence for `G-aat-quality-surface-01`.

This file gives a finite outside-support mutation obstruction for the
support-local frontier restriction theorem.  The mutation action fills the
declared storage support but changes the endpoint source-ref table outside that
support.  The endpoint then reappears in the post-repair frontier, the frontier
restriction formula fails, and the packet-to-tuple visualization is visibly
flat but source-ref lossy.  The claim is relative to supplied finite source-ref
packets and declared repair actions; it does not assert canonical repair
planning, source extraction completeness, ArchMap correctness, or whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace OutsideSupportMutationObstruction

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open SupportLocalRepairFrontier

/-! ## Weak support fill and outside-support mutation -/

/-- A weak fill law that only checks token supply on the declared support. -/
def WeakSupportFillSourceRefRepair
    (action : SourceRefRepairAction) (packet : SourceRefPacket) : Prop :=
  ∀ atom, packet.codeSupport atom -> action.repairSupport atom ->
    ∃ token, action.repairedSourceRefTable atom = some token

/--
Mutation action: it fills the declared storage support but deletes the endpoint
source reference outside that support.
-/
def outsideSupportMutationRepairAction : SourceRefRepairAction where
  repairSupport := storageRepairFrontier
  repairedSourceRefTable
    | CodeAtom.endpoint => none
    | CodeAtom.storage => some SourceRefToken.storageRef
    | CodeAtom.worker => some SourceRefToken.workerRef
  repairedObligation := StateSeparation.ObligationKind.none

/-- The finite packet obtained by applying the outside-support mutation. -/
def outsideSupportMutationRepairPacket : SourceRefPacket :=
  repairPacket outsideSupportMutationRepairAction partialPacket

/-- The mutation action still fills every declared supported atom. -/
theorem outsideSupportMutation_fillsDeclaredSupport :
    WeakSupportFillSourceRefRepair
      outsideSupportMutationRepairAction partialPacket := by
  intro atom _hsupport hrepair
  change atom = CodeAtom.storage at hrepair
  cases hrepair
  exact ⟨SourceRefToken.storageRef, rfl⟩

/-- The mutation action is not support-local: it changes endpoint outside support. -/
theorem outsideSupportMutation_not_supportLocal :
    ¬ SupportLocalSourceRefRepair
      outsideSupportMutationRepairAction partialPacket := by
  intro hlocal
  have hout :
      ¬ outsideSupportMutationRepairAction.repairSupport
        CodeAtom.endpoint := by
    intro h
    cases h
  have hpreserve := hlocal.preservesOutsideSupport CodeAtom.endpoint hout
  change (none : Option SourceRefToken) =
    some SourceRefToken.endpointRef at hpreserve
  cases hpreserve

/-! ## Frontier obstruction -/

/-- The support-external endpoint becomes a post-repair frontier atom. -/
theorem outsideSupportMutation_endpointFrontier :
    outsideSupportMutationRepairPacket.repairFrontier CodeAtom.endpoint :=
  ⟨trivial, rfl⟩

/-- The endpoint was not in the pre-repair frontier. -/
theorem partialPacket_endpoint_not_frontier :
    ¬ partialPacket.repairFrontier CodeAtom.endpoint := by
  intro h
  cases h

/-- The Cycle-31 frontier restriction formula fails at the endpoint. -/
theorem outsideSupportMutation_breaks_frontierRestriction :
    ¬ ∀ atom,
      outsideSupportMutationRepairPacket.repairFrontier atom ↔
        partialPacket.repairFrontier atom ∧
          ¬ outsideSupportMutationRepairAction.repairSupport atom := by
  intro hformula
  have hright :
      partialPacket.repairFrontier CodeAtom.endpoint ∧
        ¬ outsideSupportMutationRepairAction.repairSupport CodeAtom.endpoint :=
    (hformula CodeAtom.endpoint).mp
      outsideSupportMutation_endpointFrontier
  exact partialPacket_endpoint_not_frontier hright.1

/-! ## Visible flatness and protected defects -/

/-- The full packet and mutation-repaired packet agree at the visible surface. -/
theorem outsideSupportMutation_visiblePacketSurface :
    supportSurfaceReading.Equivalent
      fullPacket outsideSupportMutationRepairPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro _ <;> trivial

/-- The visible packet agreement projects to visible tuple agreement. -/
theorem outsideSupportMutation_visibleTupleSurface :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket outsideSupportMutationRepairPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    outsideSupportMutation_visiblePacketSurface

/-- The mutation creates an endpoint repair-frontier component defect. -/
theorem outsideSupportMutation_endpointRepairFrontierDefect :
    SourceRefRepairFrontierDefectAt
      fullPacket outsideSupportMutationRepairPacket CodeAtom.endpoint := by
  intro hsame
  have hfull : fullPacket.repairFrontier CodeAtom.endpoint :=
    hsame.mpr outsideSupportMutation_endpointFrontier
  exact hfull

/-- The mutation creates an endpoint source-ref table component defect. -/
theorem outsideSupportMutation_endpointSourceRefTableDefect :
    SourceRefTableDefectAt
      fullPacket outsideSupportMutationRepairPacket CodeAtom.endpoint := by
  intro hsame
  change some SourceRefToken.endpointRef = none at hsame
  cases hsame

/-- The endpoint repair-frontier defect is a component-indexed packet defect. -/
theorem outsideSupportMutation_endpointRepairFrontierComponentDefect :
    SourceRefPacketHolonomyDefect
      fullPacket outsideSupportMutationRepairPacket
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.endpoint) :=
  outsideSupportMutation_endpointRepairFrontierDefect

/-- The endpoint source-ref table defect is a component-indexed packet defect. -/
theorem outsideSupportMutation_endpointSourceRefTableComponentDefect :
    SourceRefPacketHolonomyDefect
      fullPacket outsideSupportMutationRepairPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
  outsideSupportMutation_endpointSourceRefTableDefect

/-- The mutation creates nonzero packet holonomy. -/
theorem outsideSupportMutation_hasPacketHolonomyDefect :
    HasSourceRefPacketHolonomyDefect
      fullPacket outsideSupportMutationRepairPacket :=
  sourceRefRepairDefect_obstructs_noPacketHolonomy
    outsideSupportMutation_endpointRepairFrontierDefect

/--
The mutation is lossy at the packet-to-tuple visualization: visible tuple data
agree, but protected packet holonomy is nonzero.
-/
theorem outsideSupportMutation_lossyPacketToTupleVisualization :
    LossyPacketToTupleVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket outsideSupportMutationRepairPacket :=
  ⟨outsideSupportMutation_visibleTupleSurface,
    outsideSupportMutation_hasPacketHolonomyDefect⟩

/-- The protected endpoint table defect obstructs source-ref exactness. -/
theorem outsideSupportMutation_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket outsideSupportMutationRepairPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    outsideSupportMutation_endpointSourceRefTableComponentDefect

/-! ## Theorem package -/

/--
Cycle-32 theorem package: a weak declared-support fill can still mutate a
support-external source-ref table, creating a new outside-support frontier atom,
breaking the Cycle-31 frontier restriction formula, and producing a visibly flat
but source-ref lossy packet-to-tuple visualization.
-/
theorem outsideSupportMutationObstruction_package :
    WeakSupportFillSourceRefRepair
        outsideSupportMutationRepairAction partialPacket ∧
      ¬ SupportLocalSourceRefRepair
        outsideSupportMutationRepairAction partialPacket ∧
      outsideSupportMutationRepairPacket.repairFrontier CodeAtom.endpoint ∧
      ¬ partialPacket.repairFrontier CodeAtom.endpoint ∧
      (¬ ∀ atom,
        outsideSupportMutationRepairPacket.repairFrontier atom ↔
          partialPacket.repairFrontier atom ∧
            ¬ outsideSupportMutationRepairAction.repairSupport atom) ∧
      supportSurfaceReading.Equivalent
        fullPacket outsideSupportMutationRepairPacket ∧
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket outsideSupportMutationRepairPacket ∧
      SourceRefPacketHolonomyDefect
        fullPacket outsideSupportMutationRepairPacket
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.endpoint) ∧
      SourceRefPacketHolonomyDefect
        fullPacket outsideSupportMutationRepairPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) ∧
      HasSourceRefPacketHolonomyDefect
        fullPacket outsideSupportMutationRepairPacket ∧
      LossyPacketToTupleVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket outsideSupportMutationRepairPacket ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket outsideSupportMutationRepairPacket := by
  exact ⟨outsideSupportMutation_fillsDeclaredSupport,
    outsideSupportMutation_not_supportLocal,
    outsideSupportMutation_endpointFrontier,
    partialPacket_endpoint_not_frontier,
    outsideSupportMutation_breaks_frontierRestriction,
    outsideSupportMutation_visiblePacketSurface,
    outsideSupportMutation_visibleTupleSurface,
    outsideSupportMutation_endpointRepairFrontierComponentDefect,
    outsideSupportMutation_endpointSourceRefTableComponentDefect,
    outsideSupportMutation_hasPacketHolonomyDefect,
    outsideSupportMutation_lossyPacketToTupleVisualization,
    outsideSupportMutation_not_sourceRefExactVisualization⟩

end OutsideSupportMutationObstruction
end QualitySurface
end Formal.AG.Research
