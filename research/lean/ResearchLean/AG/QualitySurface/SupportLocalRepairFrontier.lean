import ResearchLean.AG.QualitySurface.CodebaseTraceRepairTrajectory

/-!
Cycle 31 evidence for `G-aat-quality-surface-01`.

This file turns a declared source-ref repair support into a bounded frontier
calculus.  A support-local repair action supplies source-reference tokens on
its declared support and preserves the source-reference table outside that
support.  Under an exact pre-repair frontier, the post-repair frontier is
exactly the pre-repair frontier with the declared repair support removed.  The
claim is relative to supplied finite source-ref packets and declared repair
actions; it does not assert canonical repair planning, source extraction
completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SupportLocalRepairFrontier

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory

/-! ## Support-local repair law -/

/--
A source-ref repair action is support-local for a packet when it supplies a
token on every supported selected atom and preserves the source-ref table
outside the declared support.  The definition is table-level; it does not
assume the post-frontier formula that is proved below.
-/
structure SupportLocalSourceRefRepair
    (action : SourceRefRepairAction) (packet : SourceRefPacket) : Prop where
  fillsSupportedAtoms :
    ∀ atom, packet.codeSupport atom -> action.repairSupport atom ->
      ∃ token, action.repairedSourceRefTable atom = some token
  preservesOutsideSupport :
    ∀ atom, ¬ action.repairSupport atom ->
      action.repairedSourceRefTable atom = packet.sourceRefTable atom

/-! ## Frontier restriction -/

/-- Outside the declared repair support, source-ref missing loci are preserved. -/
theorem SupportLocalSourceRefRepair.outside_preserves_missing_iff
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hlocal : SupportLocalSourceRefRepair action packet)
    {atom : CodeAtom} (hout : ¬ action.repairSupport atom) :
    SourceRefMissingLocus (repairPacket action packet) atom ↔
      SourceRefMissingLocus packet atom := by
  constructor
  · intro hmissing
    rcases hmissing with ⟨hsupport, hnone⟩
    refine ⟨hsupport, ?_⟩
    change action.repairedSourceRefTable atom = none at hnone
    rw [← hlocal.preservesOutsideSupport atom hout]
    exact hnone
  · intro hmissing
    rcases hmissing with ⟨hsupport, hnone⟩
    refine ⟨hsupport, ?_⟩
    change action.repairedSourceRefTable atom = none
    rw [hlocal.preservesOutsideSupport atom hout]
    exact hnone

/-- Supported selected atoms are not missing after a support-local repair. -/
theorem SupportLocalSourceRefRepair.supported_atoms_not_missing
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hlocal : SupportLocalSourceRefRepair action packet)
    {atom : CodeAtom}
    (hsupport : packet.codeSupport atom)
    (hrepair : action.repairSupport atom) :
    ¬ SourceRefMissingLocus (repairPacket action packet) atom := by
  intro hmissing
  rcases hmissing with ⟨_hsupportPost, hnone⟩
  change action.repairedSourceRefTable atom = none at hnone
  rcases hlocal.fillsSupportedAtoms atom hsupport hrepair with ⟨token, hsome⟩
  rw [hsome] at hnone
  cases hnone

/--
For a support-local action over an exact pre-frontier, the post-repair frontier
is the pre-repair frontier with the declared support removed.
-/
theorem supportLocalRepair_frontier_eq_preFrontier_diff_support
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hlocal : SupportLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (repairPacket action packet).repairFrontier atom ↔
      packet.repairFrontier atom ∧ ¬ action.repairSupport atom := by
  constructor
  · intro hpost
    rcases hpost with ⟨hsupport, hnone⟩
    have hout : ¬ action.repairSupport atom := by
      intro hrepair
      exact hlocal.supported_atoms_not_missing hsupport hrepair
        ⟨hsupport, hnone⟩
    have hmissingPre :
        SourceRefMissingLocus packet atom :=
      (hlocal.outside_preserves_missing_iff hout).mp
        ⟨hsupport, hnone⟩
    exact ⟨(hexact atom).mpr hmissingPre, hout⟩
  · intro hpre
    rcases hpre with ⟨hfrontierPre, hout⟩
    have hmissingPre :
        SourceRefMissingLocus packet atom :=
      (hexact atom).mp hfrontierPre
    have hmissingPost :
        SourceRefMissingLocus (repairPacket action packet) atom :=
      (hlocal.outside_preserves_missing_iff hout).mpr hmissingPre
    exact hmissingPost

/-- Outside the declared support, pre-frontier membership is preserved. -/
theorem supportLocalRepair_preserves_outsideFrontier
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hlocal : SupportLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    {atom : CodeAtom}
    (hout : ¬ action.repairSupport atom) :
    (repairPacket action packet).repairFrontier atom ↔
      packet.repairFrontier atom := by
  constructor
  · intro hpost
    exact ((supportLocalRepair_frontier_eq_preFrontier_diff_support
      hlocal hexact atom).mp hpost).1
  · intro hfrontier
    exact (supportLocalRepair_frontier_eq_preFrontier_diff_support
      hlocal hexact atom).mpr ⟨hfrontier, hout⟩

/-- A support-local repair clears every pre-frontier atom in its support. -/
theorem supportLocalRepair_clears_supportedFrontier
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hlocal : SupportLocalSourceRefRepair action packet)
    {atom : CodeAtom}
    (hsupport : packet.codeSupport atom)
    (hrepair : action.repairSupport atom) :
    ¬ (repairPacket action packet).repairFrontier atom := by
  intro hpost
  exact hlocal.supported_atoms_not_missing hsupport hrepair hpost

/-! ## Storage repair instance -/

/-- The supplied storage repair action is support-local for the partial packet. -/
theorem storageRepairAction_supportLocal :
    SupportLocalSourceRefRepair storageRepairAction partialPacket where
  fillsSupportedAtoms := by
    intro atom _hsupport hrepair
    change atom = CodeAtom.storage at hrepair
    cases hrepair
    exact ⟨SourceRefToken.storageRef, rfl⟩
  preservesOutsideSupport := by
    intro atom hout
    change ¬ atom = CodeAtom.storage at hout
    cases atom with
    | endpoint => rfl
    | storage =>
        exact False.elim (hout rfl)
    | worker => rfl

/-- The storage repair frontier is the pre-frontier with storage support removed. -/
theorem storageRepairAction_frontier_eq_preFrontier_diff_support
    (atom : CodeAtom) :
    storageRepairPacket.repairFrontier atom ↔
      partialPacket.repairFrontier atom ∧
        ¬ storageRepairAction.repairSupport atom :=
  supportLocalRepair_frontier_eq_preFrontier_diff_support
    storageRepairAction_supportLocal
    partialTrace_repairFrontierExact atom

/-! ## Theorem package -/

/--
Cycle-31 theorem package: support-local repair actions give a non-circular
frontier restriction formula, outside-support frontier preservation, supported
frontier clearing, and the selected storage repair instance.
-/
theorem supportLocalRepairFrontierRestriction_package :
    (∀ {action : SourceRefRepairAction} {packet : SourceRefPacket},
      SupportLocalSourceRefRepair action packet ->
      RepairFrontierExact packet ->
      ∀ atom,
        (repairPacket action packet).repairFrontier atom ↔
          packet.repairFrontier atom ∧ ¬ action.repairSupport atom) ∧
      (∀ {action : SourceRefRepairAction} {packet : SourceRefPacket},
        SupportLocalSourceRefRepair action packet ->
        RepairFrontierExact packet ->
        ∀ atom,
          ¬ action.repairSupport atom ->
            ((repairPacket action packet).repairFrontier atom ↔
              packet.repairFrontier atom)) ∧
      (∀ {action : SourceRefRepairAction} {packet : SourceRefPacket},
        SupportLocalSourceRefRepair action packet ->
        ∀ atom,
          packet.codeSupport atom ->
          action.repairSupport atom ->
            ¬ (repairPacket action packet).repairFrontier atom) ∧
      SupportLocalSourceRefRepair storageRepairAction partialPacket ∧
      (∀ atom,
        storageRepairPacket.repairFrontier atom ↔
          partialPacket.repairFrontier atom ∧
            ¬ storageRepairAction.repairSupport atom) := by
  exact ⟨by
      intro action packet hlocal hexact atom
      exact supportLocalRepair_frontier_eq_preFrontier_diff_support
        hlocal hexact atom,
    by
      intro action packet hlocal hexact atom hout
      exact supportLocalRepair_preserves_outsideFrontier
        hlocal hexact hout,
    by
      intro action packet hlocal atom hsupport hrepair
      exact supportLocalRepair_clears_supportedFrontier
        hlocal hsupport hrepair,
    storageRepairAction_supportLocal,
    storageRepairAction_frontier_eq_preFrontier_diff_support⟩

end SupportLocalRepairFrontier
end QualitySurface
end ResearchLean.AG
