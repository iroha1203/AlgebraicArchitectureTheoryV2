import Formal.AG.Research.QualitySurface.SupportLocalRepairFrontier

/-!
Cycle 35 evidence for `G-aat-quality-surface-01`.

This file extracts the frontier-local law behind the support-local repair
frontier formula.  The law is stated at the missing-locus level: supported
repair atoms are cleared from the post missing locus, and outside the declared
repair support the missing locus is preserved and reflected.  This criterion is
equivalent to the post-frontier formula under exact pre-frontiers, follows from
the table-level `SupportLocalSourceRefRepair` law, and is strictly weaker than
that table-level law.  The result is relative to supplied finite source-ref
packets and declared repair actions; it does not assert canonical repair
planning, source extraction completeness, ArchMap correctness, source-ref exact
visualization, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace FrontierLocalFormulaMinimality

open CodebaseTracePacket
open CodebaseTraceRepairTrajectory
open SupportLocalRepairFrontier

/-! ## Frontier-local repair law -/

/--
A repair action is frontier-local when it has exactly the missing-locus behavior
needed for the support-local frontier formula: it clears supported repair atoms
from the post missing locus and preserves/refects missingness outside its
declared repair support.

This is intentionally weaker than table-level source-ref preservation: outside
support, token identity may change as long as missingness is unchanged.
-/
structure FrontierLocalSourceRefRepair
    (action : SourceRefRepairAction) (packet : SourceRefPacket) : Prop where
  clearsSupportedMissing :
    ∀ atom, packet.codeSupport atom -> action.repairSupport atom ->
      ¬ SourceRefMissingLocus (repairPacket action packet) atom
  preservesOutsideMissing :
    ∀ atom, ¬ action.repairSupport atom ->
      (SourceRefMissingLocus (repairPacket action packet) atom ↔
        SourceRefMissingLocus packet atom)

/--
The table-level support-local law of Cycle 31 implies the frontier-local law.
-/
theorem supportLocal_implies_frontierLocal
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hlocal : SupportLocalSourceRefRepair action packet) :
    FrontierLocalSourceRefRepair action packet where
  clearsSupportedMissing := by
    intro atom hsupport hrepair
    exact hlocal.supported_atoms_not_missing hsupport hrepair
  preservesOutsideMissing := by
    intro atom hout
    exact hlocal.outside_preserves_missing_iff hout

/-! ## Frontier-locality is the sharp formula criterion -/

/--
Under an exact pre-frontier, frontier-locality gives the post-frontier formula:
post frontier is pre frontier with the declared support removed.
-/
theorem frontierLocal_frontierRestriction
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hfrontier : FrontierLocalSourceRefRepair action packet)
    (hexact : RepairFrontierExact packet)
    (atom : CodeAtom) :
    (repairPacket action packet).repairFrontier atom ↔
      packet.repairFrontier atom ∧ ¬ action.repairSupport atom := by
  constructor
  · intro hpost
    have hout : ¬ action.repairSupport atom := by
      intro hrepair
      exact hfrontier.clearsSupportedMissing atom hpost.1 hrepair hpost
    have hmissingPre :
        SourceRefMissingLocus packet atom :=
      (hfrontier.preservesOutsideMissing atom hout).mp hpost
    exact ⟨(hexact atom).mpr hmissingPre, hout⟩
  · intro hpre
    rcases hpre with ⟨hfrontierPre, hout⟩
    have hmissingPre :
        SourceRefMissingLocus packet atom :=
      (hexact atom).mp hfrontierPre
    exact (hfrontier.preservesOutsideMissing atom hout).mpr hmissingPre

/--
Conversely, under an exact pre-frontier, the post-frontier formula implies the
frontier-local missing-locus law.
-/
theorem frontierRestriction_implies_frontierLocal
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hexact : RepairFrontierExact packet)
    (hformula :
      ∀ atom,
        (repairPacket action packet).repairFrontier atom ↔
          packet.repairFrontier atom ∧ ¬ action.repairSupport atom) :
    FrontierLocalSourceRefRepair action packet where
  clearsSupportedMissing := by
    intro atom _hsupport hrepair hmissingPost
    have hout :
        ¬ action.repairSupport atom :=
      ((hformula atom).mp hmissingPost).2
    exact hout hrepair
  preservesOutsideMissing := by
    intro atom hout
    constructor
    · intro hmissingPost
      have hfrontierPre :
          packet.repairFrontier atom :=
        ((hformula atom).mp hmissingPost).1
      exact (hexact atom).mp hfrontierPre
    · intro hmissingPre
      have hfrontierPre :
          packet.repairFrontier atom :=
        (hexact atom).mpr hmissingPre
      exact (hformula atom).mpr ⟨hfrontierPre, hout⟩

/--
For exact pre-frontiers, frontier-locality is equivalent to the support-deleting
post-frontier formula.
-/
theorem frontierLocal_iff_frontierRestriction
    {action : SourceRefRepairAction} {packet : SourceRefPacket}
    (hexact : RepairFrontierExact packet) :
    FrontierLocalSourceRefRepair action packet ↔
      ∀ atom,
        (repairPacket action packet).repairFrontier atom ↔
          packet.repairFrontier atom ∧ ¬ action.repairSupport atom := by
  constructor
  · intro hfrontier atom
    exact frontierLocal_frontierRestriction hfrontier hexact atom
  · intro hformula
    exact frontierRestriction_implies_frontierLocal hexact hformula

/-! ## Strictness witness: frontier-local is weaker than table-local -/

/--
A repair action that fills the storage frontier but renames the endpoint token
outside the declared repair support.  Missingness is preserved outside support,
but table identity is not.
-/
def tokenRenamingOutsideStorageRepairAction : SourceRefRepairAction where
  repairSupport := storageRepairFrontier
  repairedSourceRefTable
    | CodeAtom.endpoint => some SourceRefToken.workerRef
    | CodeAtom.storage => some SourceRefToken.storageRef
    | CodeAtom.worker => some SourceRefToken.workerRef
  repairedObligation := StateSeparation.ObligationKind.none

/-- The finite packet obtained from the token-renaming action. -/
def tokenRenamingOutsideStorageRepairPacket : SourceRefPacket :=
  repairPacket tokenRenamingOutsideStorageRepairAction partialPacket

/-- The token-renaming action is frontier-local. -/
theorem tokenRenaming_frontierLocal :
    FrontierLocalSourceRefRepair
      tokenRenamingOutsideStorageRepairAction partialPacket where
  clearsSupportedMissing := by
    intro atom _hsupport hrepair hmissing
    change atom = CodeAtom.storage at hrepair
    cases hrepair
    rcases hmissing with ⟨_hsupportPost, hnone⟩
    change some SourceRefToken.storageRef = none at hnone
    cases hnone
  preservesOutsideMissing := by
    intro atom hout
    constructor
    · intro hmissing
      rcases hmissing with ⟨_hsupport, hnone⟩
      cases atom with
      | endpoint =>
          change some SourceRefToken.workerRef = none at hnone
          cases hnone
      | storage =>
          exact False.elim (hout rfl)
      | worker =>
          change some SourceRefToken.workerRef = none at hnone
          cases hnone
    · intro hmissing
      rcases hmissing with ⟨_hsupport, hnone⟩
      cases atom with
      | endpoint =>
          change some SourceRefToken.endpointRef = none at hnone
          cases hnone
      | storage =>
          exact False.elim (hout rfl)
      | worker =>
          change some SourceRefToken.workerRef = none at hnone
          cases hnone

/-- The token-renaming action still satisfies the frontier restriction formula. -/
theorem tokenRenaming_frontierRestriction
    (atom : CodeAtom) :
    tokenRenamingOutsideStorageRepairPacket.repairFrontier atom ↔
      partialPacket.repairFrontier atom ∧
        ¬ tokenRenamingOutsideStorageRepairAction.repairSupport atom :=
  frontierLocal_frontierRestriction
    tokenRenaming_frontierLocal partialTrace_repairFrontierExact atom

/--
The token-renaming action is not table-level support-local: it changes the
endpoint source-ref token outside its declared storage support.
-/
theorem tokenRenaming_not_supportLocal :
    ¬ SupportLocalSourceRefRepair
      tokenRenamingOutsideStorageRepairAction partialPacket := by
  intro hlocal
  have hout :
      ¬ tokenRenamingOutsideStorageRepairAction.repairSupport
        CodeAtom.endpoint := by
    intro h
    cases h
  have hpreserve := hlocal.preservesOutsideSupport CodeAtom.endpoint hout
  change some SourceRefToken.workerRef =
    some SourceRefToken.endpointRef at hpreserve
  cases hpreserve

/-! ## The two frontier-formula conjuncts are both necessary -/

/--
The `¬ repairSupport` conjunct is necessary: storage is in the pre-frontier and
in the declared repair support, but it is not in the post frontier.
-/
theorem frontierFormula_outsideSupportConjunct_is_necessary :
    ∃ atom,
      partialPacket.repairFrontier atom ∧
        storageRepairAction.repairSupport atom ∧
        ¬ storageRepairPacket.repairFrontier atom := by
  refine ⟨CodeAtom.storage, ?_⟩
  constructor
  · exact partialTrace_forces_storage_repair
  constructor
  · rfl
  · intro hpost
    exact repairTrajectory_repairFrontier_collapses
      ⟨CodeAtom.storage, hpost⟩

/--
The pre-frontier conjunct is necessary: endpoint is outside the declared repair
support, but it was not in the pre-frontier and is not in the post frontier.
-/
theorem frontierFormula_preFrontierConjunct_is_necessary :
    ∃ atom,
      ¬ storageRepairAction.repairSupport atom ∧
        ¬ partialPacket.repairFrontier atom ∧
        ¬ storageRepairPacket.repairFrontier atom := by
  refine ⟨CodeAtom.endpoint, ?_⟩
  constructor
  · intro h
    change CodeAtom.endpoint = CodeAtom.storage at h
    cases h
  constructor
  · intro h
    change CodeAtom.endpoint = CodeAtom.storage at h
    cases h
  · intro hpost
    exact repairTrajectory_repairFrontier_collapses
      ⟨CodeAtom.endpoint, hpost⟩

/-- The two conjuncts of the support-deleting frontier formula are independent. -/
theorem frontierFormula_conjuncts_are_independent :
    (∃ atom,
      partialPacket.repairFrontier atom ∧
        storageRepairAction.repairSupport atom ∧
        ¬ storageRepairPacket.repairFrontier atom) ∧
      (∃ atom,
        ¬ storageRepairAction.repairSupport atom ∧
          ¬ partialPacket.repairFrontier atom ∧
          ¬ storageRepairPacket.repairFrontier atom) := by
  exact ⟨frontierFormula_outsideSupportConjunct_is_necessary,
    frontierFormula_preFrontierConjunct_is_necessary⟩

/-! ## Theorem package -/

/--
Cycle-35 theorem package: frontier-locality is the sharp missing-locus law for
the support-deleting frontier formula.  It follows from table-level
support-locality, is equivalent to the frontier formula under exact
pre-frontiers, is strictly weaker than table-level support-locality, and both
formula conjuncts are necessary.
-/
theorem frontierLocalFormulaMinimality_package :
    (∀ {action : SourceRefRepairAction} {packet : SourceRefPacket},
      SupportLocalSourceRefRepair action packet ->
        FrontierLocalSourceRefRepair action packet) ∧
      (∀ {action : SourceRefRepairAction} {packet : SourceRefPacket},
        RepairFrontierExact packet ->
          (FrontierLocalSourceRefRepair action packet ↔
            ∀ atom,
              (repairPacket action packet).repairFrontier atom ↔
                packet.repairFrontier atom ∧
                  ¬ action.repairSupport atom)) ∧
      FrontierLocalSourceRefRepair
        tokenRenamingOutsideStorageRepairAction partialPacket ∧
      (∀ atom,
        tokenRenamingOutsideStorageRepairPacket.repairFrontier atom ↔
          partialPacket.repairFrontier atom ∧
            ¬ tokenRenamingOutsideStorageRepairAction.repairSupport atom) ∧
      ¬ SupportLocalSourceRefRepair
        tokenRenamingOutsideStorageRepairAction partialPacket ∧
      (∃ atom,
        partialPacket.repairFrontier atom ∧
          storageRepairAction.repairSupport atom ∧
          ¬ storageRepairPacket.repairFrontier atom) ∧
      (∃ atom,
        ¬ storageRepairAction.repairSupport atom ∧
          ¬ partialPacket.repairFrontier atom ∧
          ¬ storageRepairPacket.repairFrontier atom) := by
  exact ⟨by
      intro action packet hlocal
      exact supportLocal_implies_frontierLocal hlocal,
    by
      intro action packet hexact
      exact frontierLocal_iff_frontierRestriction hexact,
    tokenRenaming_frontierLocal,
    tokenRenaming_frontierRestriction,
    tokenRenaming_not_supportLocal,
    frontierFormula_outsideSupportConjunct_is_necessary,
    frontierFormula_preFrontierConjunct_is_necessary⟩

end FrontierLocalFormulaMinimality
end QualitySurface
end Formal.AG.Research
