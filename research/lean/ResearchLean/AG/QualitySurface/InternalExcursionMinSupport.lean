import ResearchLean.AG.QualitySurface.RouteDefectExcursionSupport

/-!
Cycle 41 evidence for `G-aat-quality-surface-01`.

This file connects the route-internal excursion witness from Cycle 40 with a
finite minimal-support hitting calculus.  The selected finite witness is the
token-swap/un-swap route chain: its endpoint route support is empty, but its
internal support is grounded at the endpoint/worker source-ref table
coordinates.  We read those two coordinates as selected minimal internal
support branches and prove that a correction hitting only one branch does not
eliminate the internal excursion, while a correction hitting both branches hits
every selected branch.

The claim is relative to supplied finite source-ref packets, a selected
length-two route chain, and a selected internal support atom vocabulary.  It
does not assert global repair planning, source extraction completeness, ArchMap
correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace InternalExcursionMinSupport

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open RouteDefectExcursionSupport

/-! ## Internal excursion support atoms -/

/-- Selected protected coordinates used to detect the token-swap/un-swap excursion. -/
inductive InternalExcursionAtom where
  | endpointTable
  | workerTable
  deriving DecidableEq, Fintype

open InternalExcursionAtom

/-- Embedding of the selected internal-excursion atom vocabulary into packet components. -/
def internalExcursionAtomComponent :
    InternalExcursionAtom -> SourceRefPacketProtectedComponent
  | endpointTable => SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint
  | workerTable => SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.worker

/-- Each selected internal-excursion atom is grounded in the token-swap/un-swap internal support. -/
theorem tokenSwapUnswap_internalExcursionAtomSupport
    (atom : InternalExcursionAtom) :
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (internalExcursionAtomComponent atom) := by
  cases atom with
  | endpointTable => exact tokenSwapUnswap_internalSupport_endpointTable
  | workerTable => exact tokenSwapUnswap_internalSupport_workerTable

/-- The token-swap/un-swap witness carries both selected internal support atoms. -/
def TokenSwapUnswapSelectedInternalSupportGrounded : Prop :=
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (internalExcursionAtomComponent endpointTable) ∧
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (internalExcursionAtomComponent workerTable) ∧
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      SourceRefPacketProtectedComponent.obligation ∧
    (∀ atom,
      ¬ InternalRouteDefectSupport
        tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
        (SourceRefPacketProtectedComponent.repairFrontier atom)) ∧
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage)

/-- The selected internal atom support is grounded by the Cycle-40 exact table-pair computation. -/
theorem tokenSwapUnswap_selectedInternalSupport_grounded :
    TokenSwapUnswapSelectedInternalSupportGrounded :=
  tokenSwapUnswap_internalSupport_exact_tablePair

/-! ## Selected minimal internal support branches -/

/-- Selected minimal internal support branches for the token-swap/un-swap excursion. -/
inductive InternalExcursionBranch where
  | endpointTableBranch
  | workerTableBranch
  deriving DecidableEq, Fintype

open InternalExcursionBranch

/-- The selected atom carried by a minimal internal support branch. -/
def internalExcursionBranchAtom :
    InternalExcursionBranch -> InternalExcursionAtom
  | endpointTableBranch => endpointTable
  | workerTableBranch => workerTable

/-- A branch is grounded when its selected internal atom appears in the internal support. -/
def InternalExcursionBranchGrounded (branch : InternalExcursionBranch) : Prop :=
  InternalRouteDefectSupport
    tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
    (internalExcursionAtomComponent (internalExcursionBranchAtom branch))

/-- Every selected minimal branch is grounded in the token-swap/un-swap internal support. -/
theorem internalExcursionBranch_grounded
    (branch : InternalExcursionBranch) :
    InternalExcursionBranchGrounded branch := by
  cases branch with
  | endpointTableBranch => exact tokenSwapUnswap_internalSupport_endpointTable
  | workerTableBranch => exact tokenSwapUnswap_internalSupport_workerTable

/-- A correction hits a selected branch when it touches that branch's selected atom. -/
def CorrectionHitsBranch
    (correction : InternalExcursionAtom -> Bool)
    (branch : InternalExcursionBranch) : Prop :=
  correction (internalExcursionBranchAtom branch) = true

/-- A selected branch remains after correction when it is grounded and missed. -/
def BranchRemainsAfterCorrection
    (correction : InternalExcursionAtom -> Bool)
    (branch : InternalExcursionBranch) : Prop :=
  InternalExcursionBranchGrounded branch ∧
    ¬ CorrectionHitsBranch correction branch

/-- A correction eliminates the selected internal excursion when it hits every selected branch. -/
def InternalExcursionEliminates
    (correction : InternalExcursionAtom -> Bool) : Prop :=
  ∀ branch, ¬ BranchRemainsAfterCorrection correction branch

/-- A hit branch leaves no after-correction support on that branch. -/
theorem no_afterCorrection_of_hits
    {correction : InternalExcursionAtom -> Bool}
    {branch : InternalExcursionBranch}
    (hhit : CorrectionHitsBranch correction branch) :
    ¬ BranchRemainsAfterCorrection correction branch := by
  intro hafter
  exact hafter.2 hhit

/-- If a correction eliminates the excursion, no selected branch remains. -/
theorem eliminates_no_afterCorrection
    {correction : InternalExcursionAtom -> Bool}
    (helim : InternalExcursionEliminates correction)
    (branch : InternalExcursionBranch) :
    ¬ BranchRemainsAfterCorrection correction branch :=
  helim branch

/-- If a selected grounded branch is missed, it remains after correction. -/
theorem missed_branch_remains_afterCorrection
    {correction : InternalExcursionAtom -> Bool}
    {branch : InternalExcursionBranch}
    (hmiss : ¬ CorrectionHitsBranch correction branch) :
    BranchRemainsAfterCorrection correction branch :=
  ⟨internalExcursionBranch_grounded branch, hmiss⟩

/-- The finite hitting theorem for selected internal excursion branches. -/
theorem hits_every_minInternalSupport_of_eliminates
    {correction : InternalExcursionAtom -> Bool}
    (helim : InternalExcursionEliminates correction) :
    ∀ branch, CorrectionHitsBranch correction branch := by
  intro branch
  cases branch with
  | endpointTableBranch =>
      cases h : correction endpointTable with
      | false =>
          have hmiss :
              ¬ CorrectionHitsBranch correction endpointTableBranch := by
            intro hhit
            change correction endpointTable = true at hhit
            rw [h] at hhit
            cases hhit
          exact False.elim
            (helim endpointTableBranch
              (missed_branch_remains_afterCorrection hmiss))
      | true =>
          exact h
  | workerTableBranch =>
      cases h : correction workerTable with
      | false =>
          have hmiss :
              ¬ CorrectionHitsBranch correction workerTableBranch := by
            intro hhit
            change correction workerTable = true at hhit
            rw [h] at hhit
            cases hhit
          exact False.elim
            (helim workerTableBranch
              (missed_branch_remains_afterCorrection hmiss))
      | true =>
          exact h

/-! ## Finite witness computations -/

/-- The endpoint table branch is grounded. -/
theorem endpointTable_minInternalSupport :
    InternalExcursionBranchGrounded endpointTableBranch :=
  internalExcursionBranch_grounded endpointTableBranch

/-- The worker table branch is grounded. -/
theorem workerTable_minInternalSupport :
    InternalExcursionBranchGrounded workerTableBranch :=
  internalExcursionBranch_grounded workerTableBranch

/-- The selected minimal internal support family is nonempty. -/
theorem internalExcursion_minSupportFamily_nonempty :
    ∃ branch : InternalExcursionBranch, InternalExcursionBranchGrounded branch :=
  ⟨endpointTableBranch, endpointTable_minInternalSupport⟩

/-- The two selected minimal internal support branches are distinct. -/
theorem internalExcursion_minSupportBranches_distinct :
    endpointTableBranch ≠ workerTableBranch := by
  intro h
  cases h

/-- A correction that touches only the endpoint table branch. -/
def endpointTableCorrection : InternalExcursionAtom -> Bool
  | endpointTable => true
  | workerTable => false

/-- A correction that touches both selected table branches. -/
def endpointWorkerCorrection : InternalExcursionAtom -> Bool
  | endpointTable => true
  | workerTable => true

/-- The endpoint-only correction hits the endpoint table branch. -/
theorem endpointOnlyCorrection_hits_endpointTable :
    CorrectionHitsBranch endpointTableCorrection endpointTableBranch :=
  rfl

/-- The endpoint-only correction misses the worker table branch. -/
theorem endpointOnlyCorrection_misses_workerTable :
    ¬ CorrectionHitsBranch endpointTableCorrection workerTableBranch := by
  intro h
  cases h

/-- A correction that hits only the endpoint branch leaves the worker branch after correction. -/
theorem endpointOnlyCorrection_workerBranch_remains :
    BranchRemainsAfterCorrection endpointTableCorrection workerTableBranch :=
  missed_branch_remains_afterCorrection endpointOnlyCorrection_misses_workerTable

/-- A correction that hits only the endpoint branch does not eliminate the internal excursion. -/
theorem endpointOnlyCorrection_does_not_eliminate :
    ¬ InternalExcursionEliminates endpointTableCorrection := by
  intro helim
  exact helim workerTableBranch endpointOnlyCorrection_workerBranch_remains

/-- The endpoint/worker correction eliminates the selected internal excursion. -/
theorem endpointWorkerCorrection_eliminates :
    InternalExcursionEliminates endpointWorkerCorrection := by
  intro branch
  cases branch with
  | endpointTableBranch =>
      exact no_afterCorrection_of_hits rfl
  | workerTableBranch =>
      exact no_afterCorrection_of_hits rfl

/-- The endpoint/worker correction hits every selected minimal internal support branch. -/
theorem endpointWorkerCorrection_hits_every_minInternalSupport :
    ∀ branch, CorrectionHitsBranch endpointWorkerCorrection branch :=
  hits_every_minInternalSupport_of_eliminates
    endpointWorkerCorrection_eliminates

/-! ## Theorem package -/

/--
Cycle-41 theorem package: the token-swap/un-swap internal excursion has a
selected two-branch minimal internal support family; hitting only one branch
does not eliminate the excursion, while hitting endpoint and worker branches
meets every selected minimal support.
-/
theorem internalExcursionMinimalSupport_package :
    TokenSwapUnswapSelectedInternalSupportGrounded ∧
    InternalExcursionBranchGrounded endpointTableBranch ∧
    InternalExcursionBranchGrounded workerTableBranch ∧
    (∃ branch : InternalExcursionBranch, InternalExcursionBranchGrounded branch) ∧
    endpointTableBranch ≠ workerTableBranch ∧
    CorrectionHitsBranch endpointTableCorrection endpointTableBranch ∧
    ¬ CorrectionHitsBranch endpointTableCorrection workerTableBranch ∧
    BranchRemainsAfterCorrection endpointTableCorrection workerTableBranch ∧
    ¬ InternalExcursionEliminates endpointTableCorrection ∧
    InternalExcursionEliminates endpointWorkerCorrection ∧
    (∀ branch, CorrectionHitsBranch endpointWorkerCorrection branch) := by
  exact ⟨tokenSwapUnswap_selectedInternalSupport_grounded,
    endpointTable_minInternalSupport,
    workerTable_minInternalSupport,
    internalExcursion_minSupportFamily_nonempty,
    internalExcursion_minSupportBranches_distinct,
    endpointOnlyCorrection_hits_endpointTable,
    endpointOnlyCorrection_misses_workerTable,
    endpointOnlyCorrection_workerBranch_remains,
    endpointOnlyCorrection_does_not_eliminate,
    endpointWorkerCorrection_eliminates,
    endpointWorkerCorrection_hits_every_minInternalSupport⟩

end InternalExcursionMinSupport
end QualitySurface
end ResearchLean.AG
