import Formal.AG.Research.QualitySurface.SelectedSupportDefectLocalization

/-!
Cycle 52 evidence for `G-aat-quality-surface-01`.

This file builds a non-singleton selected correction system with two route
slots.  A two-route staged family is source-ref exact exactly when both route
slots are at the all-branches stage.  Exactness is upward closed under
componentwise stage order, and a mixed family shows that one exact route does
not make the whole family exact.

The claim is relative to the selected two-slot route family, staged selected
correction semantics, and the explicit source-ref packet bridge.  It does not
assert arbitrary multi-route planners, runtime patch synthesis, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace MultiRouteCorrectionSystem

open CodebaseTracePacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SelectedRouteDefectSupportHitting
open SelectedRouteCorrectionExactness
open SelectedRouteFamilyExactness
open ParametrizedSelectedCorrectionSystem
open ParametrizedLossAwareAtlas
open ParametrizedLossAwareCell
open RepairStage

/-! ## Two-route staged correction families -/

/-- Two selected route slots in a non-singleton correction family. -/
inductive RouteSlot where
  | primary
  | secondary
  deriving DecidableEq, Fintype

open RouteSlot

/-- A staged correction assignment for two route slots. -/
structure StagePair where
  primaryStage : RepairStage
  secondaryStage : RepairStage
  deriving DecidableEq

/-- Read a pair assignment at a route slot. -/
def StagePair.stage (pair : StagePair) : RouteSlot -> RepairStage
  | primary => pair.primaryStage
  | secondary => pair.secondaryStage

/-- Left packets of the two-route staged correction family. -/
def pairFamilyLeft (pair : StagePair) : RouteSlot -> SourceRefPacket :=
  fun slot => correctedVisibleRouteLeft (stagedCorrection (pair.stage slot))

/-- Right packets of the two-route staged correction family. -/
def pairFamilyRight : RouteSlot -> SourceRefPacket :=
  fun _slot => visibleRouteRight

/-- Source-ref exactness of the whole two-route family. -/
def PairFamilySourceRefExact (pair : StagePair) : Prop :=
  FamilySourceRefExact (pairFamilyLeft pair) pairFamilyRight

/-- Both route slots are at the all-branches stage. -/
def PairAllBranches (pair : StagePair) : Prop :=
  pair.primaryStage = allBranches ∧
    pair.secondaryStage = allBranches

/-- The two-route family is exact exactly when both slots are all-branches. -/
theorem pairFamilySourceRefExact_iff_allBranches
    (pair : StagePair) :
    PairFamilySourceRefExact pair ↔
      PairAllBranches pair := by
  constructor
  · intro hexact
    exact ⟨(stagedCorrection_exact_iff_allBranches
        pair.primaryStage).mp (by
          simpa [pairFamilyLeft, pairFamilyRight, StagePair.stage,
            CorrectionSourceRefExact] using hexact primary),
      (stagedCorrection_exact_iff_allBranches
        pair.secondaryStage).mp (by
          simpa [pairFamilyLeft, pairFamilyRight, StagePair.stage,
            CorrectionSourceRefExact] using hexact secondary)⟩
  · intro hall slot
    cases slot with
    | primary =>
        simpa [PairFamilySourceRefExact, pairFamilyLeft, pairFamilyRight,
          StagePair.stage, hall.1] using stagedCorrection_allBranches_exact
    | secondary =>
        simpa [PairFamilySourceRefExact, pairFamilyLeft, pairFamilyRight,
          StagePair.stage, hall.2] using stagedCorrection_allBranches_exact

/-! ## Componentwise stage order -/

/-- Componentwise stage order for two-route correction families. -/
def StagePairLe (left right : StagePair) : Prop :=
  StageLe left.primaryStage right.primaryStage ∧
    StageLe left.secondaryStage right.secondaryStage

/-- If all-branches is below a stage, that stage is all-branches. -/
theorem stageLe_allBranches_right
    {stage : RepairStage}
    (hle : StageLe allBranches stage) :
    stage = allBranches := by
  cases stage with
  | uncorrected =>
      cases hle
  | obligationOnly =>
      cases hle
  | allBranches =>
      rfl

/-- Two-route family exactness is upward closed under componentwise stage order. -/
theorem pairFamilySourceRefExact_upwardClosed
    {left right : StagePair}
    (hle : StagePairLe left right)
    (hexact : PairFamilySourceRefExact left) :
    PairFamilySourceRefExact right := by
  have hallLeft :=
    (pairFamilySourceRefExact_iff_allBranches left).mp hexact
  apply (pairFamilySourceRefExact_iff_allBranches right).mpr
  exact ⟨stageLe_allBranches_right (by
      simpa [hallLeft.1] using hle.1),
    stageLe_allBranches_right (by
      simpa [hallLeft.2] using hle.2)⟩

/-! ## Concrete all-hit and mixed two-route families -/

/-- Both slots are restored. -/
def allBranchesPair : StagePair where
  primaryStage := allBranches
  secondaryStage := allBranches

/-- Only the primary slot is restored; the secondary slot is obligation-only. -/
def mixedPair : StagePair where
  primaryStage := allBranches
  secondaryStage := obligationOnly

/-- The all-branches pair is family exact. -/
theorem allBranchesPair_sourceRefExact :
    PairFamilySourceRefExact allBranchesPair :=
  (pairFamilySourceRefExact_iff_allBranches allBranchesPair).mpr
    ⟨rfl, rfl⟩

/-- The mixed pair has an exact primary route. -/
theorem mixedPair_primary_sourceRefExact :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (pairFamilyLeft mixedPair primary) (pairFamilyRight primary) := by
  simpa [pairFamilyLeft, pairFamilyRight, mixedPair, StagePair.stage]
    using stagedCorrection_allBranches_exact

/-- The mixed pair has a protected-support-loss secondary route. -/
theorem mixedPair_secondary_protectedSupportLoss :
    ParamProtectedSupportLossCell (stagedCorrectionCell obligationOnly) :=
  stagedCell_protectedSupportLoss_of_not_allBranches (by intro h; cases h)

/-- One exact route does not make the two-route family exact. -/
theorem mixedPair_not_familySourceRefExact :
    ¬ PairFamilySourceRefExact mixedPair := by
  intro hexact
  have hall :=
    (pairFamilySourceRefExact_iff_allBranches mixedPair).mp hexact
  cases hall.2

/-! ## Theorem package -/

/--
Cycle-52 theorem package: a non-singleton staged correction family is exact
exactly when every route slot is all-branches; exactness is upward closed under
componentwise stage order; a mixed pair witnesses that a single exact route is
not enough for family exactness.
-/
theorem multiRouteCorrectionSystem_package :
    (∀ pair,
      PairFamilySourceRefExact pair ↔
        PairAllBranches pair) ∧
    (∀ {left right},
      StagePairLe left right ->
        PairFamilySourceRefExact left ->
          PairFamilySourceRefExact right) ∧
    PairFamilySourceRefExact allBranchesPair ∧
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (pairFamilyLeft mixedPair primary) (pairFamilyRight primary) ∧
    ParamProtectedSupportLossCell (stagedCorrectionCell obligationOnly) ∧
    ¬ PairFamilySourceRefExact mixedPair := by
  exact ⟨pairFamilySourceRefExact_iff_allBranches,
    fun hle hexact => pairFamilySourceRefExact_upwardClosed hle hexact,
    allBranchesPair_sourceRefExact,
    mixedPair_primary_sourceRefExact,
    mixedPair_secondary_protectedSupportLoss,
    mixedPair_not_familySourceRefExact⟩

end MultiRouteCorrectionSystem
end QualitySurface
end Formal.AG.Research
