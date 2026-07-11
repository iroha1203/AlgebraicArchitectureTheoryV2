import ResearchLean.AG.QualitySurface.SelectedRouteFamilyExactness

/-!
Cycle 48 evidence for `G-aat-quality-surface-01`.

This file turns the selected route correction theorem into a parametrized
correction-system theorem.  Corrections are ordered by touched selected atoms;
source-ref exactness is monotone along that order, and any monotone correction
system has an upward-closed exact locus.  A concrete three-stage schedule shows
that touching only the obligation branch is still non-exact, while the all-hit
stage is exact.

The claim is relative to the selected route-defect atom vocabulary, selected
correction semantics, and the explicit source-ref packet bridge.  It does not
assert a global repair planner, runtime patch synthesis, source extraction
completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ParametrizedSelectedCorrectionSystem

open CodebaseTracePacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SelectedRouteDefectSupportHitting
open SelectedRouteCorrectionExactness
open RouteDefectAtom
open RouteDefectBranch

universe u

/-! ## Correction order and exactness -/

/-- A selected correction is below another when every hit selected atom remains hit. -/
def CorrectionLe
    (left right : RouteDefectAtom -> Bool) : Prop :=
  ∀ atom, left atom = true -> right atom = true

/-- A selected correction hits every selected route-defect branch. -/
def CorrectionHitsAllBranches
    (correction : RouteDefectAtom -> Bool) : Prop :=
  ∀ branch, CorrectionHitsRouteDefectBranch correction branch

/-- Source-ref exactness of the corrected selected endpoint route. -/
def CorrectionSourceRefExact
    (correction : RouteDefectAtom -> Bool) : Prop :=
  SourceRefExactVisualization
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    (correctedVisibleRouteLeft correction) visibleRouteRight

/-- Correction order is reflexive. -/
theorem correctionLe_refl
    (correction : RouteDefectAtom -> Bool) :
    CorrectionLe correction correction := by
  intro atom hhit
  exact hhit

/-- Correction order is transitive. -/
theorem correctionLe_trans
    {first middle last : RouteDefectAtom -> Bool}
    (hfirstMiddle : CorrectionLe first middle)
    (hmiddleLast : CorrectionLe middle last) :
    CorrectionLe first last := by
  intro atom hhit
  exact hmiddleLast atom (hfirstMiddle atom hhit)

/-- Source-ref exactness of a correction is exactly all selected branch hitting. -/
theorem correctionSourceRefExact_iff_hitsAllBranches
    (correction : RouteDefectAtom -> Bool) :
    CorrectionSourceRefExact correction ↔
      CorrectionHitsAllBranches correction :=
  correctedVisibleRoute_exactVisualization_iff_hits correction

/-- Branch hitting is monotone along correction order. -/
theorem correctionHitsAllBranches_monotone
    {left right : RouteDefectAtom -> Bool}
    (hle : CorrectionLe left right)
    (hhits : CorrectionHitsAllBranches left) :
    CorrectionHitsAllBranches right := by
  intro branch
  exact hle (routeDefectBranchAtom branch) (hhits branch)

/-- Source-ref exactness is monotone along correction order. -/
theorem correctionSourceRefExact_monotone
    {left right : RouteDefectAtom -> Bool}
    (hle : CorrectionLe left right)
    (hexact : CorrectionSourceRefExact left) :
    CorrectionSourceRefExact right :=
  (correctionSourceRefExact_iff_hitsAllBranches right).mpr
    (correctionHitsAllBranches_monotone hle
      ((correctionSourceRefExact_iff_hitsAllBranches left).mp hexact))

/-! ## Parametrized correction systems -/

/-- A correction system indexed by an external parameter type. -/
abbrev CorrectionSystem (Parameter : Type u) :=
  Parameter -> RouteDefectAtom -> Bool

/-- A correction system is exact at a parameter when its correction is exact. -/
def SystemExactAt {Parameter : Type u}
    (system : CorrectionSystem Parameter)
    (parameter : Parameter) : Prop :=
  CorrectionSourceRefExact (system parameter)

/-- A correction system hits every selected branch at every parameter. -/
def SystemHitsAllBranches {Parameter : Type u}
    (system : CorrectionSystem Parameter) : Prop :=
  ∀ parameter, CorrectionHitsAllBranches (system parameter)

/-- A correction system is source-ref exact at every parameter. -/
def SystemSourceRefExact {Parameter : Type u}
    (system : CorrectionSystem Parameter) : Prop :=
  ∀ parameter, SystemExactAt system parameter

/-- System-level exactness is equivalent to all-branch hitting at every parameter. -/
theorem systemSourceRefExact_iff_hitsAllBranches {Parameter : Type u}
    (system : CorrectionSystem Parameter) :
    SystemSourceRefExact system ↔
      SystemHitsAllBranches system := by
  constructor
  · intro hexact parameter
    exact (correctionSourceRefExact_iff_hitsAllBranches
      (system parameter)).mp (hexact parameter)
  · intro hhits parameter
    exact (correctionSourceRefExact_iff_hitsAllBranches
      (system parameter)).mpr (hhits parameter)

/-- A correction system is monotone when larger parameters only add selected hits. -/
def MonotoneCorrectionSystem {Parameter : Type u}
    (le : Parameter -> Parameter -> Prop)
    (system : CorrectionSystem Parameter) : Prop :=
  ∀ left right, le left right ->
    CorrectionLe (system left) (system right)

/-- In a monotone correction system, the exact locus is upward closed. -/
theorem monotoneCorrectionSystem_exact_upwardClosed {Parameter : Type u}
    {le : Parameter -> Parameter -> Prop}
    {system : CorrectionSystem Parameter}
    (hmonotone : MonotoneCorrectionSystem le system)
    {left right : Parameter}
    (hle : le left right)
    (hexact : SystemExactAt system left) :
    SystemExactAt system right :=
  correctionSourceRefExact_monotone (hmonotone left right hle) hexact

/-! ## Concrete three-stage selected correction system -/

/-- A concrete staged selected correction schedule. -/
inductive RepairStage where
  | uncorrected
  | obligationOnly
  | allBranches
  deriving DecidableEq, Fintype

open RepairStage

/-- The selected correction at each stage of the concrete schedule. -/
def stagedCorrection : RepairStage -> RouteDefectAtom -> Bool
  | uncorrected, _ => false
  | obligationOnly, obligation => true
  | obligationOnly, storageRepair => false
  | obligationOnly, storageTable => false
  | allBranches, _ => true

/-- The concrete schedule as a parametrized correction system. -/
def stagedCorrectionSystem : CorrectionSystem RepairStage :=
  stagedCorrection

/-- Stage order for the concrete correction schedule. -/
def StageLe : RepairStage -> RepairStage -> Prop
  | uncorrected, _ => True
  | obligationOnly, obligationOnly => True
  | obligationOnly, allBranches => True
  | allBranches, allBranches => True
  | _, _ => False

/-- The staged correction system is monotone in the stage order. -/
theorem stagedCorrectionSystem_monotone :
    MonotoneCorrectionSystem StageLe stagedCorrectionSystem := by
  intro left right hle atom hhit
  cases left <;> cases right <;> cases atom <;>
    simp [StageLe, stagedCorrectionSystem, stagedCorrection] at hle hhit ⊢

/-- The uncorrected stage misses the obligation branch. -/
theorem stagedCorrection_uncorrected_misses_obligation :
    ¬ CorrectionHitsRouteDefectBranch
      (stagedCorrection uncorrected) obligationBranch := by
  intro hhit
  simp [CorrectionHitsRouteDefectBranch, stagedCorrection] at hhit

/-- The uncorrected stage is not source-ref exact. -/
theorem stagedCorrection_uncorrected_not_exact :
    ¬ CorrectionSourceRefExact (stagedCorrection uncorrected) := by
  intro hexact
  have hhits :=
    (correctionSourceRefExact_iff_hitsAllBranches
      (stagedCorrection uncorrected)).mp hexact
  exact stagedCorrection_uncorrected_misses_obligation
    (hhits obligationBranch)

/-- The obligation-only stage is the existing obligation-only correction. -/
theorem stagedCorrection_obligationOnly_eq :
    stagedCorrection obligationOnly = obligationOnlyCorrection := by
  funext atom
  cases atom <;> rfl

/-- The all-branches stage is the existing all-hit correction. -/
theorem stagedCorrection_allBranches_eq :
    stagedCorrection allBranches = allRouteDefectCorrection := by
  funext atom
  cases atom <;> rfl

/-- The obligation-only stage is not source-ref exact. -/
theorem stagedCorrection_obligationOnly_not_exact :
    ¬ CorrectionSourceRefExact (stagedCorrection obligationOnly) := by
  intro hexact
  exact obligationOnlyCorrection_not_sourceRefExactVisualization
    (by
      simpa [CorrectionSourceRefExact, stagedCorrection_obligationOnly_eq]
        using hexact)

/-- The all-branches stage is source-ref exact. -/
theorem stagedCorrection_allBranches_exact :
    CorrectionSourceRefExact (stagedCorrection allBranches) := by
  simpa [CorrectionSourceRefExact, stagedCorrection_allBranches_eq]
    using allRouteDefectCorrection_sourceRefExactVisualization

/-- The exact locus of the staged schedule is exactly the all-branches stage. -/
theorem stagedCorrection_exact_iff_allBranches
    (stage : RepairStage) :
    CorrectionSourceRefExact (stagedCorrection stage) ↔
      stage = allBranches := by
  cases stage with
  | uncorrected =>
      constructor
      · intro hexact
        exact False.elim (stagedCorrection_uncorrected_not_exact hexact)
      · intro hstage
        cases hstage
  | obligationOnly =>
      constructor
      · intro hexact
        exact False.elim (stagedCorrection_obligationOnly_not_exact hexact)
      · intro hstage
        cases hstage
  | allBranches =>
      constructor
      · intro _hexact
        rfl
      · intro _hstage
        exact stagedCorrection_allBranches_exact

/-- The staged correction system is not exact at every stage. -/
theorem stagedCorrectionSystem_not_sourceRefExact :
    ¬ SystemSourceRefExact stagedCorrectionSystem := by
  intro hexact
  exact stagedCorrection_uncorrected_not_exact
    (hexact uncorrected)

/-- The staged correction system is exact at a stage exactly when that stage is all-branches. -/
theorem stagedCorrectionSystem_exactAt_iff_allBranches
    (stage : RepairStage) :
    SystemExactAt stagedCorrectionSystem stage ↔
      stage = allBranches :=
  stagedCorrection_exact_iff_allBranches stage

/-! ## Theorem package -/

/--
Cycle-48 theorem package: selected corrections form a parametrized system whose
exact locus is upward closed under hit-set monotonicity.  The concrete staged
schedule has a precise exact locus: only the all-branches stage is exact.
-/
theorem parametrizedSelectedCorrectionSystem_package :
    (∀ correction,
      CorrectionSourceRefExact correction ↔
        CorrectionHitsAllBranches correction) ∧
    (∀ left right,
      CorrectionLe left right ->
        CorrectionHitsAllBranches left ->
          CorrectionHitsAllBranches right) ∧
    (∀ left right,
      CorrectionLe left right ->
        CorrectionSourceRefExact left ->
          CorrectionSourceRefExact right) ∧
    (∀ {Parameter : Type u} (system : CorrectionSystem Parameter),
      SystemSourceRefExact system ↔
        SystemHitsAllBranches system) ∧
    (∀ {Parameter : Type u}
      (le : Parameter -> Parameter -> Prop)
      (system : CorrectionSystem Parameter),
      MonotoneCorrectionSystem le system ->
        ∀ left right, le left right ->
          SystemExactAt system left ->
            SystemExactAt system right) ∧
    MonotoneCorrectionSystem StageLe stagedCorrectionSystem ∧
    (∀ stage,
      SystemExactAt stagedCorrectionSystem stage ↔
        stage = allBranches) ∧
    ¬ SystemSourceRefExact stagedCorrectionSystem := by
  exact ⟨correctionSourceRefExact_iff_hitsAllBranches,
    fun _left _right hle hhits =>
      correctionHitsAllBranches_monotone hle hhits,
    fun _left _right hle hexact =>
      correctionSourceRefExact_monotone hle hexact,
    systemSourceRefExact_iff_hitsAllBranches,
    fun _le _system hmonotone _left _right hle hexact =>
      monotoneCorrectionSystem_exact_upwardClosed hmonotone hle hexact,
    stagedCorrectionSystem_monotone,
    stagedCorrectionSystem_exactAt_iff_allBranches,
    stagedCorrectionSystem_not_sourceRefExact⟩

end ParametrizedSelectedCorrectionSystem
end QualitySurface
end ResearchLean.AG
