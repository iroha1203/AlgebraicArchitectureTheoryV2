import Formal.AG.Research.QualitySurface.TupleProtectedDataSquareCriterion
import Formal.AG.Research.QualitySurface.TupleTransportExactness

/-!
Cycle 22 evidence for `G-aat-quality-surface-01`.

This file factors hidden tuple holonomy into component defects of protected
tuple data: obligation, repair frontier, and trace field. The results are
relative to supplied finite tuple certificates and declared tuple transports;
they do not assert a global profile classification, canonical transport,
source extraction completeness, or whole-codebase traceability.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace TupleHolonomyDefectInvariant

open TraceLocus

abbrev TupleProfile :=
  ProfileTupleIntegration.TupleProfile

abbrev TupleCertificateAt :=
  ProfileTupleIntegration.TupleCertificateAt

/-! ## Same-profile tuple holonomy defects -/

/-- Protected tuple component whose defect can carry hidden holonomy. -/
inductive TupleProtectedComponent where
  | obligation
  | repairFrontier (atom : LocusAtom)
  | traceField (atom : LocusAtom)
  deriving DecidableEq

/-- Zero tuple-holonomy defect inside one profile fiber. -/
def NoTupleHolonomyDefect {p : TupleProfile}
    (left right : TupleCertificateAt p) : Prop :=
  left.omega = right.omega ∧
    ProfileTupleIntegration.SameTupleRepairFrontier left right ∧
    ProfileTupleIntegration.SameTupleTraceField left right

/-- A nonzero protected-data defect inside one profile fiber. -/
def HasTupleHolonomyDefect {p : TupleProfile}
    (left right : TupleCertificateAt p) : Prop :=
  ¬ NoTupleHolonomyDefect left right

/-- Obligation component defect. -/
def ObligationDefect {p : TupleProfile}
    (left right : TupleCertificateAt p) : Prop :=
  left.omega ≠ right.omega

/-- Repair-frontier component defect at a selected atom. -/
def RepairFrontierDefectAt {p : TupleProfile}
    (left right : TupleCertificateAt p) (atom : LocusAtom) : Prop :=
  ¬ (left.repairFrontier atom ↔ right.repairFrontier atom)

/-- Trace-field component defect at a selected atom. -/
def TraceFieldDefectAt {p : TupleProfile}
    (left right : TupleCertificateAt p) (atom : LocusAtom) : Prop :=
  left.traceField atom ≠ right.traceField atom

/-- Component-indexed tuple holonomy defect. -/
def TupleHolonomyDefect {p : TupleProfile}
    (left right : TupleCertificateAt p) :
    TupleProtectedComponent -> Prop
  | .obligation => ObligationDefect left right
  | .repairFrontier atom => RepairFrontierDefectAt left right atom
  | .traceField atom => TraceFieldDefectAt left right atom

/-- Zero component defect is exactly protected tuple data agreement. -/
theorem noTupleHolonomyDefect_iff_protectedData
    {p : TupleProfile} (left right : TupleCertificateAt p) :
    NoTupleHolonomyDefect left right ↔
      ProfileTupleIntegration.SameTupleProtectedData left right :=
  Iff.rfl

/-- Obligation disagreement obstructs zero tuple-holonomy defect. -/
theorem obligationDefect_obstructs_noTupleHolonomyDefect
    {p : TupleProfile} {left right : TupleCertificateAt p}
    (hdefect : ObligationDefect left right) :
    HasTupleHolonomyDefect left right := by
  intro hzero
  exact hdefect hzero.1

/-- Repair-frontier disagreement at one atom obstructs zero defect. -/
theorem repairFrontierDefect_obstructs_noTupleHolonomyDefect
    {p : TupleProfile} {left right : TupleCertificateAt p}
    {atom : LocusAtom}
    (hdefect : RepairFrontierDefectAt left right atom) :
    HasTupleHolonomyDefect left right := by
  intro hzero
  exact hdefect (hzero.2.1 atom)

/-- Trace-field disagreement at one atom obstructs zero defect. -/
theorem traceFieldDefect_obstructs_noTupleHolonomyDefect
    {p : TupleProfile} {left right : TupleCertificateAt p}
    {atom : LocusAtom}
    (hdefect : TraceFieldDefectAt left right atom) :
    HasTupleHolonomyDefect left right := by
  intro hzero
  exact hdefect (hzero.2.2 atom)

/-- Any component-indexed tuple holonomy defect obstructs zero defect. -/
theorem tupleHolonomyDefect_obstructs_noTupleHolonomyDefect
    {p : TupleProfile} {left right : TupleCertificateAt p}
    {component : TupleProtectedComponent}
    (hdefect : TupleHolonomyDefect left right component) :
    HasTupleHolonomyDefect left right := by
  cases component with
  | obligation =>
      exact obligationDefect_obstructs_noTupleHolonomyDefect hdefect
  | repairFrontier atom =>
      exact repairFrontierDefect_obstructs_noTupleHolonomyDefect hdefect
  | traceField atom =>
      exact traceFieldDefect_obstructs_noTupleHolonomyDefect hdefect

/-! ## Selected endpoint and square witnesses -/

/-- The selected endpoint pair has a nonzero obligation defect. -/
theorem endpointTuple_obligationDefect :
    ObligationDefect
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple :=
  ProfileTupleIntegration.endpointTuple_omega_diff

/-- The selected endpoint pair has a database repair-frontier defect. -/
theorem endpointTuple_databaseRepairDefect :
    RepairFrontierDefectAt
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple
      LocusAtom.database := by
  intro hsame
  have hrepairFull :
      ProfileTupleIntegration.fullEndpointTuple.repairFrontier
          LocusAtom.database :=
    hsame.mpr
      ProfileTupleIntegration.traceMissingEndpoint_forces_database_repair
  exact ProfileTupleIntegration.fullEndpoint_no_database_repair hrepairFull

/-- The selected endpoint pair has a database trace-field defect. -/
theorem endpointTuple_databaseTraceFieldDefect :
    TraceFieldDefectAt
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple
      LocusAtom.database := by
  intro hsame
  cases hsame

/-- The selected endpoint pair has nonzero tuple holonomy. -/
theorem endpointTuple_hasTupleHolonomyDefect :
    HasTupleHolonomyDefect
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple :=
  obligationDefect_obstructs_noTupleHolonomyDefect
    endpointTuple_obligationDefect

/-- Component-indexed endpoint obligation defect. -/
theorem endpointTuple_obligationComponentDefect :
    TupleHolonomyDefect
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple
      TupleProtectedComponent.obligation :=
  endpointTuple_obligationDefect

/-- Component-indexed endpoint repair-frontier defect. -/
theorem endpointTuple_databaseRepairComponentDefect :
    TupleHolonomyDefect
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple
      (TupleProtectedComponent.repairFrontier LocusAtom.database) :=
  endpointTuple_databaseRepairDefect

/-- Component-indexed endpoint trace-field defect. -/
theorem endpointTuple_databaseTraceFieldComponentDefect :
    TupleHolonomyDefect
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple
      (TupleProtectedComponent.traceField LocusAtom.database) :=
  endpointTuple_databaseTraceFieldDefect

/--
The visible endpoint surface is flat, but all three protected tuple components
exhibit a defect.
-/
theorem endpointTuple_visibleSurface_hides_componentDefects :
    (ProfileTupleIntegration.visibleTupleSurfaceReading
        ProfileTupleIntegration.endpointProfile).Equivalent
      ProfileTupleIntegration.fullEndpointTuple
      ProfileTupleIntegration.traceMissingEndpointTuple ∧
      ObligationDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple ∧
      RepairFrontierDefectAt
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        LocusAtom.database ∧
      TraceFieldDefectAt
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        LocusAtom.database ∧
      HasTupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple :=
  ⟨ProfileTupleIntegration.endpointTuple_visibleAgreement,
    endpointTuple_obligationDefect,
    endpointTuple_databaseRepairDefect,
    endpointTuple_databaseTraceFieldDefect,
    endpointTuple_hasTupleHolonomyDefect⟩

/--
The visible endpoint surface is flat, but the component-indexed defect surface
detects all three protected tuple components.
-/
theorem endpointTuple_visibleSurface_hides_indexedDefects :
    (ProfileTupleIntegration.visibleTupleSurfaceReading
        ProfileTupleIntegration.endpointProfile).Equivalent
      ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple ∧
        TupleHolonomyDefect
          ProfileTupleIntegration.fullEndpointTuple
          ProfileTupleIntegration.traceMissingEndpointTuple
          TupleProtectedComponent.obligation ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        (TupleProtectedComponent.repairFrontier LocusAtom.database) ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        (TupleProtectedComponent.traceField LocusAtom.database) ∧
      HasTupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple :=
  ⟨ProfileTupleIntegration.endpointTuple_visibleAgreement,
    endpointTuple_obligationComponentDefect,
    endpointTuple_databaseRepairComponentDefect,
    endpointTuple_databaseTraceFieldComponentDefect,
    endpointTuple_hasTupleHolonomyDefect⟩

/-- The selected tuple square has an obligation component defect. -/
theorem tupleProtectedDataSquare_obligationDefect :
    ObligationDefect
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst :=
  TupleProtectedDataSquareCriterion.tupleProtectedData_omega_discrepancy

/-- The selected tuple square has a database repair-frontier defect. -/
theorem tupleProtectedDataSquare_databaseRepairDefect :
    RepairFrontierDefectAt
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
      LocusAtom.database := by
  exact endpointTuple_databaseRepairDefect

/-- The selected tuple square has a database trace-field defect. -/
theorem tupleProtectedDataSquare_databaseTraceFieldDefect :
    TraceFieldDefectAt
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
      LocusAtom.database := by
  exact endpointTuple_databaseTraceFieldDefect

/-- Component-indexed selected square obligation defect. -/
theorem tupleProtectedDataSquare_obligationComponentDefect :
    TupleHolonomyDefect
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
      TupleProtectedComponent.obligation :=
  tupleProtectedDataSquare_obligationDefect

/-- Component-indexed selected square repair-frontier defect. -/
theorem tupleProtectedDataSquare_databaseRepairComponentDefect :
    TupleHolonomyDefect
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
      (TupleProtectedComponent.repairFrontier LocusAtom.database) :=
  tupleProtectedDataSquare_databaseRepairDefect

/-- Component-indexed selected square trace-field defect. -/
theorem tupleProtectedDataSquare_databaseTraceFieldComponentDefect :
    TupleHolonomyDefect
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
      TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
      (TupleProtectedComponent.traceField LocusAtom.database) :=
  tupleProtectedDataSquare_databaseTraceFieldDefect

/--
The selected finite square is visibly flat while its component defects produce
protected-data curvature.
-/
theorem tupleProtectedDataSquare_componentDefects_curve :
    FiniteSquareCriterion.VisibleFlat
        TupleProtectedDataSquareCriterion.tupleProtectedDataSquareReading
        (FiniteSquareCriterion.endpointPairOfSquare
          TupleProtectedDataSquareCriterion.tupleProtectedDataSquare) ∧
      ObligationDefect
        TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
        TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst ∧
      RepairFrontierDefectAt
        TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
        TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
        LocusAtom.database ∧
      TraceFieldDefectAt
        TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
        TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
        LocusAtom.database ∧
      FiniteSquareCriterion.ReadingCurved
        TupleProtectedDataSquareCriterion.tupleProtectedDataSquareReading
        (FiniteSquareCriterion.endpointPairOfSquare
          TupleProtectedDataSquareCriterion.tupleProtectedDataSquare) :=
  ⟨TupleProtectedDataSquareCriterion.tupleProtectedData_square_visibleFlat,
    tupleProtectedDataSquare_obligationDefect,
    tupleProtectedDataSquare_databaseRepairDefect,
    tupleProtectedDataSquare_databaseTraceFieldDefect,
    TupleProtectedDataSquareCriterion.tupleProtectedData_instantiates_finiteSquareCriterion⟩

/-! ## Cross-profile tuple holonomy defects -/

/-- Zero tuple-holonomy defect across two profile fibers. -/
def NoTupleHolonomyDefectAcross {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q) : Prop :=
  source.omega = target.omega ∧
    (∀ atom, source.repairFrontier atom ↔ target.repairFrontier atom) ∧
    (∀ atom, source.traceField atom = target.traceField atom)

/-- A nonzero protected-data defect across profile fibers. -/
def HasTupleHolonomyDefectAcross {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q) : Prop :=
  ¬ NoTupleHolonomyDefectAcross source target

/-- Cross-profile obligation component defect. -/
def ObligationDefectAcross {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q) : Prop :=
  source.omega ≠ target.omega

/-- Cross-profile repair-frontier component defect at one atom. -/
def RepairFrontierDefectAcrossAt {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q)
    (atom : LocusAtom) : Prop :=
  ¬ (source.repairFrontier atom ↔ target.repairFrontier atom)

/-- Cross-profile trace-field component defect at one atom. -/
def TraceFieldDefectAcrossAt {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q)
    (atom : LocusAtom) : Prop :=
  source.traceField atom ≠ target.traceField atom

/-- Component-indexed cross-profile tuple holonomy defect. -/
def TupleHolonomyDefectAcross {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q) :
    TupleProtectedComponent -> Prop
  | .obligation => ObligationDefectAcross source target
  | .repairFrontier atom => RepairFrontierDefectAcrossAt source target atom
  | .traceField atom => TraceFieldDefectAcrossAt source target atom

/-- Cross-profile zero defect is protected-data agreement across profiles. -/
theorem noTupleHolonomyDefectAcross_iff_protectedDataAcross
    {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q) :
    NoTupleHolonomyDefectAcross source target ↔
      TupleTransportExactness.SameTupleProtectedDataAcross source target :=
  Iff.rfl

/-- Cross-profile obligation disagreement obstructs zero defect. -/
theorem obligationDefectAcross_obstructs_noTupleHolonomyDefectAcross
    {p q : TupleProfile} {source : TupleCertificateAt p}
    {target : TupleCertificateAt q}
    (hdefect : ObligationDefectAcross source target) :
    HasTupleHolonomyDefectAcross source target := by
  intro hzero
  exact hdefect hzero.1

/-- Cross-profile repair-frontier disagreement obstructs zero defect. -/
theorem repairFrontierDefectAcross_obstructs_noTupleHolonomyDefectAcross
    {p q : TupleProfile} {source : TupleCertificateAt p}
    {target : TupleCertificateAt q} {atom : LocusAtom}
    (hdefect : RepairFrontierDefectAcrossAt source target atom) :
    HasTupleHolonomyDefectAcross source target := by
  intro hzero
  exact hdefect (hzero.2.1 atom)

/-- Cross-profile trace-field disagreement obstructs zero defect. -/
theorem traceFieldDefectAcross_obstructs_noTupleHolonomyDefectAcross
    {p q : TupleProfile} {source : TupleCertificateAt p}
    {target : TupleCertificateAt q} {atom : LocusAtom}
    (hdefect : TraceFieldDefectAcrossAt source target atom) :
    HasTupleHolonomyDefectAcross source target := by
  intro hzero
  exact hdefect (hzero.2.2 atom)

/-- Any component-indexed cross-profile defect obstructs zero defect. -/
theorem tupleHolonomyDefectAcross_obstructs_noTupleHolonomyDefectAcross
    {p q : TupleProfile} {source : TupleCertificateAt p}
    {target : TupleCertificateAt q}
    {component : TupleProtectedComponent}
    (hdefect : TupleHolonomyDefectAcross source target component) :
    HasTupleHolonomyDefectAcross source target := by
  cases component with
  | obligation =>
      exact obligationDefectAcross_obstructs_noTupleHolonomyDefectAcross
        hdefect
  | repairFrontier atom =>
      exact repairFrontierDefectAcross_obstructs_noTupleHolonomyDefectAcross
        hdefect
  | traceField atom =>
      exact traceFieldDefectAcross_obstructs_noTupleHolonomyDefectAcross
        hdefect

/-- Grid-map tuple transports have zero cross-profile tuple-holonomy defect. -/
theorem tupleTransportOfGridMap_noTupleHolonomyDefectAcross
    {p q : TupleProfile}
    (gridMap :
      ProfileGridHolonomy.CertificateAt p ->
        ProfileGridHolonomy.CertificateAt q)
    (c : TupleCertificateAt p) :
    NoTupleHolonomyDefectAcross c
      ((TupleTransportExactness.tupleTransportOfGridMap gridMap).map c) :=
  TupleTransportExactness.tupleTransportOfGridMap_preserves_protectedDataAcross
    gridMap c

/-- Any transported cross-profile defect obstructs protected-data preservation. -/
theorem hasTupleHolonomyDefectAcross_obstructs_losslessTransport
    {p q : TupleProfile}
    (τ : TupleTransportExactness.TupleTransport p q)
    {c : TupleCertificateAt p}
    (hdefect : HasTupleHolonomyDefectAcross c (τ.map c)) :
    ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ := by
  exact TupleTransportExactness.protectedDataDivergence_obstructs_losslessTupleTransport
    τ hdefect

/-- Any transported component defect obstructs protected-data preservation. -/
theorem tupleHolonomyDefectAcross_obstructs_losslessTransport
    {p q : TupleProfile}
    (τ : TupleTransportExactness.TupleTransport p q)
    {c : TupleCertificateAt p}
    {component : TupleProtectedComponent}
    (hdefect : TupleHolonomyDefectAcross c (τ.map c) component) :
    ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ :=
  hasTupleHolonomyDefectAcross_obstructs_losslessTransport τ
    (tupleHolonomyDefectAcross_obstructs_noTupleHolonomyDefectAcross
      hdefect)

/-- Cross-profile obligation defect obstructs protected-data preserving transport. -/
theorem obligationDefectAcross_obstructs_losslessTransport
    {p q : TupleProfile}
    (τ : TupleTransportExactness.TupleTransport p q)
    {c : TupleCertificateAt p}
    (hdefect : ObligationDefectAcross c (τ.map c)) :
    ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ :=
  hasTupleHolonomyDefectAcross_obstructs_losslessTransport τ
    (obligationDefectAcross_obstructs_noTupleHolonomyDefectAcross hdefect)

/-- Cross-profile repair-frontier defect obstructs protected-data preserving transport. -/
theorem repairFrontierDefectAcross_obstructs_losslessTransport
    {p q : TupleProfile}
    (τ : TupleTransportExactness.TupleTransport p q)
    {c : TupleCertificateAt p} {atom : LocusAtom}
    (hdefect : RepairFrontierDefectAcrossAt c (τ.map c) atom) :
    ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ :=
  hasTupleHolonomyDefectAcross_obstructs_losslessTransport τ
    (repairFrontierDefectAcross_obstructs_noTupleHolonomyDefectAcross hdefect)

/-- Cross-profile trace-field defect obstructs protected-data preserving transport. -/
theorem traceFieldDefectAcross_obstructs_losslessTransport
    {p q : TupleProfile}
    (τ : TupleTransportExactness.TupleTransport p q)
    {c : TupleCertificateAt p} {atom : LocusAtom}
    (hdefect : TraceFieldDefectAcrossAt c (τ.map c) atom) :
    ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ :=
  hasTupleHolonomyDefectAcross_obstructs_losslessTransport τ
    (traceFieldDefectAcross_obstructs_noTupleHolonomyDefectAcross hdefect)

/-! ## Theorem package -/

/--
Cycle-22 theorem package: tuple protected-data holonomy decomposes into
obligation, repair-frontier, and trace-field component defects. Zero defect is
protected-data agreement, concrete endpoint/square witnesses have nonzero
component defects, and cross-profile defects obstruct lossless tuple transport.
-/
theorem tupleHolonomyDefect_invariant_package :
    (∀ {p : TupleProfile} (left right : TupleCertificateAt p),
      NoTupleHolonomyDefect left right ↔
        ProfileTupleIntegration.SameTupleProtectedData left right) ∧
      ((ProfileTupleIntegration.visibleTupleSurfaceReading
          ProfileTupleIntegration.endpointProfile).Equivalent
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple ∧
        TupleHolonomyDefect
          ProfileTupleIntegration.fullEndpointTuple
          ProfileTupleIntegration.traceMissingEndpointTuple
          TupleProtectedComponent.obligation ∧
        TupleHolonomyDefect
          ProfileTupleIntegration.fullEndpointTuple
          ProfileTupleIntegration.traceMissingEndpointTuple
          (TupleProtectedComponent.repairFrontier LocusAtom.database) ∧
        TupleHolonomyDefect
          ProfileTupleIntegration.fullEndpointTuple
          ProfileTupleIntegration.traceMissingEndpointTuple
          (TupleProtectedComponent.traceField LocusAtom.database) ∧
        HasTupleHolonomyDefect
          ProfileTupleIntegration.fullEndpointTuple
          ProfileTupleIntegration.traceMissingEndpointTuple) ∧
      (FiniteSquareCriterion.ReadingCurved
        TupleProtectedDataSquareCriterion.tupleProtectedDataSquareReading
        (FiniteSquareCriterion.endpointPairOfSquare
          TupleProtectedDataSquareCriterion.tupleProtectedDataSquare) ∧
        TupleHolonomyDefect
          TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
          TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
          TupleProtectedComponent.obligation ∧
        TupleHolonomyDefect
          TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
          TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
          (TupleProtectedComponent.repairFrontier LocusAtom.database) ∧
        TupleHolonomyDefect
          TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.lawFirst
          TupleProtectedDataSquareCriterion.tupleProtectedDataEndpointPair.coverFirst
          (TupleProtectedComponent.traceField LocusAtom.database)) ∧
      (∀ {p q : TupleProfile}
        (τ : TupleTransportExactness.TupleTransport p q)
        {c : TupleCertificateAt p},
        HasTupleHolonomyDefectAcross c (τ.map c) ->
          ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ) ∧
      (∀ {p q : TupleProfile}
        (τ : TupleTransportExactness.TupleTransport p q)
        {c : TupleCertificateAt p}
        {component : TupleProtectedComponent},
        TupleHolonomyDefectAcross c (τ.map c) component ->
          ¬ TupleTransportExactness.PreservesTupleProtectedDataAcross τ) ∧
      (∀ {p q : TupleProfile}
        (gridMap :
          ProfileGridHolonomy.CertificateAt p ->
            ProfileGridHolonomy.CertificateAt q)
        (c : TupleCertificateAt p),
        NoTupleHolonomyDefectAcross c
          ((TupleTransportExactness.tupleTransportOfGridMap gridMap).map c)) := by
  exact ⟨by
    intro p left right
    exact noTupleHolonomyDefect_iff_protectedData left right,
    endpointTuple_visibleSurface_hides_indexedDefects,
    ⟨TupleProtectedDataSquareCriterion.tupleProtectedData_instantiates_finiteSquareCriterion,
      tupleProtectedDataSquare_obligationComponentDefect,
      tupleProtectedDataSquare_databaseRepairComponentDefect,
      tupleProtectedDataSquare_databaseTraceFieldComponentDefect⟩,
    by
      intro p q τ c hdefect
      exact hasTupleHolonomyDefectAcross_obstructs_losslessTransport τ
        hdefect,
    by
      intro p q τ c component hdefect
      exact tupleHolonomyDefectAcross_obstructs_losslessTransport τ
        hdefect,
    by
      intro p q gridMap c
      exact tupleTransportOfGridMap_noTupleHolonomyDefectAcross gridMap c⟩

end TupleHolonomyDefectInvariant
end QualitySurface
end Formal.AG.Research
