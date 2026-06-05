import Formal.Arch.Signature.Curvature

/-!
Minimal theorem guardrails for Architecture Curvature Transfer Spectrum (ACTS).

This module formalizes only the bounded mathematical readings that ArchSig may
use around finite curvature-support and transfer-spectrum reports. It does not
prove ArchSig implementation correctness, global semantic flatness, future
safety, empirical calibration, or ambient source-observation coverage.
-/

namespace Formal.Arch

universe u v

namespace CurvatureTransferSpectrum

/--
A measured curvature support row for one selected axis.

`supportNonempty` is an explicit precondition: an aggregate-zero theorem should
only be read for rows that really have selected witness support.
-/
structure MeasuredCurvatureSupport (Axis : Type u) (Witness : Type v) where
  axis : Axis
  witnessSupport : List Witness
  supportNonempty : witnessSupport ≠ []
  curvature : Nat
  weight : Nat

namespace MeasuredCurvatureSupport

/-- Nonnegative weighted contribution of one measured support row. -/
def contribution {Axis : Type u} {Witness : Type v}
    (entry : MeasuredCurvatureSupport Axis Witness) : Nat :=
  entry.weight * entry.curvature

end MeasuredCurvatureSupport

/-- Finite measured curvature support family. -/
abbrev FiniteCurvatureSupportFamily (Axis : Type u) (Witness : Type v) :=
  List (MeasuredCurvatureSupport Axis Witness)

/-- Weighted aggregate over a finite curvature-support family. -/
def weightedCurvatureSupportAggregate {Axis : Type u} {Witness : Type v} :
    FiniteCurvatureSupportFamily Axis Witness -> Nat
  | [] => 0
  | entry :: rest =>
      MeasuredCurvatureSupport.contribution entry +
        weightedCurvatureSupportAggregate rest

/-- Every selected measured support row has zero curvature. -/
def SelectedMeasuredCurvatureZero {Axis : Type u} {Witness : Type v}
    (family : FiniteCurvatureSupportFamily Axis Witness) : Prop :=
  ∀ entry, entry ∈ family -> entry.curvature = 0

/--
Aggregate zero implies local curvature zero for every positive-weight measured
support row in the finite support family.

The conclusion is local to the supplied finite family. It does not say that
unmeasured axes, zero-weight rows, or missing support are zero.
-/
theorem localCurvature_zero_of_weightedCurvatureSupportAggregate_zero
    {Axis : Type u} {Witness : Type v}
    (family : FiniteCurvatureSupportFamily Axis Witness)
    (hAggregate : weightedCurvatureSupportAggregate family = 0)
    (entry : MeasuredCurvatureSupport Axis Witness)
    (hEntry : entry ∈ family) (hPositiveWeight : entry.weight ≠ 0) :
    entry.curvature = 0 := by
  induction family generalizing entry with
  | nil =>
      cases hEntry
  | cons head tail ih =>
      rw [weightedCurvatureSupportAggregate] at hAggregate
      have hHeadWeighted :
          MeasuredCurvatureSupport.contribution head = 0 :=
        Nat.eq_zero_of_add_eq_zero_right hAggregate
      have hTail :
          weightedCurvatureSupportAggregate tail = 0 :=
        Nat.eq_zero_of_add_eq_zero_left hAggregate
      simp only [List.mem_cons] at hEntry
      rcases hEntry with hEq | hTailEntry
      · cases hEq
        unfold MeasuredCurvatureSupport.contribution at hHeadWeighted
        rcases Nat.mul_eq_zero.mp hHeadWeighted with hWeightZero | hCurvatureZero
        · exact False.elim (hPositiveWeight hWeightZero)
        · exact hCurvatureZero
      · exact ih hTail entry hTailEntry hPositiveWeight

/-- All selected measured curvatures being zero forces the weighted aggregate to be zero. -/
theorem weightedCurvatureSupportAggregate_zero_of_selectedMeasuredCurvatureZero
    {Axis : Type u} {Witness : Type v}
    (family : FiniteCurvatureSupportFamily Axis Witness)
    (hZero : SelectedMeasuredCurvatureZero family) :
    weightedCurvatureSupportAggregate family = 0 := by
  induction family with
  | nil =>
      simp [weightedCurvatureSupportAggregate]
  | cons head tail ih =>
      rw [weightedCurvatureSupportAggregate]
      have hHead : head.curvature = 0 := hZero head (by simp)
      have hTailZero : SelectedMeasuredCurvatureZero tail := by
        intro entry hEntry
        exact hZero entry (by simp [hEntry])
      simp [MeasuredCurvatureSupport.contribution, hHead, ih hTailZero]

/--
With positive weights on every row, aggregate zero is equivalent to all selected
measured curvature being zero.
-/
theorem weightedCurvatureSupportAggregate_zero_iff_selectedMeasuredCurvatureZero
    {Axis : Type u} {Witness : Type v}
    (family : FiniteCurvatureSupportFamily Axis Witness)
    (hPositive : ∀ entry, entry ∈ family -> entry.weight ≠ 0) :
    weightedCurvatureSupportAggregate family = 0 ↔
      SelectedMeasuredCurvatureZero family := by
  constructor
  · intro hAggregate entry hEntry
    exact localCurvature_zero_of_weightedCurvatureSupportAggregate_zero
      family hAggregate entry hEntry (hPositive entry hEntry)
  · intro hZero
    exact weightedCurvatureSupportAggregate_zero_of_selectedMeasuredCurvatureZero
      family hZero

/-- A finite nonnegative transfer edge between measured curvature support rows. -/
structure NonnegativeTransferEdge (Support : Type u) where
  source : Support
  target : Support
  weight : Nat

/-- Finite nonnegative transfer relation used by bounded ACTS readings. -/
abbrev FiniteNonnegativeTransferRelation (Support : Type u) :=
  List (NonnegativeTransferEdge Support)

/--
A positive closed transfer edge is the finite relation fragment that ArchSig may
read as recurrent obstruction support.
-/
def PositiveClosedTransferEdge {Support : Type u}
    (edge : NonnegativeTransferEdge Support) : Prop :=
  edge.source = edge.target ∧ edge.weight ≠ 0

/-- The finite relation contains a positive closed transfer edge. -/
def HasPositiveClosedTransferEdge {Support : Type u}
    (relation : FiniteNonnegativeTransferRelation Support) : Prop :=
  ∃ edge, edge ∈ relation ∧ PositiveClosedTransferEdge edge

/--
Bounded recurrent-obstruction reading from one positive closed transfer edge.

This is only a current-state support reading. It is not future incident
prediction, empirical cost amplification, or repair-safety evidence.
-/
structure BoundedRecurrentObstructionReading {Support : Type u}
    (relation : FiniteNonnegativeTransferRelation Support) where
  edge : NonnegativeTransferEdge Support
  edgeInRelation : edge ∈ relation
  positiveClosed : PositiveClosedTransferEdge edge

/-- A recurrent reading exposes the positive closed edge it records. -/
theorem hasPositiveClosedTransferEdge_of_recurrentReading
    {Support : Type u}
    {relation : FiniteNonnegativeTransferRelation Support}
    (reading : BoundedRecurrentObstructionReading relation) :
    HasPositiveClosedTransferEdge relation :=
  ⟨reading.edge, reading.edgeInRelation, reading.positiveClosed⟩

/-- A positive closed edge in the finite relation can be packaged as recurrent support. -/
def recurrentReading_of_positiveClosedTransferEdge
    {Support : Type u}
    {relation : FiniteNonnegativeTransferRelation Support}
    {edge : NonnegativeTransferEdge Support}
    (hEdge : edge ∈ relation)
    (hPositiveClosed : PositiveClosedTransferEdge edge) :
    BoundedRecurrentObstructionReading relation where
  edge := edge
  edgeInRelation := hEdge
  positiveClosed := hPositiveClosed

/-- Non-conclusion clauses that every ACTS theorem package must keep visible. -/
inductive ACTSNonConclusionClause where
  | noArchSigImplementationCorrectness
  | noGlobalSemanticFlatness
  | noFutureSafety
  | noEmpiricalCalibration
  | noExtractorCompleteness
  deriving DecidableEq, Repr

/-- Required non-conclusions for ACTS theorem packages. -/
def requiredNonConclusions : List ACTSNonConclusionClause :=
  [ .noArchSigImplementationCorrectness
  , .noGlobalSemanticFlatness
  , .noFutureSafety
  , .noEmpiricalCalibration
  , .noExtractorCompleteness
  ]

/--
Minimal ACTS theorem guardrail package.

The package records finite support and transfer carriers plus non-conclusion
clauses. Concrete ArchSig JSON generation, source extraction, and forecast
truth remain outside the theorem package.
-/
structure ACTSMinimalTheoremGuardrail
    (Axis : Type u) (Witness : Type v) (Support : Type u) where
  supportFamily : FiniteCurvatureSupportFamily Axis Witness
  transferRelation : FiniteNonnegativeTransferRelation Support
  nonConclusions : List ACTSNonConclusionClause

namespace ACTSMinimalTheoremGuardrail

/-- The package contains every required ACTS non-conclusion clause. -/
def RecordsRequiredNonConclusions
    {Axis : Type u} {Witness : Type v} {Support : Type u}
    (package : ACTSMinimalTheoremGuardrail Axis Witness Support) : Prop :=
  ∀ clause, clause ∈ requiredNonConclusions -> clause ∈ package.nonConclusions

/-- If the package stores the required list exactly, it records the boundary. -/
theorem recordsRequiredNonConclusions_of_eq_required
    {Axis : Type u} {Witness : Type v} {Support : Type u}
    (package : ACTSMinimalTheoremGuardrail Axis Witness Support)
    (hNonConclusions : package.nonConclusions = requiredNonConclusions) :
    package.RecordsRequiredNonConclusions := by
  intro clause hClause
  simpa [RecordsRequiredNonConclusions, hNonConclusions] using hClause

end ACTSMinimalTheoremGuardrail

end CurvatureTransferSpectrum

end Formal.Arch
