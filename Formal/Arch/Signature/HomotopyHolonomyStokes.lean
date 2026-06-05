/-!
Minimal theorem guardrails for Homotopy / Holonomy / Stokes readings.

This module formalizes only the bounded mathematical readings that ArchSig may
use around finite measured path pairs, loop fillings, selected continuation,
local curvature, and ArchitectureHomotopyReport-style non-conclusions. It does
not prove ArchSig implementation correctness, global homotopy completeness,
future safety, empirical calibration, or ambient source-observation coverage.
-/

namespace Formal.Arch

universe u

namespace HomotopyHolonomyStokes

/-- A measured pair of paths compared by one bounded homotopy reading. -/
structure MeasuredPathPair (Path : Type u) where
  lhs : Path
  rhs : Path

/--
A selected continuation function used by a bounded LawPolicy profile.

The codomain is `Nat` so this guardrail can state a finite distance without
choosing a general metric space or a complete homology theory.
-/
structure SelectedContinuation (Path : Type u) where
  continueValue : Path -> Nat

/-- Selected holonomy of a measured path pair under one continuation. -/
def selectedHolonomy {Path : Type u}
    (continuation : SelectedContinuation Path)
    (pair : MeasuredPathPair Path) : Nat :=
  if continuation.continueValue pair.lhs =
      continuation.continueValue pair.rhs then 0 else 1

/-- A measured loop is a path pair plus the selected boundary holonomy value. -/
structure MeasuredLoop (Path : Type u) where
  pathPair : MeasuredPathPair Path
  boundaryHolonomy : Nat

/-- A measured 2-cell records local curvature for one bounded boundary path pair. -/
structure MeasuredTwoCell (Path : Type u) where
  boundary : MeasuredPathPair Path
  localCurvature : Nat
  weight : Nat

namespace MeasuredTwoCell

/-- Nonnegative weighted contribution of one measured local curvature cell. -/
def contribution {Path : Type u} (cell : MeasuredTwoCell Path) : Nat :=
  cell.weight * cell.localCurvature

end MeasuredTwoCell

/-- Finite measured 2-cell family used as a bounded filling. -/
abbrev FiniteMeasuredTwoCellFamily (Path : Type u) :=
  List (MeasuredTwoCell Path)

/-- Weighted local curvature aggregate over a finite measured filling. -/
def localCurvatureAggregate {Path : Type u} :
    FiniteMeasuredTwoCellFamily Path -> Nat
  | [] => 0
  | cell :: rest =>
      MeasuredTwoCell.contribution cell + localCurvatureAggregate rest

/--
A bounded filling for a measured loop.

`boundedStokes` is an explicit assumption on the supplied finite measurement:
the loop boundary holonomy is bounded by the measured local curvature mass.
-/
structure MeasuredFilling (Path : Type u) where
  loop : MeasuredLoop Path
  cells : FiniteMeasuredTwoCellFamily Path
  boundedStokes : loop.boundaryHolonomy ≤ localCurvatureAggregate cells

/--
The bounded Stokes-style inequality exposed by a measured filling.

This is local to the supplied finite filling. It says nothing about unfilled
loops, unmeasured 2-cells, or global homology.
-/
theorem boundedStokesInequality_of_measuredFilling {Path : Type u}
    (filling : MeasuredFilling Path) :
    filling.loop.boundaryHolonomy ≤ localCurvatureAggregate filling.cells :=
  filling.boundedStokes

/--
If a finite local-curvature aggregate is nonzero, some measured positive-weight
cell has nonzero local curvature.
-/
theorem exists_nonzero_localCurvature_of_aggregate_nonzero {Path : Type u}
    (cells : FiniteMeasuredTwoCellFamily Path)
    (hAggregate : localCurvatureAggregate cells ≠ 0) :
    ∃ cell, cell ∈ cells ∧ cell.weight ≠ 0 ∧ cell.localCurvature ≠ 0 := by
  induction cells with
  | nil =>
      exact False.elim (hAggregate rfl)
  | cons head tail ih =>
      rw [localCurvatureAggregate] at hAggregate
      by_cases hHead : MeasuredTwoCell.contribution head = 0
      · have hTail : localCurvatureAggregate tail ≠ 0 := by
          intro hTailZero
          exact hAggregate (by simp [hHead, hTailZero])
        rcases ih hTail with ⟨cell, hCell, hWeight, hCurvature⟩
        exact ⟨cell, by simp [hCell], hWeight, hCurvature⟩
      · have hWeight : head.weight ≠ 0 := by
          intro hZero
          exact hHead (by simp [MeasuredTwoCell.contribution, hZero])
        have hCurvature : head.localCurvature ≠ 0 := by
          intro hZero
          exact hHead (by simp [MeasuredTwoCell.contribution, hZero])
        exact ⟨head, by simp, hWeight, hCurvature⟩

/-- Nonzero boundary holonomy forces nonzero local curvature mass under a filling. -/
theorem localCurvatureAggregate_nonzero_of_boundaryHolonomy_nonzero
    {Path : Type u} (filling : MeasuredFilling Path)
    (hHolonomy : filling.loop.boundaryHolonomy ≠ 0) :
    localCurvatureAggregate filling.cells ≠ 0 := by
  intro hAggregate
  have hBoundaryLeZero : filling.loop.boundaryHolonomy ≤ 0 := by
    simpa [hAggregate] using filling.boundedStokes
  exact hHolonomy (Nat.eq_zero_of_le_zero hBoundaryLeZero)

/--
Nonzero boundary holonomy implies at least one nonzero measured local curvature
cell under the supplied finite filling.

The theorem requires an actual measured filling. It does not apply to unfilled
loops or missing filler evidence.
-/
theorem exists_nonzero_localCurvature_of_boundaryHolonomy_nonzero
    {Path : Type u} (filling : MeasuredFilling Path)
    (hHolonomy : filling.loop.boundaryHolonomy ≠ 0) :
    ∃ cell, cell ∈ filling.cells ∧ cell.weight ≠ 0 ∧ cell.localCurvature ≠ 0 :=
  exists_nonzero_localCurvature_of_aggregate_nonzero filling.cells
    (localCurvatureAggregate_nonzero_of_boundaryHolonomy_nonzero filling hHolonomy)

/--
An unfilled loop reading records missing filler evidence and explicitly refuses
to promote that absence into a violation conclusion.
-/
structure UnfilledLoopReading (Path : Type u) where
  loop : MeasuredLoop Path
  missingFillerEvidence : Prop
  violationConclusion : Prop
  notViolationConclusion : ¬ violationConclusion

/-- Unfilled loops are architectural holes, not automatic violation conclusions. -/
theorem unfilledLoop_not_violationConclusion {Path : Type u}
    (reading : UnfilledLoopReading Path) :
    ¬ reading.violationConclusion :=
  reading.notViolationConclusion

/-- Non-conclusion clauses required by the Homotopy / Holonomy / Stokes guardrail. -/
inductive HomotopyStokesNonConclusionClause where
  | noArchSigImplementationCorrectness
  | noGlobalHomotopyCompleteness
  | noGlobalHomologyComputation
  | noUnfilledLoopViolationConclusion
  | noFutureSafety
  | noEmpiricalCalibration
  | noExtractorCompleteness
  deriving DecidableEq, Repr

/-- Required non-conclusions for Homotopy / Holonomy / Stokes theorem packages. -/
def requiredNonConclusions : List HomotopyStokesNonConclusionClause :=
  [ .noArchSigImplementationCorrectness
  , .noGlobalHomotopyCompleteness
  , .noGlobalHomologyComputation
  , .noUnfilledLoopViolationConclusion
  , .noFutureSafety
  , .noEmpiricalCalibration
  , .noExtractorCompleteness
  ]

/--
Minimal theorem guardrail package for Homotopy / Holonomy / Stokes readings.

Concrete ArchSig JSON generation, source extraction, and codebase diagnosis
remain outside this Lean package.
-/
structure HomotopyHolonomyStokesGuardrail (Path : Type u) where
  fillings : List (MeasuredFilling Path)
  unfilledLoops : List (UnfilledLoopReading Path)
  nonConclusions : List HomotopyStokesNonConclusionClause

namespace HomotopyHolonomyStokesGuardrail

/-- The package contains every required non-conclusion clause. -/
def RecordsRequiredNonConclusions {Path : Type u}
    (package : HomotopyHolonomyStokesGuardrail Path) : Prop :=
  ∀ clause, clause ∈ requiredNonConclusions -> clause ∈ package.nonConclusions

/-- If the package stores the required list exactly, it records the boundary. -/
theorem recordsRequiredNonConclusions_of_eq_required {Path : Type u}
    (package : HomotopyHolonomyStokesGuardrail Path)
    (hNonConclusions : package.nonConclusions = requiredNonConclusions) :
    package.RecordsRequiredNonConclusions := by
  intro clause hClause
  simpa [RecordsRequiredNonConclusions, hNonConclusions] using hClause

end HomotopyHolonomyStokesGuardrail

end HomotopyHolonomyStokes

end Formal.Arch
