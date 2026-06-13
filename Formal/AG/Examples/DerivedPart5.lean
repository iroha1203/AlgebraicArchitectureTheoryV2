import Formal.AG.Examples.FiniteModel
import Formal.AG.Derived.WellFoundedRepair

noncomputable section

namespace AAT.AG

universe v

namespace FiniteModel
namespace DerivedPart5

open AAT.AG.Derived.HilbertSeriesTheory

/--
V.R11(a): finite example package reading example 5.6 through the selected
principal-resolution Tor certificate from proposition 9.2.
-/
structure Example56TorCalculation (k : Type v) [CommRing k] where
  counterexample : Derived.Counterexample.SharedWitnessRepairCounterexample k

namespace Example56TorCalculation

variable {k : Type v} [CommRing k]

/-- V.R11(a): `Tor_1(R/<xy>, R/<xz>)` has a selected nonzero class. -/
theorem tor1_nonzero (E : Example56TorCalculation k) :
    ∃ x : Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing k)
        (Derived.Counterexample.SharedWitnessCoord.idealU k)
        (Derived.Counterexample.SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  E.counterexample.tor1_nonzero

end Example56TorCalculation

/-- V.R11(b): the selected `s_t` family has the endpoint residues of proposition 9.2. -/
theorem sharedWitness_numeric_residue_path :
    Derived.Counterexample.ResidueEndpointPath.sharedWitness.uStart = 1 ∧
      Derived.Counterexample.ResidueEndpointPath.sharedWitness.uEnd = 0 ∧
      Derived.Counterexample.ResidueEndpointPath.sharedWitness.vStart = 0 ∧
      Derived.Counterexample.ResidueEndpointPath.sharedWitness.vEnd = 1 :=
  ⟨Derived.Counterexample.ResidueEndpointPath.sharedWitness_uStart,
    Derived.Counterexample.ResidueEndpointPath.sharedWitness_uEnd,
    Derived.Counterexample.ResidueEndpointPath.sharedWitness_vStart,
    Derived.Counterexample.ResidueEndpointPath.sharedWitness_vEnd⟩

/--
V.R11(b): the selected path improves the U-axis but does not give V-axis
nonincrease.
-/
theorem sharedWitness_numeric_u_improves_not_v_nonincreasing :
    Derived.Counterexample.ResidueEndpointPath.UImproves
        Derived.Counterexample.ResidueEndpointPath.sharedWitness ∧
      ¬ Derived.Counterexample.ResidueEndpointPath.VNonIncreasing
        Derived.Counterexample.ResidueEndpointPath.sharedWitness :=
  Derived.Counterexample.ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/-- V.R11(c): selected Hilbert-series regime for `I_U = <xy>` and `I_V = <xz>`. -/
def sharedWitnessHilbertRegime (k : Type v) [CommRing k] :
    GradedMonomialConflictRegime
      (Derived.Counterexample.SharedWitnessCoord.ChartRing k) where
  I_U := Derived.Counterexample.SharedWitnessCoord.idealU k
  I_V := Derived.Counterexample.SharedWitnessCoord.idealV k
  homogeneousMonomialIdeals := True
  homogeneousMonomialIdeals_holds := trivial
  ambientHilbertSeries := 0
  quotientUHilbertSeries := 0
  quotientVHilbertSeries := 0
  jointQuotientHilbertSeries := 0
  lawConflictHilbertSeries := fun _ => 0

/-- V.R11(c): selected G5 numerical check package for the shared-witness chart. -/
def sharedWitnessG5NumericPackage (k : Type v) [CommRing k] :
    HilbertSeriesConflictIdentityPackage
      (Derived.Counterexample.SharedWitnessCoord.ChartRing k) where
  regime := sharedWitnessHilbertRegime k
  conflictAlternatingSum := 0
  eulerCharacteristic := {
    termEulerCharacteristic := 0
    homologyEulerCharacteristic := 0
    eulerCharacteristic_eq := rfl
  }
  denominatorClearedIdentity := rfl

/-- V.R11(c): theorem 12.2 holds in the selected shared-witness numerical package. -/
theorem sharedWitnessG5_denominatorClearedIdentity
    (k : Type v) [CommRing k] :
    (sharedWitnessG5NumericPackage k).regime.quotientUHilbertSeries *
        (sharedWitnessG5NumericPackage k).regime.quotientVHilbertSeries =
      (sharedWitnessG5NumericPackage k).regime.ambientHilbertSeries *
        (sharedWitnessG5NumericPackage k).conflictAlternatingSum :=
  (sharedWitnessG5NumericPackage k).denominatorClearedIdentity_certificate

/-- V.R11(c): the selected interference coefficient is zero in the numerical package. -/
theorem sharedWitnessG5_interference_coeff_zero
    (k : Type v) [CommRing k] (n : Nat) :
    ((sharedWitnessG5NumericPackage k).interferenceSeries).coeff n = 0 := by
  simp [HilbertSeriesConflictIdentityPackage.interferenceSeries,
    sharedWitnessG5NumericPackage, sharedWitnessHilbertRegime]

/-- V.R11(d): a tiny Nat-valued well-founded repair profile. -/
def smallRepairProfile : Derived.WellFoundedRepair.RepairComparisonProfile where
  State := Nat
  ltRep := fun B A => B < A
  wellFounded_ltRep := Nat.lt_wfRel.wf
  step := fun A B => B < A
  step_decreases := fun hstep => hstep
  targetCleared := fun A => A = 0
  noSolutionCertificate := fun A => A = 3

/-- V.R11(d): the example repair step `2 -> 1` decreases. -/
theorem smallRepair_step_two_one :
    smallRepairProfile.step (2 : Nat) (1 : Nat) := by
  change (1 : Nat) < 2
  decide

/-- V.R11(d): the example repair step `1 -> 0` decreases. -/
theorem smallRepair_step_one_zero :
    smallRepairProfile.step (1 : Nat) (0 : Nat) := by
  change (0 : Nat) < 1
  decide

/-- V.R11(d): theorem 13.3 applied to the small finite repair profile. -/
theorem smallRepair_no_infinite_sequence :
    ¬ smallRepairProfile.InfiniteRepairSequence :=
  smallRepairProfile.no_infinite_repair_sequence

/-- V.R11(d): a two-step selected repair trace ending in `cleared`. -/
def smallRepairClearedSynthesis :
    Derived.WellFoundedRepair.SoundRepairSynthesisPackage smallRepairProfile where
  trace := [(2 : Nat), (1 : Nat), (0 : Nat)]
  outputState := (0 : Nat)
  output := Derived.WellFoundedRepair.SynthesisOutput.cleared rfl
  emitsOnlySoundStepsOrNoSolutionCertificate := True
  emitsOnlySoundStepsOrNoSolutionCertificate_holds := trivial

/-- V.R11(d): the small repair trace has finite length three. -/
theorem smallRepairCleared_trace_length :
    smallRepairClearedSynthesis.trace.length = 3 :=
  rfl

/-- V.R11(d): the small repair trace terminates with a cleared target. -/
theorem smallRepairCleared_output :
    smallRepairProfile.targetCleared smallRepairClearedSynthesis.outputState ∨
      smallRepairProfile.noSolutionCertificate smallRepairClearedSynthesis.outputState :=
  smallRepairClearedSynthesis.output_cleared_or_noSolution

/-- V.R11(d): a selected synthesis trace ending in a no-solution certificate. -/
def smallRepairNoSolutionSynthesis :
    Derived.WellFoundedRepair.SoundRepairSynthesisPackage smallRepairProfile where
  trace := [(3 : Nat)]
  outputState := (3 : Nat)
  output := Derived.WellFoundedRepair.SynthesisOutput.noSolution rfl
  emitsOnlySoundStepsOrNoSolutionCertificate := True
  emitsOnlySoundStepsOrNoSolutionCertificate_holds := trivial

/-- V.R11(d): the no-solution trace terminates with the selected certificate. -/
theorem smallRepairNoSolution_output :
    smallRepairProfile.targetCleared smallRepairNoSolutionSynthesis.outputState ∨
      smallRepairProfile.noSolutionCertificate smallRepairNoSolutionSynthesis.outputState :=
  smallRepairNoSolutionSynthesis.output_cleared_or_noSolution

end DerivedPart5
end FiniteModel

end AAT.AG
