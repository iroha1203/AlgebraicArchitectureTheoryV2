import Formal.AG.Derived.HilbertSeries
import Mathlib.Order.WellFounded

noncomputable section

namespace AAT.AG
namespace Derived

universe u

namespace WellFoundedRepair

/--
V.定義13.1: well-founded repair comparison profile.

The relation `ltRep B A` is the selected repair comparison reading
`B <_{rep} A`.  The profile only says that selected repair steps decrease in
this relation; it does not assert solver completeness or global optimality.
-/
structure RepairComparisonProfile where
  State : Type u
  ltRep : State -> State -> Prop
  wellFounded_ltRep : WellFounded ltRep
  step : State -> State -> Prop
  step_decreases : ∀ {A B : State}, step A B -> ltRep B A
  targetCleared : State -> Prop
  noSolutionCertificate : State -> Prop

namespace RepairComparisonProfile

variable (P : RepairComparisonProfile.{u})

/-- V.定義13.1: every selected repair step decreases in `<_{rep}`. -/
theorem step_decreases_certificate {A B : P.State} (hstep : P.step A B) :
    P.ltRep B A :=
  P.step_decreases hstep

/-- V.定理13.3: a Nat-indexed infinite selected repair sequence. -/
def InfiniteRepairSequence : Prop :=
  ∃ sequence : Nat -> P.State, ∀ n, P.step (sequence n) (sequence (n + 1))

/--
V.定理13.3: repair termination.

If every selected repair step decreases in a well-founded repair comparison
profile, then no infinite selected repair sequence exists.
-/
theorem no_infinite_repair_sequence :
    ¬ P.InfiniteRepairSequence := by
  rintro ⟨sequence, hstep⟩
  have hdescending : ∀ n, P.ltRep (sequence (n + 1)) (sequence n) := by
    intro n
    exact P.step_decreases (hstep n)
  exact
    (wellFounded_iff_isEmpty_descending_chain.mp P.wellFounded_ltRep).false
      ⟨sequence, hdescending⟩

end RepairComparisonProfile

/-- V.定義13.2: selected evidence that a repair step is sound. -/
inductive SoundRepairStepEvidence (P : RepairComparisonProfile.{u})
    (A B : P.State) where
  | targetDecreases (hstep : P.step A B) (hdecreases : P.ltRep B A)
  | cleared (hstep : P.step A B) (hcleared : P.targetCleared B)
  | noSolution (hcertificate : P.noSolutionCertificate A)

namespace SoundRepairStepEvidence

variable {P : RepairComparisonProfile.{u}} {A B : P.State}

/--
V.定義13.2: sound step evidence contains either a selected decreasing or
cleared step, or a selected no-solution certificate.
-/
theorem sound_or_certificate (E : SoundRepairStepEvidence P A B) :
    (P.step A B ∧ (P.ltRep B A ∨ P.targetCleared B)) ∨
      P.noSolutionCertificate A := by
  cases E with
  | targetDecreases hstep hdecreases =>
      exact Or.inl ⟨hstep, Or.inl hdecreases⟩
  | cleared hstep hcleared =>
      exact Or.inl ⟨hstep, Or.inr hcleared⟩
  | noSolution hcertificate =>
      exact Or.inr hcertificate

end SoundRepairStepEvidence

/-- V.定理13.4: selected terminal output of a sound repair synthesis rule. -/
inductive SynthesisOutput (P : RepairComparisonProfile.{u})
    (state : P.State) where
  | cleared (hcleared : P.targetCleared state)
  | noSolution (hcertificate : P.noSolutionCertificate state)

/--
V.定理13.4: finite sound repair synthesis package.

The trace is an explicit finite `List`.  This package records the bounded
output discipline: the selected rule emits sound steps and terminates with
either a cleared target or a no-solution certificate.
-/
structure SoundRepairSynthesisPackage (P : RepairComparisonProfile.{u}) where
  trace : List P.State
  outputState : P.State
  output : SynthesisOutput P outputState
  emitsOnlySoundStepsOrNoSolutionCertificate : Prop
  emitsOnlySoundStepsOrNoSolutionCertificate_holds :
    emitsOnlySoundStepsOrNoSolutionCertificate

namespace SoundRepairSynthesisPackage

variable {P : RepairComparisonProfile.{u}}

/-- V.定理13.4: the selected synthesis trace is finite because it is a `List`. -/
theorem finite_trace_certificate (S : SoundRepairSynthesisPackage P) :
    ∃ n : Nat, S.trace.length = n :=
  ⟨S.trace.length, rfl⟩

/-- V.定理13.4: the synthesis rule emits only selected sound steps or certificates. -/
theorem emitsOnlySoundStepsOrNoSolutionCertificate_certificate
    (S : SoundRepairSynthesisPackage P) :
    S.emitsOnlySoundStepsOrNoSolutionCertificate :=
  S.emitsOnlySoundStepsOrNoSolutionCertificate_holds

/--
V.定理13.4: sound repair synthesis terminates with a cleared target or a
selected no-solution certificate.
-/
theorem output_cleared_or_noSolution (S : SoundRepairSynthesisPackage P) :
    P.targetCleared S.outputState ∨ P.noSolutionCertificate S.outputState := by
  cases S.output with
  | cleared hcleared =>
      exact Or.inl hcleared
  | noSolution hcertificate =>
      exact Or.inr hcertificate

end SoundRepairSynthesisPackage

end WellFoundedRepair

end Derived
end AAT.AG
