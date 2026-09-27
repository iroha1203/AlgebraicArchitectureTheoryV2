import ResearchLean.AG.OperationRepair.FiniteCostDecision
import ResearchLean.AG.OperationRepair.FiniteRamNumbering

/-!
# Complete primitive trace for finite repair

The counted lower and upper loops, first-failure decision, and success-table
assembly share their stored values in one run. The success branch counts the
actual numbered cells it returns; the failure branch skips that assembly.
-/

namespace AAT.AG.OperationRepair.FiniteCostOutput

open FiniteRamPrimitives
open FiniteConstruction
variable {n m : Nat} {O : Type*} [DecidableEq O]

def runWithTrace (input : FiniteRepairInput n m O) :
    Counted (RunOutput n m O) :=
  let lower := FiniteRamEnumeration.lower input
  let upper := FiniteRamUpper.upper input
  let decision := FiniteRamDecision.decision input upper.value
  let lowerPart := lowerPartitionFrom input lower.value
    (FiniteRamEnumeration.lower_value input)
  let upperPart := upperPartitionFrom input upper.value
    (FiniteRamUpper.upper_value input)
  match decision.value with
  | some bad =>
      ⟨⟨lower.value, upper.value, Sum.inl bad⟩,
        lower.trace ++ upper.trace ++ decision.trace ++
          List.replicate bad.2.2.length .wordCell ++
          List.replicate 3 .tableCell⟩
  | none =>
      let success := FiniteRamNumbering.successTablesFrom input lowerPart upperPart
      ⟨⟨lower.value, upper.value, Sum.inr success.value⟩,
        lower.trace ++ upper.trace ++ decision.trace ++ success.trace ++
          List.replicate 3 .tableCell⟩

theorem runWithTrace_value (input : FiniteRepairInput n m O) :
    (runWithTrace input).value = runRepair input := by
  simp only [runWithTrace, runRepair]
  cases h : (FiniteRamDecision.decision input
    (FiniteRamUpper.upper input).value).value with
  | some bad => rfl
  | none =>
      simp only [FiniteRamNumbering.successTablesFrom_value]

theorem runWithTrace_cost_le (input : FiniteRepairInput n m O) :
    (runWithTrace input).cost ≤
      1000 * (m + 1) * (n + 1) ^ 5 := by
  have hl := FiniteRamEnumeration.lower_cost_poly input
  have hu := FiniteRamUpper.upper_cost_le input
  have hd := FiniteRamDecision.decision_cost_le input
    (FiniteRamUpper.upper input).value
  let lowerPart := lowerPartitionFrom input
    (FiniteRamEnumeration.lower input).value
    (FiniteRamEnumeration.lower_value input)
  let upperPart := upperPartitionFrom input
    (FiniteRamUpper.upper input).value
    (FiniteRamUpper.upper_value input)
  have hs := FiniteRamNumbering.successTablesFrom_cost_le
    input lowerPart upperPart
  have hn : 1 ≤ n + 1 := by omega
  have hm : 1 ≤ m + 1 := by omega
  have hpow4 : (n + 1) ^ 4 ≤ (n + 1) ^ 5 :=
    Nat.pow_le_pow_right hn (by decide)
  have hpow2 : (n + 1) ^ 2 ≤ (n + 1) ^ 5 :=
    Nat.pow_le_pow_right hn (by decide)
  have hupper : (FiniteRamUpper.upper input).cost ≤
      60 * (m + 1) * (n + 1) ^ 5 :=
    hu.trans (Nat.mul_le_mul_left (60 * (m + 1)) hpow4)
  have hdecision :
      (FiniteRamDecision.decision input
        (FiniteRamUpper.upper input).value).cost ≤
          30 * (m + 1) * (n + 1) ^ 5 := by
    calc
      _ ≤ 30 * (n + 1) ^ 2 := hd
      _ ≤ 30 * (n + 1) ^ 5 := Nat.mul_le_mul_left 30 hpow2
      _ ≤ 30 * (m + 1) * (n + 1) ^ 5 := by nlinarith
  have hsuccess :
      (FiniteRamNumbering.successTablesFrom input lowerPart upperPart).cost ≤
        300 * (m + 1) * (n + 1) ^ 5 :=
    hs.trans (Nat.mul_le_mul_left (300 * (m + 1)) hpow4)
  have hcopy (bad : Fin n × Fin n × List (Fin m))
      (h : (FiniteRamDecision.decision input
        (FiniteRamUpper.upper input).value).value = some bad) :
      bad.2.2.length ≤ n * n := by
    have hf : failureSearch input = some bad := by
      simpa only [failureSearch, FiniteRamDecision.decision_value,
        FiniteRamUpper.upper_value] using h
    rcases bad with ⟨x, y, word⟩
    exact (failureSearch_sound input hf).2.1.le
  unfold runWithTrace
  cases h : (FiniteRamDecision.decision input
    (FiniteRamUpper.upper input).value).value with
  | some bad =>
      simp only [h, Counted.cost, List.length_append,
        List.length_replicate]
      dsimp [Counted.cost] at hl hupper hdecision
      have hb := hcopy bad h
      have hsq : n * n ≤ (n + 1) ^ 5 := by
        nlinarith [hpow2]
      nlinarith
  | none =>
      simp only [h, Counted.cost, List.length_append,
        List.length_replicate]
      dsimp [Counted.cost] at hl hupper hdecision hsuccess
      nlinarith

end AAT.AG.OperationRepair.FiniteCostOutput

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteCostOutput
