import ResearchLean.AG.OperationRepair.ExampleSequential

/-!
# The prescribed single Law in the feasible fixed examples

The Law evaluation is the original Boolean observation on the four-state
source. The general E reading and finite-output maps are instantiated here.
-/

namespace AAT.AG.OperationRepair.Examples.Four

open AAT.AG.CanonicalResolution

def laws : FiniteLawFamily (Fin 4) where
  Law := Unit
  lawFintype := inferInstance
  Value := fun _ => Bool
  valueDecidableEq := fun _ => inferInstance
  eval := fun _ => observe

theorem lawObserve_eq_iff (x y : Fin 4) :
    lawObserve laws x = lawObserve laws y ↔ inputOne.observe x = inputOne.observe y := by
  have hobs (z : Fin 4) : inputOne.observe z = observe z := by
    simp [inputOne, FiniteRepairInput.observe]
  constructor
  · intro h
    rw [hobs, hobs]
    exact congrFun h ()
  · intro h
    funext law
    cases law
    rw [hobs, hobs] at h
    exact h

theorem behavior_law_eq :
    (behavior inputOne.system (lawObserve laws)).setoid =
      (behavior inputOne.system inputOne.observe).setoid := by
  apply Setoid.ext
  intro x y
  rw [behavior_iff, behavior_iff]
  constructor
  · intro h word
    exact (lawObserve_eq_iff _ _).mp (h word)
  · intro h word
    exact (lawObserve_eq_iff _ _).mpr (h word)

theorem law_feasible :
    generated inputOne.system inputOne.requestRel ≤
      behavior inputOne.system (lawObserve laws) := by
  intro x y hxy
  rw [behavior_law_eq]
  exact feasible hxy

def lawLower : RepairQuotient inputOne.system (lawObserve laws)
    inputOne.requestRel :=
  lowerRepair inputOne.system (lawObserve laws) inputOne.requestRel law_feasible

def lawUpper : RepairQuotient inputOne.system (lawObserve laws)
    inputOne.requestRel :=
  upperRepair inputOne.system (lawObserve laws) inputOne.requestRel law_feasible

theorem lawLower_adequate : laws.Adequate lawLower.toReading :=
  (repair_to_lawReadingConditions laws inputOne.system inputOne.requestRel
    lawLower).2.1

theorem lawUpper_adequate : laws.Adequate lawUpper.toReading :=
  (repair_to_lawReadingConditions laws inputOne.system inputOne.requestRel
    lawUpper).2.1

theorem lawLower_jointKernel_factors :
    laws.jointKernelReading.FactorsThrough lawLower.toReading :=
  jointKernel_factorsThrough_of_lawReadingConditions laws inputOne.system
    inputOne.requestRel lawLower.toReading
      (repair_to_lawReadingConditions laws inputOne.system inputOne.requestRel
        lawLower)

theorem lawUpper_jointKernel_factors :
    laws.jointKernelReading.FactorsThrough lawUpper.toReading :=
  jointKernel_factorsThrough_of_lawReadingConditions laws inputOne.system
    inputOne.requestRel lawUpper.toReading
      (repair_to_lawReadingConditions laws inputOne.system inputOne.requestRel
        lawUpper)

end AAT.AG.OperationRepair.Examples.Four

namespace AAT.AG.OperationRepair.Examples.Path

open AAT.AG.CanonicalResolution

theorem law_feasible :
    generated input.system input.requestRel ≤
      behavior input.system (lawObserve Four.laws) := by
  intro x y hxy
  change (behavior Four.inputOne.system (lawObserve Four.laws)).setoid.r x y
  rw [Four.behavior_law_eq]
  change (behavior input.system input.observe).setoid.r x y
  rw [← generated_eq_behavior]
  exact hxy

def lawUpper : RepairQuotient input.system (lawObserve Four.laws)
    input.requestRel :=
  upperRepair input.system (lawObserve Four.laws) input.requestRel law_feasible

theorem lawUpper_adequate : Four.laws.Adequate lawUpper.toReading :=
  (repair_to_lawReadingConditions Four.laws input.system input.requestRel
    lawUpper).2.1

theorem lawUpper_jointKernel_factors :
    Four.laws.jointKernelReading.FactorsThrough lawUpper.toReading :=
  jointKernel_factorsThrough_of_lawReadingConditions Four.laws input.system
    input.requestRel lawUpper.toReading
      (repair_to_lawReadingConditions Four.laws input.system input.requestRel
        lawUpper)

theorem lawUpper_path_equations : lawUpper.PathEquations paths := by
  apply (lawUpper.pathRequest_identified_iff paths).mp
  intro x y hxy
  exact lawUpper.identifies x y
    ((Four.inputOne.withPathRequest_requestRel paths x y).mpr hxy)

theorem lawUpper_nonconstant :
    lawUpper.observation (lawUpper.read 0) () ≠
      lawUpper.observation (lawUpper.read 2) () := by
  rw [lawUpper.observation_comm, lawUpper.observation_comm]
  decide

/-- The actual D output carries exactly the original single Law value. -/
theorem run_upper_law_value
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair input).outcome = Sum.inr tables)
    (x : Fin 4) :
    tables.upper.observations.get (tables.upper.map.get x) =
      Four.laws.eval () x := by
  rw [FiniteConstruction.success_upper_observation_comm input tables h x]
  simp [input, FiniteRepairInput.withPathRequest, Four.inputOne,
    Four.laws, Four.observe, FiniteRepairInput.observe]

end AAT.AG.OperationRepair.Examples.Path

#assert_standard_axioms_only AAT.AG.OperationRepair.Examples.Four
#assert_standard_axioms_only AAT.AG.OperationRepair.Examples.Path
