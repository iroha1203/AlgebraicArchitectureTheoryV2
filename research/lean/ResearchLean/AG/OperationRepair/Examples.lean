import ResearchLean.AG.OperationRepair.PathEnumeration
import ResearchLean.AG.OperationRepair.FiniteSequential

/-!
# Fixed finite repair examples for G-126

These inputs use the same numbered tables and `runRepair` as the general finite
construction. Concrete table equalities below are kernel-checked computations.
-/

namespace AAT.AG.OperationRepair.Examples

open FiniteConstruction
open AAT.AG.CanonicalResolution
set_option maxRecDepth 4096

namespace Four

def step : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

def observe (x : Fin 4) : Bool := x.val ≥ 2

def requestOne (x y : Fin 4) : Bool := x = 0 && y = 1
def requestTwo (x y : Fin 4) : Bool := x = 2 && y = 3

def inputOne : FiniteRepairInput 4 1 Bool where
  transition := FiniteTable.ofFn fun _ => FiniteTable.ofFn step
  observation := FiniteTable.ofFn observe
  request := FiniteTable.ofFn fun x => FiniteTable.ofFn (requestOne x)

def inputTwo : FiniteRepairInput 4 1 Bool where
  transition := FiniteTable.ofFn fun _ => FiniteTable.ofFn step
  observation := FiniteTable.ofFn observe
  request := FiniteTable.ofFn fun x => FiniteTable.ofFn (requestTwo x)

def lowerOne (x y : Fin 4) : Bool :=
  x = y || (x.val < 2 && y.val < 2)

def upper (x y : Fin 4) : Bool :=
  (x.val < 2) == (y.val < 2)

theorem lowerOne_cells :
    ∀ x y : Fin 4, (lowerPartition inputOne).cells.get x y = lowerOne x y := by
  decide

theorem upper_cells :
    ∀ x y : Fin 4, (upperPartition inputOne).cells.get x y = upper x y := by
  decide

theorem lowerOne_count : (lowerPartition inputOne).classCount = 3 := by decide
theorem upper_count : (upperPartition inputOne).classCount = 2 := by decide

theorem lowerTwo_cells :
    ∀ x y : Fin 4,
      (lowerPartition inputTwo).cells.get x y =
        (x = y || (x.val ≥ 2 && y.val ≥ 2)) := by
  decide

def inputBoth : FiniteRepairInput 4 1 Bool where
  transition := inputOne.transition
  observation := inputOne.observation
  request := FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    requestOne x y || requestTwo x y

theorem lowerBoth_cells :
    ∀ x y : Fin 4,
      (lowerPartition inputBoth).cells.get x y = upper x y := by
  decide

theorem successOne : failureSearch inputOne = none := by decide
theorem successTwo : failureSearch inputTwo = none := by decide
theorem successBoth : failureSearch inputBoth = none := by decide

theorem runOne_success :
    ∃ tables : SuccessTables 4 1 Bool,
      (runRepair inputOne).outcome = Sum.inr tables := by
  exact (runRepair_success_iff inputOne).mpr
    (failureSearch_none inputOne successOne)

theorem runOne_counts (tables : SuccessTables 4 1 Bool)
    (h : (runRepair inputOne).outcome = Sum.inr tables) :
    tables.lower.classCount = 3 ∧ tables.upper.classCount = 2 := by
  rw [runRepair_success_payload inputOne tables h]
  exact ⟨lowerOne_count, upper_count⟩

theorem lowerOne_map_eq_iff (x y : Fin 4) :
    (lowerPartition inputOne).quotient x =
      (lowerPartition inputOne).quotient y ↔ lowerOne x y = true := by
  exact ((lowerPartition inputOne).quotient_eq_iff x y).trans
    (by rw [lowerOne_cells])

theorem upper_map_eq_iff (x y : Fin 4) :
    (upperPartition inputOne).quotient x =
      (upperPartition inputOne).quotient y ↔ upper x y = true := by
  exact ((upperPartition inputOne).quotient_eq_iff x y).trans
    (by rw [upper_cells])

theorem upper_split :
    ∀ x y : Fin 4, upper x y = true ↔
      lowerOne x y = true ∨ (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) := by
  decide

theorem interval_two_endpoints
    (c : OperationCongruence inputOne.system)
    (hlo : generated inputOne.system inputOne.requestRel ≤ c)
    (hhi : c ≤ behavior inputOne.system inputOne.observe) :
    c = generated inputOne.system inputOne.requestRel ∨
      c = behavior inputOne.system inputOne.observe := by
  have hlow (x y : Fin 4) (h : lowerOne x y = true) : c.setoid.r x y := by
    have ht : (lowerPartition inputOne).cells.get x y = true :=
      (lowerOne_cells x y).trans h
    change (FiniteClosure.lowerCongruence inputOne).setoid.r x y at ht
    rw [FiniteClosure.computedLower_eq_generated] at ht
    exact hlo ht
  have hhigh (x y : Fin 4) (h : c.setoid.r x y) : upper x y = true := by
    have hb := hhi h
    have ht := (FiniteBehavior.computedUpper_iff_behavior inputOne x y).mpr hb
    have hcell := (FiniteConstruction.upperCells_iff inputOne x y).mpr ht
    change (upperPartition inputOne).cells.get x y = true at hcell
    rw [upper_cells] at hcell
    exact hcell
  by_cases h23 : c.setoid.r (2 : Fin 4) 3
  · right
    apply OperationCongruence.ext
    apply Setoid.ext
    intro x y
    constructor
    · intro hc; exact hhi hc
    · intro hb
      have hu : upper x y = true := by
        have hcell := (FiniteConstruction.upperCells_iff inputOne x y).mpr
          ((FiniteBehavior.computedUpper_iff_behavior inputOne x y).mpr hb)
        change (upperPartition inputOne).cells.get x y = true at hcell
        rw [upper_cells] at hcell
        exact hcell
      rcases (upper_split x y).mp hu with hl | h23' | h32'
      · exact hlow x y hl
      · rcases h23' with ⟨rfl, rfl⟩; exact h23
      · rcases h32' with ⟨rfl, rfl⟩; exact c.setoid.symm h23
  · left
    apply OperationCongruence.ext
    apply Setoid.ext
    intro x y
    constructor
    · intro hc
      have hu := (upper_split x y).mp (hhigh x y hc)
      have hl : lowerOne x y = true := by
        rcases hu with hl | h23' | h32'
        · exact hl
        · rcases h23' with ⟨rfl, rfl⟩; exact False.elim (h23 hc)
        · rcases h32' with ⟨rfl, rfl⟩
          exact False.elim (h23 (c.setoid.symm hc))
      have ht : (lowerPartition inputOne).cells.get x y = true :=
        (lowerOne_cells x y).trans hl
      change (FiniteClosure.lowerCongruence inputOne).setoid.r x y at ht
      rw [FiniteClosure.computedLower_eq_generated] at ht
      exact ht
    · intro hg; exact hlo hg

theorem feasible : generated inputOne.system inputOne.requestRel ≤
    behavior inputOne.system inputOne.observe :=
  (generated_le_behavior_iff inputOne.system inputOne.observe
    inputOne.requestRel).mpr (failureSearch_none inputOne successOne)

theorem endpoints_distinct :
    generated inputOne.system inputOne.requestRel ≠
      behavior inputOne.system inputOne.observe := by
  intro heq
  have hb : (behavior inputOne.system inputOne.observe).setoid.r
      (2 : Fin 4) 3 := by
    apply (FiniteBehavior.computedUpper_iff_behavior inputOne 2 3).mp
    apply (FiniteConstruction.upperCells_iff inputOne 2 3).mp
    change (upperPartition inputOne).cells.get 2 3 = true
    rw [upper_cells]
    decide
  rw [← heq] at hb
  have hl : (lowerPartition inputOne).cells.get 2 3 = true := by
    change (FiniteClosure.lowerCongruence inputOne).setoid.r 2 3
    rw [FiniteClosure.computedLower_eq_generated]
    exact hb
  rw [lowerOne_cells] at hl
  simp [lowerOne] at hl

theorem exactly_two_repair_classes :
    ∃ a b : RepairClass inputOne.system inputOne.observe inputOne.requestRel,
      a ≠ b ∧ ∀ cl, cl = a ∨ cl = b := by
  let lo : {c : OperationCongruence inputOne.system //
      generated inputOne.system inputOne.requestRel ≤ c ∧
        c ≤ behavior inputOne.system inputOne.observe} :=
    ⟨generated inputOne.system inputOne.requestRel, le_refl _, feasible⟩
  let hi : {c : OperationCongruence inputOne.system //
      generated inputOne.system inputOne.requestRel ≤ c ∧
        c ≤ behavior inputOne.system inputOne.observe} :=
    ⟨behavior inputOne.system inputOne.observe, feasible, le_refl _⟩
  refine ⟨classOfInterval inputOne.system inputOne.observe inputOne.requestRel lo,
    classOfInterval inputOne.system inputOne.observe inputOne.requestRel hi,
    ?_, ?_⟩
  · intro h
    have heq := congrArg
      (classKernel inputOne.system inputOne.observe inputOne.requestRel) h
    rw [classKernel_classOfInterval, classKernel_classOfInterval] at heq
    exact endpoints_distinct (congrArg Subtype.val heq)
  · intro cl
    have h := interval_two_endpoints
      ((classKernel inputOne.system inputOne.observe inputOne.requestRel cl).val)
      ((classKernel inputOne.system inputOne.observe inputOne.requestRel cl).property.1)
      ((classKernel inputOne.system inputOne.observe inputOne.requestRel cl).property.2)
    rcases h with h | h
    · left
      calc
        cl = classOfInterval inputOne.system inputOne.observe inputOne.requestRel
            (classKernel inputOne.system inputOne.observe inputOne.requestRel cl) :=
          (classOfInterval_classKernel _ _ _ cl).symm
        _ = classOfInterval inputOne.system inputOne.observe inputOne.requestRel lo :=
          congrArg _ (Subtype.ext h)
    · right
      calc
        cl = classOfInterval inputOne.system inputOne.observe inputOne.requestRel
            (classKernel inputOne.system inputOne.observe inputOne.requestRel cl) :=
          (classOfInterval_classKernel _ _ _ cl).symm
        _ = classOfInterval inputOne.system inputOne.observe inputOne.requestRel hi :=
          congrArg _ (Subtype.ext h)

end Four

namespace Three

def step : Fin 3 → Fin 3
  | 0 => 0
  | _ => 2

def observe (x : Fin 3) : Bool := x = 2

def input : FiniteRepairInput 3 1 Bool where
  transition := FiniteTable.ofFn fun _ => FiniteTable.ofFn step
  observation := FiniteTable.ofFn observe
  request := FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    x = 0 && y = 1

theorem lower_universal :
    ∀ x y : Fin 3, (lowerPartition input).cells.get x y = true := by
  decide

theorem upper_equality :
    ∀ x y : Fin 3, (upperPartition input).cells.get x y = (x == y) := by
  decide

theorem empty_word_same :
    input.observe ((input.system).eval 0 []) =
      input.observe ((input.system).eval 1 []) := by decide

theorem one_step_separates :
    input.observe ((input.system).eval 0 [0]) ≠
      input.observe ((input.system).eval 1 [0]) := by decide

theorem failure_exact :
    failureSearch input = some (0, 1, [0]) := by decide

theorem run_failure_exact :
    (runRepair input).outcome = Sum.inl (0, 1, [0]) := by
  change (match failureSearch input with
    | some bad => Sum.inl bad
    | none => Sum.inr (makeSuccessTablesFrom input
        (lowerPartitionFrom input (FiniteClosure.lower input) rfl)
        (upperPartitionFrom input (FiniteBehavior.upper input) rfl))) = _
  rw [failure_exact]

theorem run_failure_certificate :
    input.requestRel (0 : Fin 3) 1 ∧
      ([0] : List (Fin 1)).length < 3 * 3 ∧
        FiniteBehavior.separates input 0 1 [0] :=
  runRepair_failure input 0 1 [0] run_failure_exact

theorem no_repair :
    ¬ Nonempty (RepairQuotient.{0, 0, 0, 0}
      input.system input.observe input.requestRel) := by
  exact (runRepair_failure_iff_no_repair input).mp
    ⟨(0 : Fin 3), (1 : Fin 3), ([0] : List (Fin 1)), run_failure_exact⟩

def laws : FiniteLawFamily (Fin 3) where
  Law := Unit
  lawFintype := inferInstance
  Value := fun _ => Bool
  valueDecidableEq := fun _ => inferInstance
  eval := fun _ => observe

theorem law_kernel_not_stable : ¬ lawKernelStable laws input.system := by
  intro h
  have h01 : laws.Equivalent (0 : Fin 3) 1 := by
    intro law
    cases law
    decide
  have h02 := h (0 : Fin 1) (0 : Fin 3) (1 : Fin 3) h01 ()
  have hs0 : input.system.step 0 0 = (0 : Fin 3) := by decide
  have hs1 : input.system.step 0 1 = (2 : Fin 3) := by decide
  rw [hs0, hs1] at h02
  simp [laws, observe] at h02

theorem joint_law_operation_not_descended :
    ¬ ∀ e, laws.jointKernelReading.Factors
      (fun x => laws.jointKernelReading.read (input.system.step e x)) := by
  intro h
  exact law_kernel_not_stable
    ((lawKernelStable_iff_jointKernelFactors laws input.system).mpr h)

end Three

namespace Path

def paths : List (List (Fin 1) × List (Fin 1)) := [([], [0])]
def input : FiniteRepairInput 4 1 Bool := Four.inputOne.withPathRequest paths

theorem generated_cells :
    ∀ x y : Fin 4,
      (lowerPartition input).cells.get x y = Four.upper x y := by
  decide

theorem future_cells :
    ∀ x y : Fin 4,
      (upperPartition input).cells.get x y = Four.upper x y := by
  decide

theorem generated_eq_behavior :
    generated input.system input.requestRel =
      behavior input.system input.observe := by
  apply OperationCongruence.ext
  apply Setoid.ext
  intro x y
  rw [← FiniteClosure.computedLower_eq_generated]
  constructor
  · intro h
    apply (FiniteBehavior.computedUpper_iff_behavior input x y).mp
    apply (FiniteConstruction.upperCells_iff input x y).mp
    change (upperPartition input).cells.get x y = true
    rw [future_cells, ← generated_cells]
    exact h
  · intro h
    have hu := (FiniteConstruction.upperCells_iff input x y).mpr
      ((FiniteBehavior.computedUpper_iff_behavior input x y).mpr h)
    change (upperPartition input).cells.get x y = true at hu
    rw [future_cells, ← generated_cells] at hu
    exact hu

theorem two_states : (upperPartition input).classCount = 2 := by decide

theorem quotient_operation_identity :
    ∀ c : Fin (upperPartition input).classCount,
      ((quotientOperationTable input (upperPartition input)).get 0).get c = c := by
  intro c
  let p := upperPartition input
  have hstep : ∀ x : Fin 4, Four.upper (input.step 0 x) x = true := by decide
  have hrel : p.cells.get (input.step 0 (p.classSection c))
      (p.classSection c) = true :=
    (future_cells _ _).trans (hstep _)
  have hquot := (p.quotient_eq_iff _ _).mpr hrel
  simpa only [quotientOperationTable, FiniteTable.get_ofFn,
    p.quotient_section] using hquot

theorem law_nonconstant :
    input.observe (0 : Fin 4) ≠ input.observe (2 : Fin 4) := by decide

theorem run_success : FiniteConstruction.failureSearch input = none := by decide

theorem run_success_output :
    ∃ tables : SuccessTables 4 1 Bool,
      (runRepair input).outcome = Sum.inr tables := by
  exact (runRepair_success_iff input).mpr
    (failureSearch_none input run_success)

theorem run_upper_two_states (tables : SuccessTables 4 1 Bool)
    (h : (runRepair input).outcome = Sum.inr tables) :
    tables.upper.classCount = 2 := by
  rw [runRepair_success_payload input tables h]
  exact two_states

theorem run_upper_operation_identity (tables : SuccessTables 4 1 Bool)
    (h : (runRepair input).outcome = Sum.inr tables)
    (c : Fin tables.upper.classCount) :
    (tables.upper.operations.get 0).get c = c := by
  cases runRepair_success_payload input tables h
  change ((quotientOperationTable input (upperPartition input)).get 0).get c = c
  exact quotient_operation_identity c

theorem run_law_nonconstant (tables : SuccessTables 4 1 Bool)
    (h : (runRepair input).outcome = Sum.inr tables) :
    tables.upper.observations.get (tables.upper.map.get 0) ≠
      tables.upper.observations.get (tables.upper.map.get 2) := by
  rw [success_upper_observation_comm input tables h 0,
    success_upper_observation_comm input tables h 2]
  exact law_nonconstant

end Path

end AAT.AG.OperationRepair.Examples

#assert_standard_axioms_only AAT.AG.OperationRepair.Examples
