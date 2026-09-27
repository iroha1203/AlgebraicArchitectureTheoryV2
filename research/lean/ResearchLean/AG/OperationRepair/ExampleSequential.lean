import ResearchLean.AG.OperationRepair.Examples

/-!
# Both orders of the fixed four-state sequential repair

The two stage lists represent chronological `R₁;R₂` and `R₂;R₁` respectively:
`sequentialList` evaluates its list from the tail. All comparisons commute with
the original four-state source map.
-/

namespace AAT.AG.OperationRepair.Examples.Four

set_option maxRecDepth 4096

private theorem generated_of_iff
    (T : OperationSystem (Fin 4) (Fin 1))
    (R R' : Fin 4 → Fin 4 → Prop)
    (h : ∀ x y, R x y ↔ R' x y) : generated T R = generated T R' := by
  apply le_antisymm
  · apply (generated_le_iff T (generated T R')).mpr
    intro x y hxy
    exact generated_contains T ((h x y).mp hxy)
  · apply (generated_le_iff T (generated T R)).mpr
    intro x y hxy
    exact generated_contains T ((h x y).mpr hxy)

private theorem both_request_iff :
    ∀ x y : Fin 4,
      listRequest [inputOne.requestRel, inputTwo.requestRel] x y ↔
        inputBoth.requestRel x y := by
  intro x y
  simp [listRequest, FiniteRepairInput.requestRel, FiniteRepairInput.wants,
    inputOne, inputTwo, inputBoth, requestOne, requestTwo,
    RelationTable.get, Bool.or_eq_true, Bool.and_eq_true]

private theorem both_request_rev_iff :
    ∀ x y : Fin 4,
      listRequest [inputTwo.requestRel, inputOne.requestRel] x y ↔
        inputBoth.requestRel x y := by
  intro x y
  simp [listRequest, FiniteRepairInput.requestRel, FiniteRepairInput.wants,
    inputOne, inputTwo, inputBoth, requestOne, requestTwo,
    RelationTable.get, Bool.or_eq_true, Bool.and_eq_true, or_comm]

private theorem both_generated_behavior :
    generated inputOne.system inputBoth.requestRel =
      behavior inputOne.system inputOne.observe := by
  apply OperationCongruence.ext
  apply Setoid.ext
  intro x y
  change (generated inputBoth.system inputBoth.requestRel).setoid.r x y ↔
    (behavior inputOne.system inputOne.observe).setoid.r x y
  rw [← FiniteClosure.computedLower_eq_generated inputBoth]
  constructor
  · intro h
    apply (FiniteBehavior.computedUpper_iff_behavior inputOne x y).mp
    apply (FiniteConstruction.upperCells_iff inputOne x y).mp
    change (FiniteConstruction.upperPartition inputOne).cells.get x y = true
    rw [upper_cells, ← lowerBoth_cells]
    exact h
  · intro h
    have hu := (FiniteConstruction.upperCells_iff inputOne x y).mpr
      ((FiniteBehavior.computedUpper_iff_behavior inputOne x y).mpr h)
    change (FiniteConstruction.upperPartition inputOne).cells.get x y = true at hu
    rw [upper_cells, ← lowerBoth_cells] at hu
    exact hu

private theorem order12_generated_behavior :
    generated inputOne.system
      (listRequest [inputTwo.requestRel, inputOne.requestRel]) =
        behavior inputOne.system inputOne.observe := by
  rw [generated_of_iff inputOne.system _ _ both_request_rev_iff]
  exact both_generated_behavior

private theorem order21_generated_behavior :
    generated inputOne.system
      (listRequest [inputOne.requestRel, inputTwo.requestRel]) =
        behavior inputOne.system inputOne.observe := by
  rw [generated_of_iff inputOne.system _ _ both_request_iff]
  exact both_generated_behavior

/-- The two prescribed requests join to the future-observation endpoint. -/
theorem generated_join_eq_behavior :
    generated inputOne.system inputOne.requestRel ⊔
      generated inputOne.system inputTwo.requestRel =
        behavior inputOne.system inputOne.observe := by
  have hsingle : generated inputOne.system
      (listRequest [inputOne.requestRel]) =
        generated inputOne.system inputOne.requestRel := by
    apply generated_of_iff
    intro x y
    simp [listRequest]
  have h := order12_generated_behavior
  rw [generated_listRequest_cons, hsingle] at h
  exact h

private theorem order12_repairable :
    generated inputOne.system
      (listRequest [inputTwo.requestRel, inputOne.requestRel]) ≤
        behavior inputOne.system inputOne.observe := by
  rw [order12_generated_behavior]

private theorem order21_repairable :
    generated inputOne.system
      (listRequest [inputOne.requestRel, inputTwo.requestRel]) ≤
        behavior inputOne.system inputOne.observe := by
  rw [order21_generated_behavior]

/-- First repair `R₁`, then repair the image of `R₂`. -/
def order12 := sequentialList inputOne.system
  [inputTwo.requestRel, inputOne.requestRel]

/-- First repair `R₂`, then repair the image of `R₁`. -/
def order21 := sequentialList inputOne.system
  [inputOne.requestRel, inputTwo.requestRel]

/-- Actual first-stage source maps for the two chronological orders. -/
def first12 := sequentialList inputOne.system [inputOne.requestRel]
def first21 := sequentialList inputOne.system [inputTwo.requestRel]

/-- The second quotient map in each order uses the image request on the
already formed first quotient. -/
def second12 (z : first12.Carrier) : order12.Carrier :=
  Quotient.mk
    (generated first12.system (mappedRequest first12.read inputTwo.requestRel)).setoid z

def second21 (z : first21.Carrier) : order21.Carrier :=
  Quotient.mk
    (generated first21.system (mappedRequest first21.read inputOne.requestRel)).setoid z

theorem order12_source_map (x : Fin 4) :
    order12.read x = second12 (first12.read x) := rfl

theorem order21_source_map (x : Fin 4) :
    order21.read x = second21 (first21.read x) := rfl

/-- The first stage has exactly the originally requested lower endpoint. -/
theorem first12_kernel : Setoid.ker first12.read =
    (generated inputOne.system inputOne.requestRel).setoid := by
  rw [first12, (sequentialList inputOne.system _).kernel_eq]
  congr 1
  apply generated_of_iff
  intro x y
  simp [listRequest]

theorem first21_kernel : Setoid.ker first21.read =
    (generated inputOne.system inputTwo.requestRel).setoid := by
  rw [first21, (sequentialList inputOne.system _).kernel_eq]
  congr 1
  apply generated_of_iff
  intro x y
  simp [listRequest]

theorem first12_map_eq_iff (x y : Fin 4) :
    first12.read x = first12.read y ↔ lowerOne x y = true := by
  change (Setoid.ker first12.read).r x y ↔ lowerOne x y = true
  rw [first12_kernel, ← FiniteClosure.computedLower_eq_generated inputOne]
  change (FiniteConstruction.lowerPartition inputOne).cells.get x y = true ↔ _
  rw [lowerOne_cells]

theorem first21_map_eq_iff (x y : Fin 4) :
    first21.read x = first21.read y ↔
      (x = y || (x.val ≥ 2 && y.val ≥ 2)) = true := by
  change (Setoid.ker first21.read).r x y ↔ _
  rw [first21_kernel]
  change (generated inputTwo.system inputTwo.requestRel).setoid.r x y ↔ _
  rw [← FiniteClosure.computedLower_eq_generated inputTwo]
  change (FiniteConstruction.lowerPartition inputTwo).cells.get x y = true ↔ _
  rw [lowerTwo_cells]

/-- Both actual two-stage source maps have the fixed upper-endpoint kernel. -/
theorem order12_kernel : Setoid.ker order12.read =
    (behavior inputOne.system inputOne.observe).setoid := by
  rw [order12, (sequentialList inputOne.system _).kernel_eq,
    order12_generated_behavior]

theorem order21_kernel : Setoid.ker order21.read =
    (behavior inputOne.system inputOne.observe).setoid := by
  rw [order21, (sequentialList inputOne.system _).kernel_eq,
    order21_generated_behavior]

theorem order12_map_eq_iff (x y : Fin 4) :
    order12.read x = order12.read y ↔ upper x y = true := by
  change (Setoid.ker order12.read).r x y ↔ _
  rw [order12_kernel]
  rw [← (FiniteBehavior.computedUpper_iff_behavior inputOne x y)]
  rw [← (FiniteConstruction.upperCells_iff inputOne x y)]
  change (FiniteConstruction.upperPartition inputOne).cells.get x y = true ↔ _
  rw [upper_cells]

theorem order21_map_eq_iff (x y : Fin 4) :
    order21.read x = order21.read y ↔ upper x y = true := by
  change (Setoid.ker order21.read).r x y ↔ _
  rw [order21_kernel]
  rw [← (FiniteBehavior.computedUpper_iff_behavior inputOne x y)]
  rw [← (FiniteConstruction.upperCells_iff inputOne x y)]
  change (FiniteConstruction.upperPartition inputOne).cells.get x y = true ↔ _
  rw [upper_cells]

/-- The source determines the map between the two chronological orders. -/
noncomputable def orderCompare : order12.Carrier ≃ order21.Carrier :=
  stageCompare inputOne.system order12 order21
    (order12_generated_behavior.trans order21_generated_behavior.symm)

@[simp] theorem orderCompare_read (x : Fin 4) :
    orderCompare (order12.read x) = order21.read x :=
  stageCompare_read inputOne.system order12 order21
    (order12_generated_behavior.trans order21_generated_behavior.symm) x

theorem orderCompare_step (e : Fin 1) (z : order12.Carrier) :
    orderCompare (order12.system.step e z) =
      order21.system.step e (orderCompare z) :=
  stageCompare_step inputOne.system order12 order21
    (order12_generated_behavior.trans order21_generated_behavior.symm) e z

/-- The one-shot D procedure succeeds on the combined request table. -/
theorem runBoth_success :
    ∃ tables : FiniteConstruction.SuccessTables 4 1 Bool,
      (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables := by
  exact (FiniteConstruction.runRepair_success_iff inputBoth).mpr
    (FiniteConstruction.failureSearch_none inputBoth successBoth)

theorem runTwo_success :
    ∃ tables : FiniteConstruction.SuccessTables 4 1 Bool,
      (FiniteConstruction.runRepair inputTwo).outcome = Sum.inr tables := by
  exact (FiniteConstruction.runRepair_success_iff inputTwo).mpr
    (FiniteConstruction.failureSearch_none inputTwo successTwo)

theorem runTwo_counts
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputTwo).outcome = Sum.inr tables) :
    tables.lower.classCount = 3 ∧ tables.upper.classCount = 2 := by
  rw [FiniteConstruction.runRepair_success_payload inputTwo tables h]
  constructor <;> decide

theorem runBoth_counts
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables) :
    tables.lower.classCount = 2 ∧ tables.upper.classCount = 2 := by
  rw [FiniteConstruction.runRepair_success_payload inputBoth tables h]
  constructor <;> decide

/-- The first chronological order maps to the actual one-shot D upper
output. Its construction uses the equality of the two source kernels. -/
noncomputable def order12ToD
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables) :
    order12.Carrier ≃
      (FiniteConstruction.successUpperRepair inputBoth tables h).Target := by
  let q := FiniteConstruction.successUpperRepair inputBoth tables h
  have hset : Setoid.ker order12.read = q.kernel.setoid := by
    change Setoid.ker order12.read =
      (FiniteConstruction.successUpperRepair inputBoth tables h).kernel.setoid
    rw [order12_kernel, FiniteConstruction.successUpperRepair_kernel_eq]
    rfl
  exact (Setoid.quotientKerEquivOfSurjective order12.read
    order12.surjective).symm.trans
      ((Quotient.congr (Equiv.refl _) (fun x y => by
        change (Setoid.ker order12.read).r x y ↔ q.kernel.setoid.r x y
        rw [hset])).trans q.standardEquiv)

@[simp] theorem order12ToD_read
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (x : Fin 4) :
    order12ToD tables h (order12.read x) =
      (FiniteConstruction.successUpperRepair inputBoth tables h).read x := by
  simp only [order12ToD, Equiv.trans_apply,
    Setoid.quotientKerEquivOfSurjective]
  let q := FiniteConstruction.successUpperRepair inputBoth tables h
  have hset : Setoid.ker order12.read = q.kernel.setoid := by
    change Setoid.ker order12.read =
      (FiniteConstruction.successUpperRepair inputBoth tables h).kernel.setoid
    rw [order12_kernel, FiniteConstruction.successUpperRepair_kernel_eq]
    rfl
  have hr := Function.rightInverse_surjInv order12.surjective (order12.read x)
  change q.read (Function.surjInv order12.surjective (order12.read x)) = q.read x
  change q.kernel.setoid.r _ _
  rw [← hset]
  exact hr

theorem order12ToD_step
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (e : Fin 1) (z : order12.Carrier) :
    order12ToD tables h (order12.system.step e z) =
      (FiniteConstruction.successUpperRepair inputBoth tables h).step e
        (order12ToD tables h z) := by
  obtain ⟨x, rfl⟩ := order12.surjective z
  rw [← order12.step_comm, order12ToD_read, order12ToD_read]
  exact (FiniteConstruction.successUpperRepair inputBoth tables h).step_comm e x

theorem order12ToD_observation
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (z : order12.Carrier) :
    (FiniteConstruction.successUpperRepair inputBoth tables h).observation
      (order12ToD tables h z) =
        SequentialStage.observation inputOne.system inputOne.observe
          order12 order12_repairable z := by
  obtain ⟨x, rfl⟩ := order12.surjective z
  rw [order12ToD_read,
    (FiniteConstruction.successUpperRepair inputBoth tables h).observation_comm,
    SequentialStage.observation_read]
  rfl

/-- The opposite chronological order maps to the same actual one-shot D
output; the comparison is uniquely determined by the source maps. -/
noncomputable def order21ToD
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables) :
    order21.Carrier ≃
      (FiniteConstruction.successUpperRepair inputBoth tables h).Target :=
  orderCompare.symm.trans (order12ToD tables h)

@[simp] theorem order21ToD_read
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (x : Fin 4) :
    order21ToD tables h (order21.read x) =
      (FiniteConstruction.successUpperRepair inputBoth tables h).read x := by
  have hcompare : orderCompare.symm (order21.read x) = order12.read x :=
    by rw [← orderCompare_read x, Equiv.symm_apply_apply]
  rw [order21ToD, Equiv.trans_apply, hcompare, order12ToD_read]

theorem order21ToD_step
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (e : Fin 1) (z : order21.Carrier) :
    order21ToD tables h (order21.system.step e z) =
      (FiniteConstruction.successUpperRepair inputBoth tables h).step e
        (order21ToD tables h z) := by
  obtain ⟨x, rfl⟩ := order21.surjective z
  rw [← order21.step_comm, order21ToD_read, order21ToD_read]
  exact (FiniteConstruction.successUpperRepair inputBoth tables h).step_comm e x

theorem order21ToD_observation
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (z : order21.Carrier) :
    (FiniteConstruction.successUpperRepair inputBoth tables h).observation
      (order21ToD tables h z) =
        SequentialStage.observation inputOne.system inputOne.observe
          order21 order21_repairable z := by
  obtain ⟨x, rfl⟩ := order21.surjective z
  rw [order21ToD_read,
    (FiniteConstruction.successUpperRepair inputBoth tables h).observation_comm,
    SequentialStage.observation_read]
  rfl

/-- Source commutation also fixes the comparison between the two orders
and the one-shot output uniquely. -/
theorem order12ToD_unique
    (tables : FiniteConstruction.SuccessTables 4 1 Bool)
    (h : (FiniteConstruction.runRepair inputBoth).outcome = Sum.inr tables)
    (f : order12.Carrier →
      (FiniteConstruction.successUpperRepair inputBoth tables h).Target)
    (hf : ∀ x, f (order12.read x) =
      (FiniteConstruction.successUpperRepair inputBoth tables h).read x) :
    f = order12ToD tables h := by
  funext z
  obtain ⟨x, rfl⟩ := order12.surjective z
  exact (hf x).trans (order12ToD_read tables h x).symm

end AAT.AG.OperationRepair.Examples.Four

#assert_standard_axioms_only AAT.AG.OperationRepair.Examples.Four
