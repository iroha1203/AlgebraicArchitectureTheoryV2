import ResearchLean.AG.OperationRepair.PathEnumeration

/-!
# General finite output bridge for operation repair

The explicit state and operation numberings are the only extra input. The
same D `runRepair` produces both endpoint tables or a failure certificate;
these declarations transport those exact outputs back to the original source.
-/

namespace AAT.AG.OperationRepair.FiniteEnumeration

universe u v w

variable {S : Type u} {E : Type v} {O : Type w} {n m : Nat}

def Input.sourceRequest (a : Input S E O n m) (x y : S) : Prop :=
  a.request x y = true

/-- The source generated congruence is precisely the numbered generated
congruence, reindexed by the two input equivalences. -/
theorem Input.generated_iff_tables (a : Input S E O n m) (x y : S) :
    (generated a.system a.sourceRequest).setoid.r x y ↔
      (generated a.toTables.system a.toTables.requestRel).setoid.r
        (a.states x) (a.states y) := by
  let pull : OperationCongruence a.system := {
    setoid := Setoid.comap a.states
      (generated a.toTables.system a.toTables.requestRel).setoid
    stable := by
      intro e s t hst
      change (generated a.toTables.system a.toTables.requestRel).setoid.r
        (a.states (a.system.step e s)) (a.states (a.system.step e t))
      rw [← a.toTables_step e s, ← a.toTables_step e t]
      exact (generated a.toTables.system a.toTables.requestRel).stable
        (a.operations e) _ _ hst }
  have hforward : generated a.system a.sourceRequest ≤ pull := by
    apply (generated_le_iff a.system pull).mpr
    intro s t hst
    exact generated_contains a.toTables.system
      ((a.toTables_requestRel s t).mpr hst)
  let push : OperationCongruence a.toTables.system := {
    setoid := Setoid.comap a.states.symm
      (generated a.system a.sourceRequest).setoid
    stable := by
      intro e s t hst
      let sourceS := a.states.symm s
      let sourceT := a.states.symm t
      have hs : a.states (a.system.step (a.operations.symm e) sourceS) =
          a.toTables.system.step e s := by
        simpa [sourceS] using (a.toTables_step (a.operations.symm e) sourceS).symm
      have ht : a.states (a.system.step (a.operations.symm e) sourceT) =
          a.toTables.system.step e t := by
        simpa [sourceT] using (a.toTables_step (a.operations.symm e) sourceT).symm
      change (generated a.system a.sourceRequest).setoid.r
        (a.states.symm (a.toTables.system.step e s))
        (a.states.symm (a.toTables.system.step e t))
      rw [← hs, ← ht, a.states.symm_apply_apply,
        a.states.symm_apply_apply]
      exact (generated a.system a.sourceRequest).stable
        (a.operations.symm e) _ _ hst }
  have hbackward :
      generated a.toTables.system a.toTables.requestRel ≤ push := by
    apply (generated_le_iff a.toTables.system push).mpr
    intro s t hst
    let sourceS := a.states.symm s
    let sourceT := a.states.symm t
    have hs : a.states sourceS = s := a.states.apply_symm_apply s
    have ht : a.states sourceT = t := a.states.apply_symm_apply t
    change (generated a.system a.sourceRequest).setoid.r sourceS sourceT
    apply generated_contains a.system
    exact ((a.toTables_requestRel sourceS sourceT).mp
      (by simpa only [hs, ht] using hst))
  constructor
  · intro hxy
    exact hforward hxy
  · intro hxy
    have hs := hbackward hxy
    change (generated a.system a.sourceRequest).setoid.r
      (a.states.symm (a.states x)) (a.states.symm (a.states y)) at hs
    simpa only [a.states.symm_apply_apply] using hs

/-- The unchanged D run succeeds precisely for repairable original data. -/
theorem Input.run_success_iff_repair_exists [DecidableEq O]
    (a : Input S E O n m) :
    (∃ tables : FiniteConstruction.SuccessTables n m O,
      a.run.outcome = Sum.inr tables) ↔
      Nonempty (RepairQuotient.{u, v, w, u} a.system a.observe
        a.sourceRequest) := by
  rw [show a.run = FiniteConstruction.runRepair a.toTables from rfl,
    FiniteConstruction.runRepair_success_iff,
    repair_exists_iff_request_behavior]
  constructor
  · intro h x y hrequest
    apply (a.behavior_iff_tables x y).mpr
    exact h (a.states x) (a.states y)
      ((a.toTables_requestRel x y).mpr hrequest)
  · intro h numberedX numberedY hrequest
    let x := a.states.symm numberedX
    let y := a.states.symm numberedY
    have hx : a.states x = numberedX := a.states.apply_symm_apply numberedX
    have hy : a.states y = numberedY := a.states.apply_symm_apply numberedY
    rw [← hx, ← hy] at hrequest ⊢
    apply (a.behavior_iff_tables x y).mp
    exact h x y ((a.toTables_requestRel x y).mp hrequest)

/-- Every numbered repair output reindexes to a repair of the source input. -/
def Input.transportRepair (a : Input S E O n m)
    (q : RepairQuotient a.toTables.system a.toTables.observe
      a.toTables.requestRel) :
    RepairQuotient.{u, v, w, _} a.system a.observe a.sourceRequest where
  Target := q.Target
  read := fun x => q.read (a.states x)
  surjective := by
    intro target
    obtain ⟨numbered, hread⟩ := q.surjective target
    refine ⟨a.states.symm numbered, ?_⟩
    simpa using hread
  step := fun e => q.step (a.operations e)
  observation := q.observation
  step_comm := by
    intro e x
    rw [← a.toTables_step e x]
    exact q.step_comm (a.operations e) (a.states x)
  observation_comm := by
    intro x
    rw [q.observation_comm]
    exact a.toTables_observe x
  identifies := by
    intro x y hxy
    apply q.identifies
    exact (a.toTables_requestRel x y).mpr hxy

def Input.sourceLowerRepair [DecidableEq O] (a : Input S E O n m)
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : a.run.outcome = Sum.inr tables) :
    RepairQuotient.{u, v, w, 0} a.system a.observe a.sourceRequest :=
  a.transportRepair (FiniteConstruction.successLowerRepair a.toTables tables h)

def Input.sourceUpperRepair [DecidableEq O] (a : Input S E O n m)
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : a.run.outcome = Sum.inr tables) :
    RepairQuotient.{u, v, w, 0} a.system a.observe a.sourceRequest :=
  a.transportRepair (FiniteConstruction.successUpperRepair a.toTables tables h)

/-- The returned lower table has the original generated congruence kernel. -/
theorem Input.sourceLowerRepair_kernel_eq [DecidableEq O]
    (a : Input S E O n m)
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : a.run.outcome = Sum.inr tables) :
    (a.sourceLowerRepair tables h).kernel = generated a.system a.sourceRequest := by
  apply OperationCongruence.ext
  apply Setoid.ext
  intro x y
  change (FiniteConstruction.successLowerRepair a.toTables tables h).kernel.setoid.r
    (a.states x) (a.states y) ↔
    (generated a.system a.sourceRequest).setoid.r x y
  rw [FiniteConstruction.successLowerRepair_kernel_eq]
  exact (a.generated_iff_tables x y).symm

/-- The returned upper table has the original behavior kernel. -/
theorem Input.sourceUpperRepair_kernel_eq [DecidableEq O]
    (a : Input S E O n m)
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : a.run.outcome = Sum.inr tables) :
    (a.sourceUpperRepair tables h).kernel = behavior a.system a.observe := by
  apply OperationCongruence.ext
  apply Setoid.ext
  intro x y
  change (FiniteConstruction.successUpperRepair a.toTables tables h).kernel.setoid.r
    (a.states x) (a.states y) ↔
    (behavior a.system a.observe).setoid.r x y
  rw [FiniteConstruction.successUpperRepair_kernel_eq]
  exact (a.behavior_iff_tables x y).symm

/-- The table factor map is the source-level repair morphism, with the same
returned class map and original operation names. -/
def Input.sourceFactorHom [DecidableEq O] (a : Input S E O n m)
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : a.run.outcome = Sum.inr tables) :
    RepairHom a.system a.observe a.sourceRequest
      (a.sourceLowerRepair tables h) (a.sourceUpperRepair tables h) where
  toFun := tables.lowerToUpper.get
  source_comm := by
    intro x
    exact FiniteConstruction.success_factor_comm a.toTables tables h (a.states x)
  step_comm := by
    intro e z
    exact FiniteConstruction.success_factor_operation_comm
      a.toTables tables h (a.operations e) z
  observation_comm := by
    intro z
    exact FiniteConstruction.success_factor_observation_comm
      a.toTables tables h z

/-- A failed numbered run returns a requested original pair and a bounded
separating word written in the original operation alphabet. -/
theorem Input.run_failure [DecidableEq O] (a : Input S E O n m)
    (numberedX numberedY : Fin n) (word : List (Fin m))
    (h : a.run.outcome = Sum.inl (numberedX, numberedY, word)) :
    let x := a.states.symm numberedX
    let y := a.states.symm numberedY
    let originalWord := word.map a.operations.symm
    a.sourceRequest x y ∧ originalWord.length < n * n ∧
      a.observe (a.system.eval x originalWord) ≠
        a.observe (a.system.eval y originalWord) := by
  let x := a.states.symm numberedX
  let y := a.states.symm numberedY
  let originalWord := word.map a.operations.symm
  have hx : a.states x = numberedX := a.states.apply_symm_apply numberedX
  have hy : a.states y = numberedY := a.states.apply_symm_apply numberedY
  obtain ⟨hreq, hlen, hsep⟩ :=
    FiniteConstruction.runRepair_failure a.toTables numberedX numberedY word h
  have hrel : a.sourceRequest x y := by
    apply (a.toTables_requestRel x y).mp
    rw [hx, hy]
    exact hreq
  have hmap : originalWord.map a.operations = word := by
    simp [originalWord]
  have hobsx : a.toTables.observe
      (a.toTables.system.eval (a.states x) (originalWord.map a.operations)) =
      a.observe (a.system.eval x originalWord) := by
    rw [a.toTables_eval]
    exact a.toTables_observe (a.system.eval x originalWord)
  have hobsy : a.toTables.observe
      (a.toTables.system.eval (a.states y) (originalWord.map a.operations)) =
      a.observe (a.system.eval y originalWord) := by
    rw [a.toTables_eval]
    exact a.toTables_observe (a.system.eval y originalWord)
  rw [hx, hmap] at hobsx
  rw [hy, hmap] at hobsy
  refine ⟨hrel, by simpa [originalWord] using hlen, ?_⟩
  intro heq
  exact hsep (hobsx.trans (heq.trans hobsy.symm))

end AAT.AG.OperationRepair.FiniteEnumeration

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteEnumeration
