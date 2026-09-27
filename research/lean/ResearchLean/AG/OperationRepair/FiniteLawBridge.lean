import ResearchLean.AG.OperationRepair.LawUniverse
import ResearchLean.AG.OperationRepair.FiniteEnumeration

/-!
# Finite Law output and the future-observation Reading

Explicit numberings materialize the same operations and original Law values
for D's table procedure. The returned upper quotient has the future Law
kernel and is compared with the semantic beta Reading by a source-commuting
equivalence.
-/

namespace AAT.AG.OperationRepair

open AAT.AG.CanonicalResolution

namespace FiniteLawBridge

universe u v

variable {S : Type u} {E : Type v} {n m : Nat}

/-- The dependent Law observation has decidable equality from the given
finite Law index and each supplied value equality decision. -/
def observationDecidableEq (laws : FiniteLawFamily S) :
    DecidableEq ((law : laws.Law) → laws.Value law) := by
  letI : Fintype laws.Law := laws.lawFintype
  letI (law : laws.Law) : DecidableEq (laws.Value law) :=
    laws.valueDecidableEq law
  infer_instance

/-- Materialize the original Law observation and the original request table
using explicit numberings; no quotient or repairability proof is supplied. -/
def input (laws : FiniteLawFamily S) (T : OperationSystem S E)
    (request : S → S → Bool) (states : S ≃ Fin n)
    (operations : E ≃ Fin m) :
    FiniteEnumeration.Input S E
      ((law : laws.Law) → laws.Value law) n m where
  states := states
  operations := operations
  system := T
  observe := lawObserve laws
  request := request

variable (laws : FiniteLawFamily S) (T : OperationSystem S E)
variable (request : S → S → Bool) (states : S ≃ Fin n)
variable (operations : E ≃ Fin m)

/-- The future-observation Reading carries the operations descended from
the original system's stable behavioral kernel. -/
def betaStep (e : E) : (betaReading laws T).Target →
    (betaReading laws T).Target :=
  Quotient.lift (fun x =>
    Quotient.mk (behavior T (lawObserve laws)).setoid (T.step e x))
    (fun x y hxy => Quotient.sound
      ((behavior T (lawObserve laws)).stable e x y hxy))

@[simp] theorem betaStep_read (e : E) (x : S) :
    betaStep laws T e ((betaReading laws T).read x) =
      (betaReading laws T).read (T.step e x) := rfl

private theorem tables_eval (x : S) (word : List E) :
    (input laws T request states operations).toTables.system.eval
      (states x) (word.map operations) = states (T.eval x word) := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, OperationSystem.eval_cons,
        OperationSystem.eval_cons]
      have hs :=
        (input laws T request states operations).toTables_step e x
      have hs' :
          (input laws T request states operations).toTables.system.step
            (operations e) (states x) = states (T.step e x) := by
        exact hs
      change
        (input laws T request states operations).toTables.system.eval
          ((input laws T request states operations).toTables.system.step
            (operations e) (states x)) (rest.map operations) =
          states (T.eval (T.step e x) rest)
      rw [hs', ih]

private theorem tables_observe_eval (x : S) (word : List E) :
    (input laws T request states operations).toTables.observe
      ((input laws T request states operations).toTables.system.eval
        (states x) (word.map operations)) =
      lawObserve laws (T.eval x word) := by
  rw [tables_eval]
  exact (input laws T request states operations).toTables_observe
    (T.eval x word)

/-- Equality of all future Law evaluations is preserved by the explicit
state and operation numberings in the finite input. -/
theorem behavior_iff_tables (x y : S) :
    (behavior T (lawObserve laws)).setoid.r x y ↔
      (behavior (input laws T request states operations).toTables.system
        (input laws T request states operations).toTables.observe).setoid.r
        (states x) (states y) := by
  constructor
  · intro h
    apply (behavior_iff
      (input laws T request states operations).toTables.system
      (input laws T request states operations).toTables.observe
      (states x) (states y)).mpr
    intro word
    have hsource := (behavior_iff T (lawObserve laws) x y).mp h
      (word.map operations.symm)
    have hx := tables_observe_eval laws T request states operations x
      (word.map operations.symm)
    have hy := tables_observe_eval laws T request states operations y
      (word.map operations.symm)
    have hmap : (word.map operations.symm).map operations = word := by
      simp
    rw [hmap] at hx hy
    exact hx.trans (hsource.trans hy.symm)
  · intro h
    apply (behavior_iff T (lawObserve laws) x y).mpr
    intro word
    have htable := (behavior_iff
      (input laws T request states operations).toTables.system
      (input laws T request states operations).toTables.observe
      (states x) (states y)).mp h (word.map operations)
    exact (tables_observe_eval laws T request states operations x word).symm.trans
      (htable.trans (tables_observe_eval laws T request states operations y word))

/-- Execute D on the numbered table with the decidable product Law value. -/
def run : FiniteConstruction.RunOutput n m
    ((law : laws.Law) → laws.Value law) := by
  letI := observationDecidableEq laws
  exact (input laws T request states operations).run

/-- The numbered Law procedure succeeds exactly when the original
operation/Law/request input admits a B repair quotient. -/
theorem run_success_iff_repair_exists :
    (∃ tables : FiniteConstruction.SuccessTables n m
        ((law : laws.Law) → laws.Value law),
      (run laws T request states operations).outcome = Sum.inr tables) ↔
      Nonempty (RepairQuotient.{u, v, u, u} T (lawObserve laws)
        (fun x y => request x y = true)) := by
  letI := observationDecidableEq laws
  rw [show run laws T request states operations =
    FiniteConstruction.runRepair
      (input laws T request states operations).toTables from rfl,
    FiniteConstruction.runRepair_success_iff,
    repair_exists_iff_request_behavior]
  constructor
  · intro h x y hrequest
    apply (behavior_iff_tables laws T request states operations x y).mpr
    apply h (states x) (states y)
    exact ((input laws T request states operations).toTables_requestRel x y).mpr
      hrequest
  · intro h numberedX numberedY hrequest
    let x := states.symm numberedX
    let y := states.symm numberedY
    have hx : states x = numberedX := states.apply_symm_apply numberedX
    have hy : states y = numberedY := states.apply_symm_apply numberedY
    rw [← hx, ← hy] at hrequest ⊢
    apply (behavior_iff_tables laws T request states operations x y).mp
    apply h x y
    exact ((input laws T request states operations).toTables_requestRel x y).mp
      hrequest

/-- The actual returned upper table, viewed as a B repair quotient. -/
def returnedUpper
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables) :
    RepairQuotient
      (input laws T request states operations).toTables.system
      (input laws T request states operations).toTables.observe
      (input laws T request states operations).toTables.requestRel := by
  letI := observationDecidableEq laws
  exact FiniteConstruction.successUpperRepair
    (input laws T request states operations).toTables tables h

/-- The source map into the returned upper numbered quotient factors the
semantic future-Law Reading through the original source numbering. -/
noncomputable def betaToReturned
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables) :
    (betaReading laws T).Target →
      (returnedUpper laws T request states operations tables h).Target :=
  Quotient.lift
    (fun x => (returnedUpper laws T request states operations tables h).read
      (states x)) (by
    intro x y hxy
    change (returnedUpper laws T request states operations tables h).kernel.setoid.r
      (states x) (states y)
    rw [show (returnedUpper laws T request states operations tables h).kernel =
      behavior (input laws T request states operations).toTables.system
        (input laws T request states operations).toTables.observe from
      FiniteConstruction.successUpperRepair_kernel_eq
        (input laws T request states operations).toTables tables h]
    exact (behavior_iff_tables laws T request states operations x y).mp hxy)

@[simp] theorem betaToReturned_read
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (x : S) :
    betaToReturned laws T request states operations tables h
      ((betaReading laws T).read x) =
        (returnedUpper laws T request states operations tables h).read
          (states x) := rfl

theorem betaToReturned_bijective
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables) :
    Function.Bijective
      (betaToReturned laws T request states operations tables h) := by
  let q := returnedUpper laws T request states operations tables h
  constructor
  · intro z₁ z₂ heq
    refine Quotient.inductionOn₂ z₁ z₂ ?_ heq
    intro x y hxy
    apply Quotient.sound
    apply (behavior_iff_tables laws T request states operations x y).mpr
    have hk : q.kernel.setoid.r (states x) (states y) := hxy
    rw [show q.kernel =
      behavior (input laws T request states operations).toTables.system
        (input laws T request states operations).toTables.observe from
      FiniteConstruction.successUpperRepair_kernel_eq
        (input laws T request states operations).toTables tables h] at hk
    exact hk
  · intro target
    obtain ⟨numbered, hread⟩ := q.surjective target
    refine ⟨(betaReading laws T).read (states.symm numbered), ?_⟩
    rw [betaToReturned_read]
    simpa [q] using hread

/-- The concrete upper output and the semantic future-Law quotient are
canonically equivalent over the original source. -/
noncomputable def betaReturnedEquiv
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables) :
    (betaReading laws T).Target ≃
      (returnedUpper laws T request states operations tables h).Target :=
  Equiv.ofBijective (betaToReturned laws T request states operations tables h)
    (betaToReturned_bijective laws T request states operations tables h)

@[simp] theorem betaReturnedEquiv_read
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (x : S) :
    betaReturnedEquiv laws T request states operations tables h
      ((betaReading laws T).read x) =
        (returnedUpper laws T request states operations tables h).read
          (states x) :=
  betaToReturned_read laws T request states operations tables h x

/-- The finite upper equivalence also preserves every named operation,
with operation names transported by the supplied enumeration. -/
theorem betaReturnedEquiv_step
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (e : E) (z : (betaReading laws T).Target) :
    betaReturnedEquiv laws T request states operations tables h
      (betaStep laws T e z) =
      (returnedUpper laws T request states operations tables h).step
        (operations e)
        (betaReturnedEquiv laws T request states operations tables h z) := by
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  rw [betaStep_read, betaReturnedEquiv_read, betaReturnedEquiv_read]
  have hs := (input laws T request states operations).toTables_step e x
  have hs' :
      (input laws T request states operations).toTables.system.step
        (operations e) (states x) = states (T.step e x) := hs
  change
    (returnedUpper laws T request states operations tables h).read
      (states (T.step e x)) =
        (returnedUpper laws T request states operations tables h).step
          (operations e)
          ((returnedUpper laws T request states operations tables h).read
            (states x))
  rw [← hs']
  exact (returnedUpper laws T request states operations tables h).step_comm
    (operations e) (states x)

/-- The returned observation table preserves every original Law value
under this equivalence, on every quotient point. -/
theorem betaReturnedEquiv_law
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (law : laws.Law) (z : (betaReading laws T).Target) :
    ((returnedUpper laws T request states operations tables h).observation
      (betaReturnedEquiv laws T request states operations tables h z)) law =
        betaLawFactor laws T law z := by
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  rw [betaReturnedEquiv_read,
    (returnedUpper laws T request states operations tables h).observation_comm]
  have ho := (input laws T request states operations).toTables_observe x
  have holaw := congrFun ho law
  change (input laws T request states operations).toTables.observe
    ((input laws T request states operations).states x) law =
      betaLawFactor laws T law ((betaReading laws T).read x)
  rw [holaw]
  rfl

/-- A source-commuting comparison map to the returned upper target is unique. -/
theorem betaReturnedEquiv_unique
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (f : (betaReading laws T).Target →
      (returnedUpper laws T request states operations tables h).Target)
    (hsource : ∀ x : S, f ((betaReading laws T).read x) =
      (returnedUpper laws T request states operations tables h).read (states x)) :
    f = betaReturnedEquiv laws T request states operations tables h := by
  funext z
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  exact (hsource x).trans
    (betaReturnedEquiv_read laws T request states operations tables h x).symm

/-- With no operation names, the actual returned upper quotient is the
standard G-103 Law quotient up to the unique source-commuting equivalence. -/
noncomputable def returnedJointEquiv_of_isEmpty [IsEmpty E]
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables) :
    (returnedUpper laws T request states operations tables h).Target ≃
      laws.jointKernelReading.Target :=
  (betaReturnedEquiv laws T request states operations tables h).symm.trans
    (betaJointEquiv_of_isEmpty laws T)

@[simp] theorem returnedJointEquiv_of_isEmpty_read [IsEmpty E]
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (x : S) :
    returnedJointEquiv_of_isEmpty laws T request states operations tables h
      ((returnedUpper laws T request states operations tables h).read
        (states x)) = laws.jointKernelReading.read x := by
  change betaJointEquiv_of_isEmpty laws T
    ((betaReturnedEquiv laws T request states operations tables h).symm
      ((returnedUpper laws T request states operations tables h).read
        (states x))) = laws.jointKernelReading.read x
  rw [← betaReturnedEquiv_read laws T request states operations tables h x]
  rw [Equiv.symm_apply_apply]
  exact betaJointEquiv_of_isEmpty_comm laws T x

/-- The empty-operation comparison also preserves every returned Law value. -/
theorem returnedJointEquiv_of_isEmpty_law [IsEmpty E]
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (law : laws.Law)
    (z : (returnedUpper laws T request states operations tables h).Target) :
    laws.jointKernelLawFactor law
      (returnedJointEquiv_of_isEmpty laws T request states operations tables h z) =
        (returnedUpper laws T request states operations tables h).observation z law := by
  obtain ⟨numbered, rfl⟩ :=
    (returnedUpper laws T request states operations tables h).surjective z
  let x := states.symm numbered
  have hx : states x = numbered := states.apply_symm_apply numbered
  rw [← hx, returnedJointEquiv_of_isEmpty_read,
    (returnedUpper laws T request states operations tables h).observation_comm]
  have ho := (input laws T request states operations).toTables_observe x
  have holaw := congrFun ho law
  change laws.eval law x =
    (input laws T request states operations).toTables.observe
      ((input laws T request states operations).states x) law
  rw [holaw]
  rfl

theorem returnedJointEquiv_of_isEmpty_unique [IsEmpty E]
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (run laws T request states operations).outcome = Sum.inr tables)
    (f : (returnedUpper laws T request states operations tables h).Target →
      laws.jointKernelReading.Target)
    (hsource : ∀ x : S,
      f ((returnedUpper laws T request states operations tables h).read
        (states x)) = laws.jointKernelReading.read x) :
    f = returnedJointEquiv_of_isEmpty laws T request states operations tables h := by
  funext z
  obtain ⟨numbered, rfl⟩ :=
    (returnedUpper laws T request states operations tables h).surjective z
  let x := states.symm numbered
  have hx : states x = numbered := states.apply_symm_apply numbered
  rw [← hx]
  exact (hsource x).trans
    (returnedJointEquiv_of_isEmpty_read laws T request states operations tables h x).symm

end FiniteLawBridge

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
