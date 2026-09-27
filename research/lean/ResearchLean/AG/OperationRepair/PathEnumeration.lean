import ResearchLean.AG.OperationRepair.PathBridge
import ResearchLean.AG.OperationRepair.FiniteLawBridge

/-!
# Numbering general finite path requests

The finite list of operation-word pairs on an arbitrary enumerated source is
transported to the exact Boolean request table consumed by D. Both success
and failure of that same run are compared with the original unnumbered data.
-/

namespace AAT.AG.OperationRepair

namespace FiniteEnumeration

universe u v w

variable {S : Type u} {E : Type v} {O : Type w} {n m : Nat}

/-- Transport each original operation word through the supplied numbering. -/
def Input.numberPaths (a : Input S E O n m)
    (paths : List (List E × List E)) :
    List (List (Fin m) × List (Fin m)) :=
  paths.map fun pair =>
    (pair.1.map a.operations, pair.2.map a.operations)

theorem Input.toTables_eval (a : Input S E O n m)
    (source : S) (word : List E) :
    a.toTables.system.eval (a.states source) (word.map a.operations) =
      a.states (a.system.eval source word) := by
  induction word generalizing source with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, OperationSystem.eval_cons,
        OperationSystem.eval_cons]
      have hs' : a.toTables.system.step (a.operations e) (a.states source) =
          a.states (a.system.step e source) := a.toTables_step e source
      rw [hs', ih]

private theorem Input.toTables_observe_eval (a : Input S E O n m)
    (source : S) (word : List E) :
    a.toTables.observe
      (a.toTables.system.eval (a.states source) (word.map a.operations)) =
        a.observe (a.system.eval source word) := by
  rw [a.toTables_eval]
  exact a.toTables_observe (a.system.eval source word)

/-- Behavioral equivalence itself is invariant under the supplied state
and operation numberings. -/
theorem Input.behavior_iff_tables (a : Input S E O n m) (x y : S) :
    (behavior a.system a.observe).setoid.r x y ↔
      (behavior a.toTables.system a.toTables.observe).setoid.r
        (a.states x) (a.states y) := by
  constructor
  · intro h
    apply (behavior_iff a.toTables.system a.toTables.observe
      (a.states x) (a.states y)).mpr
    intro word
    have hsource := (behavior_iff a.system a.observe x y).mp h
      (word.map a.operations.symm)
    have hx := a.toTables_observe_eval x (word.map a.operations.symm)
    have hy := a.toTables_observe_eval y (word.map a.operations.symm)
    have hmap : (word.map a.operations.symm).map a.operations = word := by
      simp
    rw [hmap] at hx hy
    exact hx.trans (hsource.trans hy.symm)
  · intro h
    apply (behavior_iff a.system a.observe x y).mpr
    intro word
    have htable := (behavior_iff a.toTables.system a.toTables.observe
      (a.states x) (a.states y)).mp h (word.map a.operations)
    exact (a.toTables_observe_eval x word).symm.trans
      (htable.trans (a.toTables_observe_eval y word))

/-- The generated relation on numbered states is exactly the image of the
original source path relation, including empty state and operation types. -/
theorem Input.numberPaths_request_iff (a : Input S E O n m)
    (paths : List (List E × List E)) (x y : S) :
    pathRequest a.toTables.system (a.numberPaths paths)
      (a.states x) (a.states y) ↔ pathRequest a.system paths x y := by
  constructor
  · rintro ⟨numberedPair, hpair, numberedSource, hx, hy⟩
    obtain ⟨pair, hp, hpairEq⟩ := List.mem_map.mp hpair
    subst numberedPair
    let source := a.states.symm numberedSource
    have hsource : a.states source = numberedSource :=
      a.states.apply_symm_apply numberedSource
    have hx' : a.states x = a.states (a.system.eval source pair.1) := by
      calc
        a.states x = a.toTables.system.eval numberedSource
          (pair.1.map a.operations) := hx
        _ = a.toTables.system.eval (a.states source)
          (pair.1.map a.operations) := by rw [hsource]
        _ = a.states (a.system.eval source pair.1) :=
          a.toTables_eval source pair.1
    have hy' : a.states y = a.states (a.system.eval source pair.2) := by
      calc
        a.states y = a.toTables.system.eval numberedSource
          (pair.2.map a.operations) := hy
        _ = a.toTables.system.eval (a.states source)
          (pair.2.map a.operations) := by rw [hsource]
        _ = a.states (a.system.eval source pair.2) :=
          a.toTables_eval source pair.2
    exact ⟨pair, hp, source, a.states.injective hx', a.states.injective hy'⟩
  · rintro ⟨pair, hp, source, hx, hy⟩
    refine ⟨(pair.1.map a.operations, pair.2.map a.operations),
      List.mem_map.mpr ⟨pair, hp, rfl⟩, a.states source, ?_, ?_⟩
    · rw [hx]
      exact (a.toTables_eval source pair.1).symm
    · rw [hy]
      exact (a.toTables_eval source pair.2).symm

/-- Materialize the actual path-generated request table on the numbered
operation system, retaining the original transition and observation tables. -/
def Input.pathTables (a : Input S E O n m)
    (paths : List (List E × List E)) : FiniteRepairInput n m O :=
  a.toTables.withPathRequest (a.numberPaths paths)

theorem Input.pathTables_requestRel (a : Input S E O n m)
    (paths : List (List E × List E)) (x y : S) :
    (a.pathTables paths).requestRel (a.states x) (a.states y) ↔
      pathRequest a.system paths x y :=
  (a.toTables.withPathRequest_requestRel (a.numberPaths paths)
    (a.states x) (a.states y)).trans (a.numberPaths_request_iff paths x y)

/-- The numbered path input runs D's unchanged procedure. -/
def Input.runPaths [DecidableEq O] (a : Input S E O n m)
    (paths : List (List E × List E)) :
    FiniteConstruction.RunOutput n m O :=
  a.toTables.runPathRepair (a.numberPaths paths)

/-- D on the generated numbered path table succeeds exactly when the
original unnumbered path request admits a B repair quotient. -/
theorem Input.runPaths_success_iff_repair_exists [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E)) :
    (∃ tables : FiniteConstruction.SuccessTables n m O,
      (a.runPaths paths).outcome = Sum.inr tables) ↔
      Nonempty (RepairQuotient.{u, v, w, u} a.system a.observe
        (pathRequest a.system paths)) := by
  rw [show a.runPaths paths = FiniteConstruction.runRepair
    (a.pathTables paths) from rfl,
    FiniteConstruction.runRepair_success_iff,
    repair_exists_iff_request_behavior]
  constructor
  · intro h x y hrequest
    apply (a.behavior_iff_tables x y).mpr
    exact h (a.states x) (a.states y)
      ((a.pathTables_requestRel paths x y).mpr hrequest)
  · intro h numberedX numberedY hrequest
    let x := a.states.symm numberedX
    let y := a.states.symm numberedY
    have hx : a.states x = numberedX := a.states.apply_symm_apply numberedX
    have hy : a.states y = numberedY := a.states.apply_symm_apply numberedY
    rw [← hx, ← hy] at hrequest ⊢
    apply (a.behavior_iff_tables x y).mp
    exact h x y ((a.pathTables_requestRel paths x y).mp hrequest)

/-- A failing D run returns a pair generated by the original unnumbered
paths and a concrete separating word on the original operation names. -/
theorem Input.runPaths_failure [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (numberedX numberedY : Fin n) (word : List (Fin m))
    (h : (a.runPaths paths).outcome =
      Sum.inl (numberedX, numberedY, word)) :
    let x := a.states.symm numberedX
    let y := a.states.symm numberedY
    let originalWord := word.map a.operations.symm
    pathRequest a.system paths x y ∧ originalWord.length < n * n ∧
      a.observe (a.system.eval x originalWord) ≠
        a.observe (a.system.eval y originalWord) := by
  let x := a.states.symm numberedX
  let y := a.states.symm numberedY
  let originalWord := word.map a.operations.symm
  have hx : a.states x = numberedX := a.states.apply_symm_apply numberedX
  have hy : a.states y = numberedY := a.states.apply_symm_apply numberedY
  obtain ⟨hreq, hlen, hsep⟩ :=
    a.toTables.runPathRepair_failure (a.numberPaths paths)
      numberedX numberedY word h
  have hrel : pathRequest a.system paths x y := by
    apply (a.numberPaths_request_iff paths x y).mp
    rw [hx, hy]
    exact hreq
  have hmap : originalWord.map a.operations = word := by
    simp [originalWord]
  have hobsx := a.toTables_observe_eval x originalWord
  have hobsy := a.toTables_observe_eval y originalWord
  rw [hx, hmap] at hobsx
  rw [hy, hmap] at hobsy
  refine ⟨hrel, by simpa [originalWord] using hlen, ?_⟩
  intro heq
  exact hsep (hobsx.trans (heq.trans hobsy.symm))

/-- The actual successful upper quotient of the numbered path run. -/
def Input.pathUpperRepair [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (a.runPaths paths).outcome = Sum.inr tables) :
    RepairQuotient (a.pathTables paths).system
      (a.pathTables paths).observe (a.pathTables paths).requestRel :=
  FiniteConstruction.successUpperRepair (a.pathTables paths) tables h

/-- Reindex the returned operation tables by the original operation names. -/
def Input.pathTargetSystem [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (a.runPaths paths).outcome = Sum.inr tables) :
    OperationSystem (a.pathUpperRepair paths tables h).Target E where
  step := fun e => (a.pathUpperRepair paths tables h).step (a.operations e)

private theorem Input.pathTargetSystem_eval [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (a.runPaths paths).outcome = Sum.inr tables)
    (z : (a.pathUpperRepair paths tables h).Target) (word : List E) :
    (a.pathTargetSystem paths tables h).eval z word =
      (a.pathUpperRepair paths tables h).targetSystem.eval z
        (word.map a.operations) := by
  induction word generalizing z with
  | nil => rfl
  | cons e rest ih =>
      rw [List.map_cons, OperationSystem.eval_cons,
        OperationSystem.eval_cons]
      exact ih ((a.pathUpperRepair paths tables h).step
        (a.operations e) z)

/-- Every original listed path equation holds on the whole returned upper
target, not merely on images of chosen source representatives. -/
theorem Input.runPaths_upper_equations [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (a.runPaths paths).outcome = Sum.inr tables) :
    ∀ pair ∈ paths, ∀ z : (a.pathUpperRepair paths tables h).Target,
      (a.pathTargetSystem paths tables h).eval z pair.1 =
        (a.pathTargetSystem paths tables h).eval z pair.2 := by
  have heq := a.toTables.runPathRepair_upper_equations
    (a.numberPaths paths) tables h
  change (a.pathUpperRepair paths tables h).PathEquations
    (a.numberPaths paths) at heq
  intro pair hp z
  rw [a.pathTargetSystem_eval paths tables h z pair.1,
    a.pathTargetSystem_eval paths tables h z pair.2]
  exact heq (pair.1.map a.operations, pair.2.map a.operations)
    (List.mem_map.mpr ⟨pair, hp, rfl⟩) z

/-- Transport the actual numbered upper success output back to the original
source and operation names. This is a repair for the original path relation,
with no chosen quotient supplied as an input. -/
def Input.pathUpperRepairSource [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (a.runPaths paths).outcome = Sum.inr tables) :
    RepairQuotient.{u, v, w, 0} a.system a.observe
      (pathRequest a.system paths) where
  Target := (a.pathUpperRepair paths tables h).Target
  read := fun x => (a.pathUpperRepair paths tables h).read (a.states x)
  surjective := by
    intro target
    obtain ⟨numbered, hread⟩ :=
      (a.pathUpperRepair paths tables h).surjective target
    refine ⟨a.states.symm numbered, ?_⟩
    simpa using hread
  step := fun e => (a.pathUpperRepair paths tables h).step (a.operations e)
  observation := (a.pathUpperRepair paths tables h).observation
  step_comm := by
    intro e x
    have hs := a.toTables_step e x
    have hs' : (a.pathTables paths).system.step
        (a.operations e) (a.states x) = a.states (a.system.step e x) := hs
    rw [← hs']
    exact (a.pathUpperRepair paths tables h).step_comm (a.operations e)
      (a.states x)
  observation_comm := by
    intro x
    rw [(a.pathUpperRepair paths tables h).observation_comm]
    exact a.toTables_observe x
  identifies := by
    intro x y hxy
    apply (a.pathUpperRepair paths tables h).identifies
    exact (a.pathTables_requestRel paths x y).mpr hxy

/-- The transported upper output has exactly the original source's
future-observation kernel, rather than merely a refinement of it. -/
theorem Input.pathUpperRepairSource_kernel_eq [DecidableEq O]
    (a : Input S E O n m) (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (a.runPaths paths).outcome = Sum.inr tables) :
    (a.pathUpperRepairSource paths tables h).kernel.setoid =
      (behavior a.system a.observe).setoid := by
  apply Setoid.ext
  intro x y
  change (a.pathUpperRepair paths tables h).kernel.setoid.r
    (a.states x) (a.states y) ↔
      (behavior a.system a.observe).setoid.r x y
  rw [show (a.pathUpperRepair paths tables h).kernel =
    behavior (a.pathTables paths).system (a.pathTables paths).observe from
    FiniteConstruction.successUpperRepair_kernel_eq
      (a.pathTables paths) tables h]
  exact (a.behavior_iff_tables x y).symm

end FiniteEnumeration

namespace FiniteLawPath

open AAT.AG.CanonicalResolution

variable {S : Type u} {E : Type v} {n m : Nat}
variable (laws : FiniteLawFamily S) (T : OperationSystem S E)
variable (states : S ≃ Fin n)
variable (operations : E ≃ Fin m)

-- The request field is initialized here and replaced by the path table before D runs.
private def sourceInput : FiniteEnumeration.Input S E
    ((law : laws.Law) → laws.Value law) n m :=
  FiniteLawBridge.input laws T (fun _ _ => false) states operations

/-- Execute D on a source path list, with Law observation from the original
finite family and explicit state/operation numberings. -/
def runPaths (paths : List (List E × List E)) :
    FiniteConstruction.RunOutput n m
      ((law : laws.Law) → laws.Value law) := by
  letI := FiniteLawBridge.observationDecidableEq laws
  exact (sourceInput laws T states operations).runPaths paths

/-- The actual returned upper quotient, transported to original sources. -/
def returnedUpper (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (runPaths laws T states operations paths).outcome =
      Sum.inr tables) :
    RepairQuotient.{u, v, u, 0} T (lawObserve laws)
      (pathRequest T paths) := by
  letI := FiniteLawBridge.observationDecidableEq laws
  exact (sourceInput laws T states operations).pathUpperRepairSource
    paths tables h

/-- This path run's upper output is the semantic future-Law quotient, as a
source-commuting equivalence of the actual numbered target. -/
noncomputable def betaEquiv (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (runPaths laws T states operations paths).outcome =
      Sum.inr tables) :
    (betaReading laws T).Target ≃
      (returnedUpper laws T states operations paths tables h).Target :=
  (Quotient.congrRight (fun x y => by
    rw [show (returnedUpper laws T states operations paths tables h).kernel.setoid =
      (behavior T (lawObserve laws)).setoid from
      (sourceInput laws T states operations).pathUpperRepairSource_kernel_eq
        paths tables h])).trans
      (returnedUpper laws T states operations paths tables h).standardEquiv

@[simp] theorem betaEquiv_read (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (runPaths laws T states operations paths).outcome =
      Sum.inr tables) (x : S) :
    betaEquiv laws T states operations paths tables h
      ((betaReading laws T).read x) =
        (returnedUpper laws T states operations paths tables h).read x :=
  rfl

/-- The path output comparison preserves every original named operation. -/
theorem betaEquiv_step (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (runPaths laws T states operations paths).outcome =
      Sum.inr tables) (e : E) (z : (betaReading laws T).Target) :
    betaEquiv laws T states operations paths tables h
      (FiniteLawBridge.betaStep laws T e z) =
      (returnedUpper laws T states operations paths tables h).step e
        (betaEquiv laws T states operations paths tables h z) := by
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  rw [FiniteLawBridge.betaStep_read, betaEquiv_read, betaEquiv_read]
  exact (returnedUpper laws T states operations paths tables h).step_comm
    e x

/-- Every Law evaluation is preserved by the same output equivalence. -/
theorem betaEquiv_law (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (runPaths laws T states operations paths).outcome =
      Sum.inr tables) (law : laws.Law)
    (z : (betaReading laws T).Target) :
    (returnedUpper laws T states operations paths tables h).observation
      (betaEquiv laws T states operations paths tables h z) law =
        betaLawFactor laws T law z := by
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  rw [betaEquiv_read,
    (returnedUpper laws T states operations paths tables h).observation_comm]
  rfl

/-- Source commutation uniquely determines this Law/operation comparison. -/
theorem betaEquiv_unique (paths : List (List E × List E))
    (tables : FiniteConstruction.SuccessTables n m
      ((law : laws.Law) → laws.Value law))
    (h : (runPaths laws T states operations paths).outcome =
      Sum.inr tables)
    (f : (betaReading laws T).Target →
      (returnedUpper laws T states operations paths tables h).Target)
    (hsource : ∀ x : S, f ((betaReading laws T).read x) =
      (returnedUpper laws T states operations paths tables h).read x) :
    f = betaEquiv laws T states operations paths tables h := by
  funext z
  obtain ⟨x, rfl⟩ := (betaReading laws T).surjective z
  exact (hsource x).trans
    (betaEquiv_read laws T states operations paths tables h x).symm

end FiniteLawPath

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
