import ResearchLean.AG.RepairObservationDuality.FiberSufficiency
import Mathlib.Data.ENat.Lattice

/-!
# G-131 C: deterministic primitive-query executions

## Implementation notes

A next-step function sees only the question/answer list and returns either a
complete output value or one primitive index. The run records repeated indices
separately. The fixed procedure asks a prescribed list; its final answer is
chosen from the set of values correct for every remaining possible input.
This is an existence construction in the free-computation query model.
Finite enumeration replacing that choice is the separate planning obligation D.
-/

namespace AAT.AG.RepairObservationDuality.PrimitiveQueries
variable {V J K A : Type*}

/-- C's visible history records each exact primitive question and response. -/
abbrev History (J K : Type*) := List (J × K)

/-- C's deterministic next step reads only a history, never the unknown input. -/
abbrev Procedure (J K A : Type*) := History J K → A ⊕ J

/-- C's terminating execution includes every primitive query in its question list. -/
inductive Run (eval : V → J → K) (next : Procedure J K A) (v : V) :
    History J K → A → List J → Prop
  | halt {hist a} (h : next hist = Sum.inl a) : Run eval next v hist a []
  | ask {hist a j qs} (h : next hist = Sum.inr j)
      (tail : Run eval next v (hist ++ [(j, eval v j)]) a qs) :
      Run eval next v hist a (j :: qs)

/-- C's procedures terminate and return an independently valid output on every
input in the known fiber. Both properties apply to the same procedure. -/
def Correct (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (next : Procedure J K A) : Prop :=
  (∀ v ∈ F, ∃ a qs, Run eval next v [] a qs) ∧
  (∀ v ∈ F, ∀ a qs, Run eval next v [] a qs → valid v a)

/-- Determinism preserves both the final full value and the entire question list. -/
theorem Run.deterministic {eval : V → J → K} {next : Procedure J K A} {v hist a qs}
    (run : Run eval next v hist a qs) :
    ∀ {a' qs'}, Run eval next v hist a' qs' → a = a' ∧ qs = qs' := by
  induction run with
  | halt h =>
      intro a' qs' run'
      cases run' with
      | halt h' => exact ⟨Sum.inl.inj (h.symm.trans h'), rfl⟩
      | ask h' _ => rw [h] at h'; cases h'
  | @ask hist a j qs h tail ih =>
      intro a' qs' run'
      cases run' with
      | halt h' => rw [h] at h'; cases h'
      | @ask _ _ j' qs' h' tail' =>
          have hj := Sum.inr.inj (h.symm.trans h')
          subst j'
          obtain ⟨ha, hqs⟩ := ih tail'
          exact ⟨ha, by simp [hqs]⟩

/-- Equal replies on the actual questions reproduce the entire adaptive run,
including repeated questions and its same complete output. -/
theorem Run.replay {eval : V → J → K} {next : Procedure J K A} {v hist a qs}
    (run : Run eval next v hist a qs) (w : V)
    (he : ∀ j ∈ qs, eval w j = eval v j) : Run eval next w hist a qs := by
  induction run with
  | halt h => exact Run.halt h
  | @ask hist a j qs h tail ih =>
      apply Run.ask h
      have hj := he j (by simp)
      have ht : ∀ j ∈ qs, eval w j = eval v j := fun j hj => he j (by simp [hj])
      simpa only [hj] using ih ht

/-- C's actual worst cost counts every query on every terminating known-fiber run. -/
noncomputable def worst (eval : V → J → K) (F : Set V) (next : Procedure J K A) : ℕ∞ :=
  ⨆ (v : V) (_ : v ∈ F) (a : A) (qs : List J)
    (_ : Run eval next v [] a qs), (qs.length : ℕ∞)

/-- C's optimum ranges over all total correct deterministic procedures. No
correct procedure gives the empty infimum, namely infinity. -/
noncomputable def optimum (eval : V → J → K) (F : Set V) (valid : V → A → Prop) : ℕ∞ :=
  ⨅ next : {next : Procedure J K A // Correct eval F valid next}, worst eval F next.1

/-- Every actual run length is bounded by its procedure's worst cost. -/
theorem run_le_worst (eval : V → J → K) (F : Set V) (next : Procedure J K A)
    {v a qs} (hv : v ∈ F) (run : Run eval next v [] a qs) :
    (qs.length : ℕ∞) ≤ worst eval F next :=
  le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le a
    (le_iSup_of_le qs (le_iSup_of_le run le_rfl))))

/-- A correct candidate provides an upper bound on the infimum over all procedures. -/
theorem optimum_le_worst (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (next : Procedure J K A) (hn : Correct eval F valid next) :
    optimum eval F valid ≤ worst eval F next := by
  change (⨅ p : {p : Procedure J K A // Correct eval F valid p}, worst eval F p.1) ≤ _
  exact iInf_le (fun p : {p : Procedure J K A // Correct eval F valid p} =>
    worst eval F p.1) ⟨next, hn⟩

/-- A constant full output uses zero questions; this also implements an all-impossible fiber. -/
def constant (a : A) : Procedure J K A := fun _ => Sum.inl a

/-- The zero-query procedure terminates with exactly its supplied full value. -/
theorem constant_run (eval : V → J → K) (v : V) (a : A) :
    Run eval (constant a) v [] a [] := Run.halt rfl

/-- A constant value valid throughout the known fiber gives a total correct procedure. -/
theorem constant_correct (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (a : A) (ha : ∀ v ∈ F, valid v a) : Correct eval F valid (constant a) := by
  constructor
  · intro v _
    exact ⟨a, [], constant_run eval v a⟩
  · intro v hv out qs run
    obtain ⟨ho, _⟩ := (constant_run eval v a).deterministic run
    subst out
    exact ha v hv

/-- Every terminating run of a constant procedure has zero queries. -/
theorem worst_constant (eval : V → J → K) (F : Set V) (a : A) :
    worst eval F (constant a) = 0 := by
  apply le_antisymm _ bot_le
  refine iSup_le fun v => iSup_le fun hv => iSup_le fun out =>
    iSup_le fun qs => iSup_le fun run => ?_
  obtain ⟨_, hq⟩ := (constant_run eval v a).deterministic run
  subst qs
  rfl

/-- Uniformly valid full output makes the optimum exactly zero. -/
theorem optimum_zero_of_constant (eval : V → J → K) (F : Set V)
    (valid : V → A → Prop) (a : A) (ha : ∀ v ∈ F, valid v a) :
    optimum eval F valid = 0 := by
  apply le_antisymm _ bot_le
  exact (optimum_le_worst eval F valid (constant a)
    (constant_correct eval F valid a ha)).trans_eq (worst_constant eval F a)

section Fixed
variable [Inhabited A]

/-- Fixed plans produce a complete value valid on the entire response fiber.
The choice is taken over known model data, not a supplied correct answer. -/
noncomputable def finish (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (hist : History J K) : A := by
  classical
  exact if h : ∃ a, ∀ v ∈ F, (∀ pair ∈ hist, eval v pair.1 = pair.2) → valid v a
    then Classical.choose h else default

/-- The generated final value is correct whenever the response fiber admits
one common valid full output. This is the basic construction API for finish. -/
theorem finish_valid (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (hist : History J K)
    (ha : ∃ a, ∀ v ∈ F, (∀ pair ∈ hist, eval v pair.1 = pair.2) → valid v a)
    {v : V} (hv : v ∈ F) (hc : ∀ pair ∈ hist, eval v pair.1 = pair.2) :
    valid v (finish eval F valid hist) := by
  classical
  simp only [finish, dif_pos ha]
  exact Classical.choose_spec ha v hv hc

/-- A fixed plan asks the supplied primitive list in order and then returns
the generated full value. History length counts repeated questions. -/
noncomputable def fixed (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (points : List J) : Procedure J K A :=
  fun hist => match points.drop hist.length with
    | [] => Sum.inl (finish eval F valid hist)
    | j :: _ => Sum.inr j

/-- The whole actual question/response list of a prescribed primitive plan. -/
def transcript (eval : V → J → K) (points : List J) (v : V) : History J K :=
  points.map fun j => (j, eval v j)

/-- Fixed execution asks exactly the prescribed list from any completed prefix. -/
theorem fixed_run_aux (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (points : List J) (v : V) (pre remaining : List J)
    (hp : points = pre ++ remaining) :
    Run eval (fixed eval F valid points) v (transcript eval pre v)
      (finish eval F valid (transcript eval points v)) remaining := by
  induction remaining generalizing pre with
  | nil =>
      apply Run.halt
      simp [fixed, transcript, hp]
  | cons j js ih =>
      have ht : points = (pre ++ [j]) ++ js := by simpa [List.append_assoc] using hp
      apply Run.ask (by simp [fixed, transcript, hp])
      simpa only [transcript, List.map_append, List.map_singleton] using ih (pre ++ [j]) ht

/-- Every input terminates after exactly the fixed list of primitive questions. -/
theorem fixed_run (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (points : List J) (v : V) :
    Run eval (fixed eval F valid points) v []
      (finish eval F valid (transcript eval points v)) points := by
  simpa [transcript] using fixed_run_aux eval F valid points v [] points (by simp)

/-- Equality on all asked indices is exactly consistency with the actual transcript. -/
theorem transcript_consistent_iff (eval : V → J → K) (points : List J) (v w : V) :
    (∀ pair ∈ transcript eval points v, eval w pair.1 = pair.2) ↔
      ∀ j ∈ points, eval w j = eval v j := by
  simp [transcript]

/-- The generated fixed plan is correct when each possible transcript admits
a common valid full output on its entire response fiber. -/
theorem fixed_correct (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (points : List J)
    (ha : ∀ v ∈ F, ∃ a, ∀ w ∈ F,
      (∀ j ∈ points, eval w j = eval v j) → valid w a) :
    Correct eval F valid (fixed eval F valid points) := by
  constructor
  · intro v _
    exact ⟨_, points, fixed_run eval F valid points v⟩
  · intro v hv out qs run
    obtain ⟨ho, _⟩ := (fixed_run eval F valid points v).deterministic run
    subst out
    obtain ⟨a, ha⟩ := ha v hv
    apply finish_valid eval F valid (transcript eval points v)
      ⟨a, fun w hw hc => ha w hw ((transcript_consistent_iff eval points v w).mp hc)⟩ hv
    exact (transcript_consistent_iff eval points v v).mpr (fun _ _ => rfl)

/-- The worst count of a fixed primitive plan is at most its list length. -/
theorem worst_fixed_le (eval : V → J → K) (F : Set V) (valid : V → A → Prop)
    (points : List J) :
    worst eval F (fixed eval F valid points) ≤ (points.length : ℕ∞) := by
  refine iSup_le fun v => iSup_le fun hv => iSup_le fun out =>
    iSup_le fun qs => iSup_le fun run => ?_
  obtain ⟨_, hq⟩ := (fixed_run eval F valid points v).deterministic run
  subst qs
  rfl

end Fixed

/-- The run relation has an actual zero-query run and rejects a different final value. -/
theorem run_examples :
    Run (fun (_ : Bool) (_ : Unit) => ()) (constant true) true [] true [] ∧
    ¬ Run (fun (_ : Bool) (_ : Unit) => ()) (constant true) true [] false [] := by
  constructor
  · exact constant_run _ _ _
  · intro run
    have h := (constant_run (fun (_ : Bool) (_ : Unit) => ()) true true).deterministic run
    exact Bool.noConfusion h.1

/-- Correctness has both valid and invalid deterministic procedures on the same
nonempty known input set, using independently prescribed exact output equality. -/
theorem correct_examples :
    Correct (fun (_ : Bool) (_ : Unit) => ()) {true} (fun v a => a = v) (constant true) ∧
    ¬ Correct (fun (_ : Bool) (_ : Unit) => ()) {true} (fun v a => a = v) (constant false) := by
  constructor
  · apply constant_correct
    intro v hv
    exact (Set.mem_singleton_iff.mp hv).symm
  · intro hn
    have he := hn.2 true (Set.mem_singleton true) false [] (constant_run _ _ _)
    exact Bool.noConfusion he

end AAT.AG.RepairObservationDuality.PrimitiveQueries
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.PrimitiveQueries
