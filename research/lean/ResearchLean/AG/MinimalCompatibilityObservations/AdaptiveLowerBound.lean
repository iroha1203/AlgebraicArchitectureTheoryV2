import ResearchLean.AG.MinimalCompatibilityObservations.PointObservation
import Formal.Util.AssertStandardAxioms

/-!
# G-128: the identity-run lower bound for adaptive point queries

The next action sees only the finite question-answer history. Every query,
including a repeated query, adds one entry to the query list.
-/

namespace AAT.AG.MinimalCompatibilityObservations

variable {G X : Type*} [Group G] [MulAction G X]

/-- A transcript records questions and exact replies from the unknown change. -/
abbrev QueryHistory (X : Type*) := List (X × X)

/-- A deterministic procedure chooses a result or a next point from the
visible history. -/
abbrev QueryProcedure (X : Type*) := QueryHistory X → Bool ⊕ X

/-- Terminating execution against `g`; the final list records every query. -/
inductive QueryRun (next : QueryProcedure X) (g : G) :
    QueryHistory X → Bool → List X → Prop where
  | halt {hist : QueryHistory X} {result : Bool}
      (h : next hist = Sum.inl result) : QueryRun next g hist result []
  | ask {hist : QueryHistory X} {result : Bool} {x : X} {qs : List X}
      (h : next hist = Sum.inr x)
      (tail : QueryRun next g (hist ++ [(x, g • x)]) result qs) :
      QueryRun next g hist result (x :: qs)

/-- A terminating procedure is correct on every possible unknown change. -/
def CorrectQueryProcedure (Gamma : Subgroup G) (next : QueryProcedure X) : Prop :=
  (∀ g : G, ∃ result qs, QueryRun next g [] result qs) ∧
  (∀ (g : G) (result : Bool) (qs : List X),
    QueryRun next g [] result qs → (result = true ↔ g ∈ Gamma))

theorem QueryRun.deterministic
    (next : QueryProcedure X) (g : G) {hist : QueryHistory X}
    {result : Bool} {qs : List X}
    (run : QueryRun next g hist result qs) :
    ∀ {result' qs'}, QueryRun next g hist result' qs' →
      result = result' ∧ qs = qs' := by
  induction run with
  | halt h =>
      intro result' qs' run'
      cases run' with
      | halt h' =>
          have he := Sum.inl.inj (h.symm.trans h')
          exact ⟨he, rfl⟩
      | ask h' _ =>
          rw [h] at h'
          cases h'
  | @ask hist result x qs h tail ih =>
      intro result' qs' run'
      cases run' with
      | halt h' =>
          rw [h] at h'
          cases h'
      | @ask _ _ x' qs' h' tail' =>
          have hx : x = x' := Sum.inr.inj (h.symm.trans h')
          subst x'
          obtain ⟨hr, hqs⟩ := ih tail'
          exact ⟨hr, by simp [hqs]⟩

/-- A change fixing every point asked on the identity run reproduces that
run exactly, including all repeated questions and the final answer. -/
theorem QueryRun.replay_identity
    (next : QueryProcedure X) (k : G) {hist : QueryHistory X}
    {result : Bool} {qs : List X}
    (run : QueryRun next (1 : G) hist result qs)
    (hfix : ∀ x ∈ qs, k • x = x) : QueryRun next k hist result qs := by
  induction run with
  | halt h => exact QueryRun.halt h
  | @ask hist result x qs h tail ih =>
      have hx : k • x = x := hfix x (by simp)
      have htail : ∀ y ∈ qs, k • y = y := by
        intro y hy
        exact hfix y (by simp [hy])
      apply QueryRun.ask h
      simpa [hx] using ih htail

variable [DecidableEq X]

/-- The queried points on the identity run form a sufficient observation
set for any procedure that always terminates and answers correctly. -/
theorem identity_queries_sufficient
    (Gamma : Subgroup G) (next : QueryProcedure X)
    (correct : CorrectQueryProcedure Gamma next)
    (result : Bool) (qs : List X)
    (run : QueryRun next (1 : G) [] result qs) :
    Sufficient Gamma qs.toFinset := by
  classical
  intro k hk
  have hfix : ∀ x ∈ qs, k • x = x := by
    intro x hx
    exact hk x (List.mem_toFinset.mpr hx)
  have replay : QueryRun next k [] result qs :=
    QueryRun.replay_identity next k run hfix
  have hresult : result = true :=
    (correct.2 1 result qs run).mpr Gamma.one_mem
  exact (correct.2 k result qs replay).mp hresult

/-- The number of distinct identity-run questions is at most its total
query count, and already bounds the optimal fixed observation size. -/
theorem minObservations_le_identity_queries
    (Gamma : Subgroup G) (next : QueryProcedure X)
    (correct : CorrectQueryProcedure Gamma next)
    (result : Bool) (qs : List X)
    (run : QueryRun next (1 : G) [] result qs) :
    minObservations (X := X) Gamma ≤ (qs.length : ℕ∞) := by
  classical
  have hS := identity_queries_sufficient Gamma next correct result qs run
  calc
    minObservations (X := X) Gamma ≤ ((qs.toFinset.card : ℕ) : ℕ∞) :=
      minObservations_le Gamma qs.toFinset hS
    _ ≤ (qs.length : ℕ∞) := by exact_mod_cast List.toFinset_card_le qs

/-- Infinite fixed-observation number rules out every terminating correct
adaptive procedure: its identity run would supply a finite sufficient set. -/
theorem no_correct_procedure_of_minObservations_top
    (Gamma : Subgroup G)
    (hmin : minObservations (X := X) Gamma = ⊤) :
    ¬ ∃ next : QueryProcedure X, CorrectQueryProcedure Gamma next := by
  intro h
  obtain ⟨next, correct⟩ := h
  obtain ⟨result, qs, run⟩ := correct.1 (1 : G)
  have hS := identity_queries_sufficient Gamma next correct result qs run
  exact (minObservations_eq_top_iff (X := X) Gamma).mp hmin ⟨qs.toFinset, hS⟩

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
