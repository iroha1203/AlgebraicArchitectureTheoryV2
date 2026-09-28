import ResearchLean.AG.MinimalCompatibilityObservations.AdaptiveLowerBound
import Formal.Util.AssertStandardAxioms

/-!
# G-128: the minimax query count

The supremum counts every terminating run, including repeated questions. For a
correct procedure every unknown change has exactly one such run.
-/

namespace AAT.AG.MinimalCompatibilityObservations

variable {G X : Type*} [Group G] [MulAction G X]

/-- The worst number of exact point queries of a procedure. -/
noncomputable def worstQueries (next : QueryProcedure X) : ℕ∞ :=
  ⨆ (g : G) (result : Bool) (qs : List X)
      (_ : QueryRun next g [] result qs), (qs.length : ℕ∞)

/-- The optimal worst query count, with infinity for no correct procedure. -/
noncomputable def optimalQueries (Gamma : Subgroup G) : ℕ∞ :=
  ⨅ next : {next : QueryProcedure X // CorrectQueryProcedure Gamma next},
    worstQueries (G := G) next.1

theorem run_count_le_worst (next : QueryProcedure X) (g : G)
    (result : Bool) (qs : List X) (run : QueryRun next g [] result qs) :
    (qs.length : ℕ∞) ≤ worstQueries (G := G) next := by
  unfold worstQueries
  exact le_iSup_of_le g (le_iSup_of_le result
    (le_iSup_of_le qs (le_iSup_of_le run le_rfl)))

variable [DecidableEq X]

/-- Every correct adaptive procedure costs at least the minimum sufficient
fixed observation size on its identity run. -/

theorem minObservations_le_worst (Gamma : Subgroup G)
    (next : QueryProcedure X) (correct : CorrectQueryProcedure Gamma next) :
    minObservations (X := X) Gamma ≤ worstQueries (G := G) next := by
  obtain ⟨result, qs, run⟩ := correct.1 (1 : G)
  exact (minObservations_le_identity_queries Gamma next correct result qs run).trans
    (run_count_le_worst next 1 result qs run)

/-- Adaptive choice cannot improve the worst case below the fixed-set minimum. -/
theorem minObservations_le_optimalQueries (Gamma : Subgroup G) :
    minObservations (X := X) Gamma ≤ optimalQueries (X := X) Gamma := by
  unfold optimalQueries
  refine le_iInf fun next => ?_
  exact minObservations_le_worst Gamma next.1 next.2

section FixedProcedure

/-- A fixed-query procedure asks each point in order, then checks whether any
compatible change agrees with the recorded answers. -/
noncomputable def fixedProcedure (Gamma : Subgroup G) (points : List X) :
    QueryProcedure X := by
  classical
  exact fun hist =>
    match points.drop hist.length with
    | [] => Sum.inl (decide (∃ h : G, h ∈ Gamma ∧
        ∀ pair ∈ hist, h • pair.1 = pair.2))
    | x :: _ => Sum.inr x

/-- The result obtained after all fixed queries are answered by `g`. -/
noncomputable def fixedAnswer (Gamma : Subgroup G) (points : List X) (g : G) : Bool := by
  classical
  exact decide (∃ h : G, h ∈ Gamma ∧ ∀ x ∈ points, h • x = g • x)

private theorem fixedProcedure_run_aux (Gamma : Subgroup G) (points : List X)
    (g : G) (pre remaining : List X) (hpoints : points = pre ++ remaining) :
    QueryRun (fixedProcedure Gamma points) g
      (pre.map fun x => (x, g • x)) (fixedAnswer Gamma points g) remaining := by
  induction remaining generalizing pre with
  | nil =>
      classical
      apply QueryRun.halt
      simp [fixedProcedure, fixedAnswer, hpoints]
  | cons x xs ih =>
      have htail : points = (pre ++ [x]) ++ xs := by
        simpa [List.append_assoc] using hpoints
      have run := ih (pre ++ [x]) htail
      have hnext : fixedProcedure Gamma points (pre.map fun y => (y, g • y)) =
          Sum.inr x := by
        classical
        simp [fixedProcedure, hpoints]
      have hrun : QueryRun (fixedProcedure Gamma points) g
          ((pre.map fun y => (y, g • y)) ++ [(x, g • x)])
          (fixedAnswer Gamma points g) xs := by
        simpa only [List.map_append, List.map_singleton] using run
      exact QueryRun.ask hnext hrun

theorem fixedProcedure_run (Gamma : Subgroup G) (points : List X) (g : G) :
    QueryRun (fixedProcedure Gamma points) g [] (fixedAnswer Gamma points g) points := by
  simpa using fixedProcedure_run_aux Gamma points g [] points (by simp)

/-- Sufficient observations make the terminal compatibility search exact. -/
theorem fixedAnswer_correct (Gamma : Subgroup G) (B : Finset X)
    (hB : Sufficient Gamma B) (g : G) :
    fixedAnswer Gamma B.toList g = true ↔ g ∈ Gamma := by
  classical
  simp only [fixedAnswer, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hgamma, heq⟩
    have hfix : h⁻¹ * g ∈ pointStabilizer B := by
      intro x hx
      have hpoint : h • x = g • x := heq x (Finset.mem_toList.mpr hx)
      have := congrArg (fun y => h⁻¹ • y) hpoint
      simpa [mul_smul] using this.symm
    have hk : h⁻¹ * g ∈ Gamma := hB hfix
    have hg : g = h * (h⁻¹ * g) := by simp
    rw [hg]
    exact Gamma.mul_mem hgamma hk
  · intro hg
    exact ⟨g, hg, by intro x hx; rfl⟩

/-- The fixed finite observation set supplies a total, correct query
procedure with exactly one query per listed point. -/
theorem fixedProcedure_correct (Gamma : Subgroup G) (B : Finset X)
    (hB : Sufficient Gamma B) :
    CorrectQueryProcedure Gamma (fixedProcedure Gamma B.toList) := by
  constructor
  · intro g
    exact ⟨fixedAnswer Gamma B.toList g, B.toList,
      fixedProcedure_run Gamma B.toList g⟩
  · intro g result qs run
    obtain ⟨hresult, hqs⟩ :=
      (fixedProcedure_run Gamma B.toList g).deterministic _ _ run
    subst result
    exact fixedAnswer_correct Gamma B hB g

theorem worst_fixedProcedure_le (Gamma : Subgroup G) (B : Finset X) :
    worstQueries (G := G) (fixedProcedure Gamma B.toList) ≤ (B.card : ℕ∞) := by
  unfold worstQueries
  refine iSup_le fun g => iSup_le fun result => iSup_le fun qs => iSup_le fun run => ?_
  obtain ⟨_, hqs⟩ :=
    (fixedProcedure_run Gamma B.toList g).deterministic _ _ run
  subst qs
  simp

theorem optimalQueries_le_minObservations (Gamma : Subgroup G) :
    optimalQueries (X := X) Gamma ≤ minObservations (X := X) Gamma := by
  by_cases htop : minObservations (X := X) Gamma = ⊤
  · simp [htop]
  · obtain ⟨B, hB, hcard⟩ := minObservations_attained (X := X) Gamma htop
    have hc := fixedProcedure_correct Gamma B hB
    calc
      optimalQueries (X := X) Gamma ≤
          worstQueries (G := G) (fixedProcedure Gamma B.toList) := by
        let candidate : {next : QueryProcedure X // CorrectQueryProcedure Gamma next} :=
          ⟨fixedProcedure Gamma B.toList, hc⟩
        have h := iInf_le
          (fun next : {next : QueryProcedure X // CorrectQueryProcedure Gamma next} =>
            worstQueries (G := G) next.1) candidate
        exact h
      _ ≤ (B.card : ℕ∞) := worst_fixedProcedure_le Gamma B
      _ = minObservations (X := X) Gamma := hcard

/-- The fixed observation number equals the optimal adaptive worst case,
including the infinite case. -/
theorem optimalQueries_eq_minObservations (Gamma : Subgroup G) :
    optimalQueries (X := X) Gamma = minObservations (X := X) Gamma := by
  exact le_antisymm (optimalQueries_le_minObservations Gamma)
    (minObservations_le_optimalQueries Gamma)

/-- When the optimum is finite, a minimum fixed observation set and its
procedure attain the optimal worst case. -/
theorem exists_optimal_fixed_procedure (Gamma : Subgroup G)
    (hfinite : minObservations (X := X) Gamma ≠ ⊤) :
    ∃ B : Finset X, Sufficient Gamma B ∧
      (B.card : ℕ∞) = minObservations (X := X) Gamma ∧
      CorrectQueryProcedure Gamma (fixedProcedure Gamma B.toList) ∧
      worstQueries (G := G) (fixedProcedure Gamma B.toList) =
        minObservations (X := X) Gamma := by
  obtain ⟨B, hB, hcard⟩ := minObservations_attained (X := X) Gamma hfinite
  refine ⟨B, hB, hcard, fixedProcedure_correct Gamma B hB, ?_⟩
  exact le_antisymm
    ((worst_fixedProcedure_le Gamma B).trans_eq hcard)
    (minObservations_le_worst Gamma _ (fixedProcedure_correct Gamma B hB))

end FixedProcedure

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
