import ResearchLean.AG.MinimalCompatibilityObservations.AdaptiveLowerBound
import ResearchLean.AG.MinimalCompatibilityObservations.FiniteExtension
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

section FiniteMaximum

/-- The unique questions on the selected terminating run. -/
noncomputable def chosenQueries (Gamma : Subgroup G) (next : QueryProcedure X)
    (correct : CorrectQueryProcedure Gamma next) (g : G) : List X :=
  Classical.choose (Classical.choose_spec (correct.1 g))

private theorem chosenQueries_run (Gamma : Subgroup G) (next : QueryProcedure X)
    (correct : CorrectQueryProcedure Gamma next) (g : G) :
    ∃ result : Bool, QueryRun next g [] result (chosenQueries Gamma next correct g) := by
  let result := Classical.choose (correct.1 g)
  exact ⟨result, Classical.choose_spec (Classical.choose_spec (correct.1 g))⟩

/-- On finite `G`, the supremum defining worstQueries is the actual maximum
of run lengths and is attained by an unknown change. -/
theorem worstQueries_attained [Finite G] (Gamma : Subgroup G)
    (next : QueryProcedure X) (correct : CorrectQueryProcedure Gamma next) :
    ∃ g : G, ∃ result : Bool, ∃ qs : List X,
      QueryRun next g [] result qs ∧ worstQueries (G := G) next = (qs.length : ℕ∞) := by
  letI : Nonempty G := ⟨1⟩
  obtain ⟨gmax, hmax⟩ := Finite.exists_max
    (fun g : G => (chosenQueries Gamma next correct g).length)
  obtain ⟨result, run⟩ := chosenQueries_run Gamma next correct gmax
  refine ⟨gmax, result, chosenQueries Gamma next correct gmax, run, ?_⟩
  apply le_antisymm
  · unfold worstQueries
    refine iSup_le fun g => iSup_le fun result' => iSup_le fun qs => iSup_le fun run' => ?_
    obtain ⟨_, hqs⟩ :=
      (Classical.choose_spec (chosenQueries_run Gamma next correct g)).deterministic
        next g run'
    subst qs
    exact_mod_cast hmax g
  · exact run_count_le_worst next gmax result _ run

end FiniteMaximum

section FixedProcedure

open AAT.AG.ProtocolHolonomy

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

/-- Finite-table search for a compatible change matching a query history. -/
def findHistoryCompatible (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (hist : QueryHistory X) : Option G :=
  scan (fun h => decide (h ∈ Gamma ∧
    ∀ pair ∈ hist, h • pair.1 = pair.2)) EG.values

theorem findHistoryCompatible_isSome_iff (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (hist : QueryHistory X) :
    (findHistoryCompatible Gamma EG hist).isSome = true ↔
      ∃ h : G, h ∈ Gamma ∧ ∀ pair ∈ hist, h • pair.1 = pair.2 := by
  cases hscan : findHistoryCompatible Gamma EG hist with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      intro ⟨h, hh⟩
      have hf := (scan_none_iff _ EG.values).mp hscan h (EG.complete h)
      have ht : decide (h ∈ Gamma ∧
          ∀ pair ∈ hist, h • pair.1 = pair.2) = true := by
        exact decide_eq_true hh
      exact Bool.false_ne_true (hf.symm.trans ht)
  | some h =>
      simp only [Option.isSome_some, true_iff]
      have hp := (scan_some _ EG.values h hscan).1
      exact ⟨h, of_decide_eq_true hp⟩

/-- The finite table supplies the terminal Boolean by a terminating scan. -/
def finiteFixedProcedure (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (points : List X) : QueryProcedure X :=
  fun hist =>
    match points.drop hist.length with
    | [] => Sum.inl ((findHistoryCompatible Gamma EG hist).isSome)
    | x :: _ => Sum.inr x

theorem finiteFixedProcedure_eq_fixed (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G) (points : List X) :
    finiteFixedProcedure Gamma EG points = fixedProcedure Gamma points := by
  funext hist
  classical
  cases hdrop : points.drop hist.length with
  | nil =>
      have hiff := findHistoryCompatible_isSome_iff Gamma EG hist
      have hbool : (findHistoryCompatible Gamma EG hist).isSome =
          decide (∃ h : G, h ∈ Gamma ∧
            ∀ pair ∈ hist, h • pair.1 = pair.2) := by
        cases hb : (findHistoryCompatible Gamma EG hist).isSome <;>
          simp_all [decide_eq_true_eq]
      simp [finiteFixedProcedure, fixedProcedure, hdrop, hbool]
  | cons x xs =>
      simp [finiteFixedProcedure, fixedProcedure, hdrop]

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

theorem fixedAnswer_correct_of_list (Gamma : Subgroup G) (B : Finset X)
    (hB : Sufficient Gamma B) (points : List X) (hpoints : points.toFinset = B)
    (g : G) : fixedAnswer Gamma points g = true ↔ g ∈ Gamma := by
  classical
  simp only [fixedAnswer, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hgamma, heq⟩
    have hfix : h⁻¹ * g ∈ pointStabilizer B := by
      intro x hx
      have hmem : x ∈ points := List.mem_toFinset.mp (hpoints.symm ▸ hx)
      have hpoint : h • x = g • x := heq x hmem
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

theorem finiteFixedProcedure_correct (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (B : Finset X) (hB : Sufficient Gamma B) :
    CorrectQueryProcedure Gamma (finiteFixedProcedure Gamma EG B.toList) := by
  rw [finiteFixedProcedure_eq_fixed]
  exact fixedProcedure_correct Gamma B hB

theorem finiteFixedProcedure_correct_of_list (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (B : Finset X) (hB : Sufficient Gamma B)
    (points : List X) (hpoints : points.toFinset = B) :
    CorrectQueryProcedure Gamma (finiteFixedProcedure Gamma EG points) := by
  rw [finiteFixedProcedure_eq_fixed]
  constructor
  · intro g
    exact ⟨fixedAnswer Gamma points g, points, fixedProcedure_run Gamma points g⟩
  · intro g result qs run
    obtain ⟨hresult, _⟩ :=
      (fixedProcedure_run Gamma points g).deterministic _ _ run
    subst result
    exact fixedAnswer_correct_of_list Gamma B hB points hpoints g

/-- An executable duplicate-free list of the supplied finite observation
set, using the input enumeration rather than `Finset.toList`. -/
def finitePoints (EX : ExplicitEnumeration X) (B : Finset X) : List X :=
  (EX.values.filter fun x => decide (x ∈ B)).dedup

theorem finitePoints_toFinset (EX : ExplicitEnumeration X) (B : Finset X) :
    (finitePoints EX B).toFinset = B := by
  ext x
  simp [finitePoints, List.mem_dedup, List.mem_filter, EX.complete]

theorem finitePoints_length (EX : ExplicitEnumeration X) (B : Finset X) :
    (finitePoints EX B).length = B.card := by
  have hnodup : (finitePoints EX B).Nodup := List.nodup_dedup _
  have hcard := List.toFinset_card_of_nodup hnodup
  rw [finitePoints_toFinset] at hcard
  exact hcard.symm

theorem finiteFixedProcedure_executable_optimal (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) (hfinite : minObservations (X := X) Gamma ≠ ⊤) :
    ∃ B : Finset X, Sufficient Gamma B ∧
      (B.card : ℕ∞) = minObservations (X := X) Gamma ∧
      CorrectQueryProcedure Gamma
        (finiteFixedProcedure Gamma EG (finitePoints EX B)) ∧
      worstQueries (G := G) (finiteFixedProcedure Gamma EG (finitePoints EX B)) =
        minObservations (X := X) Gamma := by
  obtain ⟨B, hB, hcard⟩ := minObservations_attained (X := X) Gamma hfinite
  let points := finitePoints EX B
  have hcorrect := finiteFixedProcedure_correct_of_list Gamma EG B hB points
    (finitePoints_toFinset EX B)
  refine ⟨B, hB, hcard, hcorrect, ?_⟩
  apply le_antisymm
  · rw [finiteFixedProcedure_eq_fixed]
    have hupper : worstQueries (G := G) (fixedProcedure Gamma points) ≤
        (points.length : ℕ∞) := by
      unfold worstQueries
      refine iSup_le fun g => iSup_le fun result => iSup_le fun qs => iSup_le fun run => ?_
      obtain ⟨_, hqs⟩ := (fixedProcedure_run Gamma points g).deterministic _ _ run
      subst qs
      rfl
    have hlen : (points.length : ℕ∞) = minObservations (X := X) Gamma := by
      simpa only [points, finitePoints_length] using hcard
    exact hupper.trans_eq hlen
  · exact (minObservations_le_worst Gamma _ hcorrect)

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
