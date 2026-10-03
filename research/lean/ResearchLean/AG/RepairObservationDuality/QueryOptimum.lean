import ResearchLean.AG.RepairObservationDuality.PrimitiveQueries

/-!
# G-131 C: exact adaptive decision and full numerical costs

## Implementation notes

The lower bound replays the successful base input's actual run after adding
an unobserved direction in the known-information kernel. The numerical proof
uses the identical returned full correction on both inputs. Fixed plans give
the upper bound via the independent fiber sufficiency theorems. Minima range
over primitive indices, and repeated adaptive indices remain counted in runs.
This module proves the free-computation query model; finite symbolic planning
and restoration of the actual operations are subsequent obligations.
-/

namespace AAT.AG.RepairObservationDuality
open PrimitiveQueries

section Linear
variable {k V H W I J : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup H] [Module k H]
variable [AddCommGroup W] [Module k W] [AddCommGroup I] [Module k I]
variable (lam : J → V →ₗ[k] k)

/-- B and C's same primitive observation table on a finite set of indices. -/
def observation (points : Finset J) : V →ₗ[k] (points → k) :=
  LinearMap.pi fun j => lam j.1

/-- The table's evaluation is exactly the indicated original primitive value. -/
theorem observation_apply (points : Finset J) (v : V) (j : points) :
    observation lam points v j = lam j.1 v := rfl

/-- The observation kernel consists precisely of inputs killed by every asked primitive. -/
theorem mem_ker_observation (points : Finset J) (n : V) :
    n ∈ LinearMap.ker (observation lam points) ↔ ∀ j ∈ points, lam j n = 0 := by
  constructor
  · intro hn j hj
    exact congrFun hn ⟨j, hj⟩
  · intro hn
    exact funext fun j => hn j.1 j.2

/-- Equality of the tables retains exactly equality on their original indices. -/
theorem observation_eq_iff (points : Finset J) (v w : V) :
    observation lam points v = observation lam points w ↔
      ∀ j ∈ points, lam j v = lam j w := by
  constructor
  · intro he j hj
    exact congrFun he ⟨j, hj⟩
  · intro he
    exact funext fun j => he j.1 j.2

/-- C's independently defined sufficient-set condition for a target kernel. -/
def SufficientSet (L : V →ₗ[k] I) (R : Submodule k V) (points : Finset J) : Prop :=
  LinearMap.ker L ⊓ LinearMap.ker (observation lam points) ≤ R

/-- C's sufficient-set API reads exactly the known and observed kernel intersection. -/
theorem sufficientSet_iff (L : V →ₗ[k] I) (R : Submodule k V) (points : Finset J) :
    SufficientSet lam L R points ↔
      LinearMap.ker L ⊓ LinearMap.ker (observation lam points) ≤ R := Iff.rfl

/-- B's full-input sufficient-set API removes the zero known-information map. -/
theorem sufficientSet_zero_iff (R : Submodule k V) (points : Finset J) :
    SufficientSet lam (0 : V →ₗ[k] k) R points ↔
      LinearMap.ker (observation lam points) ≤ R := by
  simp only [SufficientSet, LinearMap.ker_zero, top_inf_eq]

/-- C's minimum sufficient primitive cardinal, with infinity for an empty set of plans. -/
noncomputable def minimum (L : V →ₗ[k] I) (R : Submodule k V) : ℕ∞ :=
  ⨅ p : {p : Finset J // SufficientSet lam L R p}, (p.1.card : ℕ∞)

/-- A common lower bound for all sufficient primitive sets bounds the minimum. -/
theorem le_minimum (L : V →ₗ[k] I) (R : Submodule k V) (n : ℕ∞)
    (hn : ∀ points, SufficientSet lam L R points → n ≤ (points.card : ℕ∞)) :
    n ≤ minimum lam L R := by
  change n ≤ ⨅ p : {p : Finset J // SufficientSet lam L R p}, (p.1.card : ℕ∞)
  exact le_iInf fun p => hn p.1 p.2

/-- Every sufficient primitive set bounds the exact minimum from above. -/
theorem minimum_le_card (L : V →ₗ[k] I) (R : Submodule k V) (points : Finset J)
    (hp : SufficientSet lam L R points) : minimum lam L R ≤ (points.card : ℕ∞) := by
  change (⨅ p : {p : Finset J // SufficientSet lam L R p}, (p.1.card : ℕ∞)) ≤ _
  exact iInf_le (fun p : {p : Finset J // SufficientSet lam L R p} =>
    (p.1.card : ℕ∞)) ⟨points, hp⟩

/-- No sufficient primitive set gives precisely the infinite minimum. -/
theorem minimum_eq_top_iff (L : V →ₗ[k] I) (R : Submodule k V) :
    minimum lam L R = ⊤ ↔ ¬ ∃ points, SufficientSet lam L R points := by
  constructor
  · intro ht ⟨points, hp⟩
    have hle := minimum_le_card lam L R points hp
    rw [ht] at hle
    exact ENat.coe_ne_top points.card (top_le_iff.mp hle)
  · intro hn
    apply le_antisymm le_top
    change ⊤ ≤ ⨅ p : {p : Finset J // SufficientSet lam L R p}, (p.1.card : ℕ∞)
    exact le_iInf fun p => (hn ⟨p.1, p.2⟩).elim

/-- A finite sufficient minimum is attained by an actual finite primitive set. -/
theorem minimum_attained (L : V →ₗ[k] I) (R : Submodule k V)
    (hfinite : minimum lam L R ≠ ⊤) :
    ∃ points, SufficientSet lam L R points ∧ (points.card : ℕ∞) = minimum lam L R := by
  have hex : ∃ points, SufficientSet lam L R points := by
    by_contra hn
    exact hfinite ((minimum_eq_top_iff lam L R).mpr hn)
  letI : Nonempty {p : Finset J // SufficientSet lam L R p} :=
    ⟨⟨Classical.choose hex, Classical.choose_spec hex⟩⟩
  obtain ⟨p, hp⟩ := ENat.exists_eq_iInf
    (fun p : {p : Finset J // SufficientSet lam L R p} => (p.1.card : ℕ∞))
  exact ⟨p.1, p.2, hp⟩

variable [DecidableEq J]
variable (D : H →ₗ[k] W) (B : V →ₗ[k] W) (b₀ : W) (L : V →ₗ[k] I) (s : I)

/-- C's Boolean output reports exactly solvability of the same full correction equation. -/
def ValidDecision (v : V) (a : Bool) : Prop :=
  a = true ↔ Solvable D (affineRhs B b₀) v

omit [DecidableEq J] in
/-- C's Boolean validator API keeps the same independently defined full equation for every Boolean. -/
theorem valid_decision_iff (v : V) (a : Bool) :
    ValidDecision D B b₀ v a ↔ (a = true ↔ Solvable D (affineRhs B b₀) v) := Iff.rfl

omit [DecidableEq J] in
/-- The basic Boolean API identifies a decided proposition with the independent
correction equation, without unfolding the validator in downstream proofs. -/
theorem valid_decision_decide_iff (v : V) (p : Prop) [Decidable p] :
    ValidDecision D B b₀ v (decide p) ↔
      (p ↔ Solvable D (affineRhs B b₀) v) := by
  change (decide p = true ↔ Solvable D (affineRhs B b₀) v) ↔ _
  simp only [decide_eq_true_eq]

/-- A success-run's distinct primitive indices must satisfy the decision kernel bound. -/
theorem decision_run_sufficient (next : Procedure J k Bool)
    (hn : Correct (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) next)
    {w : V} (hw : w ∈ informationFiber L s) (hs : Solvable D (affineRhs B b₀) w)
    {a qs} (run : Run (fun v j => lam j v) next w [] a qs) :
    SufficientSet lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) qs.toFinset := by
  classical
  intro n hnker
  have hobs := (mem_ker_observation lam qs.toFinset n).mp hnker.2
  have hf := add_mem_fiber L s hw hnker.1
  have replay := run.replay (w + n) (fun j hj => by
    rw [map_add, hobs j (List.mem_toFinset.mpr hj), add_zero])
  have htrue := (hn.2 w hw a qs run).mpr hs
  have hsuccess := (hn.2 (w + n) hf a qs replay).mp htrue
  exact (solvable_add_iff D B b₀ hs n).mp hsuccess

/-- A numerical success-run must kill B on its unobserved known-information directions. -/
theorem numerical_run_sufficient (next : Procedure J k (Option H))
    (hn : Correct (fun v j => lam j v) (informationFiber L s)
      (ValidOutput D (affineRhs B b₀)) next)
    {w : V} (hw : w ∈ informationFiber L s) (hs : Solvable D (affineRhs B b₀) w)
    {a qs} (run : Run (fun v j => lam j v) next w [] a qs) :
    SufficientSet lam L (LinearMap.ker B) qs.toFinset := by
  classical
  intro n hnker
  have hobs := (mem_ker_observation lam qs.toFinset n).mp hnker.2
  have hf := add_mem_fiber L s hw hnker.1
  have replay := run.replay (w + n) (fun j hj => by
    rw [map_add, hobs j (List.mem_toFinset.mpr hj), add_zero])
  have hwout := hn.2 w hw a qs run
  have hnout := hn.2 (w + n) hf a qs replay
  cases a with
  | none => exact (hwout hs).elim
  | some h =>
      have he := hwout.symm.trans hnout
      have hb := (affineRhs_eq_iff B b₀ w (w + n)).mp he
      change B n = 0
      rw [map_add] at hb
      exact add_left_cancel (hb.symm.trans (add_zero (B w)).symm)

/-- One successful run provides the common lower bound, counting repeats as well. -/
theorem minimum_le_run {A : Type*} (R : Submodule k V) (next : Procedure J k A)
    {w : V} (hw : w ∈ informationFiber L s) {a qs}
    (run : Run (fun v j => lam j v) next w [] a qs)
    (hp : SufficientSet lam L R qs.toFinset) :
    minimum lam L R ≤ worst (fun v j => lam j v) (informationFiber L s) next := by
  exact (minimum_le_card lam L R qs.toFinset hp).trans
    ((ENat.coe_le_coe.mpr (List.toFinset_card_le qs)).trans
      (run_le_worst _ _ _ hw run))

omit [DecidableEq J] in
/-- Fixed decision plans attain every sufficient-set cardinal without reading the input. -/
theorem decision_fixed_correct (points : Finset J)
    {w : V} (hw : w ∈ informationFiber L s) (hs : Solvable D (affineRhs B b₀) w)
    (hp : SufficientSet lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) points) :
    Correct (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀)
      (fixed (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀)
        points.toList) := by
  classical
  obtain ⟨p, hp⟩ := (decision_sufficient_linear_iff D B b₀ L s
    (observation lam points) hw hs).mpr hp
  apply fixed_correct
  intro v hv
  refine ⟨decide (p (observation lam points v)), ?_⟩
  intro z hz he
  have ho : observation lam points z = observation lam points v :=
    (observation_eq_iff lam points z v).mpr (fun j hj => he j (Finset.mem_toList.mpr hj))
  rw [valid_decision_decide_iff]
  rw [← ho]
  exact hp z hz

omit [DecidableEq J] in
/-- Fixed numerical plans terminate with a common full correction, rather than a lazy expression. -/
theorem numerical_fixed_correct (points : Finset J)
    {w : V} (hw : w ∈ informationFiber L s) (hs : Solvable D (affineRhs B b₀) w)
    (hp : SufficientSet lam L (LinearMap.ker B) points) :
    Correct (fun v j => lam j v) (informationFiber L s)
      (ValidOutput D (affineRhs B b₀))
      (fixed (fun v j => lam j v) (informationFiber L s)
        (ValidOutput D (affineRhs B b₀)) points.toList) := by
  classical
  obtain ⟨out, hout⟩ := (numerical_sufficient_linear_iff D B b₀ L s
    (observation lam points) hw hs).mpr hp
  apply fixed_correct
  intro v hv
  refine ⟨out (observation lam points v), ?_⟩
  intro z hz he
  have ho : observation lam points z = observation lam points v :=
    (observation_eq_iff lam points z v).mpr (fun j hj => he j (Finset.mem_toList.mpr hj))
  rw [← ho]
  exact hout z hz

/-- C's exact decision optimum equals the minimum primitive sufficient-set cardinal. -/
theorem decision_optimum {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w) :
    optimum (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) =
      minimum lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) := by
  classical
  apply le_antisymm
  · change _ ≤ ⨅ p : {p : Finset J //
      SufficientSet lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) p},
      (p.1.card : ℕ∞)
    refine le_iInf fun p => ?_
    have hc := decision_fixed_correct lam D B b₀ L s p.1 hw hs p.2
    have hcost := worst_fixed_le (fun (v : V) (j : J) => lam j v)
      (informationFiber L s) (ValidDecision D B b₀) p.1.toList
    exact (optimum_le_worst _ _ _ _ hc).trans (by simpa using hcost)
  · change _ ≤ ⨅ p : {p : Procedure J k Bool //
      Correct (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) p},
      worst (fun v j => lam j v) (informationFiber L s) p.1
    refine le_iInf fun p => ?_
    obtain ⟨a, qs, run⟩ := p.2.1 w hw
    exact minimum_le_run lam L s _ p.1 hw run
      (decision_run_sufficient lam D B b₀ L s p.1 p.2 hw hs run)

/-- C's numerical optimum uses ker B even when every input is repairable. -/
theorem numerical_optimum {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w) :
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidOutput D (affineRhs B b₀)) = minimum lam L (LinearMap.ker B) := by
  classical
  apply le_antisymm
  · change _ ≤ ⨅ p : {p : Finset J // SufficientSet lam L (LinearMap.ker B) p},
      (p.1.card : ℕ∞)
    refine le_iInf fun p => ?_
    have hc := numerical_fixed_correct lam D B b₀ L s p.1 hw hs p.2
    have hcost := worst_fixed_le (fun (v : V) (j : J) => lam j v)
      (informationFiber L s) (ValidOutput D (affineRhs B b₀)) p.1.toList
    exact (optimum_le_worst _ _ _ _ hc).trans (by simpa using hcost)
  · change _ ≤ ⨅ p : {p : Procedure J k (Option H) //
      Correct (fun v j => lam j v) (informationFiber L s)
        (ValidOutput D (affineRhs B b₀)) p},
      worst (fun v j => lam j v) (informationFiber L s) p.1
    refine le_iInf fun p => ?_
    obtain ⟨a, qs, run⟩ := p.2.1 w hw
    exact minimum_le_run lam L s _ p.1 hw run
      (numerical_run_sufficient lam D B b₀ L s p.1 p.2 hw hs run)

omit [DecidableEq J] in
/-- An entirely impossible fiber requires no primitive queries for either output kind. -/
theorem all_impossible_optima_zero
    (hi : ∀ v ∈ informationFiber L s, ¬ Solvable D (affineRhs B b₀) v) :
    optimum (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) = 0 ∧
    optimum (fun v j => lam j v) (informationFiber L s)
      (ValidOutput D (affineRhs B b₀)) = 0 := by
  constructor
  · apply optimum_zero_of_constant _ _ _ false
    intro v hv
    exact iff_of_false Bool.false_ne_true (hi v hv)
  · exact optimum_zero_of_constant _ _ _ none hi

/-- With a success input, absence of a decision sufficient set excludes every
total correct adaptive decision procedure, rather than merely assigning infinity. -/
theorem no_decision_procedure {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w)
    (hno : ¬ ∃ points,
      SufficientSet lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) points) :
    ¬ ∃ next : Procedure J k Bool,
      Correct (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) next := by
  rintro ⟨next, hn⟩
  obtain ⟨a, qs, run⟩ := hn.1 w hw
  exact hno ⟨qs.toFinset, decision_run_sufficient lam D B b₀ L s next hn hw hs run⟩

/-- The numerical impossibility statement uses the same full correction output
and the stronger ker B criterion. -/
theorem no_numerical_procedure {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w)
    (hno : ¬ ∃ points, SufficientSet lam L (LinearMap.ker B) points) :
    ¬ ∃ next : Procedure J k (Option H),
      Correct (fun v j => lam j v) (informationFiber L s)
        (ValidOutput D (affineRhs B b₀)) next := by
  rintro ⟨next, hn⟩
  obtain ⟨a, qs, run⟩ := hn.1 w hw
  exact hno ⟨qs.toFinset, numerical_run_sufficient lam D B b₀ L s next hn hw hs run⟩

omit [DecidableEq J] in
/-- Every finite decision optimum is attained by a minimum fixed primitive plan. -/
theorem decision_optimum_attained {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w)
    (hf : minimum lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) ≠ ⊤) :
    ∃ points : Finset J,
      SufficientSet lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) points ∧
      (points.card : ℕ∞) = minimum lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) ∧
      Correct (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀)
        (fixed (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) points.toList) ∧
      worst (fun v j => lam j v) (informationFiber L s)
        (fixed (fun v j => lam j v) (informationFiber L s) (ValidDecision D B b₀) points.toList) =
        minimum lam L (LinearMap.ker ((LinearMap.range D).mkQ.comp B)) := by
  classical
  obtain ⟨points, hp, hcard⟩ := minimum_attained lam L _ hf
  have hc := decision_fixed_correct lam D B b₀ L s points hw hs hp
  refine ⟨points, hp, hcard, hc, le_antisymm ?_ ?_⟩
  · have hcost := worst_fixed_le (fun v j => lam j v) (informationFiber L s)
      (ValidDecision D B b₀) points.toList
    rw [← hcard]
    simpa using hcost
  · rw [← decision_optimum lam D B b₀ L s hw hs]
    exact optimum_le_worst _ _ _ _ hc

omit [DecidableEq J] in
/-- Every finite numerical optimum is attained with all correction components fixed. -/
theorem numerical_optimum_attained {w : V} (hw : w ∈ informationFiber L s)
    (hs : Solvable D (affineRhs B b₀) w) (hf : minimum lam L (LinearMap.ker B) ≠ ⊤) :
    ∃ points : Finset J,
      SufficientSet lam L (LinearMap.ker B) points ∧
      (points.card : ℕ∞) = minimum lam L (LinearMap.ker B) ∧
      Correct (fun v j => lam j v) (informationFiber L s)
        (ValidOutput D (affineRhs B b₀))
        (fixed (fun v j => lam j v) (informationFiber L s)
          (ValidOutput D (affineRhs B b₀)) points.toList) ∧
      worst (fun v j => lam j v) (informationFiber L s)
        (fixed (fun v j => lam j v) (informationFiber L s)
          (ValidOutput D (affineRhs B b₀)) points.toList) = minimum lam L (LinearMap.ker B) := by
  classical
  obtain ⟨points, hp, hcard⟩ := minimum_attained lam L _ hf
  have hc := numerical_fixed_correct lam D B b₀ L s points hw hs hp
  refine ⟨points, hp, hcard, hc, le_antisymm ?_ ?_⟩
  · have hcost := worst_fixed_le (fun v j => lam j v) (informationFiber L s)
      (ValidOutput D (affineRhs B b₀)) points.toList
    rw [← hcard]
    simpa using hcost
  · rw [← numerical_optimum lam D B b₀ L s hw hs]
    exact optimum_le_worst _ _ _ _ hc

end Linear

section Nonvacuity
variable (k : Type*) [Field k]

/-- A single identity primitive is sufficient for zero residual input, while
the empty plan fails on the same nonzero field and unconstrained input space. -/
theorem sufficient_set_examples :
    SufficientSet (fun _ : Unit => LinearMap.id (R := k) (M := k))
      (0 : k →ₗ[k] k) (⊥ : Submodule k k) {()} ∧
    ¬ SufficientSet (fun _ : Unit => LinearMap.id (R := k) (M := k))
      (0 : k →ₗ[k] k) (⊥ : Submodule k k) ∅ := by
  constructor
  · intro n hn
    exact (mem_ker_observation _ {()} n).mp hn.2 () (by simp)
  · intro hp
    have hn : (1 : k) ∈ LinearMap.ker (observation
        (fun _ : Unit => LinearMap.id (R := k) (M := k)) ∅) :=
      (mem_ker_observation _ ∅ 1).mpr (by simp)
    exact one_ne_zero (hp ⟨by simp, hn⟩)

/-- The decision validator accepts and rejects each Boolean on concrete success
and failure inputs of the same independently fixed correction equation. -/
theorem valid_decision_examples :
    ValidDecision (0 : k →ₗ[k] k) LinearMap.id 0 0 true ∧
    ¬ ValidDecision (0 : k →ₗ[k] k) LinearMap.id 0 0 false ∧
    ValidDecision (0 : k →ₗ[k] k) LinearMap.id 0 1 false ∧
    ¬ ValidDecision (0 : k →ₗ[k] k) LinearMap.id 0 1 true := by
  have hzero : Solvable (0 : k →ₗ[k] k) (affineRhs (LinearMap.id (R := k) (M := k)) 0) 0 := ⟨0, by simp [affineRhs]⟩
  have hone : ¬ Solvable (0 : k →ₗ[k] k) (affineRhs (LinearMap.id (R := k) (M := k)) 0) 1 := by
    rintro ⟨h, he⟩
    simp only [affineRhs, LinearMap.zero_apply, LinearMap.id_apply, zero_add] at he
    exact (zero_ne_one : (0 : k) ≠ 1) he
  exact ⟨iff_of_true rfl hzero, fun h => Bool.false_ne_true (h.mpr hzero),
    iff_of_false Bool.false_ne_true hone, fun h => hone (h.mp rfl)⟩

end Nonvacuity
end AAT.AG.RepairObservationDuality
#assert_standard_axioms_only AAT.AG.RepairObservationDuality
