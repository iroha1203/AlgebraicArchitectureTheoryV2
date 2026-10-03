import ResearchLean.AG.RepairObservationDuality.QueryOptimum
import ResearchLean.AG.RelativeRepairComposition.FiniteFunctionEnumeration
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Dedup

/-!
# G-131 D: finite minimum plans before observing input values

## Implementation notes

All lists are generated from complete input enumerations. The kernel test
checks unknown directions, independently of s and all actual replies. List
argmin selects a minimum cardinal among all sufficient original sets. The
question list is generated from the original ordered index list; no quotient
to list conversion or selected sufficient answer is supplied.
-/
namespace AAT.AG.RepairObservationDuality.FiniteMinimumPlan
open RelativeRepairComposition
variable {k V I W J : Type*} [Field k] [DecidableEq k]
variable [AddCommGroup V] [Module k V] [AddCommGroup I] [Module k I]
variable [AddCommGroup W] [Module k W] [DecidableEq I] [DecidableEq W] [DecidableEq J]
variable (enumJ : FiniteElimination.Enumeration J)

/-- D's actual fixed question order is generated from the original complete index list. -/
def questions (points : Finset J) : List J := enumJ.values.dedup.filter (· ∈ points)

/-- The generated list contains exactly the selected original primitive indices. -/
theorem mem_questions (points : Finset J) (j : J) :
    j ∈ questions enumJ points ↔ j ∈ points := by
  simp only [questions, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
  exact and_iff_right (enumJ.complete j)

/-- Generated question lists do not repeat an index. -/
theorem questions_nodup (points : Finset J) : (questions enumJ points).Nodup :=
  (List.nodup_dedup _).filter _

/-- The same original selected set is recovered from the generated question list. -/
theorem questions_toFinset (points : Finset J) : (questions enumJ points).toFinset = points := by
  ext j
  rw [List.mem_toFinset, mem_questions]

/-- The generated list has exactly the selected primitive cardinal. -/
theorem questions_length (points : Finset J) : (questions enumJ points).length = points.card := by
  calc
    _ = (questions enumJ points).toFinset.card :=
      (List.toFinset_card_of_nodup (questions_nodup enumJ points)).symm
    _ = points.card := congrArg Finset.card (questions_toFinset enumJ points)

/-- D enumerates every original primitive subset from the original finite list. -/
def sets : List (Finset J) := enumJ.values.dedup.sublists.map List.toFinset

/-- Every selected primitive set occurs in the finite planning list. -/
theorem mem_sets (points : Finset J) : points ∈ sets enumJ := by
  apply List.mem_map.mpr
  refine ⟨questions enumJ points,?_,questions_toFinset enumJ points⟩
  apply List.mem_sublists.mpr
  exact List.filter_sublist

variable (enumV : FiniteElimination.Enumeration V) (lam : J → V →ₗ[k] k)
variable (L : V →ₗ[k] I) (Q : V →ₗ[k] W)

/-- D's finite symbolic test checks the full unobserved known-kernel condition. -/
def test (points : Finset J) : Bool := enumV.values.all fun n =>
  decide (L n = 0 → (∀ j ∈ questions enumJ points, lam j n = 0) → Q n = 0)

/-- The finite test is exactly C's independently defined sufficient-set condition. -/
theorem test_iff (points : Finset J) :
    test enumJ enumV lam L Q points = true ↔ SufficientSet lam L (LinearMap.ker Q) points := by
  rw [sufficientSet_iff]
  simp only [test, List.all_eq_true, decide_eq_true_eq, mem_questions]
  constructor
  · intro ht n hn
    exact ht n (enumV.complete n) hn.1 ((mem_ker_observation lam points n).mp hn.2)
  · intro hk n _ hl ho
    exact hk ⟨hl,(mem_ker_observation lam points n).mpr ho⟩

/-- D's complete finite list of plans is filtered by a symbolic kernel test alone. -/
def sufficientSets : List (Finset J) := (sets enumJ).filter (test enumJ enumV lam L Q)

/-- Membership in the filtered list is exactly sufficiency, without a selected certificate. -/
theorem mem_sufficientSets (points : Finset J) :
    points ∈ sufficientSets enumJ enumV lam L Q ↔ SufficientSet lam L (LinearMap.ker Q) points := by
  simp only [sufficientSets, List.mem_filter, test_iff]
  exact and_iff_right (mem_sets enumJ points)

/-- D chooses its minimum plan by a terminating fold over the finite symbolic list. -/
def plan : Option (Finset J) := (sufficientSets enumJ enumV lam L Q).argmin Finset.card

/-- Every returned finite plan is sufficient and has no greater cost than any sufficient set. -/
theorem plan_spec {points : Finset J} (hp : plan enumJ enumV lam L Q = some points) :
    SufficientSet lam L (LinearMap.ker Q) points ∧
      ∀ q, SufficientSet lam L (LinearMap.ker Q) q → points.card ≤ q.card := by
  have hm : points ∈ (sufficientSets enumJ enumV lam L Q).argmin Finset.card := hp
  constructor
  · exact (mem_sufficientSets enumJ enumV lam L Q points).mp (List.argmin_mem hm)
  · intro q hq
    exact List.le_of_mem_argmin ((mem_sufficientSets enumJ enumV lam L Q q).mpr hq) hm

/-- Failure of the finite plan search is precisely nonexistence of any sufficient original set. -/
theorem plan_none_iff : plan enumJ enumV lam L Q = none ↔
    ¬ ∃ points, SufficientSet lam L (LinearMap.ker Q) points := by
  rw [plan, List.argmin_eq_none]
  constructor
  · intro he ⟨points,hp⟩
    have hm := (mem_sufficientSets enumJ enumV lam L Q points).mpr hp
    rw [he] at hm
    exact List.not_mem_nil hm
  · intro hn
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro points hp
    exact hn ⟨points,(mem_sufficientSets enumJ enumV lam L Q points).mp hp⟩

/-- Every successful finite search realizes C's exact minimum cardinal. -/
theorem plan_card {points : Finset J} (hp : plan enumJ enumV lam L Q = some points) :
    (points.card : ℕ∞) = minimum lam L (LinearMap.ker Q) := by
  obtain ⟨hs,hm⟩ := plan_spec enumJ enumV lam L Q hp
  apply le_antisymm
  · change (points.card : ℕ∞) ≤ ⨅ q : {q : Finset J // SufficientSet lam L (LinearMap.ker Q) q},
      (q.1.card : ℕ∞)
    exact le_iInf fun q => ENat.coe_le_coe.mpr (hm q.1 q.2)
  · exact minimum_le_card lam L (LinearMap.ker Q) points hs

end AAT.AG.RepairObservationDuality.FiniteMinimumPlan
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteMinimumPlan
