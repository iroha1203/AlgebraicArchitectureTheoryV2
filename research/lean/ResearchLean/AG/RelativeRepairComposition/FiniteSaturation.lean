import Formal.Util.AssertStandardAxioms
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup
import Mathlib.Tactic

/-!
# Terminating finite saturation for elementary elimination operations

## Implementation notes

The states and generators are actual lists, so the algorithm never extracts an
ordered list from a quotient multiset. Every recursive step strictly increases
the visited finite set. Its complement cardinality proves termination. No
repair, right-hand side, or supported range is used in this computation.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteElimination
universe u
variable {A : Type u} [Fintype A] [DecidableEq A]
variable (step : A → A → A) (generators : List A)

/-- Apply each listed elementary generator to each visited state. -/
def expand (s : List A) : List A :=
  (s ++ s.flatMap (fun x => generators.map (fun g => step g x))).dedup

omit [Fintype A] in
/-- Expansion retains precisely old states and one-step successors. -/
theorem mem_expand (s : List A) (a : A) :
    a ∈ expand step generators s ↔ a ∈ s ∨ ∃ x ∈ s, ∃ g ∈ generators, step g x = a := by
  simp [expand]

omit [Fintype A] in
/-- Every previously visited state remains visited. -/
theorem subset_expand (s : List A) : s.toFinset ⊆ (expand step generators s).toFinset := by
  intro x hx
  exact List.mem_toFinset.mpr ((mem_expand step generators s x).mpr (Or.inl (List.mem_toFinset.mp hx)))

/-- Compute finite closure using only lists and decidable equality. -/
def saturate {A : Type u} [Fintype A] [DecidableEq A]
    (step : A → A → A) (generators : List A) (s : List A) : List A :=
  if _h : (expand step generators s).toFinset ⊆ s.toFinset then s
  else saturate step generators (expand step generators s)
termination_by Fintype.card A - s.toFinset.card
decreasing_by
  have hs := subset_expand step generators s
  have hlt : s.toFinset.card < (expand step generators s).toFinset.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, fun he => _h (he ▸ Finset.Subset.refl _)⟩)
  have hbound : (expand step generators s).toFinset.card ≤ Fintype.card A := Finset.card_le_univ _
  omega

/-- Saturation retains every initial state. -/
theorem subset_saturate (s : List A) : s.toFinset ⊆ (saturate step generators s).toFinset := by
  fun_induction saturate step generators s with
  | case1 s _ => exact Finset.Subset.refl _
  | case2 s _ ih => exact (subset_expand step generators s).trans ih

/-- The returned list is closed under every elementary step. -/
theorem saturate_closed (s : List A) :
    (expand step generators (saturate step generators s)).toFinset ⊆
      (saturate step generators s).toFinset := by
  fun_induction saturate step generators s with
  | case1 s h => exact h
  | case2 s _ ih => exact ih

/-- Initial invariants preserved by elementary steps hold on every output state. -/
theorem saturate_invariant (P : A → Prop)
    (hg : ∀ g ∈ generators, ∀ x, P x → P (step g x)) (s : List A) :
    (∀ x ∈ s, P x) → ∀ x ∈ saturate step generators s, P x := by
  fun_induction saturate step generators s with
  | case1 s _ => exact fun hs => hs
  | case2 s _ ih =>
    intro hs
    apply ih
    intro x hx
    rcases (mem_expand step generators s x).mp hx with hx | ⟨y,hy,g,hg',rfl⟩
    · exact hs x hx
    · exact hg g hg' y (hs y hy)

/-- Every finite sequence of listed elementary steps occurs in the computed output. -/
theorem foldr_mem_saturate (s : List A) (a : A) (ha : a ∈ s)
    (L : List A) (hL : ∀ g ∈ L, g ∈ generators) :
    L.foldr step a ∈ saturate step generators s := by
  induction L with
  | nil => exact List.mem_toFinset.mp (subset_saturate step generators s (List.mem_toFinset.mpr ha))
  | cons g L ih =>
    apply List.mem_toFinset.mp
    apply saturate_closed step generators s
    apply List.mem_toFinset.mpr
    apply (mem_expand step generators _ _).mpr
    right
    exact ⟨L.foldr step a, ih (fun x hx => hL x (List.mem_cons_of_mem g hx)),g,hL g List.mem_cons_self,rfl⟩

end AAT.AG.RelativeRepairComposition.FiniteElimination

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
