import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseCompositionFinite
import Formal.Util.AssertStandardAxioms

/-!
# Primitive inverse-fiber composition against backward index maps

Implementation notes: the second backward index graph chooses the middle
index. The first backward flag then selects the source row. Fiber values
still compose in source-to-target order, with the backward value directions
reversed by the ordinary inverse-graph composition API. This is the indexing
used by raw coordinate and relation transport.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph

noncomputable section

universe u v w x y z

variable {I : Type u} {J : Type v} {K : Type w}
variable (p : I → J → Bool) (S : I → Type x) (M : J → Type y) (T : K → Type z)
variable (h : Table.{u, v, x, y} I J) (hh : IsLawful p S M h)
variable (q : J → K → Bool) (hq : ∀ l, ∃! j, q j l = true)
variable (k : Table.{v, w, y, z} J K) (hk : IsLawful q M T k)

/-- Choose the middle index from the second backward graph and compose the two active fiber rows. -/
def composeAgainst : Table.{u, w, x, z} I K := by
  classical
  intro a
  cases a with
  | edge i l a =>
    let j := IndependentIndexedCarrierGraph.index (fun l j => q j l) hq l
    exact if hi : p i j = true then
      IndependentInverseGraph.compose (S i) (M j) (T l) (row h i j) (hh.active i j hi)
        (row k j l) (hk.active j l ((IndependentIndexedCarrierGraph.active_iff _ hq l j).2 rfl)) a
      else false

/-- At two true index points, composition uses exactly the two original inverse-fiber rows. -/
theorem composeAgainst_at_pair (i : I) (j : J) (l : K) (hjl : q j l = true) (hij : p i j = true) :
    row (composeAgainst p S M T h hh q hq k hk) i l =
      IndependentInverseGraph.compose (S i) (M j) (T l) (row h i j) (hh.active i j hij)
        (row k j l) (hk.active j l hjl) := by
  have he := (IndependentIndexedCarrierGraph.active_iff (fun l j => q j l) hq l j).1 hjl
  subst j
  funext a
  simp only [row, composeAgainst, hij, dif_pos]

/-- A false first index flag makes every composite fiber point false, including all carrier candidates. -/
theorem composeAgainst_false_at_pair (i : I) (j : J) (l : K) (hjl : q j l = true) (hij : p i j = false) :
    row (composeAgainst p S M T h hh q hq k hk) i l = fun _ => false := by
  have he := (IndependentIndexedCarrierGraph.active_iff (fun l j => q j l) hq l j).1 hjl
  subst j
  funext a
  simp only [row, composeAgainst, hij, Bool.false_eq_true, ↓reduceDIte]

/-- Backward-index composition retains inactivity and both inverse laws on every active fiber. -/
theorem composeAgainst_isLawful :
    IsLawful (fun i l => p i (IndependentIndexedCarrierGraph.index (fun l j => q j l) hq l)) S T
      (composeAgainst p S M T h hh q hq k hk) := by
  constructor
  · intro i l hil a
    exact congrFun (composeAgainst_false_at_pair p S M T h hh q hq k hk i _ l
      ((IndependentIndexedCarrierGraph.active_iff _ hq l _).2 rfl) hil) a
  · intro i l hil
    rw [composeAgainst_at_pair p S M T h hh q hq k hk i _ l
      ((IndependentIndexedCarrierGraph.active_iff _ hq l _).2 rfl) hil]
    exact IndependentInverseGraph.compose_isLawful _ _ _ _ _ _ _

end

end AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph
