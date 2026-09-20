import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointComposition
import Formal.Util.AssertStandardAxioms

/-!
# Both primitive directions of context-indexed inverse composition

Implementation notes: the forward row follows the first value point and then
the second. At an active second index pair the backward row chooses the second
inverse value and reads the first backward row. False index pairs remain false.
The inverse equations compare these constructions on the same ordered point
pair without requiring an inverse index map.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

noncomputable section

universe u v w x y z

variable {I : Type u} {J : Type v} {K : Type w}
variable {S : I → Type x} {M : J → Type y} {T : K → Type z}
variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (h r : Table S M) (hh : InverseLaws p h r)
variable (q : J → K → Bool) (k s : Table M T) (hk : InverseLaws q k s)

/-- Follow the second backward value point before reading the first backward row at the selected middle index. -/
def composeBackward : Table S T := by
  classical
  intro i l x y
  let j := IndependentIndexedCarrierGraph.index p hp i
  exact if hjl : q j l = true then
    r i j x ((backwardGraph k s hk j l hjl).assemble y)
  else false

/-- Two true index points expose the successive backward values in reverse order. -/
theorem composeBackward_at_pair (i : I) (j : J) (l : K) (hij : p i j = true) (hjl : q j l = true)
    (x : S i) (y : T l) : composeBackward p hp r q k s hk i l x y =
      r i j x ((backwardGraph k s hk j l hjl).assemble y) := by
  have he := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
  subst j
  simp only [composeBackward, hjl, dif_pos]

/-- A false second index point removes every backward composite value at a true first pair. -/
theorem composeBackward_inactive (i : I) (j : J) (l : K) (hij : p i j = true) (hjl : q j l = false)
    (x : S i) (y : T l) : composeBackward p hp r q k s hk i l x y = false := by
  have he := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
  subst j
  simp only [composeBackward, hjl, Bool.false_eq_true, ↓reduceDIte]

/-- Primitive backward composition and forward composition retain exactly the same ordered inverse edges. -/
theorem composeBackward_eq_forward : composeBackward p hp r q k s hk = compose p hp h hh.forward k := by
  classical
  funext i l x y
  let j := IndependentIndexedCarrierGraph.index p hp i
  have hij : p i j = true := (IndependentIndexedCarrierGraph.active_iff p hp i j).2 rfl
  by_cases hjl : q j l = true
  · rw [composeBackward_at_pair p hp r q k s hk i j l hij hjl x y,
      compose_at_pair p hp h hh.forward k i j l hij x y]
    let u := (graph h hh.forward i j hij).assemble x
    let v := (backwardGraph k s hk j l hjl).assemble y
    have hu : h i j x u = true := (graph h hh.forward i j hij).edge_target x
    have hv : s j l v y = true := (backwardGraph k s hk j l hjl).edge_target y
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have he : u = v := (graph h hh.forward i j hij).target_eq_of_edge ((hh.inverse i j x v).trans hx)
      exact (congrArg (fun a => k j l a y) he).trans ((hk.inverse j l v y).trans hv)
    · intro hy
      have he : v = u := (backwardGraph k s hk j l hjl).target_eq_of_edge ((hk.inverse j l u y).symm.trans hy)
      exact (congrArg (fun a => r i j x a) he).trans ((hh.inverse i j x u).symm.trans hu)
  · have hjl0 : q j l = false := Bool.eq_false_iff.mpr hjl
    rw [composeBackward_inactive p hp r q k s hk i j l hij hjl0 x y,
      compose_at_pair p hp h hh.forward k i j l hij x y, hk.forward.inactive j l hjl0]

/-- The two directly composed directions satisfy every original dependent inverse-row condition. -/
theorem compose_inverseLaws : InverseLaws (IndependentIndexedCarrierGraph.composeIndex p hp q)
    (compose p hp h hh.forward k) (composeBackward p hp r q k s hk) := by
  refine ⟨compose_isLawful p hp h hh.forward k q hk.forward, ?_, ?_⟩
  · intro i l hil y
    let j := IndependentIndexedCarrierGraph.index p hp i
    have hij : p i j = true := (IndependentIndexedCarrierGraph.active_iff p hp i j).2 rfl
    have hjl : q j l = true := hil
    let v := (backwardGraph k s hk j l hjl).assemble y
    obtain ⟨x, hx, hu⟩ := hh.backward i j hij v
    refine ⟨x, ?_, ?_⟩
    · exact (composeBackward_at_pair p hp r q k s hk i j l hij hjl x y).trans hx
    · intro x' hx'
      exact hu x' ((composeBackward_at_pair p hp r q k s hk i j l hij hjl x' y).symm.trans hx')
  · intro i l x y
    exact (congrArg (fun t => t i l x y) (composeBackward_eq_forward p hp h r hh q k s hk)).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph
