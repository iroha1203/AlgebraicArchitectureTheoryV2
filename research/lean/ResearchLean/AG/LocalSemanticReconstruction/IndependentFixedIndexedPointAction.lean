import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedInverseComposition
import Formal.Util.AssertStandardAxioms

/-!
# Actual action points from dependent inverse graphs

Implementation notes: each action point reads one backward value, applies the
original source operation at that value, and reads one forward output point.
Both index flags guard the row. The native comparison consumes the ordinary
naturality square, so it applies to support and axis maps and to observable
restriction after reversing the source and target indices.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

noncomputable section

universe u v w z

variable {I : Type u} {J : Type v} {S : I → Type w} {T : J → Type z}
variable (p : I → J → Bool) (h r : Table S T) (hl : InverseLaws p h r)

/-- Transport one source operation point through the original backward and forward fiber graphs. -/
def action (i i' : I) (j j' : J) (a : S i → S i') (y : T j) (z : T j') : Bool := by
  classical
  exact if hij : p i j = true then
    if p i' j' = true then h i' j' (a ((backwardGraph h r hl i j hij).assemble y)) z else false
  else false

/-- Two active index pairs expose the primitive backward-value and forward-value action. -/
theorem action_active (i i' : I) (j j' : J) (a : S i → S i') (y : T j) (z : T j')
    (hij : p i j = true) (hij' : p i' j' = true) : action p h r hl i i' j j' a y z =
      h i' j' (a ((backwardGraph h r hl i j hij).assemble y)) z := by
  classical
  simp only [action, hij, hij', dif_pos, if_pos]

/-- Either inactive index pair forces the entire candidate action point to false. -/
theorem action_inactive (i i' : I) (j j' : J) (a : S i → S i') (y : T j) (z : T j')
    (hn : p i j = false ∨ p i' j' = false) : action p h r hl i i' j j' a y z = false := by
  classical
  rcases hn with hi | hi'
  · simp only [action, hi, Bool.false_eq_true, ↓reduceDIte]
  · by_cases hi : p i j = true <;> simp only [action, hi, hi', Bool.false_eq_true, ↓reduceDIte, if_false]

variable (F : I → J) (hpF : ∀ i j, p i j = true ↔ F i = j)
variable (e : ∀ i, S i ≃ T (F i)) (he : read F (fun i => e i) = h)

include hpF he in
/-- The direct action point equals the native target-operation graph whenever its naturality square holds. -/
theorem action_point_iff (i i' : I) (a : S i → S i') (b : T (F i) → T (F i'))
    (hn : ∀ x, e i' (a x) = b (e i x)) (y : T (F i)) (z : T (F i')) :
    action p h r hl i i' (F i) (F i') a y z = true ↔ b y = z := by
  have hi : p i (F i) = true := (hpF i (F i)).2 rfl
  have hi' : p i' (F i') = true := (hpF i' (F i')).2 rfl
  let x := (backwardGraph h r hl i (F i) hi).assemble y
  have hx : r i (F i) x y = true := (backwardGraph h r hl i (F i) hi).edge_target y
  have hexy : e i x = y := (read_point_iff F (fun i => e i) i x y).1
    ((congrArg (fun t => t i (F i) x y) he).trans ((hl.inverse i (F i) x y).trans hx))
  have hav : e i' (a x) = b y := (hn x).trans (congrArg b hexy)
  rw [action_active p h r hl i i' (F i) (F i') a y z hi hi']
  have hr : h i' (F i') (a x) z = read F (fun i => e i) i' (F i') (a x) z :=
    (congrArg (fun t => t i' (F i') (a x) z) he).symm
  exact (congrArg (fun b => b = true) hr).to_iff.trans
    ((read_point_iff F (fun i => e i) i' (a x) z).trans (congrArg (fun v => v = z) hav).to_iff)

end

end AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph
