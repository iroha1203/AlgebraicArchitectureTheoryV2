import ResearchLean.AG.ProtocolHolonomy.TwoVertexOppositeEdges
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Formal.Util.AssertStandardAxioms

/-!
# The two-vertex example's visible C₂

Because each original edge starts at the vertex with the same Bool label,
the vertex and edge permutations of any graph automorphism coincide.
The full visible H therefore has exactly identity and the simultaneous
vertex/name exchange, with its actual group multiplication.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

private theorem twoVertex_perm_eq_one_or_swap (p : Equiv.Perm Bool) :
    p = 1 ∨ p = Equiv.swap false true := by
  rcases oneLoop_visible_eq_one_or_swap (oneLoopGraphAutOfPerm p) with h | h
  · exact Or.inl (congrArg
      (fun g : FixedFGraphAutomorphism oneLoopGraph => g.edge) h)
  · exact Or.inr (congrArg
      (fun g : FixedFGraphAutomorphism oneLoopGraph => g.edge) h)

/-- Every Bool permutation gives a graph automorphism when used on both
vertices and original opposite edge names. -/
def twoVertexGraphAutOfPerm (p : Equiv.Perm Bool) :
    FixedFGraphAutomorphism twoVertexGraph where
  vertex := p
  edge := p
  source_rename := by intro e; rfl
  target_rename := by
    intro e
    rcases twoVertex_perm_eq_one_or_swap p with hp | hp
    · subst p; cases e <;> rfl
    · subst p; cases e <;> rfl

/-- In any automorphism of this original graph, the vertex and named-edge
permutations coincide. -/
theorem twoVertex_vertex_eq_edge
    (g : FixedFGraphAutomorphism twoVertexGraph) : g.vertex = g.edge := by
  apply Equiv.ext
  intro e
  exact (g.source_rename e).symm

theorem twoVertex_visible_eq_one_or_swap
    (g : FixedFGraphAutomorphism twoVertexGraph) :
    g = 1 ∨ g = twoVertexSwap := by
  rcases twoVertex_perm_eq_one_or_swap g.edge with he | he
  · left
    apply FixedFGraphAutomorphism.ext
    · exact (twoVertex_vertex_eq_edge g).trans he
    · exact he
  · right
    apply FixedFGraphAutomorphism.ext
    · exact (twoVertex_vertex_eq_edge g).trans he
    · exact he

theorem twoVertexSwap_ne_one :
    twoVertexSwap ≠ (1 : FixedFGraphAutomorphism twoVertexGraph) := by
  intro h
  have he := congrArg
    (fun g : FixedFGraphAutomorphism twoVertexGraph => g.edge false) h
  change true = false at he
  cases he

/-- The actual full visible H is isomorphic to permutations of the two
original Bool edge names, preserving graph-automorphism multiplication. -/
def twoVertexHEquivPermBool : twoVertexInput.H ≃* Equiv.Perm Bool where
  toFun g := g.1.edge
  invFun p := ⟨twoVertexGraphAutOfPerm p, by trivial⟩
  left_inv g := by
    apply Subtype.ext
    apply FixedFGraphAutomorphism.ext
    · exact (twoVertex_vertex_eq_edge g.1).symm
    · rfl
  right_inv p := rfl
  map_mul' _ _ := rfl

theorem twoVertex_H_exact (g : twoVertexInput.H) :
    g.1 = 1 ∨ g.1 = twoVertexSwap :=
  twoVertex_visible_eq_one_or_swap g.1

theorem twoVertex_H_card_two : Nat.card twoVertexInput.H = 2 := by
  rw [Nat.card_congr twoVertexHEquivPermBool.toEquiv]
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

theorem twoVertex_H_isCyclic : IsCyclic twoVertexInput.H :=
  isCyclic_of_prime_card twoVertex_H_card_two

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertexGraphAutOfPerm
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_vertex_eq_edge
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_visible_eq_one_or_swap
#print axioms AAT.AG.ProtocolHolonomy.twoVertexSwap_ne_one
#print axioms AAT.AG.ProtocolHolonomy.twoVertexHEquivPermBool
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_H_exact
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_H_card_two
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_H_isCyclic
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
