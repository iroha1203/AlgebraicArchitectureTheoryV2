import ResearchLean.AG.ProtocolHolonomy.FiniteSelectionBridge
import Formal.Util.AssertStandardAxioms

/-!
# Selected original reachability has actual named signed paths

The equivalence closure of selected original edge steps is realized by paths
in Mathlib's symmetrified quiver, with every traversal carrying its original
edge name. This supplies the connected field for a generated named forest.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- A one-edge signed path uses its underlying original name. -/
theorem usesNamedEdges_single
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Q.Edge → Prop) {a b : Q.Vertex}
    (edge : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom a b)
    (he : selected (match edge with
      | Sum.inl f => f.1
      | Sum.inr f => f.1)) :
    UsesNamedEdges selected (signedToPath Q edge) := by
  change UsesNamedEdges selected (signedCons Q (signedNil Q a) edge)
  exact UsesNamedEdges.cons _ _ (UsesNamedEdges.nil a) he

/-- Concatenation preserves the exact permitted original edge names. -/
theorem usesNamedEdges_comp
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Q.Edge → Prop) {a b c : Q.Vertex}
    (p : SignedPath Q a b) (q : SignedPath Q b c)
    (hp : UsesNamedEdges selected p) (hq : UsesNamedEdges selected q) :
    UsesNamedEdges selected (signedComp Q p q) := by
  induction hq with
  | nil => simpa [signedComp, signedNil] using hp
  | cons q edge hq he ih =>
      change UsesNamedEdges selected (signedCons Q (signedComp Q p q) edge)
      exact UsesNamedEdges.cons _ _ ih he

/-- Reversal preserves every original name while swapping each traversal
direction. -/
theorem usesNamedEdges_reverse
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Q.Edge → Prop) {a b : Q.Vertex}
    (p : SignedPath Q a b) (hp : UsesNamedEdges selected p) :
    UsesNamedEdges selected (signedReverse Q p) := by
  induction hp with
  | nil => exact UsesNamedEdges.nil _
  | cons p edge hp he ih =>
      have hone : UsesNamedEdges selected (signedToPath Q edge.swap) := by
        cases edge with
        | inl f => exact usesNamedEdges_single Q selected (Sum.inr f) he
        | inr f => exact usesNamedEdges_single Q selected (Sum.inl f) he
      change UsesNamedEdges selected
        (signedComp Q (signedToPath Q edge.swap) (signedReverse Q p))
      exact usesNamedEdges_comp Q selected _ _ hone ih

/-- Selected-name equivalence closure and actual selected signed paths are
the same connectivity statement. -/
theorem selectedNamedReachable_iff_usesNamedEdges
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] (selected : Finset Q.Edge)
    (a b : Q.Vertex) :
    SelectedNamedReachable Q selected a b ↔
      ∃ p : SignedPath Q a b,
        UsesNamedEdges (fun e => e ∈ selected) p := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
        obtain ⟨e, he, hs, ht⟩ := hab
        let edge : TypedEdge Q a b := ⟨e, hs, ht⟩
        exact ⟨signedToPath Q (Sum.inl edge),
          usesNamedEdges_single Q _ _ he⟩
    | refl a => exact ⟨signedNil Q a, UsesNamedEdges.nil a⟩
    | symm a b hab ih =>
        obtain ⟨p, hp⟩ := ih
        exact ⟨signedReverse Q p, usesNamedEdges_reverse Q _ p hp⟩
    | trans a b c hab hbc ih₁ ih₂ =>
        obtain ⟨p, hp⟩ := ih₁
        obtain ⟨q, hq⟩ := ih₂
        exact ⟨signedComp Q p q, usesNamedEdges_comp Q _ p q hp hq⟩
  · rintro ⟨p, hp⟩
    exact usesNamedEdges_selectedReachable Q _ selected
      (by intro e he; exact he) p hp

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.usesNamedEdges_single
#print axioms AAT.AG.ProtocolHolonomy.usesNamedEdges_comp
#print axioms AAT.AG.ProtocolHolonomy.usesNamedEdges_reverse
#print axioms AAT.AG.ProtocolHolonomy.selectedNamedReachable_iff_usesNamedEdges
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
