import ResearchLean.AG.ProtocolHolonomy.FiniteSpanningSelection
import Formal.Util.AssertStandardAxioms

/-!
# Every retained original named edge is necessary for spanning

Selected-edge reachability is monotone in the finite set of original names.
The deletion algorithm processes every original name exactly as listed. If
it keeps a name, deleting that name at that stage fails the spanning test;
later stages only remove more names, so the failure persists in the final
selection. This proves edge irredundancy. Turning that condition into the
literal named-path bridge field is the next obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Reachability through selected original names is monotone under adding
names. -/
theorem selectedNamedReachable_mono
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] {selected larger : Finset Q.Edge}
    (hsub : selected ⊆ larger) {a b : Q.Vertex}
    (h : SelectedNamedReachable Q selected a b) :
    SelectedNamedReachable Q larger a b := by
  induction h with
  | rel a b hab =>
      obtain ⟨e, he, hs, ht⟩ := hab
      exact Relation.EqvGen.rel _ _ ⟨e, hsub he, hs, ht⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A larger selected set preserves any all-component spanning result. -/
theorem spansOriginalComponents_mono
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Edge] (edges : ExplicitEnumeration Q.Edge)
    {selected larger : Finset Q.Edge}
    (hsub : selected ⊆ larger)
    (h : SpansOriginalComponents Q edges selected) :
    SpansOriginalComponents Q edges larger := by
  intro a b hab
  exact selectedNamedReachable_mono Q hsub (h a b hab)

/-- A name that remains after the whole deletion pass cannot be erased
without destroying the spanning condition, provided it appeared in the
processed name list. -/
theorem pruneNamedEdges_irredundant
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (names : List Q.Edge) (selected : Finset Q.Edge)
    (e : Q.Edge) (hname : e ∈ names)
    (hkept : e ∈ pruneNamedEdges Q vertices edges names selected) :
    ¬ SpansOriginalComponents Q edges
      ((pruneNamedEdges Q vertices edges names selected).erase e) := by
  induction names generalizing selected with
  | nil => simp at hname
  | cons x rest ih =>
      by_cases hsmall : SpansOriginalComponents Q edges (selected.erase x)
      · have hout : pruneNamedEdges Q vertices edges (x :: rest) selected =
            pruneNamedEdges Q vertices edges rest (selected.erase x) := by
          simp [pruneNamedEdges, hsmall]
        rw [hout] at hkept ⊢
        rcases List.mem_cons.mp hname with heq | hrest
        · subst e
          have hsub := pruneNamedEdges_subset Q vertices edges rest
            (selected.erase x)
          have hx : x ∈ selected.erase x := hsub hkept
          simp at hx
        · exact ih (selected.erase x) hrest hkept
      · have hout : pruneNamedEdges Q vertices edges (x :: rest) selected =
            pruneNamedEdges Q vertices edges rest selected := by
          simp [pruneNamedEdges, hsmall]
        rw [hout] at hkept ⊢
        rcases List.mem_cons.mp hname with heq | hrest
        · subst e
          intro hspan
          have hsub : (pruneNamedEdges Q vertices edges rest selected).erase x ⊆
              selected.erase x :=
            Finset.erase_subset_erase x
              (pruneNamedEdges_subset Q vertices edges rest selected)
          exact hsmall (spansOriginalComponents_mono Q edges hsub hspan)
        · exact ih selected hrest hkept

/-- Every retained edge in the input-generated spanning selection is
individually necessary for all-component connectivity. -/
theorem finiteSpanningEdgeSelection_irredundant
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (e : Q.Edge)
    (he : e ∈ finiteSpanningEdgeSelection Q vertices edges) :
    ¬ SpansOriginalComponents Q edges
      ((finiteSpanningEdgeSelection Q vertices edges).erase e) := by
  have hname : e ∈ edges.values :=
    List.mem_toFinset.mp (finiteSpanningEdgeSelection_subset Q vertices edges he)
  exact pruneNamedEdges_irredundant Q vertices edges edges.values
    (allNamedEdges Q edges) e hname he

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.selectedNamedReachable_mono
#print axioms AAT.AG.ProtocolHolonomy.spansOriginalComponents_mono
#print axioms AAT.AG.ProtocolHolonomy.pruneNamedEdges_irredundant
#print axioms AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection_irredundant
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
