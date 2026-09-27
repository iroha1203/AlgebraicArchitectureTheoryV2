import ResearchLean.AG.ProtocolHolonomy.RootedPaths
import Formal.Util.AssertStandardAxioms

/-!
# Named edge loops and their holonomy generators

Each original named edge determines a loop at its component root. Its action
is the operation table conjugated by the selected root paths, as in B1.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace RootedPaths

variable {Q : FixedFDirectedMultigraph.{u, v}} (R : RootedPaths Q)

/-- An original edge has both endpoints in its source component. -/
theorem target_component (e : Q.Edge) :
    fixedFComponentMk Q (Q.target e) = fixedFComponentMk Q (Q.source e) := by
  apply (component_eq_iff_signedReachable Q _ _).mpr
  exact ⟨signedToPath Q (Sum.inr ⟨e, rfl, rfl⟩)⟩

/-- A named edge whose source lies in a selected component also ends there. -/
theorem target_component_at (j : FixedFComponent Q) (e : Q.Edge)
    (he : fixedFComponentMk Q (Q.source e) = j) :
    fixedFComponentMk Q (Q.target e) = j :=
  (target_component e).trans he

/-- The signed traversal of one original named edge. -/
def edgePath (e : Q.Edge) : SignedPath Q (Q.source e) (Q.target e) :=
  signedToPath Q (Sum.inl ⟨e, rfl, rfl⟩)

/-- The B1 loop: root to source, named edge, reverse root-to-target path. -/
def edgeLoop (e : Q.Edge) :
    SignedPath Q (R.root (fixedFComponentMk Q (Q.source e)))
      (R.root (fixedFComponentMk Q (Q.source e))) :=
  signedComp Q
    (R.path _ (Q.source e) rfl)
    (signedComp Q (RootedPaths.edgePath e)
      (signedReverse Q (R.path _ (Q.target e)
        (RootedPaths.target_component e))))

/-- The same loop indexed by any proof of the edge's component. -/
def edgeLoopAt (j : FixedFComponent Q) (e : Q.Edge)
    (he : fixedFComponentMk Q (Q.source e) = j) :
    SignedPath Q (R.root j) (R.root j) :=
  signedComp Q
    (R.path j (Q.source e) he)
    (signedComp Q (edgePath e)
      (signedReverse Q (R.path j (Q.target e)
        (target_component_at j e he))))

end RootedPaths

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q) (R : RootedPaths Q)

/-- Transport along the selected root path. -/
def rootTransport (j : FixedFComponent Q) (x : Q.Vertex)
    (hx : fixedFComponentMk Q x = j) : D.Fiber (R.root j) ≃ D.Fiber x :=
  D.transport (R.path j x hx)

/-- The endpoint of any signed named path stays in the same original component. -/
theorem path_target_component {s t : Q.Vertex} (p : SignedPath Q s t)
    (j : FixedFComponent Q) (hs : fixedFComponentMk Q s = j) :
    fixedFComponentMk Q t = j :=
  ((component_eq_iff_signedReachable Q s t).mpr ⟨p⟩).symm.trans hs

/-- Move any path transport to the fiber at its chosen component root. -/
def normalizedTransport {s t : Q.Vertex} (p : SignedPath Q s t)
    (j : FixedFComponent Q) (hs : fixedFComponentMk Q s = j) :
    Equiv.Perm (D.Fiber (R.root j)) :=
  ((D.rootTransport R j s hs).trans (D.transport p)).trans
    (D.rootTransport R j t (path_target_component p j hs)).symm

/-- Normalization respects path concatenation, in traversal order. -/
theorem normalizedTransport_comp {s t z : Q.Vertex}
    (p : SignedPath Q s t) (q : SignedPath Q t z)
    (j : FixedFComponent Q) (hs : fixedFComponentMk Q s = j) :
    D.normalizedTransport R (signedComp Q p q) j hs =
      (D.normalizedTransport R p j hs).trans
        (D.normalizedTransport R q j (path_target_component p j hs)) := by
  apply Equiv.ext
  intro x
  simp [normalizedTransport, rootTransport, transport_comp, Equiv.trans_apply]

@[simp] theorem normalizedTransport_nil (j : FixedFComponent Q)
    (s : Q.Vertex) (hs : fixedFComponentMk Q s = j) :
    D.normalizedTransport R (signedNil Q s) j hs = 1 := by
  apply Equiv.ext
  intro x
  simp [normalizedTransport, rootTransport]

/-- The generator from the original named edge table, on its component root fiber. -/
def edgeMonodromy (e : Q.Edge) :
    Equiv.Perm (D.Fiber (R.root (fixedFComponentMk Q (Q.source e)))) :=
  ((D.rootTransport R _ (Q.source e) rfl).trans (D.edgeEquiv e)).trans
    (D.rootTransport R _ (Q.target e) (RootedPaths.target_component e)).symm

/-- B1's table-derived generator for an edge in a selected component. -/
def edgeMonodromyAt (j : FixedFComponent Q) (e : Q.Edge)
    (he : fixedFComponentMk Q (Q.source e) = j) :
    Equiv.Perm (D.Fiber (R.root j)) :=
  ((D.rootTransport R j (Q.source e) he).trans (D.edgeEquiv e)).trans
    (D.rootTransport R j (Q.target e) (RootedPaths.target_component_at j e he)).symm

/-- The named edge loop acts by the table-derived B1 monodromy. -/
theorem transport_edgeLoop (e : Q.Edge) :
    D.transport (R.edgeLoop e) = D.edgeMonodromy R e := by
  rw [RootedPaths.edgeLoop, transport_comp, transport_comp, transport_reverse]
  rfl

/-- The indexed B1 generator is the transport of its actual named loop. -/
theorem transport_edgeLoopAt (j : FixedFComponent Q) (e : Q.Edge)
    (he : fixedFComponentMk Q (Q.source e) = j) :
    D.transport (R.edgeLoopAt j e he) = D.edgeMonodromyAt R j e he := by
  rw [RootedPaths.edgeLoopAt, transport_comp, transport_comp, transport_reverse]
  rfl

/-- The holonomy generated by the B1 elements from the original edge table. -/
def holonomy (j : FixedFComponent Q) :
    Subgroup (Equiv.Perm (D.Fiber (R.root j))) :=
  Subgroup.closure
    {m | ∃ (e : Q.Edge) (he : fixedFComponentMk Q (Q.source e) = j),
      m = D.edgeMonodromyAt R j e he}

theorem edgeMonodromyAt_mem_holonomy (j : FixedFComponent Q) (e : Q.Edge)
    (he : fixedFComponentMk Q (Q.source e) = j) :
    D.edgeMonodromyAt R j e he ∈ D.holonomy R j := by
  apply Subgroup.subset_closure
  exact ⟨e, he, rfl⟩

/-- Actual transports of root loops, closed under composition and reversal. -/
def rootedLoopTransportGroup (j : FixedFComponent Q) :
    Subgroup (Equiv.Perm (D.Fiber (R.root j))) where
  carrier := {m | ∃ p : SignedPath Q (R.root j) (R.root j), m = D.transport p}
  one_mem' := by
    refine ⟨signedNil Q (R.root j), ?_⟩
    apply Equiv.ext
    intro x
    rfl
  mul_mem' := by
    rintro a b ⟨pa, rfl⟩ ⟨pb, rfl⟩
    refine ⟨signedComp Q pb pa, ?_⟩
    rw [transport_comp]
    rfl
  inv_mem' := by
    rintro a ⟨p, rfl⟩
    refine ⟨signedReverse Q p, ?_⟩
    rw [transport_reverse]
    apply Equiv.ext
    intro x
    rfl

/-- A positive or negative traversal has normalized action in the table group. -/
theorem normalizedTransport_edge_mem {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t)
    (j : FixedFComponent Q) (hs : fixedFComponentMk Q s = j) :
    D.normalizedTransport R (signedToPath Q e) j hs ∈ D.holonomy R j := by
  cases e with
  | inl f =>
      rcases f with ⟨a, hsa, hta⟩
      cases hsa
      cases hta
      simpa [normalizedTransport, edgeMonodromyAt, rootTransport,
        typedEdgeEquiv, signedEdgeEquiv] using
        (D.edgeMonodromyAt_mem_holonomy R j a hs)
  | inr f =>
      rcases f with ⟨a, hta, hsa⟩
      cases hsa
      cases hta
      have he : fixedFComponentMk Q (Q.source a) = j :=
        path_target_component
          (signedToPath Q (Sum.inr ⟨a, rfl, rfl⟩)) j hs
      have h : D.edgeMonodromyAt R j a he ∈ D.holonomy R j :=
        D.edgeMonodromyAt_mem_holonomy R j a he
      have heq : D.normalizedTransport R
          (signedToPath Q (Sum.inr ⟨a, rfl, rfl⟩)) j hs =
          (D.edgeMonodromyAt R j a he).symm := by
        apply Equiv.ext
        intro x
        simp [normalizedTransport, edgeMonodromyAt, rootTransport,
          typedEdgeEquiv, signedEdgeEquiv, Equiv.trans_apply]
      rw [heq]
      exact (D.holonomy R j).inv_mem h

/-- Every signed named path has normalized action in the edge-generated group. -/
theorem normalizedTransport_mem_holonomy {s t : Q.Vertex}
    (p : SignedPath Q s t) (j : FixedFComponent Q)
    (hs : fixedFComponentMk Q s = j) :
    D.normalizedTransport R p j hs ∈ D.holonomy R j := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil =>
      change D.normalizedTransport R (signedNil Q _) j hs ∈ D.holonomy R j
      rw [D.normalizedTransport_nil R j _ hs]
      exact (D.holonomy R j).one_mem
  | cons p e ih =>
      have ht := path_target_component p j hs
      have hp := ih
      have he := D.normalizedTransport_edge_mem R e j ht
      have hmul := (D.holonomy R j).mul_mem he hp
      have hcomp := D.normalizedTransport_comp R p (signedToPath Q e) j hs
      change D.normalizedTransport R (signedComp Q p (signedToPath Q e)) j hs ∈
        D.holonomy R j
      rw [hcomp]
      convert hmul using 1

/-- B1 as an equality with the actual set of all root-loop transports. -/
theorem holonomy_eq_rootedLoopTransportGroup (j : FixedFComponent Q) :
    D.holonomy R j = D.rootedLoopTransportGroup R j := by
  apply le_antisymm
  · apply (Subgroup.closure_le (D.rootedLoopTransportGroup R j)).mpr
    rintro m ⟨e, he, rfl⟩
    exact ⟨R.edgeLoopAt j e he, (D.transport_edgeLoopAt R j e he).symm⟩
  · rintro m ⟨p, rfl⟩
    have h := D.normalizedTransport_mem_holonomy R p j (R.root_component j)
    simpa [normalizedTransport, rootTransport, R.path_root] using h

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.RootedPaths.target_component
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.transport_edgeLoop
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.transport_edgeLoopAt
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.edgeMonodromyAt_mem_holonomy
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.holonomy_eq_rootedLoopTransportGroup
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
