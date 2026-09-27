import ResearchLean.AG.ProtocolHolonomy.SpanningTrees
import Formal.Util.AssertStandardAxioms

/-!
# Root holonomy condition forced by every actual lift

The forward direction of C1 is derived from the original named-edge law A1.
Renaming signed paths retains every original edge name and reverses inverse
traversals. The converse construction C2 is a separate obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- Rename one signed passage, retaining its original named edge and sign. -/
def renameSignedEdge {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom
      (g.vertex s) (g.vertex t) := by
  cases e with
  | inl f => exact Sum.inl (renameTypedEdge g f)
  | inr f => exact Sum.inr (renameTypedEdge g f)

/-- Rename every passage of a signed original named path. -/
def renameSigned {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (p : SignedPath Q s t) :
    SignedPath Q (g.vertex s) (g.vertex t) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => exact signedNil Q _
  | cons p e ih => exact signedCons Q ih (renameSignedEdge g e)

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}} (D : ReversibleData.{u, v, w} Q)

private theorem Lift.typed_edge_naturality
    {g : FixedFGraphAutomorphism Q} (a : D.Lift g)
    {s t : Q.Vertex} (f : TypedEdge Q s t) :
    (D.typedEdgeEquiv f).trans (a.fiber t) =
      (a.fiber s).trans (D.typedEdgeEquiv (renameTypedEdge g f)) := by
  rcases f with ⟨e, hs, ht⟩
  cases hs
  cases ht
  apply Equiv.ext
  intro x
  simpa [ReversibleData.typedEdgeEquiv, ReversibleData.renamedEdgeEquiv,
    renameTypedEdge] using a.edge_naturality e x

theorem Lift.signed_edge_naturality
    {g : FixedFGraphAutomorphism Q} (a : D.Lift g)
    {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    (D.signedEdgeEquiv e).trans (a.fiber t) =
      (a.fiber s).trans (D.signedEdgeEquiv (renameSignedEdge g e)) := by
  cases e with
  | inl f =>
      simpa [ReversibleData.signedEdgeEquiv, renameSignedEdge] using
        Lift.typed_edge_naturality D a f
  | inr f =>
      let T := D.typedEdgeEquiv f
      let U := D.typedEdgeEquiv (renameTypedEdge g f)
      have h : T.trans (a.fiber s) = (a.fiber t).trans U :=
        Lift.typed_edge_naturality D a f
      apply Equiv.ext
      intro x
      have hp : U (a.fiber t (T.symm x)) = a.fiber s x := by
        have hp0 := congrArg (fun k => k (T.symm x)) h
        simpa [Equiv.trans_apply, T, U] using hp0.symm
      change a.fiber t (T.symm x) = U.symm (a.fiber s x)
      calc
        a.fiber t (T.symm x) = U.symm (U (a.fiber t (T.symm x))) := by simp
        _ = U.symm (a.fiber s x) := congrArg U.symm hp

/-- A1 extends from each original named edge to every signed named path. -/
theorem Lift.signed_path_naturality
    {g : FixedFGraphAutomorphism Q} (a : D.Lift g)
    {s t : Q.Vertex} (p : SignedPath Q s t) :
    (D.transport p).trans (a.fiber t) =
      (a.fiber s).trans (D.transport (renameSigned g p)) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => rfl
  | cons p e ih =>
      change ((D.transport p).trans (D.signedEdgeEquiv e)).trans (a.fiber _) =
        (a.fiber _).trans
          ((D.transport (renameSigned g p)).trans
            (D.signedEdgeEquiv (renameSignedEdge g e)))
      rw [Equiv.trans_assoc, Lift.signed_edge_naturality D a e]
      rw [← Equiv.trans_assoc, ih, Equiv.trans_assoc]

/-- The C1 data consists only of root equivalences and their equations for
the original named-edge loops; no vertexwise lift is supplied. -/
structure RootSolutions (R : RootedPaths Q)
    (g : FixedFGraphAutomorphism Q) where
  rootFiber : ∀ j : FixedFComponent Q,
    D.Fiber (R.root j) ≃ D.Fiber (g.vertex (R.root j))
  edge_holonomy : ∀ (j : FixedFComponent Q) (e : Q.Edge)
    (he : fixedFComponentMk Q (Q.source e) = j),
    (D.transport (R.edgeLoopAt j e he)).trans (rootFiber j) =
      (rootFiber j).trans
        (D.transport (renameSigned g (R.edgeLoopAt j e he)))

/-- Every genuine A1 lift supplies root values satisfying all of C1. -/
def Lift.toRootSolutions
    {g : FixedFGraphAutomorphism Q} (a : D.Lift g)
    (R : RootedPaths Q) : D.RootSolutions R g where
  rootFiber j := a.fiber (R.root j)
  edge_holonomy j e he :=
    a.signed_path_naturality D (R.edgeLoopAt j e he)

/-- The values at the selected roots determine every fiber of a genuine
lift; this is the injectivity direction of the C1/C2 correspondence. -/
theorem Lift.eq_of_root_fiber_eq
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (a b : D.Lift g)
    (hroot : ∀ j : FixedFComponent Q,
      a.fiber (R.root j) = b.fiber (R.root j)) : a = b := by
  apply Lift.ext
  intro x y
  let j := fixedFComponentMk Q x
  let p := R.path j x rfl
  have ha := a.signed_path_naturality D p
  have hb := b.signed_path_naturality D p
  have h : (D.transport p).trans (a.fiber x) =
      (D.transport p).trans (b.fiber x) := by
    calc
      (D.transport p).trans (a.fiber x) =
          (a.fiber (R.root j)).trans (D.transport (renameSigned g p)) := ha
      _ = (b.fiber (R.root j)).trans (D.transport (renameSigned g p)) := by
        rw [hroot j]
      _ = (D.transport p).trans (b.fiber x) := hb.symm
  have h' := congrArg (fun k => (D.transport p).symm.trans k) h
  have hfiber : a.fiber x = b.fiber x := by
    simpa only [← Equiv.trans_assoc, Equiv.symm_trans_self,
      Equiv.refl_trans] using h'
  exact congrArg (fun k => k y) hfiber

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.signed_edge_naturality
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.signed_path_naturality
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.toRootSolutions
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.eq_of_root_fiber_eq
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
