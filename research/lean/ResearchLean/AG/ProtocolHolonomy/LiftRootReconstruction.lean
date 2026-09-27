import ResearchLean.AG.ProtocolHolonomy.LiftRootCondition
import Formal.Util.AssertStandardAxioms

/-!
# Reconstructing a lift from the root equations

The C1 equations yield the vertexwise family by C2. The edge square and two
inverse laws connect this family to the original `Lift` type.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

theorem renameSignedEdge_swap {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    renameSignedEdge g e.swap = (renameSignedEdge g e).swap := by
  cases e <;> rfl

theorem renameSigned_comp {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t z : Q.Vertex}
    (p : SignedPath Q s t) (q : SignedPath Q t z) :
    renameSigned g (signedComp Q p q) =
      signedComp Q (renameSigned g p) (renameSigned g q) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction q with
  | nil => rfl
  | cons q e ih =>
      change signedCons Q (renameSigned g (signedComp Q p q))
          (renameSignedEdge g e) =
        signedComp Q (renameSigned g p)
          (signedCons Q (renameSigned g q) (renameSignedEdge g e))
      rw [ih]
      rfl

@[simp] theorem renameSigned_toPath {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    renameSigned g (signedToPath Q e) =
      signedToPath Q (renameSignedEdge g e) := rfl

theorem renameSigned_reverse {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (p : SignedPath Q s t) :
    renameSigned g (signedReverse Q p) =
      signedReverse Q (renameSigned g p) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => rfl
  | cons p e ih =>
      change renameSigned g (signedComp Q (signedToPath Q e.swap)
          (signedReverse Q p)) =
        signedComp Q (signedToPath Q (renameSignedEdge g e).swap)
          (signedReverse Q (renameSigned g p))
      rw [renameSigned_comp, ih, renameSigned_toPath, renameSignedEdge_swap]

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- The elementary groupoid calculation underlying the C1-to-A1 direction.
The source and renamed root paths may have different target roots. -/
private theorem square_of_root_equation
    {K L S T S' T' : Type*}
    (Ps : K ≃ S) (Pt : K ≃ T)
    (Qs : L ≃ S') (Qt : L ≃ T')
    (E : S ≃ T) (E' : S' ≃ T') (b : K ≃ L)
    (h : ((Ps.trans E).trans Pt.symm).trans b =
      b.trans ((Qs.trans E').trans Qt.symm)) :
    E.trans ((Pt.symm.trans b).trans Qt) =
      ((Ps.symm.trans b).trans Qs).trans E' := by
  apply Equiv.ext
  intro x
  have hp := congrArg (fun f => f (Ps.symm x)) h
  apply Qt.symm.injective
  simpa [Equiv.trans_apply] using hp

private theorem transport_renamed_edgePath
    (g : FixedFGraphAutomorphism Q) (e : Q.Edge) :
    D.transport (renameSigned g (RootedPaths.edgePath e)) =
      D.renamedEdgeEquiv g e := by
  change D.typedEdgeEquiv (renameTypedEdge g ⟨e, rfl, rfl⟩) =
    D.renamedEdgeEquiv g e
  apply Equiv.ext
  intro x
  simp [ReversibleData.renamedEdgeEquiv,
    ReversibleData.typedEdgeEquiv, renameTypedEdge]

/-- The C2 expression, with target path obtained by renaming the chosen
source root path, independent of any target-side tree choice. -/
def RootSolutions.reconstructedFiber
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (b : D.RootSolutions R g) (x : Q.Vertex) :
    D.Fiber x ≃ D.Fiber (g.vertex x) :=
  let j := fixedFComponentMk Q x
  let p := R.path j x rfl
  ((D.transport p).symm.trans (b.rootFiber j)).trans
    (D.transport (renameSigned g p))

theorem RootSolutions.reconstructedFiber_eq_at
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (b : D.RootSolutions R g) (j : FixedFComponent Q)
    (x : Q.Vertex) (hx : fixedFComponentMk Q x = j) :
    b.reconstructedFiber D R x =
      ((D.transport (R.path j x hx)).symm.trans (b.rootFiber j)).trans
        (D.transport (renameSigned g (R.path j x hx))) := by
  cases hx
  rfl

/-- C1 on one original named edge yields the A1 square for C2. -/
theorem RootSolutions.reconstructed_edge_naturality
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (b : D.RootSolutions R g) (e : Q.Edge) :
    (D.edgeEquiv e).trans (b.reconstructedFiber D R (Q.target e)) =
      (b.reconstructedFiber D R (Q.source e)).trans
        (D.renamedEdgeEquiv g e) := by
  let j := fixedFComponentMk Q (Q.source e)
  have ht : fixedFComponentMk Q (Q.target e) = j :=
    RootedPaths.target_component e
  let Ps := D.transport (R.path j (Q.source e) rfl)
  let Pt := D.transport (R.path j (Q.target e) ht)
  let Qs := D.transport (renameSigned g (R.path j (Q.source e) rfl))
  let Qt := D.transport (renameSigned g (R.path j (Q.target e) ht))
  have hsrc : D.transport (R.edgeLoopAt j e rfl) =
      (Ps.trans (D.edgeEquiv e)).trans Pt.symm := by
    simp [RootedPaths.edgeLoopAt, D.transport_comp,
      D.transport_reverse, Ps, Pt, RootedPaths.edgePath,
      ReversibleData.signedEdgeEquiv, ReversibleData.typedEdgeEquiv,
      Equiv.trans_assoc]
  have hdst : D.transport (renameSigned g (R.edgeLoopAt j e rfl)) =
      (Qs.trans (D.renamedEdgeEquiv g e)).trans Qt.symm := by
    simp [RootedPaths.edgeLoopAt, renameSigned_comp,
      renameSigned_reverse, D.transport_comp, D.transport_reverse,
      D.transport_renamed_edgePath, Qs, Qt, Equiv.trans_assoc]
  have hc := b.edge_holonomy j e rfl
  rw [hsrc, hdst] at hc
  rw [b.reconstructedFiber_eq_at D R j (Q.source e) rfl]
  rw [b.reconstructedFiber_eq_at D R j (Q.target e) ht]
  exact square_of_root_equation Ps Pt Qs Qt
    (D.edgeEquiv e) (D.renamedEdgeEquiv g e) (b.rootFiber j) hc

/-- The C2 family is a genuine A1 lift on every original named edge. -/
def RootSolutions.toLift
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (b : D.RootSolutions R g) : D.Lift g where
  fiber := b.reconstructedFiber D R
  edge_naturality := by
    intro e x
    have h := congrArg
      (fun f : D.Fiber (Q.source e) ≃ D.Fiber (g.vertex (Q.target e)) => f x)
      (b.reconstructed_edge_naturality D R e)
    simpa [Equiv.trans_apply] using h

/-- At a component root, the C2 expression is the prescribed C1 value. -/
theorem RootSolutions.reconstructedFiber_root
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (b : D.RootSolutions R g) (j : FixedFComponent Q) :
    b.reconstructedFiber D R (R.root j) = b.rootFiber j := by
  rw [b.reconstructedFiber_eq_at D R j (R.root j) (R.root_component j)]
  simp [R.path_root, renameSigned, signedNil, ReversibleData.transport]

@[ext] theorem RootSolutions.ext
    {g : FixedFGraphAutomorphism Q} {R : RootedPaths Q}
    {b c : D.RootSolutions R g}
    (h : ∀ j, b.rootFiber j = c.rootFiber j) : b = c := by
  cases b with
  | mk bf bh =>
      cases c with
      | mk cf ch =>
          have hf : bf = cf := funext h
          cases hf
          rfl

/-- Root evaluation of the reconstructed lift returns every C1 root value. -/
theorem RootSolutions.toLift_toRootSolutions
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (b : D.RootSolutions R g) :
    (b.toLift D R).toRootSolutions D R = b := by
  apply RootSolutions.ext D
  intro j
  exact RootSolutions.reconstructedFiber_root D R b j

/-- Reconstructing from an actual lift's roots recovers the original lift. -/
theorem Lift.toRootSolutions_toLift
    {g : FixedFGraphAutomorphism Q} (R : RootedPaths Q)
    (a : D.Lift g) :
    (a.toRootSolutions D R).toLift D R = a := by
  apply Lift.eq_of_root_fiber_eq D R
  intro j
  exact RootSolutions.reconstructedFiber_root D R
    (a.toRootSolutions D R) j

/-- C1/C2: actual lifts over `g` are exactly the simultaneous root
solutions for all original named-edge loops. -/
def liftEquivRootSolutions
    (R : RootedPaths Q) (g : FixedFGraphAutomorphism Q) :
    D.Lift g ≃ D.RootSolutions R g where
  toFun a := a.toRootSolutions D R
  invFun b := b.toLift D R
  left_inv := Lift.toRootSolutions_toLift D R
  right_inv := RootSolutions.toLift_toRootSolutions D R

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.renameSigned_comp
#print axioms AAT.AG.ProtocolHolonomy.renameSigned_reverse
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.RootSolutions.reconstructedFiber
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.RootSolutions.reconstructed_edge_naturality
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftEquivRootSolutions
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
