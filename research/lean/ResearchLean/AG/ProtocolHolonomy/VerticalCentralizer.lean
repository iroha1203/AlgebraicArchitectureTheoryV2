import ResearchLean.AG.ProtocolHolonomy.HolonomyGenerators
import ResearchLean.AG.ProtocolHolonomy.LiftBridge
import Mathlib.GroupTheory.Subgroup.Centralizer
import Formal.Util.AssertStandardAxioms

/-!
# Vertical changes and root holonomy centralizers

The named-edge square for a change with identity visible action extends to
all signed paths. Root evaluation therefore commutes with every holonomy
generator. The converse reconstruction is treated separately.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- The A1 square for a vertical lift, as an equality of equivalences. -/
theorem vertical_edge_naturality (a : D.Lift (1 : FixedFGraphAutomorphism Q))
    (e : Q.Edge) :
    (D.edgeEquiv e).trans (a.fiber (Q.target e)) =
      (a.fiber (Q.source e)).trans (D.edgeEquiv e) := by
  apply Equiv.ext
  intro x
  simpa [renamedEdgeEquiv, Equiv.trans_apply] using a.edge_naturality e x

/-- The vertical square extends to a positive or negative named passage. -/
theorem vertical_signedEdge_naturality
    (a : D.Lift (1 : FixedFGraphAutomorphism Q))
    {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    (D.signedEdgeEquiv e).trans (a.fiber t) =
      (a.fiber s).trans (D.signedEdgeEquiv e) := by
  cases e with
  | inl f =>
      rcases f with ⟨edge, hsource, htarget⟩
      cases hsource
      cases htarget
      simpa [signedEdgeEquiv, typedEdgeEquiv] using
        D.vertical_edge_naturality a edge
  | inr f =>
      rcases f with ⟨edge, htarget, hsource⟩
      cases hsource
      cases htarget
      apply Equiv.ext
      intro x
      apply (D.edgeEquiv edge).injective
      have h := congrArg (fun f : D.Fiber (Q.source edge) ≃
          D.Fiber (Q.target edge) => f ((D.edgeEquiv edge).symm x))
        (D.vertical_edge_naturality a edge)
      simpa [signedEdgeEquiv, typedEdgeEquiv, Equiv.trans_apply] using h.symm

/-- A vertical change commutes with transport along every signed named path. -/
theorem vertical_transport_naturality
    (a : D.Lift (1 : FixedFGraphAutomorphism Q))
    {s t : Q.Vertex} (p : SignedPath Q s t) :
    (D.transport p).trans (a.fiber t) =
      (a.fiber s).trans (D.transport p) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => rfl
  | cons p e ih =>
      apply Equiv.ext
      intro x
      have he := congrArg
        (fun f : D.Fiber _ ≃ D.Fiber _ => f (D.transport p x))
        (D.vertical_signedEdge_naturality a e)
      have hp := congrArg (fun f : D.Fiber _ ≃ D.Fiber _ => f x) ih
      simpa [transport_cons, Equiv.trans_apply] using
        he.trans (congrArg (D.signedEdgeEquiv e) hp)

/-- Root evaluation of a vertical lift centralizes its component holonomy. -/
theorem vertical_root_mem_centralizer
    (a : D.Lift (1 : FixedFGraphAutomorphism Q))
    (R : RootedPaths Q) (j : FixedFComponent Q) :
    a.fiber (R.root j) ∈
      Subgroup.centralizer (D.holonomy R j :
        Set (Equiv.Perm (D.Fiber (R.root j)))) := by
  let aRoot : Equiv.Perm (D.Fiber (R.root j)) := a.fiber (R.root j)
  change aRoot ∈
    Subgroup.centralizer (D.holonomy R j :
      Set (Equiv.Perm (D.Fiber (R.root j))))
  rw [D.holonomy_eq_rootedLoopTransportGroup R j]
  change ∀ m ∈ (D.rootedLoopTransportGroup R j :
      Set (Equiv.Perm (D.Fiber (R.root j)))),
    m * aRoot = aRoot * m
  rintro m ⟨p, rfl⟩
  have h := D.vertical_transport_naturality a p
  simpa [aRoot, Equiv.Perm.mul_def] using h.symm

/-- One holonomy-centralizing permutation for each original graph component. -/
def RootCentralizers (R : RootedPaths Q) : Type _ :=
  ∀ j : FixedFComponent Q,
    Subgroup.centralizer (D.holonomy R j :
      Set (Equiv.Perm (D.Fiber (R.root j))))

instance (R : RootedPaths Q) : Group (D.RootCentralizers R) := by
  unfold RootCentralizers
  infer_instance

/-- Evaluate an actual A1 vertical lift at every component root. -/
def verticalRootEvaluation (R : RootedPaths Q) :
    D.Lift (1 : FixedFGraphAutomorphism Q) → D.RootCentralizers R :=
  fun a j => ⟨a.fiber (R.root j), D.vertical_root_mem_centralizer a R j⟩

/-- A vertical lift is determined by its root values. -/
theorem verticalRootEvaluation_injective (R : RootedPaths Q) :
    Function.Injective (D.verticalRootEvaluation R) := by
  intro a b h
  apply Lift.ext
  intro v x
  let j := fixedFComponentMk Q v
  let P := D.rootTransport R j v rfl
  have hroot : a.fiber (R.root j) = b.fiber (R.root j) := by
    have hj := congrFun h j
    exact congrArg Subtype.val hj
  have ha := congrArg (fun f : D.Fiber (R.root j) ≃ D.Fiber v =>
      f (P.symm x))
    (D.vertical_transport_naturality a (R.path j v rfl))
  have hb := congrArg (fun f : D.Fiber (R.root j) ≃ D.Fiber v =>
      f (P.symm x))
    (D.vertical_transport_naturality b (R.path j v rfl))
  change a.fiber v (P (P.symm x)) = P (a.fiber (R.root j) (P.symm x)) at ha
  change b.fiber v (P (P.symm x)) = P (b.fiber (R.root j) (P.symm x)) at hb
  have hmid : P (a.fiber (R.root j) (P.symm x)) =
      P (b.fiber (R.root j) (P.symm x)) :=
    congrArg (fun f : Equiv.Perm (D.Fiber (R.root j)) => P (f (P.symm x))) hroot
  simpa using ha.trans (hmid.trans hb.symm)

/-- A centralizer equation at the root yields the edge square after
transporting the root permutation to the two endpoint fibers. -/
private theorem conjugate_naturality
    {K S T : Type*} (Ps : K ≃ S) (Pt : K ≃ T) (Tst : S ≃ T)
    (a : Equiv.Perm K)
    (h : (((Ps.trans Tst).trans Pt.symm) : Equiv.Perm K) * a =
      a * (((Ps.trans Tst).trans Pt.symm) : Equiv.Perm K)) :
    Tst.trans ((Pt.symm.trans a).trans Pt) =
      ((Ps.symm.trans a).trans Ps).trans Tst := by
  apply Equiv.ext
  intro x
  have hx := congrArg (fun f : Equiv.Perm K => f (Ps.symm x)) h
  apply Pt.symm.injective
  simpa [Equiv.Perm.mul_def, Equiv.trans_apply] using hx.symm

/-- Recover the fiber permutation by transporting a centralizing root value. -/
def reconstructedFiber (R : RootedPaths Q) (a : D.RootCentralizers R)
    (v : Q.Vertex) : Equiv.Perm (D.Fiber v) :=
  let j := fixedFComponentMk Q v
  let P := D.rootTransport R j v rfl
  (P.symm.trans (a j).1).trans P

theorem reconstructedFiber_eq_at (R : RootedPaths Q)
    (a : D.RootCentralizers R) (j : FixedFComponent Q) (v : Q.Vertex)
    (hv : fixedFComponentMk Q v = j) :
    D.reconstructedFiber R a v =
      ((D.rootTransport R j v hv).symm.trans (a j).1).trans
        (D.rootTransport R j v hv) := by
  cases hv
  rfl

/-- The recovered family satisfies A1 on each original named edge. -/
theorem reconstructed_edge_naturality (R : RootedPaths Q)
    (a : D.RootCentralizers R) (e : Q.Edge) :
    (D.edgeEquiv e).trans (D.reconstructedFiber R a (Q.target e)) =
      (D.reconstructedFiber R a (Q.source e)).trans (D.edgeEquiv e) := by
  let j := fixedFComponentMk Q (Q.source e)
  have ht : fixedFComponentMk Q (Q.target e) = j :=
    RootedPaths.target_component e
  let Ps := D.rootTransport R j (Q.source e) rfl
  let Pt := D.rootTransport R j (Q.target e) ht
  let rootA : Equiv.Perm (D.Fiber (R.root j)) := (a j).1
  have hm : D.edgeMonodromyAt R j e rfl ∈ D.holonomy R j :=
    D.edgeMonodromyAt_mem_holonomy R j e rfl
  have hc : D.edgeMonodromyAt R j e rfl * rootA =
      rootA * D.edgeMonodromyAt R j e rfl :=
    (Subgroup.mem_centralizer_iff.mp (a j).2) _ hm
  have h := conjugate_naturality Ps Pt (D.edgeEquiv e) rootA hc
  rw [D.reconstructedFiber_eq_at R a j (Q.target e) ht]
  rw [D.reconstructedFiber_eq_at R a j (Q.source e) rfl]
  simpa [Ps, Pt, rootA] using h

/-- Reconstruct the A1 vertical lift from the simultaneous root centralizers. -/
def reconstructVertical (R : RootedPaths Q) (a : D.RootCentralizers R) :
    D.Lift (1 : FixedFGraphAutomorphism Q) where
  fiber := D.reconstructedFiber R a
  edge_naturality := by
    intro e x
    have h := congrArg
      (fun f : D.Fiber (Q.source e) ≃ D.Fiber (Q.target e) => f x)
      (D.reconstructed_edge_naturality R a e)
    simpa [renamedEdgeEquiv, Equiv.trans_apply] using h

/-- Evaluation at roots recovers exactly the prescribed centralizers. -/
theorem verticalRootEvaluation_reconstruct (R : RootedPaths Q)
    (a : D.RootCentralizers R) :
    D.verticalRootEvaluation R (D.reconstructVertical R a) = a := by
  funext j
  apply Subtype.ext
  change D.reconstructedFiber R a (R.root j) = (a j).1
  rw [D.reconstructedFiber_eq_at R a j (R.root j) (R.root_component j)]
  apply Equiv.ext
  intro x
  simp [rootTransport, R.path_root]

/-- Reconstruction also recovers every fiber of the original vertical lift. -/
theorem reconstructVertical_evaluation (R : RootedPaths Q)
    (a : D.Lift (1 : FixedFGraphAutomorphism Q)) :
    D.reconstructVertical R (D.verticalRootEvaluation R a) = a := by
  apply D.verticalRootEvaluation_injective R
  exact D.verticalRootEvaluation_reconstruct R _

/-- The vertical A1 solutions are classified by all root centralizers. -/
def verticalRootEquiv (R : RootedPaths Q) :
    D.Lift (1 : FixedFGraphAutomorphism Q) ≃ D.RootCentralizers R where
  toFun := D.verticalRootEvaluation R
  invFun := D.reconstructVertical R
  left_inv := D.reconstructVertical_evaluation R
  right_inv := D.verticalRootEvaluation_reconstruct R

/-- The actual subgroup of state changes with identity visible action. -/
def VerticalStateGroup : Subgroup D.StateChange :=
  (StateChange.projection (D := D)).ker

/-- A1 vertical lifts are the identity-visible actual state changes. -/
noncomputable def liftEquivVerticalStateGroup :
    D.Lift (1 : FixedFGraphAutomorphism Q) ≃ D.VerticalStateGroup :=
  D.liftEquivStateChangeOver 1

/-- The group on `Lift_F(1)` comes from actual state-change composition. -/
noncomputable instance : Group (D.Lift (1 : FixedFGraphAutomorphism Q)) :=
  (D.liftEquivVerticalStateGroup).group

/-- The group law above is isomorphic to the actual vertical state-change group. -/
noncomputable def liftMulEquivVerticalStateGroup :
    D.Lift (1 : FixedFGraphAutomorphism Q) ≃* D.VerticalStateGroup where
  toEquiv := D.liftEquivVerticalStateGroup
  map_mul' _ _ := (D.liftEquivVerticalStateGroup).apply_symm_apply _

/-- The transported group law is the actual pointwise A2 composition. -/
theorem vertical_mul_fiber_apply
    (a b : D.Lift (1 : FixedFGraphAutomorphism Q))
    (v : Q.Vertex) (x : D.Fiber v) :
    (a * b).fiber v x = a.fiber v (b.fiber v x) := by
  change (a.toStateChange * b.toStateChange).fiberTo v x = _
  simpa using a.comp_fiber_apply b v x

/-- B2: root evaluation is a group isomorphism to the product of
holonomy centralizers. -/
noncomputable def verticalRootMulEquiv (R : RootedPaths Q) :
    D.Lift (1 : FixedFGraphAutomorphism Q) ≃* D.RootCentralizers R where
  toEquiv := D.verticalRootEquiv R
  map_mul' a b := by
    funext j
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact D.vertical_mul_fiber_apply a b (R.root j) x

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.vertical_edge_naturality
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.vertical_transport_naturality
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.vertical_root_mem_centralizer
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.reconstructed_edge_naturality
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalRootEquiv
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.vertical_mul_fiber_apply
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalRootMulEquiv
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
