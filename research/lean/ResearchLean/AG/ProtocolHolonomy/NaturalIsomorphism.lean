import ResearchLean.AG.ProtocolHolonomy.VisibleRename
import ResearchLean.AG.RealizationReconstruction.ProtocolReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Original A1 lifts and independent semantic natural isomorphisms

The semantic target is formed by renaming quotient executions using the
original visible graph automorphism, then interpreting them by the original
reversible protocol realization. Vertex components retain the original A1
fiber equivalences.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction CategoryTheory

universe u v w

namespace FiniteProtocolInput

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (P : FiniteProtocolInput.{u, v, w} Q)
  (g : FixedFGraphAutomorphism Q) (hg : g ∈ P.H)

/-- The original realization after the visible change renames every quotient
execution. The observation is again the specified one-point observation. -/
def renamedRealization : ProtocolRealization P.schema P.singletonObservation where
  toFunctor := P.renameExecutionFunctor g hg ⋙ P.executionFunctor
  state_finite := by
    intro x
    change Finite (P.schemaFiber ((P.renamePrefunctor g).obj x))
    infer_instance
  observation :=
    { app := fun _ _ => ULift.up ()
      naturality := by intros; rfl }

/-- The renamed semantic action of an original named operation is the
original action of its renamed named edge. -/
theorem renamed_edgeAction_down {s t : Q.Vertex}
    (e : TypedEdge Q s t) (x : P.data.Fiber (g.vertex s)) :
    ((P.renamedRealization g hg).edgeAction
      (ULift.up e : P.schema.Edge (ULift.up s) (ULift.up t))
        (ULift.up x)).down =
      P.data.typedEdgeEquiv (renameTypedEdge g e) x := by
  rfl

/-- A genuine A1 lift supplies the vertex generator maps for the independent
semantic realization. Naturality on every quotient execution is then built
by the existing `ProtocolRealization.ext`. -/
def liftGeneratorMap (a : P.data.Lift g) :
    ProtocolRealization.GeneratorMap P.realization
      (P.renamedRealization g hg) where
  component x y := ULift.up (a.fiber x.down y.down)
  edge_naturality := by
    intro x y e
    funext z
    cases x with
    | up s =>
      cases y with
      | up t =>
        cases e with
        | up f =>
          cases z with
          | up k =>
            rcases f with ⟨named, hs, ht⟩
            cases hs
            cases ht
            apply ULift.down_injective
            exact a.edge_naturality named k
  observation_naturality := by
    intro x
    funext y
    rfl

/-- The A1 lift extends from all named generators to a genuine morphism
natural along every quotient execution. -/
def liftHom (a : P.data.Lift g) :
    P.realization ⟶ P.renamedRealization g hg :=
  ProtocolRealization.ext (P.liftGeneratorMap g hg a)

/-- Inverses of the original A1 fiber equivalences satisfy every renamed
generator square in the reverse direction. -/
def liftInverseGeneratorMap (a : P.data.Lift g) :
    ProtocolRealization.GeneratorMap (P.renamedRealization g hg)
      P.realization where
  component x y := ULift.up ((a.fiber x.down).symm y.down)
  edge_naturality := by
    intro x y e
    funext z
    cases x with
    | up s =>
      cases y with
      | up t =>
        cases e with
        | up f =>
          cases z with
          | up k =>
            rcases f with ⟨named, hs, ht⟩
            cases hs
            cases ht
            apply ULift.down_injective
            apply (a.fiber (Q.target named)).injective
            simpa [ReversibleData.renamedEdgeEquiv, Equiv.trans_apply]
              using (a.edge_naturality named
                ((a.fiber (Q.source named)).symm k)).symm
  observation_naturality := by
    intro x
    funext y
    rfl

/-- An original A1 lift determines an isomorphism of independent protocol
realizations, natural along every quotient execution. -/
def liftIso (a : P.data.Lift g) :
    P.realization ≅ P.renamedRealization g hg where
  hom := P.liftHom g hg a
  inv := ProtocolRealization.ext (P.liftInverseGeneratorMap g hg a)
  hom_inv_id := by
    apply ProtocolRealization.Hom.ext
    ext x y
    cases x with
    | mk z =>
      cases y with
      | up k =>
        change (ULift.up ((a.fiber z.down).symm (a.fiber z.down k)) :
          P.schemaFiber z) = ULift.up k
        simp
  inv_hom_id := by
    apply ProtocolRealization.Hom.ext
    ext x y
    cases x with
    | mk z =>
      cases y with
      | up k =>
        change (ULift.up (a.fiber z.down ((a.fiber z.down).symm k)) :
          P.schemaFiber ((P.renamePrefunctor g).obj z)) = ULift.up k
        simp

/-- Read the original vertexwise equivalence from a genuine isomorphism
of the two independent protocol realizations. -/
def isoFiber (i : P.realization ≅ P.renamedRealization g hg)
    (s : Q.Vertex) : P.data.Fiber s ≃ P.data.Fiber (g.vertex s) where
  toFun x := (i.hom.toNatTrans.app (P.schema.vertexObject (ULift.up s))
    (ULift.up x)).down
  invFun y := (i.inv.toNatTrans.app (P.schema.vertexObject (ULift.up s))
    (ULift.up y)).down
  left_inv := by
    intro x
    have h := congrArg (fun f : P.realization ⟶ P.realization =>
      f.toNatTrans.app (P.schema.vertexObject (ULift.up s)) (ULift.up x))
      i.hom_inv_id
    exact congrArg ULift.down h
  right_inv := by
    intro y
    have h := congrArg (fun f : P.renamedRealization g hg ⟶
        P.renamedRealization g hg =>
      f.toNatTrans.app (P.schema.vertexObject (ULift.up s)) (ULift.up y))
      i.inv_hom_id
    exact congrArg ULift.down h

/-- Any semantic natural isomorphism restricts to the original A1
operation-preserving lift on all named edges. -/
def isoToLift (i : P.realization ≅ P.renamedRealization g hg) :
    P.data.Lift g where
  fiber := P.isoFiber g hg i
  edge_naturality := by
    intro e x
    let f : TypedEdge Q (Q.source e) (Q.target e) := ⟨e, rfl, rfl⟩
    have h := ProtocolRealization.edge_naturality i.hom
      (ULift.up f : P.schema.Edge
        (ULift.up (Q.source e)) (ULift.up (Q.target e)))
    have hx := congrFun h (ULift.up x)
    change i.hom.toNatTrans.app (P.schema.vertexObject (ULift.up (Q.target e)))
        (P.realization.edgeAction (ULift.up f) (ULift.up x)) =
      (P.renamedRealization g hg).edgeAction (ULift.up f)
        (i.hom.toNatTrans.app (P.schema.vertexObject (ULift.up (Q.source e)))
          (ULift.up x)) at hx
    have hd := congrArg
      (fun y : (P.renamedRealization g hg).State (ULift.up (Q.target e)) =>
        y.down) hx
    exact hd

/-- The semantic isomorphism associated to a lift retains each original
fiber equivalence. -/
theorem isoToLift_liftIso (a : P.data.Lift g) :
    P.isoToLift g hg (P.liftIso g hg a) = a := by
  apply ReversibleData.Lift.ext
  intro s x
  rfl

/-- Every independent semantic isomorphism is recovered from its original
vertexwise A1 lift, including all quotient-execution naturality. -/
theorem liftIso_isoToLift
    (i : P.realization ≅ P.renamedRealization g hg) :
    P.liftIso g hg (P.isoToLift g hg i) = i := by
  apply Iso.ext
  apply ProtocolRealization.Hom.ext
  ext q x
  cases q with
  | mk z =>
    cases z with
    | up s =>
      cases x with
      | up y =>
        rfl

/-- A1 lifts are exactly the natural isomorphisms of the independently
constructed quotient execution realizations. -/
def liftEquivSemanticIso :
    P.data.Lift g ≃ (P.realization ≅ P.renamedRealization g hg) where
  toFun := P.liftIso g hg
  invFun := P.isoToLift g hg
  left_inv := P.isoToLift_liftIso g hg
  right_inv := P.liftIso_isoToLift g hg

end FiniteProtocolInput
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renamedRealization
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftGeneratorMap
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftHom
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftInverseGeneratorMap
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftIso
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.isoFiber
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.isoToLift
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftEquivSemanticIso
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
