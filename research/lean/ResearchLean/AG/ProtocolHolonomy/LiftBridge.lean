import ResearchLean.AG.ProtocolHolonomy.ChangeGroup
import Mathlib.Algebra.Group.TransferInstance
import Formal.Util.AssertStandardAxioms

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  {D : ReversibleData.{u, v, w} Q}
  {g : FixedFGraphAutomorphism Q}

/-- A named edge has one output for each fixed input state. -/
theorem namedExecution_functional {e : Q.Edge}
    {p q r : Σ x, D.Fiber x}
    (hq : D.NamedExecution e p q)
    (hr : D.NamedExecution e p r) : q = r := by
  rcases hq with ⟨x, rfl, rfl⟩
  rcases hr with ⟨y, hp, hr⟩
  have hxy : x = y := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  subst y
  exact hr.symm

namespace Lift

/-- A lift carries one named execution to the renamed named execution. -/
theorem maps_namedExecution (a : D.Lift g)
    (e : Q.Edge) (x : D.Fiber (Q.source e)) :
    D.NamedExecution (g.edge e)
      (a.stateEquiv ⟨Q.source e, x⟩)
      (a.stateEquiv ⟨Q.target e, D.edgeEquiv e x⟩) := by
  refine ⟨Equiv.cast (congrArg D.Fiber (g.source_rename e).symm)
    (a.fiber (Q.source e) x), ?_, ?_⟩
  · simp [stateEquiv_apply, g.source_rename, Equiv.cast]
  · simp [stateEquiv_apply, a.edge_naturality e x,
      ReversibleData.renamedEdgeEquiv]
    exact (g.target_rename e).symm

/-- The fiberwise edge square is equivalent to preserving the named execution
relation under the induced total-state equivalence. -/
theorem preserves_namedExecution (a : D.Lift g)
    (e : Q.Edge) (p q : Σ x, D.Fiber x) :
    D.NamedExecution e p q ↔
      D.NamedExecution (g.edge e) (a.stateEquiv p) (a.stateEquiv q) := by
  constructor
  · rintro ⟨x, rfl, rfl⟩
    exact a.maps_namedExecution e x
  · intro h
    rcases p with ⟨v, x⟩
    have hp : (a.stateEquiv ⟨v, x⟩).1 = Q.source (g.edge e) := by
      rcases h with ⟨y, hp, _⟩
      exact congrArg Sigma.fst hp
    have hv : v = Q.source e := g.vertex.injective (by
      calc
        g.vertex v = (a.stateEquiv ⟨v, x⟩).1 :=
          (a.stateEquiv_observation v x).symm
        _ = Q.source (g.edge e) := hp
        _ = g.vertex (Q.source e) := g.source_rename e)
    subst v
    refine ⟨x, rfl, ?_⟩
    have hm := a.maps_namedExecution e x
    exact a.stateEquiv.injective (namedExecution_functional h hm)

/-- Turn a fiberwise lift into an actual operation-preserving state change. -/
def toStateChange (a : D.Lift g) : D.StateChange where
  visible := g
  state := a.stateEquiv
  observation := by
    rintro ⟨v, x⟩
    exact a.stateEquiv_observation v x
  preserves := a.preserves_namedExecution

end Lift

namespace StateChange

/-- The state map of an actual change, restricted to one source fiber. -/
def fiberTo (c : D.StateChange) (v : Q.Vertex) (x : D.Fiber v) :
    D.Fiber (c.visible.vertex v) :=
  Eq.mp (congrArg D.Fiber (c.observation ⟨v, x⟩))
    (c.state ⟨v, x⟩).2

theorem state_eq_mk (c : D.StateChange)
    (v : Q.Vertex) (x : D.Fiber v) :
    c.state ⟨v, x⟩ = ⟨c.visible.vertex v, c.fiberTo v x⟩ := by
  apply Sigma.ext (c.observation ⟨v, x⟩)
  exact (cast_heq (congrArg D.Fiber (c.observation ⟨v, x⟩))
    (c.state ⟨v, x⟩).2).symm

theorem fiberTo_injective (c : D.StateChange) (v : Q.Vertex) :
    Function.Injective (c.fiberTo v) := by
  intro x y h
  apply (Sigma.mk.inj_iff.mp (c.state.injective (by
    rw [c.state_eq_mk, c.state_eq_mk, h]))).2 |> eq_of_heq

theorem fiberTo_surjective (c : D.StateChange) (v : Q.Vertex) :
    Function.Surjective (c.fiberTo v) := by
  intro y
  obtain ⟨⟨w, x⟩, h⟩ := c.state.surjective
    (⟨c.visible.vertex v, y⟩ : Σ z, D.Fiber z)
  have hw : w = v := c.visible.vertex.injective (by
    calc
      c.visible.vertex w = (c.state ⟨w, x⟩).1 :=
        (c.observation ⟨w, x⟩).symm
      _ = c.visible.vertex v := congrArg Sigma.fst h)
  subst w
  refine ⟨x, ?_⟩
  have hh := h
  rw [c.state_eq_mk] at hh
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

/-- Recover the fiber equivalence from the actual total-state equivalence. -/
noncomputable def fiberEquiv (c : D.StateChange) (v : Q.Vertex) :
    D.Fiber v ≃ D.Fiber (c.visible.vertex v) :=
  Equiv.ofBijective (c.fiberTo v)
    ⟨c.fiberTo_injective v, c.fiberTo_surjective v⟩

/-- Recover the fiberwise named-edge square from preservation of the actual
named execution graph. -/
theorem fiberEquiv_naturality (c : D.StateChange)
    (e : Q.Edge) (x : D.Fiber (Q.source e)) :
    c.fiberEquiv (Q.target e) (D.edgeEquiv e x) =
      D.renamedEdgeEquiv c.visible e (c.fiberEquiv (Q.source e) x) := by
  have h := (c.preserves e
    ⟨Q.source e, x⟩ ⟨Q.target e, D.edgeEquiv e x⟩).mp
      ⟨x, rfl, rfl⟩
  rcases h with ⟨y, hs, ht⟩
  change c.fiberTo (Q.target e) (D.edgeEquiv e x) =
    D.renamedEdgeEquiv c.visible e (c.fiberTo (Q.source e) x)
  rw [c.state_eq_mk] at hs ht
  have hy :
      Equiv.cast (congrArg D.Fiber (c.visible.source_rename e).symm)
        (c.fiberTo (Q.source e) x) = y :=
    eq_of_heq ((cast_heq _ _).trans (Sigma.mk.inj_iff.mp hs).2)
  have hz :
      c.fiberTo (Q.target e) (D.edgeEquiv e x) =
        Equiv.cast (congrArg D.Fiber (c.visible.target_rename e))
          (D.edgeEquiv (c.visible.edge e) y) :=
    eq_of_heq ((Sigma.mk.inj_iff.mp ht).2.trans (cast_heq _ _).symm)
  rw [hz, ← hy]
  rfl

/-- Recover a fiberwise lift from an actual state change. -/
noncomputable def toLift (c : D.StateChange) : D.Lift c.visible where
  fiber := c.fiberEquiv
  edge_naturality := c.fiberEquiv_naturality

theorem toStateChange_toLift (c : D.StateChange) :
    c.toLift.toStateChange = c := by
  apply StateChange.ext
  · rfl
  apply Equiv.ext
  rintro ⟨v, x⟩
  change (⟨c.visible.vertex v, c.fiberTo v x⟩ : Σ z, D.Fiber z) =
    c.state ⟨v, x⟩
  exact (c.state_eq_mk v x).symm

end StateChange

namespace Lift

theorem toLift_toStateChange (a : D.Lift g) :
    a.toStateChange.toLift = a := by
  apply Lift.ext
  intro v x
  rfl

end Lift

/-- Actual state changes over a fixed visible graph automorphism. -/
def StateChangeOver (g : FixedFGraphAutomorphism Q) :=
  {c : D.StateChange // c.visible = g}

/-- Fiberwise A1 solutions and actual changes over the same visible
automorphism are equivalent, preserving the total-state map. -/
noncomputable def liftEquivStateChangeOver
    (g : FixedFGraphAutomorphism Q) :
    D.Lift g ≃ D.StateChangeOver g where
  toFun a := ⟨a.toStateChange, rfl⟩
  invFun c := c.2 ▸ c.1.toLift
  left_inv a := by
    exact a.toLift_toStateChange
  right_inv c := by
    rcases c with ⟨c, h⟩
    dsimp at h ⊢
    cases h
    apply Subtype.ext
    exact c.toStateChange_toLift

namespace Lift

/-- Composition of lifts, obtained from composition of their actual changes. -/
noncomputable def comp
    {g₁ g₂ : FixedFGraphAutomorphism Q}
    (a : D.Lift g₁) (b : D.Lift g₂) : D.Lift (g₁ * g₂) :=
  (a.toStateChange * b.toStateChange).toLift

/-- The dependent fiber formula for the actual composition, matching A2. -/
theorem comp_fiber_apply
    {g₁ g₂ : FixedFGraphAutomorphism Q}
    (a : D.Lift g₁) (b : D.Lift g₂)
    (v : Q.Vertex) (x : D.Fiber v) :
    (a.comp b).fiber v x =
      a.fiber (g₂.vertex v) (b.fiber v x) := by
  change (a.toStateChange * b.toStateChange).fiberTo v x = _
  have h := (a.toStateChange * b.toStateChange).state_eq_mk v x
  change (a.stateEquiv (b.stateEquiv ⟨v, x⟩)) =
    (⟨(g₁ * g₂).vertex v,
      (a.toStateChange * b.toStateChange).fiberTo v x⟩ : Σ z, D.Fiber z) at h
  simpa only [stateEquiv_apply, FixedFGraphAutomorphism.mul_vertex]
    using eq_of_heq (Sigma.mk.inj_iff.mp h).2.symm

end Lift

/-- The set of all visible changes in `H` paired with their fiberwise lifts. -/
def LiftPair (H : Subgroup (FixedFGraphAutomorphism Q)) :=
  Σ g : H, D.Lift g.1

/-- The pairs `(u, φ)` are exactly the actual operation-preserving changes
whose visible component belongs to `H`. -/
noncomputable def liftPairEquivChangeGroup
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.LiftPair H ≃ D.ChangeGroup H where
  toFun p := ⟨p.2.toStateChange, p.1.2⟩
  invFun c := ⟨ChangeGroup.projection c, c.1.toLift⟩
  left_inv p := by
    rcases p with ⟨g, a⟩
    change (⟨g, a.toStateChange.toLift⟩ : D.LiftPair H) = ⟨g, a⟩
    rw [a.toLift_toStateChange]
  right_inv c := by
    apply Subtype.ext
    exact c.1.toStateChange_toLift

/-- The group law on the actual pairs `(u, φ)` is transported from the
already constructed group of total-state changes. -/
noncomputable instance (H : Subgroup (FixedFGraphAutomorphism Q)) :
    Group (D.LiftPair H) :=
  (D.liftPairEquivChangeGroup H).group

/-- The pair presentation and actual state-change presentation are isomorphic
as groups. -/
noncomputable def liftPairMulEquivChangeGroup
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.LiftPair H ≃* D.ChangeGroup H where
  toEquiv := D.liftPairEquivChangeGroup H
  map_mul' _ _ :=
    (D.liftPairEquivChangeGroup H).apply_symm_apply _

/-- The actual group law on pairs has the A2 fiber formula. -/
theorem liftPair_mul_fiber_apply
    {H : Subgroup (FixedFGraphAutomorphism Q)}
    (a b : D.LiftPair H) (v : Q.Vertex) (x : D.Fiber v) :
    (a * b).2.fiber v x =
      a.2.fiber (b.1.1.vertex v) (b.2.fiber v x) := by
  change (a.2.toStateChange * b.2.toStateChange).fiberTo v x = _
  exact a.2.comp_fiber_apply b.2 v x

/-- Visible projection of the pair presentation. -/
noncomputable def liftPairProjection
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.LiftPair H →* H :=
  (ChangeGroup.projection (D := D) (H := H)).comp
    (D.liftPairMulEquivChangeGroup H).toMonoidHom

@[simp] theorem liftPairProjection_apply
    {H : Subgroup (FixedFGraphAutomorphism Q)}
    (a : D.LiftPair H) :
    D.liftPairProjection H a = a.1 := rfl

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftEquivStateChangeOver
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.comp_fiber_apply
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftPairEquivChangeGroup
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftPairMulEquivChangeGroup
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftPair_mul_fiber_apply
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftPairProjection
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
end ReversibleData
end AAT.AG.ProtocolHolonomy
