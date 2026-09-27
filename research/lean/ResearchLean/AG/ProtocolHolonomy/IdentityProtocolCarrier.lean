import ResearchLean.AG.ProtocolHolonomy.IdentityFiberTorsor
import ResearchLean.AG.RealizationReconstruction.FixedFProtocolGroupConnection
import Formal.Util.AssertStandardAxioms

/-!
# Identity operations and the independently defined FixedF protocol group

For the no-equation schema, both constructions retain the same original
graph automorphism, named edges and vertexwise state equivalences. This
file first fixes the direct carrier correspondence and its readback.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

/-- Read an original actual identity-operation change as an independently
defined FixedF protocol change, retaining every original vertex map. -/
noncomputable def identityChangeToProtocol
    (c : (identityReversibleData Q K).ChangeGroup H) :
    ProtocolChangeGroup (F := Q) (K := K) H where
  visible := ReversibleData.ChangeGroup.projection c
  stateEquiv := c.1.toLift.fiber
  edge_naturality := by
    intro source target edge state
    rcases edge with ⟨e, hs, ht⟩
    cases hs
    cases ht
    have h := c.1.toLift.edge_naturality e state
    simpa [FixedFProtocolConnection.realization_edgeAction,
      ReversibleData.renamedEdgeEquiv, identityReversibleData] using h
  observation_naturality := by intros; rfl

/-- Recover the original A1 lift and actual change group member from an
independent FixedF protocol change, using its named-edge squares. -/
def identityProtocolToChange
    (c : ProtocolChangeGroup (F := Q) (K := K) H) :
    (identityReversibleData Q K).ChangeGroup H := by
  let a : (identityReversibleData Q K).Lift c.visible.1 :=
    { fiber := c.stateEquiv
      edge_naturality := by
        intro e x
        have h := c.edge_naturality
          (FixedFProtocolConnection.typedEdge Q e) x
        simpa [FixedFProtocolConnection.realization_edgeAction,
          ReversibleData.renamedEdgeEquiv, identityReversibleData] using h }
  exact ⟨a.toStateChange, c.visible.2⟩

/-- The direct correspondence is a full carrier equivalence. -/
noncomputable def identityChangeEquivProtocol :
    (identityReversibleData Q K).ChangeGroup H ≃
      ProtocolChangeGroup (F := Q) (K := K) H where
  toFun := identityChangeToProtocol
  invFun := identityProtocolToChange
  left_inv c := by
    apply Subtype.ext
    apply ReversibleData.StateChange.ext
    · rfl
    · apply Equiv.ext
      rintro ⟨v, x⟩
      change (⟨c.1.visible.vertex v, c.1.fiberTo v x⟩ :
        Σ z, (identityReversibleData Q K).Fiber z) = c.1.state ⟨v, x⟩
      exact (c.1.state_eq_mk v x).symm
  right_inv c := by
    apply ProtocolChangeGroup.ext
    · rfl
    · funext v
      apply Equiv.ext
      intro x
      rfl

/-- The correspondence retains the original visible vertex and named-edge
automorphism, as an element of exactly the supplied H. -/
theorem identityChangeEquivProtocol_visible
    (c : (identityReversibleData Q K).ChangeGroup H) :
    (identityChangeEquivProtocol c).visible =
      ReversibleData.ChangeGroup.projection c := rfl

/-- The independent protocol state adapter reads the original total-state
change at every vertex and hidden state. -/
theorem identityChangeEquivProtocol_state
    (c : (identityReversibleData Q K).ChangeGroup H)
    (v : Q.Vertex) (x : K) :
    c.1.state ⟨v, x⟩ =
      ⟨c.1.visible.vertex v,
        (identityChangeEquivProtocol c).stateEquiv v x⟩ :=
  c.1.state_eq_mk v x

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityChangeToProtocol
#print axioms AAT.AG.ProtocolHolonomy.identityProtocolToChange
#print axioms AAT.AG.ProtocolHolonomy.identityChangeEquivProtocol
#print axioms AAT.AG.ProtocolHolonomy.identityChangeEquivProtocol_visible
#print axioms AAT.AG.ProtocolHolonomy.identityChangeEquivProtocol_state
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
