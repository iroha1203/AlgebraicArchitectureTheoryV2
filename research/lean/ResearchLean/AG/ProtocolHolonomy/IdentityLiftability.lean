import ResearchLean.AG.ProtocolHolonomy.IdentityTransport
import ResearchLean.AG.ProtocolHolonomy.LiftableVisible
import Formal.Util.AssertStandardAxioms

/-!
# The arbitrary finite identity-operation A input and its visible image

The path equations and selected visible subgroup remain the original A
inputs. Identity named-edge actions satisfy every equation automatically;
no change of the authored path relation or visible group is needed.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- The original finite protocol input specialized to identity operations,
for any finite named graph, common finite fiber, equations and admissible
visible subgroup. -/
def identityFiniteProtocolInput
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    [Finite Q.Vertex] [Finite Q.Edge] [Finite K]
    (eqs : PathEquations Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (hH : ∀ g, g ∈ H → eqs.PreservesGenerators g) :
    FiniteProtocolInput.{u, v, w} Q where
  data := identityReversibleData Q K
  finiteVertex := inferInstance
  finiteEdge := inferInstance
  finiteFiber := fun _ => show Finite K from inferInstance
  equations := eqs
  satisfies := by
    intro r
    change (identityReversibleData Q K).transport
        (positiveToSigned Q (eqs.left r)) =
      (identityReversibleData Q K).transport
        (positiveToSigned Q (eqs.right r))
    rw [identity_transport, identity_transport]
  H := H
  renaming_preserves := hH

/-- Every original visible graph automorphism has a literal identity
fiberwise A1 lift in the identity-operation system. -/
def identityLift
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (g : FixedFGraphAutomorphism Q) :
    (identityReversibleData Q K).Lift g where
  fiber := fun _ => Equiv.refl K
  edge_naturality := by
    intro e x
    rfl

/-- The original C3 visible image is all of the supplied H for identity
operations, with no restriction to particular equations or components. -/
theorem identity_liftableVisible_eq_top
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    (identityReversibleData Q K).LiftableVisible H = ⊤ := by
  ext g
  constructor
  · intro _
    trivial
  · intro _
    exact ((identityReversibleData Q K).mem_liftableVisible_iff_lift H g).2
      ⟨identityLift Q K g.1⟩

/-- The same equality is attached to the complete finite A-side input,
including arbitrary admissible path equations and visible subgroup. -/
theorem identityFiniteProtocolInput_liftableVisible_eq_top
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    [Finite Q.Vertex] [Finite Q.Edge] [Finite K]
    (eqs : PathEquations Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (hH : ∀ g, g ∈ H → eqs.PreservesGenerators g) :
    (identityFiniteProtocolInput Q K eqs H hH).data.LiftableVisible H = ⊤ :=
  identity_liftableVisible_eq_top Q K H

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityFiniteProtocolInput
#print axioms AAT.AG.ProtocolHolonomy.identityLift
#print axioms AAT.AG.ProtocolHolonomy.identity_liftableVisible_eq_top
#print axioms AAT.AG.ProtocolHolonomy.identityFiniteProtocolInput_liftableVisible_eq_top
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
