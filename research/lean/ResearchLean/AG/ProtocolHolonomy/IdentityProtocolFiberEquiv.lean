import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolFiberAction
import Formal.Util.AssertStandardAxioms

/-!
# Full original-to-independent protocol projection fibers

For every supplied visible automorphism, the original A1 lifts and the
independent FixedF protocol projection fiber correspond in both directions.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

private noncomputable def protocolFiberToIdentityLift (g : H)
    (b : ProtocolChangeGroup.ProjectionFiber (K := K) g) :
    (identityReversibleData Q K).Lift g.1 := by
  let c := identityProtocolToChange b.1
  have h : c.1.visible = g.1 := by
    exact congrArg Subtype.val b.2
  exact h ▸ c.1.toLift

/-- The direct carrier correspondence restricts to every literal projection
fiber, preserving each original A1 lift and every protocol change. -/
noncomputable def identityLiftEquivProtocolFiber (g : H) :
    (identityReversibleData Q K).Lift g.1 ≃
      ProtocolChangeGroup.ProjectionFiber (K := K) g where
  toFun := identityLiftToProtocolFiber (Q := Q) (K := K) g
  invFun := protocolFiberToIdentityLift g
  left_inv a := by
    apply ReversibleData.Lift.ext
    intro v x
    rfl
  right_inv b := by
    rcases b with ⟨b, hb⟩
    change b.visible = g at hb
    cases hb
    apply Subtype.ext
    apply ProtocolChangeGroup.ext
    · rfl
    · funext v
      apply Equiv.ext
      intro x
      rfl

/-- Read back the original lift's state map from the independent fiber. -/
theorem identityLiftEquivProtocolFiber_state (g : H)
    (a : (identityReversibleData Q K).Lift g.1)
    (v : Q.Vertex) (x : K) :
    (identityLiftEquivProtocolFiber g a).1.stateEquiv v x =
      a.fiber v x := rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityLiftEquivProtocolFiber
#print axioms AAT.AG.ProtocolHolonomy.identityLiftEquivProtocolFiber_state
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
