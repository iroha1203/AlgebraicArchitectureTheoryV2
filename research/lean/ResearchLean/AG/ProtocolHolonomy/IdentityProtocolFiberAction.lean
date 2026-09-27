import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolVertical
import Formal.Util.AssertStandardAxioms

/-!
# Direct comparison of original and protocol right fiber actions

The original A1 lift fiber over every visible automorphism maps into the
literal fiber of the independently defined FixedF protocol projection.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

/-- The original A1 lift appears as an element of the literal independent
protocol projection fiber, preserving the whole visible automorphism. -/
noncomputable def identityLiftToProtocolFiber (g : H)
    (a : (identityReversibleData Q K).Lift g.1) :
    ProtocolChangeGroup.ProjectionFiber (K := K) g :=
  ⟨identityChangeMulEquivProtocol
    ⟨a.toStateChange, g.2⟩, rfl⟩

/-- Both right actions are literal composition with the same vertical map. -/
theorem identityLiftToProtocolFiber_action (g : H)
    (a : (identityReversibleData Q K).Lift g.1)
    (α : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q)) :
    identityLiftToProtocolFiber (Q := Q) (K := K) g
      (identityRightAction Q K H g a α) =
    (MulOpposite.op
      (identityVerticalProtocolKernelMulEquiv (H := H) α)) •
      identityLiftToProtocolFiber (Q := Q) (K := K) g a := by
  apply Subtype.ext
  apply ProtocolChangeGroup.ext
  · rfl
  · funext v
    apply Equiv.ext
    intro x
    change (identityRightAction Q K H g a α).fiber v x =
      a.fiber v (α.fiber v x)
    exact (identityReversibleData Q K).verticalRightAction_fiber_apply
      H (identityLiftableVisible Q K H g) a α v x

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityLiftToProtocolFiber
#print axioms AAT.AG.ProtocolHolonomy.identityLiftToProtocolFiber_action
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
