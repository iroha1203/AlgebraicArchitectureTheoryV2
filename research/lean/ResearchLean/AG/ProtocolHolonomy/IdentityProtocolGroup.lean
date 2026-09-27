import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolCarrier
import Formal.Util.AssertStandardAxioms

/-!
# Identity operation changes as the FixedF protocol group

The direct carrier correspondence preserves actual composition. The visible
automorphism includes the original named-edge permutation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

/-- Actual identity-operation changes and independently defined protocol
changes have the same group law, including the original visible action. -/
noncomputable def identityChangeMulEquivProtocol :
    (identityReversibleData Q K).ChangeGroup H ≃*
      ProtocolChangeGroup (F := Q) (K := K) H where
  toEquiv := identityChangeEquivProtocol
  map_mul' a b := by
    apply ProtocolChangeGroup.ext
    · rfl
    · funext v
      apply Equiv.ext
      intro x
      change ((a.1 * b.1).toLift).fiber v x =
        a.1.toLift.fiber (b.1.visible.vertex v) (b.1.toLift.fiber v x)
      have h := (a.1.toLift).comp_fiber_apply (b.1.toLift) v x
      change ((a.1.toLift.toStateChange * b.1.toLift.toStateChange).toLift).fiber v x = _ at h
      rw [a.1.toStateChange_toLift, b.1.toStateChange_toLift] at h
      exact h

/-- The group isomorphism preserves the supplied subgroup element itself. -/
theorem identityChangeMulEquivProtocol_visible
    (c : (identityReversibleData Q K).ChangeGroup H) :
    (identityChangeMulEquivProtocol c).visible =
      ReversibleData.ChangeGroup.projection c := rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityChangeMulEquivProtocol
#print axioms AAT.AG.ProtocolHolonomy.identityChangeMulEquivProtocol_visible
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
