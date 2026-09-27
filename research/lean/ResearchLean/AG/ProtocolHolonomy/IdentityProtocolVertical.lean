import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolKernel
import Formal.Util.AssertStandardAxioms

/-!
# Original vertical A1 lifts inside the independent protocol kernel

This map starts from the original C3 vertical group and its actual inclusion,
then uses the direct literal-kernel comparison. Its state readback is the
original fiber map at every vertex.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

private noncomputable def originalVerticalToActualKernel :
    (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q) →*
    MonoidHom.ker (ReversibleData.ChangeGroup.projection
      (D := identityReversibleData Q K) (H := H)) where
  toFun a := ⟨(identityReversibleData Q K).verticalLiftInclusion H a, by
    have h := ((identityReversibleData Q K).verticalLiftEquivLiftableKernel H a).2
    rw [← (identityReversibleData Q K).projectionToLiftable_ker H]
    exact h⟩
  map_one' := by
    apply Subtype.ext
    exact map_one ((identityReversibleData Q K).verticalLiftInclusion H)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul ((identityReversibleData Q K).verticalLiftInclusion H) a b

/-- The original vertical inclusion lands in the literal independent protocol
kernel, with the original group multiplication. -/
noncomputable def identityVerticalToProtocolKernel :
    (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q) →*
    MonoidHom.ker (ProtocolChangeGroup.projection (K := K) (H := H)) :=
  identityProtocolKernelMulEquiv.toMonoidHom.comp originalVerticalToActualKernel

/-- Protocol kernel readback is exactly the original vertical A1 fiber map. -/
theorem identityVerticalToProtocolKernel_fiber
    (a : (identityReversibleData Q K).Lift (1 : FixedFGraphAutomorphism Q))
    (v : Q.Vertex) (x : K) :
    ((identityVerticalToProtocolKernel (Q := Q) (K := K) (H := H) a).1.stateEquiv v) x =
      a.fiber v x := by
  rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityVerticalToProtocolKernel
#print axioms AAT.AG.ProtocolHolonomy.identityVerticalToProtocolKernel_fiber
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
