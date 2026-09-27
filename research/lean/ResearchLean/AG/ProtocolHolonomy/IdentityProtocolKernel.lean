import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolCompatibility
import Formal.Util.AssertStandardAxioms

/-!
# Literal kernel comparison for identity FixedF operations

The direct group isomorphism restricts to the literal kernels of the two
independently defined visible projections.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

/-- The actual-change kernel and the independent protocol kernel consist of
the same changes under the direct group isomorphism. -/
noncomputable def identityProtocolKernelMulEquiv :
    MonoidHom.ker (ReversibleData.ChangeGroup.projection
      (D := identityReversibleData Q K) (H := H)) ≃*
    MonoidHom.ker (ProtocolChangeGroup.projection (K := K) (H := H)) where
  toFun a := ⟨identityChangeMulEquivProtocol a.1, by
    rw [MonoidHom.mem_ker, identityProtocol_projection,
      MonoidHom.mem_ker.mp a.2]⟩
  invFun b := ⟨identityChangeMulEquivProtocol.symm b.1, by
    rw [MonoidHom.mem_ker]
    have h := identityProtocol_projection
      (identityChangeMulEquivProtocol.symm b.1)
    rw [identityChangeMulEquivProtocol.apply_symm_apply] at h
    exact h.symm.trans (MonoidHom.mem_ker.mp b.2)⟩
  left_inv a := by
    apply Subtype.ext
    exact identityChangeMulEquivProtocol.symm_apply_apply a.1
  right_inv b := by
    apply Subtype.ext
    exact identityChangeMulEquivProtocol.apply_symm_apply b.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul identityChangeMulEquivProtocol a.1 b.1

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityProtocolKernelMulEquiv
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
