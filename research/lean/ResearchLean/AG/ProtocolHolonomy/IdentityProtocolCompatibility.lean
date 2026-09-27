import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolGroup
import Formal.Util.AssertStandardAxioms

/-!
# Projection and section compatibility in the identity FixedF comparison

The direct group isomorphism commutes with the two independently defined
visible projections and takes the actual identity-hidden section to the
canonical FixedF protocol section.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolGroupConnection

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {H : Subgroup (FixedFGraphAutomorphism Q)}

/-- Both independent projections return exactly the same original H element. -/
theorem identityProtocol_projection (c : (identityReversibleData Q K).ChangeGroup H) :
    ProtocolChangeGroup.projection
      (identityChangeMulEquivProtocol c) =
      ReversibleData.ChangeGroup.projection c := rfl

/-- The original actual section corresponds to the protocol section at every
visible automorphism, including the names of its operations. -/
theorem identityProtocol_section (g : H) :
    identityChangeMulEquivProtocol (identitySection Q K H g) =
      ProtocolChangeGroup.canonicalSection (K := K) g := by
  apply ProtocolChangeGroup.ext
  · rfl
  · funext v
    apply Equiv.ext
    intro x
    rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityProtocol_projection
#print axioms AAT.AG.ProtocolHolonomy.identityProtocol_section
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
