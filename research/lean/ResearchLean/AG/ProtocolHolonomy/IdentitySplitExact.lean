import ResearchLean.AG.ProtocolHolonomy.IdentityComponentGroup
import ResearchLean.AG.ProtocolHolonomy.IdentitySection
import Formal.Util.AssertStandardAxioms

/-!
# Split short exact sequence of the original identity-operation changes

The left map is the C3 inclusion of the original vertical A1 group into
actual named-operation-preserving changes. The right map is the original
visible projection to the supplied H. The identity-hidden section splits it.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.ComparisonInformationLoss

universe u v w

/-- Identity operations give the original C3 sequence with codomain all of
H, rather than only the liftable-visible image. -/
theorem identity_shortExact
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    IsGroupShortExact
      ((identityReversibleData Q K).verticalLiftInclusion H)
      (ReversibleData.ChangeGroup.projection
        (D := identityReversibleData Q K) (H := H)) := by
  let D := identityReversibleData Q K
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    exact (D.verticalLiftEquivLiftableKernel H).injective
      (Subtype.val_injective h)
  · rw [MonoidHom.mulExact_iff]
    rw [← D.projectionToLiftable_ker H]
    apply le_antisymm
    · intro c hc
      let k : (D.projectionToLiftable H).ker := ⟨c, hc⟩
      refine ⟨(D.verticalLiftEquivLiftableKernel H).symm k, ?_⟩
      change ((D.verticalLiftEquivLiftableKernel H)
        ((D.verticalLiftEquivLiftableKernel H).symm k)).1 = c
      exact congrArg Subtype.val
        ((D.verticalLiftEquivLiftableKernel H).apply_symm_apply k)
    · rintro c ⟨a, ha⟩
      rw [← ha]
      exact (D.verticalLiftEquivLiftableKernel H a).2
  · intro g
    exact ⟨identitySection Q K H g,
      identitySection_rightInverse Q K H g⟩

/-- The split is explicitly by the same original identity-hidden section. -/
theorem identity_shortExact_section
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    IsGroupShortExact
      ((identityReversibleData Q K).verticalLiftInclusion H)
      (ReversibleData.ChangeGroup.projection
        (D := identityReversibleData Q K) (H := H)) ∧
    Function.RightInverse
      (identitySection Q K H)
      (ReversibleData.ChangeGroup.projection
        (D := identityReversibleData Q K) (H := H)) :=
  ⟨identity_shortExact Q K H, identitySection_rightInverse Q K H⟩

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identity_shortExact
#print axioms AAT.AG.ProtocolHolonomy.identity_shortExact_section
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
