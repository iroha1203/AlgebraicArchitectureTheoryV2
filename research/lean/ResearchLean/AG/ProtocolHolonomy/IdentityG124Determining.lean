import ResearchLean.AG.ProtocolHolonomy.IdentityG124Extension
import Formal.Util.AssertStandardAxioms

/-!
# G-124 determining representatives for original identity A1 lifts

The accepted G-124 separation and coherent-extension statement transfers
across the direct equivalence of actual preserving changes with original A1
lifts, using the same finite representative set and the same vertex tables.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.LocalSemanticReconstruction

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]

omit [Finite Q.Edge] [Finite K] in
/-- G-124's exact finite representative set determines and extends the
original A1 lifts over every visible graph automorphism. `Nontrivial K` is
used only where the accepted G-124 determining theorem requires it. -/
theorem identityLift_representatives_determining [Nontrivial K]
    (g : FixedFGraphAutomorphism Q) :
    FiniteReading.Determining
      (fun (a : (identityReversibleData Q K).Lift g) v => a.fiber v)
      (CSFixedFDetermining.protocolRepresentativeSet Q)
      (FinitePermutationReadingCriteria.EdgeCoherent Q K
        (CSFixedFDetermining.protocolRepresentativeSet Q)) := by
  obtain ⟨hsep, hext⟩ :=
    CSFixedFDetermining.protocol_representatives_determining (K := K) Q g
  constructor
  · intro a b hab
    apply (identityLiftEquivG124Preserving (Q := Q) (K := K) (g := g)).injective
    apply hsep
    funext v
    have hv := congrFun hab v
    simpa only [FiniteReading.restrict, identityG124_readAt] using hv
  · intro table hcoh
    obtain ⟨c, hc⟩ := hext table hcoh
    refine ⟨(identityLiftEquivG124Preserving (Q := Q) (K := K) (g := g)).symm c, ?_⟩
    funext v
    have hv := congrFun hc v
    simpa only [FiniteReading.restrict, identityG124_readAt,
      Equiv.apply_symm_apply] using hv

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityLift_representatives_determining
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
