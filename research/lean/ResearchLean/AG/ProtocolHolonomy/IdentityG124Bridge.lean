import ResearchLean.AG.ProtocolHolonomy.IdentityProtocolFiberEquiv
import ResearchLean.AG.LocalSemanticReconstruction.CSFixedFDetermining
import Formal.Util.AssertStandardAxioms

/-!
# Original identity-operation A1 lifts and G-124 preserving changes

Both constructions retain the same vertexwise hidden permutation and all
original named-edge equations for a fixed visible graph automorphism.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.LocalSemanticReconstruction

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {g : FixedFGraphAutomorphism Q}

/-- Read an original A1 lift as the edge-constant family used by G-124. -/
def identityLiftToG124Family
    (a : (identityReversibleData Q K).Lift g) :
    FixedFEdgeConstantPermutationFamily Q K where
  perm := a.fiber
  edge_constant := by
    intro e
    apply Equiv.ext
    intro x
    have h := a.edge_naturality e x
    simpa [identityReversibleData, ReversibleData.renamedEdgeEquiv]
      using h.symm

/-- Recover the original A1 lift from an edge-constant G-124 family. -/
def g124FamilyToIdentityLift
    (a : FixedFEdgeConstantPermutationFamily Q K) :
    (identityReversibleData Q K).Lift g where
  fiber := a.perm
  edge_naturality := by
    intro e x
    have h := congrArg (fun p : Equiv.Perm K => p x)
      (a.edge_constant e)
    simpa [identityReversibleData, ReversibleData.renamedEdgeEquiv]
      using h.symm

/-- The original A1 lift and the G-124 edge-constant carrier agree for every
fixed visible automorphism, not only the vertical identity. -/
def identityLiftEquivG124Family :
    (identityReversibleData Q K).Lift g ≃
      FixedFEdgeConstantPermutationFamily Q K where
  toFun := identityLiftToG124Family
  invFun := g124FamilyToIdentityLift
  left_inv a := by
    apply ReversibleData.Lift.ext
    intro v x
    rfl
  right_inv a := by
    apply FixedFEdgeConstantPermutationFamily.ext
    rfl

/-- Directly compare G-124's actual preserving changes with the original A1
lifts over the same complete named-edge graph automorphism. -/
def identityLiftEquivG124Preserving :
    (identityReversibleData Q K).Lift g ≃
      PermutationRestriction.PreservingChange Q K g :=
  identityLiftEquivG124Family.trans
    (FixedFFollowingStateChange.preservingEquivEdgeConstantFamilies).symm

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
/-- The G-124 vertex reading is exactly the original A1 fiber map. -/
theorem identityG124_readAt (a : (identityReversibleData Q K).Lift g)
    (v : Q.Vertex) :
    FinitePermutationReadingCriteria.readAt Q K g
      (identityLiftEquivG124Preserving a) v = a.fiber v := by
  change ((FixedFFollowingStateChange.preservingEquivEdgeConstantFamilies)
    ((FixedFFollowingStateChange.preservingEquivEdgeConstantFamilies).symm
      (identityLiftToG124Family a))).perm v = a.fiber v
  rw [Equiv.apply_symm_apply]
  rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityLiftToG124Family
#print axioms AAT.AG.ProtocolHolonomy.g124FamilyToIdentityLift
#print axioms AAT.AG.ProtocolHolonomy.identityLiftEquivG124Family
#print axioms AAT.AG.ProtocolHolonomy.identityLiftEquivG124Preserving
#print axioms AAT.AG.ProtocolHolonomy.identityG124_readAt
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
