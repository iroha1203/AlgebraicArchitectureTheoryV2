import ResearchLean.AG.ProtocolHolonomy.IdentitySection
import ResearchLean.AG.RealizationReconstruction.FixedFComponentClassification
import Formal.Util.AssertStandardAxioms

/-!
# Vertical identity-operation changes as component permutations

The original A1 vertical lifts are exactly hidden permutation families
constant along every original named edge. The established independent
component quotient then classifies these families.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- Read the original A1 vertical lift as its actual vertex permutation
family, with edge constancy derived from its named-edge square. -/
def identityVerticalToEdgeConstant
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (a : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q)) :
    FixedFEdgeConstantPermutationFamily Q K where
  perm := a.fiber
  edge_constant := by
    intro e
    apply Equiv.ext
    intro x
    have h := a.edge_naturality e x
    simpa [identityReversibleData, ReversibleData.renamedEdgeEquiv]
      using h.symm

/-- Construct the original A1 vertical lift from an edge-constant family;
the required operation squares are the original named-edge equalities. -/
def identityEdgeConstantToVertical
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (a : FixedFEdgeConstantPermutationFamily Q K) :
    (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q) where
  fiber := a.perm
  edge_naturality := by
    intro e x
    have h := congrArg (fun p : Equiv.Perm K => p x)
      (a.edge_constant e)
    simpa [identityReversibleData, ReversibleData.renamedEdgeEquiv]
      using h.symm

/-- The original vertical A1 lifts and source-owned edge-constant hidden
permutations are equivalent, preserving every vertex map. -/
def identityVerticalEquivEdgeConstant
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w) :
    (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q) ≃
      FixedFEdgeConstantPermutationFamily Q K where
  toFun := identityVerticalToEdgeConstant Q K
  invFun := identityEdgeConstantToVertical Q K
  left_inv a := by
    apply ReversibleData.Lift.ext
    intro v x
    rfl
  right_inv a := by
    apply FixedFEdgeConstantPermutationFamily.ext
    rfl

/-- Identity-operation vertical changes are classified by one hidden
permutation for each original undirected component. -/
def identityVerticalEquivComponents
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w) :
    (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q) ≃
      FixedFComponentPermutationFamily Q K :=
  (identityVerticalEquivEdgeConstant Q K).trans
    FixedFEdgeConstantPermutationFamily.equivComponentPermutationFamilies

/-- Component classification reads the original vertical map at each
vertex, rather than an independently supplied permutation. -/
theorem identityVerticalEquivComponents_apply
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (a : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q)) (v : Q.Vertex) :
    (identityVerticalEquivComponents Q K a) (fixedFComponentMk Q v) =
      a.fiber v := rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityVerticalToEdgeConstant
#print axioms AAT.AG.ProtocolHolonomy.identityEdgeConstantToVertical
#print axioms AAT.AG.ProtocolHolonomy.identityVerticalEquivEdgeConstant
#print axioms AAT.AG.ProtocolHolonomy.identityVerticalEquivComponents
#print axioms AAT.AG.ProtocolHolonomy.identityVerticalEquivComponents_apply
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
