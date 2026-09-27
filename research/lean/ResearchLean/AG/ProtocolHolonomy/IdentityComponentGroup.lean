import ResearchLean.AG.ProtocolHolonomy.IdentityComponents
import ResearchLean.AG.ProtocolHolonomy.VerticalCentralizer
import Formal.Util.AssertStandardAxioms

/-!
# Identity vertical changes form the component permutation group

The group on original vertical A1 lifts comes from actual total-state
changes. The component classification preserves that product pointwise.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- The original identity-operation vertical group is the full product of
permutation groups over the generated undirected components. -/
noncomputable def identityVerticalMulEquivComponents
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w) :
    (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q) ≃*
      FixedFComponentPermutationFamily Q K where
  toEquiv := identityVerticalEquivComponents Q K
  map_mul' a b := by
    funext j
    refine Quotient.inductionOn j ?_
    intro v
    apply Equiv.ext
    intro x
    change (a * b).fiber v x = a.fiber v (b.fiber v x)
    exact (identityReversibleData Q K).vertical_mul_fiber_apply a b v x

/-- The group isomorphism reads an actual original vertical fiber map at
every vertex of its component. -/
theorem identityVerticalMulEquivComponents_apply
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (a : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q)) (v : Q.Vertex) :
    (identityVerticalMulEquivComponents Q K a)
      (fixedFComponentMk Q v) = a.fiber v :=
  identityVerticalEquivComponents_apply Q K a v

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityVerticalMulEquivComponents
#print axioms AAT.AG.ProtocolHolonomy.identityVerticalMulEquivComponents_apply
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
