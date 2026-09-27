import ResearchLean.AG.ProtocolHolonomy.IdentityG124Representatives
import Formal.Util.AssertStandardAxioms

/-!
# G-124 component extension and original C2 reconstruction

For identity operations, every signed transport is identity. Thus the
original C2 formula extends a component-root permutation to each vertex by
its original undirected component, exactly as the G-124 classification does.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.LocalSemanticReconstruction

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]
  {g : FixedFGraphAutomorphism Q}

private abbrev D (Q : FixedFDirectedMultigraph.{u, u}) (K : Type u) :=
  identityReversibleData Q K

/-- Every component permutation is C1 root data in the identity-operation
system, using G-124's exact component representatives as roots. -/
def identityComponentRootSolutions
    (α : FixedFComponentPermutationFamily Q K) :
    (D Q K).RootSolutions (g124RepresentativeRootedPaths Q) g where
  rootFiber := α
  edge_holonomy := by
    intro j e he
    simp only [identity_transport Q K]
    rfl

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
/-- C2 extends the root permutation by its original component at every
vertex, with no dependence on the selected path or edge orientation. -/
theorem identity_C2_component_extension
    (α : FixedFComponentPermutationFamily Q K) (v : Q.Vertex) :
    (identityComponentRootSolutions (g := g) α).reconstructedFiber
      (D Q K) (g124RepresentativeRootedPaths Q) v =
      α (fixedFComponentMk Q v) := by
  simp only [ReversibleData.RootSolutions.reconstructedFiber,
    identity_transport Q K]
  rfl

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
/-- The actual G-124 preserving change reconstructed from the component
family has the same vertex reading as the original C2 extension. -/
theorem identity_G124_C2_extension_agree
    (α : FixedFComponentPermutationFamily Q K) (v : Q.Vertex) :
    FinitePermutationReadingCriteria.readAt Q K g
      ((FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies).symm α)
      v =
    (identityComponentRootSolutions (g := g) α).reconstructedFiber
      (D Q K) (g124RepresentativeRootedPaths Q) v := by
  rw [identity_C2_component_extension]
  change (FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
    ((FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies).symm α))
      (fixedFComponentMk Q v) = α (fixedFComponentMk Q v)
  rw [Equiv.apply_symm_apply]

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityComponentRootSolutions
#print axioms AAT.AG.ProtocolHolonomy.identity_C2_component_extension
#print axioms AAT.AG.ProtocolHolonomy.identity_G124_C2_extension_agree
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
