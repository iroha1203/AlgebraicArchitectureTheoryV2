import ResearchLean.AG.ProtocolHolonomy.IdentityG124Bridge
import Formal.Util.AssertStandardAxioms

/-!
# G-124 determining representatives as B2 roots

The same original chosen vertex represents each undirected component in the
G-124 finite reading and the B2 root-centralizer classification.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.LocalSemanticReconstruction

universe u

variable {Q : FixedFDirectedMultigraph.{u, u}} [Finite Q.Vertex] [Finite Q.Edge]
  {K : Type u} [Finite K]

/-- Use exactly G-124's chosen component representatives as B2 roots. -/
noncomputable def g124RepresentativeRootedPaths (Q : FixedFDirectedMultigraph) :
    RootedPaths Q :=
  rootedPathsOfRoots Q (InducedComponent.representative Q)
    (InducedComponent.componentMk_representative Q)

omit [Finite Q.Edge] in
/-- Every B2 root is in G-124's exact finite set of selected vertices. -/
theorem g124_root_mem_representativeSet
    (j : FixedFComponent Q) :
    (g124RepresentativeRootedPaths Q).root j ∈
      CSFixedFDetermining.protocolRepresentativeSet Q := by
  classical
  change InducedComponent.representative Q j ∈
    CSFixedFDetermining.protocolRepresentativeSet Q
  letI : Fintype (FixedFComponent Q) := Fintype.ofFinite _
  unfold CSFixedFDetermining.protocolRepresentativeSet
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

omit [Finite Q.Vertex] [Finite Q.Edge] [Finite K] in
/-- The B2 root permutation and G-124 vertex reading coincide at each
original component representative, for the same actual A1 lift. -/
theorem identityG124_B2_representative_reading
    (a : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q))
    (j : FixedFComponent Q) :
    (((identityReversibleData Q K).verticalRootMulEquiv
      (g124RepresentativeRootedPaths Q) a) j).1 =
      FinitePermutationReadingCriteria.readAt Q K
        (1 : FixedFGraphAutomorphism Q)
        (identityLiftEquivG124Preserving a)
        (InducedComponent.representative Q j) := by
  change a.fiber (InducedComponent.representative Q j) = _
  exact (identityG124_readAt a (InducedComponent.representative Q j)).symm

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.g124RepresentativeRootedPaths
#print axioms AAT.AG.ProtocolHolonomy.g124_root_mem_representativeSet
#print axioms AAT.AG.ProtocolHolonomy.identityG124_B2_representative_reading
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
