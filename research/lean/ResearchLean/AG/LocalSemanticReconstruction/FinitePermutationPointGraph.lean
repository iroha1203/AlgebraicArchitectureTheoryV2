import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence
import Formal.Util.AssertStandardAxioms

/-! The vertex permutation value in G-124(D) has an independently lawful
forward/backward primitive Bool graph presentation.  For finite hidden
carriers the point-pair query type is finite; no such assumption is used by
the general component criteria. -/

namespace AAT.AG.LocalSemanticReconstruction.FinitePermutationPointGraph

open RealizationReconstruction
open FinitePermutationReadingCriteria

universe u v w

/-- A role and an ordered pair of hidden values select one Bool graph cell. -/
abbrev PointQuery (K : Type w) := Bool × K × K

/-- Evaluate the selected forward or backward primitive graph cell. -/
def point {K : Type w}
    (code : AlgebraicGraphCoherence.EquivGraphCode K K)
    (query : PointQuery K) : Bool :=
  if query.1 then code.backward.edge query.2.1 query.2.2
  else code.forward.edge query.2.1 query.2.2

/-- The two directions of the point table determine the lawful graph code. -/
theorem point_injective {K : Type w} :
    Function.Injective (point (K := K)) := by
  intro first second h
  apply AlgebraicGraphCoherence.EquivGraphCode.ext
  · apply PrimitiveFunctionGraph.GraphCode.ext
    funext source target
    exact congrFun h (false, source, target)
  · apply PrimitiveFunctionGraph.GraphCode.ext
    funext source target
    exact congrFun h (true, source, target)

/-- The existing independent graph construction presents all hidden
permutations, including their inverse graphs. -/
noncomputable def permutationGraphEquiv (K : Type w) :
    Equiv.Perm K ≃ AlgebraicGraphCoherence.EquivGraphCode K K :=
  AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.symm

/-- The actual preserving change's finite graph table is read from its
component permutation, at the selected vertex. -/
noncomputable def readAtPoint
    (F : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (visible : FixedFGraphAutomorphism F)
    (change : PermutationRestriction.PreservingChange F K visible)
    (vertex : F.Vertex) : PointQuery K → Bool :=
  point (permutationGraphEquiv K (readAt F K visible change vertex))

/-- A forward point cell records precisely the image of its source. -/
theorem readAtPoint_forward_iff
    (F : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (visible : FixedFGraphAutomorphism F)
    (change : PermutationRestriction.PreservingChange F K visible)
    (vertex : F.Vertex) (source target : K) :
    readAtPoint F K visible change vertex (false, source, target) = true ↔
      readAt F K visible change vertex source = target := by
  change (PrimitiveFunctionGraph.GraphCode.read
      (readAt F K visible change vertex)).edge source target = true ↔ _
  exact PrimitiveFunctionGraph.GraphCode.read_edge_eq_true_iff _ _ _

/-- A backward point cell records the inverse image. -/
theorem readAtPoint_backward_iff
    (F : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (visible : FixedFGraphAutomorphism F)
    (change : PermutationRestriction.PreservingChange F K visible)
    (vertex : F.Vertex) (source target : K) :
    readAtPoint F K visible change vertex (true, source, target) = true ↔
      (readAt F K visible change vertex).symm source = target := by
  change (PrimitiveFunctionGraph.GraphCode.read
      (readAt F K visible change vertex).symm).edge source target = true ↔ _
  exact PrimitiveFunctionGraph.GraphCode.read_edge_eq_true_iff _ _ _

/-- For an explicitly enumerated hidden carrier, every point-pair query is
in one finite support. -/
def finiteSupport (K : Type w) [Fintype K] : Finset (PointQuery K) :=
  Finset.univ

@[simp] theorem mem_finiteSupport (K : Type w) [Fintype K]
    (query : PointQuery K) : query ∈ finiteSupport K := by
  simp [finiteSupport]

/-- On a finite hidden carrier, a finite list of point-pair Bool readings
determines the full hidden permutation. -/
theorem finitePointTable_injective (K : Type w) [Fintype K] :
    Function.Injective (fun permutation : Equiv.Perm K =>
      fun query : {query // query ∈ finiteSupport K} =>
        point (permutationGraphEquiv K permutation) query.1) := by
  intro first second h
  apply (permutationGraphEquiv K).injective
  apply point_injective
  funext query
  exact congrFun h ⟨query, mem_finiteSupport K query⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationPointGraph

end AAT.AG.LocalSemanticReconstruction.FinitePermutationPointGraph
