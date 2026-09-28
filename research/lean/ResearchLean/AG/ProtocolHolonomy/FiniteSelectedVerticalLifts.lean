import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedRootedPaths
import ResearchLean.AG.ProtocolHolonomy.FiniteVerticalLifts
import Formal.Util.AssertStandardAxioms

/-!
# B2 centralizers and vertical lifts using the generated named forest

The input-generated selected roots and forest paths now feed the original
B2 generator-centralizer enumeration on every original component. Their
dependent product reconstructs precisely all original vertical A1 lifts.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- Enumerate B2 root-centralizer tuples for the actual finite-table forest
root paths, over every original component. -/
def finiteSelectedRootCentralizerFamilies
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    ExplicitEnumeration
      (D.RootCentralizers (finiteSelectedRootedPaths Q vertices edges)) := by
  letI : DecidableEq (FixedFComponent Q) :=
    finiteComponentDecidableEq Q vertices edges
  let R := finiteSelectedRootedPaths Q vertices edges
  exact ExplicitEnumeration.pi (finiteComponentEnumeration Q vertices)
    (fun j => {
      values := D.finiteRootCentralizers R j edges (fibers (R.root j))
      complete := D.centralizer_mem_finiteRootCentralizers R j edges
        (fibers (R.root j)) })

/-- Reconstruct every original vertical A1 lift from the B2 tuples of the
same generated selected forest and normalized root paths. -/
def finiteSelectedVerticalLifts
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    ExplicitEnumeration (D.Lift (1 : FixedFGraphAutomorphism Q)) := by
  let R := finiteSelectedRootedPaths Q vertices edges
  let candidates := D.finiteSelectedRootCentralizerFamilies
    vertices edges fibers
  exact {
    values := candidates.values.map (D.reconstructVertical R)
    complete := by
      intro a
      apply List.mem_map.mpr
      refine ⟨D.verticalRootEvaluation R a, candidates.complete _, ?_⟩
      exact D.reconstructVertical_evaluation R a }

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteSelectedRootCentralizerFamilies
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteSelectedVerticalLifts
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
