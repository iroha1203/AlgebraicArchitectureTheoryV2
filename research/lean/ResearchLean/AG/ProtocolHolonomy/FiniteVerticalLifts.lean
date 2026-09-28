import ResearchLean.AG.ProtocolHolonomy.FiniteRootedPaths
import ResearchLean.AG.ProtocolHolonomy.FiniteCentralizerDecision
import Formal.Util.AssertStandardAxioms

/-!
# All vertical lifts from finite original tables

The complete original vertex table enumerates the original component
quotient. At each component, the previously checked finite B2 centralizer
list is exhaustive. Their dependent product reconstructs every actual A1
vertical lift, using root paths computed from the same graph tables.
This concerns the vertical group only; combining it with a successful C1
lift to list every lift over a visible change is a later E obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- Enumerate the original component quotient by mapping the complete
vertex table; `Quotient.out` appears only in the completeness proof. -/
def finiteComponentEnumeration (Q : FixedFDirectedMultigraph.{u, v})
    (vertices : ExplicitEnumeration Q.Vertex) :
    ExplicitEnumeration (FixedFComponent Q) where
  values := vertices.values.map (fixedFComponentMk Q)
  complete := by
    intro j
    apply List.mem_map.mpr
    exact ⟨Quotient.out j, vertices.complete (Quotient.out j), Quotient.out_eq j⟩

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- Enumerate every B2 root-centralizer tuple from the same finite graph
and fiber tables, across every original undirected component. -/
def finiteRootCentralizerFamilies
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    ExplicitEnumeration (D.RootCentralizers (finiteRootedPaths Q vertices edges)) := by
  letI : DecidableEq (FixedFComponent Q) :=
    finiteComponentDecidableEq Q vertices edges
  let R := finiteRootedPaths Q vertices edges
  exact ExplicitEnumeration.pi (finiteComponentEnumeration Q vertices)
    (fun j => {
      values := D.finiteRootCentralizers R j edges (fibers (R.root j))
      complete := D.centralizer_mem_finiteRootCentralizers R j edges
        (fibers (R.root j)) })

/-- Every actual vertical A1 lift is reconstructed from a table-enumerated
tuple of genuine B2 centralizers. -/
def finiteVerticalLifts
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    ExplicitEnumeration (D.Lift (1 : FixedFGraphAutomorphism Q)) := by
  let R := finiteRootedPaths Q vertices edges
  let candidates := D.finiteRootCentralizerFamilies vertices edges fibers
  exact {
    values := candidates.values.map (D.reconstructVertical R)
    complete := by
      intro a
      apply List.mem_map.mpr
      refine ⟨D.verticalRootEvaluation R a, candidates.complete _, ?_⟩
      exact D.reconstructVertical_evaluation R a }

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.finiteComponentEnumeration
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteRootCentralizerFamilies
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteVerticalLifts
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
