import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeometry

/-!
# Whole target-indexed values on retained edges and both factors

Assignments use every complete retained name and both factor names. The indexed
endpoint equality transports each value to the target of its actual edge.

## Implementation notes

The family remains indexed by each actual target. Eq.mp uses only the supplied incidence equality to carry the value to that target. A nondependent assignment on source-target pairs would lose the coefficient type and complete names of parallel edges, so it cannot implement the original full family.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence
universe uG uA
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))

/-- All retained target values and the two actual factor values, at their original indexed targets. -/
def edgeValue (A : Vertex K → Sort uA)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → A (.inl j))
    (first : A (.inr ())) (second : A (.inl chosen.2.1))
    {i j : Vertex K} (e : Edge K chosen i j) : A j := by
  let a : A (target K chosen e.1) := match e.1 with
    | .inl n => old n.1.2.2
    | .inr false => first
    | .inr true => second
  exact Eq.mp (congrArg A e.2.2) a

/-- Every retained complete edge name has its supplied original target value. -/
theorem edgeValue_old (A : Vertex K → Sort uA)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → A (.inl j))
    (first : A (.inr ())) (second : A (.inl chosen.2.1))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    edgeValue K chosen A old first second (oldEdge K chosen e he) = old e.2.2 := by
  simp [edgeValue,oldEdge,target]

/-- The first actual factor has the supplied full target value at the fresh vertex. -/
theorem edgeValue_first (A : Vertex K → Sort uA)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → A (.inl j))
    (first : A (.inr ())) (second : A (.inl chosen.2.1)) :
    edgeValue K chosen A old first second (firstEdge K chosen) = first := by
  simp [edgeValue,firstEdge,target]

/-- The second actual factor has the supplied full value at the old selected target. -/
theorem edgeValue_second (A : Vertex K → Sort uA)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → A (.inl j))
    (first : A (.inr ())) (second : A (.inl chosen.2.1)) :
    edgeValue K chosen A old first second (secondEdge K chosen) = second := by
  simp [edgeValue,secondEdge,target]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
