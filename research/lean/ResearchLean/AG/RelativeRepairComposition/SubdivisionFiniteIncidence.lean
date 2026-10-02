import ResearchLean.AG.RelativeRepairComposition.SubdivisionClosedCovers

/-!
# Finite incidence decisions generated from the original closed regions

## Implementation notes

Membership decisions inspect the original vertex or edge predicate. Both new
factors read the same original edge, and the fresh vertex reads precisely the
chosen edge. A retained permission set is decided through its proved equality
with full substitution when it avoids chosen. No new membership oracle or
private/public partition is supplied.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))
variable (U : ClosedRegion K)

/-- Expanded vertex membership reads the original vertex or the chosen edge. -/
instance expandedVerticesDecidable [DecidablePred (· ∈ U.vertices)]
    [DecidablePred (· ∈ U.edges)] :
    DecidablePred (· ∈ (expandedRegion K chosen U).vertices) := fun v => by
  cases v with
  | inl v => exact inferInstanceAs (Decidable (v ∈ U.vertices))
  | inr _ => exact inferInstanceAs (Decidable (chosen ∈ U.edges))

/-- Expanded edge membership reads its same complete original edge name. -/
instance expandedEdgesDecidable [DecidablePred (· ∈ U.edges)] :
    DecidablePred (· ∈ (expandedRegion K chosen U).edges) :=
  fun e => inferInstanceAs (Decidable (edgeOrigin K chosen e ∈ U.edges))

/-- Expanded face membership reads the literal original authored face predicate. -/
instance expandedFacesDecidable [DecidablePred (· ∈ U.faces)] :
    DecidablePred (· ∈ (expandedRegion K chosen U).faces) :=
  fun f => inferInstanceAs (Decidable (f ∈ U.faces))

/-- Expanded triple membership reads the literal original authored triple predicate. -/
instance expandedTriplesDecidable [DecidablePred (· ∈ U.triples)] :
    DecidablePred (· ∈ (expandedRegion K chosen U).triples) :=
  fun t => inferInstanceAs (Decidable (t ∈ U.triples))

/-- A retained set avoiding chosen is decided from its original full membership predicate. -/
def retainedSetDecidable (S : Set (EdgeName (K := K)))
    [DecidablePred (· ∈ S)] (hs : chosen ∉ S) :
    DecidablePred (· ∈ oldEdgeSet K chosen S) := fun e =>
  decidable_of_iff (edgeOrigin K chosen e ∈ S) (by
    rw [← expanded_set_avoiding K chosen S hs]
    exact Iff.rfl)

/-- Retained membership still tests the original name, including every noncandidate public name. -/
theorem retained_set_test (S : Set (EdgeName (K := K))) (hs : chosen ∉ S)
    (e : EdgeName (K := presentation K chosen)) :
    e ∈ oldEdgeSet K chosen S ↔ edgeOrigin K chosen e ∈ S := by
  rw [← expanded_set_avoiding K chosen S hs]
  exact Iff.rfl

end AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.FiniteIncidence
