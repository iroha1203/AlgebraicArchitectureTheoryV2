import ResearchLean.AG.RelativeRepairComposition.W1Regions
import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinatePartition
import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers
import ResearchLean.AG.RelativeRepairComposition.FiniteElimination

/-!
# The complete indexed original W1 cover and its private/public partition

The two independently defined closed patches retain their complete authored
Laws. Exactly a is private to V; U has no private edge. The shared always edge
e and both original candidates remain public before any permission selection.
-/
namespace AAT.AG.RelativeRepairComposition.W1IndexedCover
open TransportCoherence AbelianLiftingObstruction W1AffineInput W1Regions

/-- The same original U,V patches with fixed indices false,true. -/
def regions : Bool → ClosedRegion geometry
  | false => leftRegion
  | true => rightRegion

/-- Both original patches cover all original cells in every degree. -/
theorem indexed_cover : ClosedRegion.IndexedCover regions := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v; exact ⟨false, Set.mem_univ _⟩
  · intro e
    have he : e ∈ leftRegion.edges ∪ rightRegion.edges := by
      rw [regions_cover.edges]; exact Set.mem_univ _
    rcases he with hl | hr
    · exact ⟨false, hl⟩
    · exact ⟨true, hr⟩
  · intro f; cases f
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  · intro t; exact t.elim

/-- U has no nonshared noncandidate nonfixed edge to eliminate. -/
theorem private_left : ClosedRegion.privateAlwaysEdges regions fixedRegion candidates false = ∅ := by
  ext e
  rcases e with ⟨s,t,e⟩
  cases s; cases t
  fin_cases e <;> simp [geometry, ClosedRegion.privateAlwaysEdges, ClosedRegion.sharedEdges,
    regions, leftRegion, rightRegion, fixedRegion, candidates, name,
    edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]

/-- The whole original a kernel is precisely the private variable of V. -/
theorem private_right : ClosedRegion.privateAlwaysEdges regions fixedRegion candidates true = {name edgeA} := by
  ext e
  rcases e with ⟨s,t,e⟩
  cases s; cases t
  fin_cases e <;> simp [geometry, ClosedRegion.privateAlwaysEdges, ClosedRegion.sharedEdges,
    regions, leftRegion, rightRegion, fixedRegion, candidates, name,
    edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]

/-- The shared always edge is public in each original local generator. -/
theorem shared_e_public (j : Bool) :
    name edgeE ∉ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j := by
  cases j
  · rw [private_left]; simp
  · rw [private_right]; simp [geometry, name, edgeE, edgeA]

/-- Every original candidate is public in both generators before any permission restriction. -/
theorem candidates_public (j : Bool) (e : candidates) :
    e.1 ∉ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j :=
  ClosedRegion.candidate_not_private regions fixedRegion candidates j e.1 e.2

/-- The complete cover selector is fixed before values or permission subsets are supplied. -/
def enumRegions : FiniteElimination.Enumeration Bool :=
  ⟨[false, true], by intro j; cases j <;> simp⟩

end AAT.AG.RelativeRepairComposition.W1IndexedCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1IndexedCover
