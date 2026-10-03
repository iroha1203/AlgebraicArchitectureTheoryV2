import ResearchLean.AG.RelativeRepairComposition.W3AffineInput
import ResearchLean.AG.RelativeRepairComposition.ClosedCovers
import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers

/-!
# W3's empty physical fixed part and original two-patch cover

U contains e and both original vertices; V contains f and both vertices.
Their original overlap has both vertices and no edge. Both original edge
names remain candidates, independently of every later permission set.
-/
namespace AAT.AG.RelativeRepairComposition.W3Regions
open TransportCoherence AbelianLiftingObstruction W3AffineInput

/-- The specified physical fixed region is entirely empty. -/
def fixedRegion : ClosedRegion geometry where
  vertices := ∅
  edges := ∅
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact he.elim
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- U retains the original forward edge and both original vertices. -/
def leftRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeE}
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- V retains the original return edge and both original vertices. -/
def rightRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeF}
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- W is the actual closed intersection of the original patches. -/
def overlap := ClosedRegion.inter leftRegion rightRegion

/-- Both original vertices belong to W. -/
theorem overlap_vertices : overlap.vertices = Set.univ := by
  simp [overlap, ClosedRegion.inter, leftRegion, rightRegion]

/-- No original edge belongs to W. -/
theorem overlap_edges : overlap.edges = ∅ := by
  ext e
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e <;> simp [geometry, overlap, ClosedRegion.inter, leftRegion, rightRegion,
    name, edgeE, edgeF, edgeSource, edgeTarget]

/-- The original patches cover every original cell in every degree. -/
theorem regions_cover : ClosedRegion.Cover leftRegion rightRegion := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [leftRegion, rightRegion]
  · ext e
    rcases e with ⟨i,j,e,hs,ht⟩
    cases hs
    cases ht
    fin_cases e <;> simp [geometry, leftRegion, rightRegion, name,
      edgeE, edgeF, edgeSource, edgeTarget]
  · ext f; exact f.elim
  · ext t; exact t.elim

/-- Both original named edges are candidates; the always part is empty. -/
def candidates : Set (EdgeName (K := geometry)) := {name edgeE, name edgeF}

/-- The candidate names exhaust the complete original typed edge family. -/
theorem candidates_all : candidates = Set.univ := by
  ext e
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e <;> simp [geometry, candidates, name, edgeE, edgeF, edgeSource, edgeTarget]

/-- Forbidden candidates are fixed as actual edges without fixing any original vertex. -/
def fixedEdges (S : Set (EdgeName (K := geometry))) := fixedRegion.edges ∪ (candidates \ S)

/-- Empty permission fixes both original reference operations. -/
theorem fixed_empty : fixedEdges ∅ = Set.univ := by
  simp [fixedEdges, fixedRegion, candidates_all]

/-- Allowing all original candidates fixes no actual edge. -/
theorem fixed_all : fixedEdges candidates = ∅ := by
  simp [fixedEdges, fixedRegion]

/-- No original candidate belongs to the empty physical fixed region. -/
theorem candidates_outside : Disjoint candidates fixedRegion.edges := by
  simp [fixedRegion]

/-- The complete original finite patch family is fixed before S. -/
def regions : Bool → ClosedRegion geometry
  | false => leftRegion
  | true => rightRegion

/-- Every original cell is included in the finite original patch family. -/
theorem indexed_cover : ClosedRegion.IndexedCover regions := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v; exact ⟨false, Set.mem_univ _⟩
  · intro e
    have h : e ∈ leftRegion.edges ∪ rightRegion.edges := by
      rw [regions_cover.edges]; exact Set.mem_univ _
    rcases h with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · intro f; exact f.elim
  · intro t; exact t.elim

/-- All original variables are public candidates; no private always edge exists. -/
theorem private_empty (j : Bool) :
    ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j = ∅ := by
  ext e
  simp [ClosedRegion.privateAlwaysEdges, candidates_all]

end AAT.AG.RelativeRepairComposition.W3Regions
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3Regions
