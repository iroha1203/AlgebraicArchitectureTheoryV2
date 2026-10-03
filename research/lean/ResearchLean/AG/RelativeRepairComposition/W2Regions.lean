import ResearchLean.AG.RelativeRepairComposition.W2AffineInput
import ResearchLean.AG.RelativeRepairComposition.ClosedCovers
import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers
import Mathlib.Tactic.FinCases

/-!
# W2's physical endpoints, original cover and candidate permissions

Physical P contains only p and q. Fixing a forbidden candidate edge imposes
its actual operation equality; it does not add w to physical P. The two closed
patches meet in the original vertex w and have no shared edge.
-/
namespace AAT.AG.RelativeRepairComposition.W2Regions
open TransportCoherence AbelianLiftingObstruction W2AffineInput

/-- The physical fixed region contains exactly the two original endpoints. -/
def fixedRegion : ClosedRegion geometry where
  vertices := {vertexP, vertexQ}
  edges := ∅
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact he.elim
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- U keeps the complete original e1:p→w and its two endpoints. -/
def leftRegion : ClosedRegion geometry where
  vertices := {vertexP, vertexW}
  edges := {name edgeOne}
  faces := ∅
  triples := ∅
  edge_closed := by
    intro e he
    have h : e = name edgeOne := he
    subst e
    constructor <;> simp [name, edgeOne, edgeSource, edgeTarget, vertexP, vertexW]
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- V keeps the complete original e2:w→q and its two endpoints. -/
def rightRegion : ClosedRegion geometry where
  vertices := {vertexW, vertexQ}
  edges := {name edgeTwo}
  faces := ∅
  triples := ∅
  edge_closed := by
    intro e he
    have h : e = name edgeTwo := he
    subst e
    constructor <;> simp [name, edgeTwo, edgeSource, edgeTarget, vertexW, vertexQ]
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- The overlap is the closed intersection of the original two patches. -/
def overlap := ClosedRegion.inter leftRegion rightRegion

/-- The original internal vertex is physically free. -/
theorem internal_not_fixed : vertexW ∉ fixedRegion.vertices := by
  simp [fixedRegion, vertexW, vertexP, vertexQ]

/-- The actual overlap keeps exactly the original internal vertex w. -/
theorem overlap_vertices : overlap.vertices = {vertexW} := by
  ext v
  fin_cases v <;> simp [geometry, overlap, ClosedRegion.inter, leftRegion, rightRegion,
    vertexP, vertexW, vertexQ]

/-- The actual overlap has no original edge. -/
theorem overlap_edges : overlap.edges = ∅ := by
  ext e
  rcases e with ⟨i, j, e, hs, ht⟩
  cases hs
  cases ht
  fin_cases e <;> simp [geometry, overlap, ClosedRegion.inter, leftRegion, rightRegion,
    name, edgeOne, edgeTwo, edgeSource, edgeTarget]

/-- The two original patches cover all cells in every original degree. -/
theorem regions_cover : ClosedRegion.Cover leftRegion rightRegion := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    fin_cases v <;> simp [geometry, leftRegion, rightRegion, vertexP, vertexW, vertexQ]
  · ext e
    rcases e with ⟨i, j, e, hs, ht⟩
    cases hs
    cases ht
    fin_cases e <;> simp [geometry, leftRegion, rightRegion, name, edgeOne, edgeTwo,
      edgeSource, edgeTarget]
  · ext f; exact f.elim
  · ext t; exact t.elim

/-- Both original names are the candidate edges; no always edge is introduced. -/
def candidates : Set (EdgeName (K := geometry)) := {name edgeOne, name edgeTwo}

/-- The named candidate set is the entire original two-edge family. -/
theorem candidates_all : candidates = Set.univ := by
  ext e
  rcases e with ⟨i, j, e, hs, ht⟩
  cases hs
  cases ht
  fin_cases e <;> simp [geometry, candidates, name, edgeOne, edgeTwo, edgeSource, edgeTarget]

/-- Permissions fix each forbidden candidate's actual edge without changing physical vertices. -/
def fixedEdges (S : Set (EdgeName (K := geometry))) := fixedRegion.edges ∪ (candidates \ S)

/-- Empty permission fixes both original affine edges. -/
theorem fixed_empty : fixedEdges ∅ = Set.univ := by
  simp [fixedEdges, fixedRegion, candidates_all]

/-- Every candidate is outside the physical edge part P. -/
theorem candidates_outside : Disjoint candidates fixedRegion.edges := by
  simp [fixedRegion]

/-- The fixed Bool index lists the same original U,V, before any permission choice. -/
def regions : Bool → ClosedRegion geometry
  | false => leftRegion
  | true => rightRegion

/-- The original Bool-indexed cover contains every original cell. -/
theorem indexed_cover : ClosedRegion.IndexedCover regions := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    have h : v ∈ leftRegion.vertices ∪ rightRegion.vertices := by
      rw [regions_cover.vertices]; exact Set.mem_univ _
    rcases h with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · intro e
    have h : e ∈ leftRegion.edges ∪ rightRegion.edges := by
      rw [regions_cover.edges]; exact Set.mem_univ _
    rcases h with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · intro f; exact f.elim
  · intro t; exact t.elim

/-- No local generator has a private always edge: every original edge is a candidate. -/
theorem private_empty (j : Bool) :
    ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j = ∅ := by
  ext e
  simp [ClosedRegion.privateAlwaysEdges, candidates_all]

end AAT.AG.RelativeRepairComposition.W2Regions
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2Regions
