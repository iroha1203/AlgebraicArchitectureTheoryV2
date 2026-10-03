import ResearchLean.AG.RelativeRepairComposition.W5AffineInput
import ResearchLean.AG.RelativeRepairComposition.ClosedCovers
import Mathlib.Tactic.FinCases

/-!
# W5's original physical fixed part and shared-edge cover

P contains both original vertices and a,b, with no face. U and V contain
respectively e,a and e,b and their complete authored face. Their actual
intersection contains e and both physically fixed endpoints.
-/
namespace AAT.AG.RelativeRepairComposition.W5Regions
open TransportCoherence AbelianLiftingObstruction W5AffineInput

/-- The physical fixed part retains both endpoints and the original input a,b. -/
def fixedRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeA, name edgeB}
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _,Set.mem_univ _⟩
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- U keeps both original vertices, e,a and the entire first face e⇒a. -/
def leftRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeE, name edgeA}
  faces := {false}
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _,Set.mem_univ _⟩
  face_closed := by
    intro f hf
    have hf' : (f : Bool) = false := hf
    subst f
    refine ⟨Set.mem_univ _,Set.mem_univ _,?_,?_⟩ <;>
      simp [geometry,pathEdges,name,Set.singleton_subset_iff]
  triple_closed := by intro t ht; exact ht.elim

/-- V keeps both original vertices, e,b and the entire second face e⇒b. -/
def rightRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeE, name edgeB}
  faces := {true}
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _,Set.mem_univ _⟩
  face_closed := by
    intro f hf
    have hf' : (f : Bool) = true := hf
    subst f
    refine ⟨Set.mem_univ _,Set.mem_univ _,?_,?_⟩ <;>
      simp [geometry,pathEdges,name,Set.singleton_subset_iff]
  triple_closed := by intro t ht; exact ht.elim

/-- The overlap is the original closed intersection, retaining e and both vertices. -/
def overlap := ClosedRegion.inter leftRegion rightRegion

/-- Both original endpoints are present and physically fixed in the actual overlap. -/
theorem overlap_vertices : overlap.vertices = Set.univ := by
  simp [overlap,ClosedRegion.inter,leftRegion,rightRegion]
/-- The original shared edge e is the entire overlap edge family. -/
theorem overlap_edges : overlap.edges = {name edgeE} := by
  ext e
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e <;> simp [geometry,overlap,ClosedRegion.inter,leftRegion,rightRegion,
    name,edgeE,edgeA,edgeB]
/-- Neither authored face belongs to the original overlap. -/
theorem overlap_faces : overlap.faces = ∅ := by
  ext f
  cases f <;> simp [overlap,ClosedRegion.inter,leftRegion,rightRegion]
/-- Both full authored faces and all original cells are covered. -/
theorem regions_cover : ClosedRegion.Cover leftRegion rightRegion := by
  refine ⟨?_,?_,?_,?_⟩
  · ext v; simp [leftRegion,rightRegion]
  · ext e
    rcases e with ⟨i,j,e,hs,ht⟩
    cases hs
    cases ht
    fin_cases e <;> simp [geometry,leftRegion,rightRegion,name,edgeE,edgeA,edgeB]
  · ext f; cases f <;> simp [leftRegion,rightRegion]
  · ext t; exact t.elim

/-- W5 has no candidate edge: the original e is always correctable. -/
def candidates : Set (EdgeName (K := geometry)) := ∅
/-- The sole always-correctable edge is the original shared e. -/
def alwaysEdges : Set (EdgeName (K := geometry)) := {name edgeE}
/-- The same complete original edge family is partitioned into P and the always edge. -/
theorem edge_partition : fixedRegion.edges ∪ alwaysEdges = Set.univ := by
  ext e
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e <;> simp [geometry,fixedRegion,alwaysEdges,name,edgeE,edgeA,edgeB]
/-- The original shared edge remains outside the physical fixed edge set. -/
theorem shared_not_fixed : name edgeE ∉ fixedRegion.edges := by
  simp [geometry,fixedRegion,name,edgeE,edgeA,edgeB]
/-- The original shared edge occurs on each side, so it is never a private variable. -/
theorem shared_in_both : name edgeE ∈ leftRegion.edges ∧ name edgeE ∈ rightRegion.edges := by
  constructor <;> exact Or.inl rfl

/-- The Boolean index retains the original complete left or right region. -/
def region (side : Bool) : ClosedRegion geometry := if side then rightRegion else leftRegion
/-- The physical input selected by either original face is a or b. -/
def inputEdge (side : Bool) : Fin 3 := if side then edgeB else edgeA
/-- Each indexed region retains its original authored face. -/
theorem face_in_region (side : Bool) : side ∈ (region side).faces := by
  cases side <;> rfl
/-- Each indexed region retains both e and its physically fixed input edge. -/
theorem region_edges (side : Bool) :
    (region side).edges = {name edgeE, name (inputEdge side)} := by
  cases side <;> rfl
/-- Every original vertex remains physically fixed on each indexed patch. -/
theorem region_vertices (side : Bool) : (region side).vertices = Set.univ := by
  cases side <;> rfl

end AAT.AG.RelativeRepairComposition.W5Regions
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5Regions
