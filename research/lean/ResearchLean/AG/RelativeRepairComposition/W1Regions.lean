import ResearchLean.AG.RelativeRepairComposition.W1AffineInput
import ResearchLean.AG.RelativeRepairComposition.ClosedCovers
import Mathlib.Tactic.FinCases

/-!
# The original W1 fixed region, cover and permissions

## Implementation notes

All regions use the original six named loops. P fixes the vertex and rx,ry,
and contains neither authored face. Candidate permissions add physical edge
equalities without closing a candidate edge under either Law. U and V keep
their respective complete authored face; their intersection keeps e,b.
-/
namespace AAT.AG.RelativeRepairComposition.W1Regions
open TransportCoherence AbelianLiftingObstruction W1AffineInput

/-- A named original loop, with its unchanged original endpoints. -/
def name (e : Fin 6) : EdgeName (K := geometry) := ⟨(), (), e⟩

/-- Every original edge name has the same literal original endpoints. -/
theorem name_edge (e : EdgeName (K := geometry)) : name e.2.2 = e := by
  rcases e with ⟨i, j, e⟩
  cases i
  cases j
  rfl

/-- The closed physical fixed input contains p,rx,ry and no authored face. -/
def fixedRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeRx, name edgeRy}
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- U retains the complete first Law and exactly its three original named loops. -/
def leftRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeE, name edgeB, name edgeRx}
  faces := {false}
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  face_closed := by
    intro f hf
    have hf' : (f : Bool) = false := hf
    subst f
    refine ⟨Set.mem_univ _, Set.mem_univ _, ?_, ?_⟩ <;>
      simp [geometry, pathEdges, name, Set.insert_subset_iff, Set.singleton_subset_iff]
  triple_closed := by intro t ht; exact ht.elim

/-- V retains both visits to a in the complete second Law and all its five named loops. -/
def rightRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeE, name edgeA, name edgeB, name edgeC, name edgeRy}
  faces := {true}
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  face_closed := by
    intro f hf
    have hf' : (f : Bool) = true := hf
    subst f
    refine ⟨Set.mem_univ _, Set.mem_univ _, ?_, ?_⟩ <;>
      simp [geometry, pathEdges, name, Set.insert_subset_iff, Set.singleton_subset_iff]
  triple_closed := by intro t ht; exact ht.elim

/-- The actual overlap is the closed intersection on the original indices. -/
def overlap := ClosedRegion.inter leftRegion rightRegion

/-- The two complete original patches cover every original cell, including both Laws. -/
theorem regions_cover : ClosedRegion.Cover leftRegion rightRegion := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i; simp [leftRegion, rightRegion]
  · ext e
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases e with ⟨i, j, e⟩
    cases i
    cases j
    fin_cases e <;> simp [geometry, leftRegion, rightRegion, name, edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]
  · ext f; cases f <;> simp [leftRegion, rightRegion]
  · ext t; exact t.elim

/-- The overlap has exactly the original shared e,b loops; a remains outside it. -/
theorem overlap_edges : overlap.edges = {name edgeE, name edgeB} := by
  ext e
  rcases e with ⟨i, j, e⟩
  cases i
  cases j
  fin_cases e <;> simp [geometry, overlap, ClosedRegion.inter, leftRegion, rightRegion,
    name, edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]

/-- The physical fixed original vertex belongs to the actual overlap. -/
theorem overlap_vertices : overlap.vertices = Set.univ := by
  simp [overlap, ClosedRegion.inter, leftRegion, rightRegion]

/-- The distinct original candidate names are b,c. -/
def candidates : Set (EdgeName (K := geometry)) := {name edgeB, name edgeC}

/-- All S use the same original physical anchors and fix each forbidden candidate by its own name. -/
def fixedEdges (S : Set (EdgeName (K := geometry))) := fixedRegion.edges ∪ (candidates \ S)

/-- The physical rx input stays fixed for every permission set. -/
theorem rx_fixed (S : Set (EdgeName (K := geometry))) : name edgeRx ∈ fixedEdges S :=
  Or.inl (Or.inl rfl)

/-- The physical ry input stays fixed for every permission set. -/
theorem ry_fixed (S : Set (EdgeName (K := geometry))) : name edgeRy ∈ fixedEdges S :=
  Or.inl (Or.inr rfl)

/-- Candidate b is fixed precisely when its original name is not allowed. -/
theorem b_fixed_iff (S : Set (EdgeName (K := geometry))) :
    name edgeB ∈ fixedEdges S ↔ name edgeB ∉ S := by
  simp [geometry, fixedEdges, fixedRegion, candidates, name, edgeB, edgeC, edgeRx, edgeRy]

/-- Candidate c is fixed precisely when its original name is not allowed. -/
theorem c_fixed_iff (S : Set (EdgeName (K := geometry))) :
    name edgeC ∈ fixedEdges S ↔ name edgeC ∉ S := by
  simp [geometry, fixedEdges, fixedRegion, candidates, name, edgeB, edgeC, edgeRx, edgeRy]

/-- Both original always loops remain free for every permission set. -/
theorem always_not_fixed (S : Set (EdgeName (K := geometry))) :
    name edgeE ∉ fixedEdges S ∧ name edgeA ∉ fixedEdges S := by
  simp [geometry, fixedEdges, fixedRegion, candidates, name, edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]

end AAT.AG.RelativeRepairComposition.W1Regions
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1Regions
