import ResearchLean.AG.RelativeRepairComposition.W2ActualRepairs

/-!
# Whole original W2 gauge labels

The edge-fixing conditions force the global and each one-edge patch label to
zero. The original edge-free overlap retains every full F3 label at w. These
are the actual label subgroups, before any isomorphism-class quotient.
-/
namespace AAT.AG.RelativeRepairComposition.W2GaugeLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs

/-- Full original labels with physical endpoint and actual candidate constraints. -/
abbrev GlobalLabels (S : Set (EdgeName (K := geometry))) :=
  gaugeLabels geometry reference fixedRegion.vertices (fixedEdges S)

/-- Every actual global label vanishes on the original physical fixed vertices. -/
theorem global_fixed (S : Set (EdgeName (K := geometry))) (b : GlobalLabels S)
    (v : geometry.Vertex) (hv : v ∈ fixedRegion.vertices) : b.1 v = 0 := b.2.1 v hv

/-- Each forbidden original edge equates its complete source and target labels. -/
theorem global_edge (S : Set (EdgeName (K := geometry))) (b : GlobalLabels S)
    (e : EdgeName (K := geometry)) (he : e ∈ fixedEdges S) : b.1 e.2.1 = b.1 e.1 := by
  exact b.2.2 e he

/-- Fixing e1 together with physical p forces the full original w label to zero. -/
theorem global_empty_w (b : GlobalLabels ∅) : b.1 vertexW = 0 := by
  have h := global_edge ∅ b (name edgeOne) (by rw [fixed_empty]; exact Set.mem_univ _)
  change b.1 vertexW = b.1 vertexP at h
  exact h.trans (global_fixed ∅ b vertexP (Or.inl rfl))

/-- The entire global original label is zero under empty permission. -/
theorem global_empty_zero (b : GlobalLabels ∅) : b = 0 := by
  apply Subtype.ext
  funext v
  fin_cases v
  · exact global_fixed ∅ b vertexP (Or.inl rfl)
  · exact global_empty_w b
  · exact global_fixed ∅ b vertexQ (Or.inr rfl)

/-- All full global labels have mutually inverse zero-group coordinates. -/
def globalEmptyLabelEquiv : GlobalLabels ∅ ≃+ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => 0
  left_inv b := (global_empty_zero b).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Full actual original local labels with the original physical restriction. -/
noncomputable abbrev LocalLabels (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry))) :=
  gaugeLabels (ClosedRegion.presentation U) (restrictOperations U reference)
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- Local labels vanish on precisely the selected original physical fixed vertices. -/
theorem local_fixed (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry)))
    (b : LocalLabels U S) (v : (ClosedRegion.presentation U).Vertex)
    (hv : v ∈ ClosedRegion.restrictedVertices U fixedRegion.vertices) : b.1 v = 0 := b.2.1 v hv

/-- Every selected forbidden edge preserves its complete original endpoint label equation. -/
theorem local_edge (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry)))
    (b : LocalLabels U S) (e : EdgeName (K := ClosedRegion.presentation U))
    (he : e ∈ ClosedRegion.restrictedEdges U (fixedEdges S)) : b.1 e.2.1 = b.1 e.1 := by
  exact b.2.2 e he

/-- Original p as the selected left vertex. -/
def leftP : (ClosedRegion.presentation leftRegion).Vertex := ⟨vertexP, Or.inl rfl⟩
/-- Original w as the selected left vertex. -/
def leftW : (ClosedRegion.presentation leftRegion).Vertex := ⟨vertexW, Or.inr rfl⟩
/-- The same original w as the selected right vertex. -/
def rightW : (ClosedRegion.presentation rightRegion).Vertex := ⟨vertexW, Or.inl rfl⟩
/-- Original q as the selected right vertex. -/
def rightQ : (ClosedRegion.presentation rightRegion).Vertex := ⟨vertexQ, Or.inr rfl⟩

/-- The left patch keeps the actual original typed e1. -/
def leftEdge : EdgeName (K := ClosedRegion.presentation leftRegion) :=
  (ClosedRegion.edgeNameEquiv leftRegion).symm ⟨name edgeOne, rfl⟩
/-- The right patch keeps the actual original typed e2. -/
def rightEdge : EdgeName (K := ClosedRegion.presentation rightRegion) :=
  (ClosedRegion.edgeNameEquiv rightRegion).symm ⟨name edgeTwo, rfl⟩

/-- The fixed original e1 and physical p force the entire local w label to vanish. -/
theorem left_empty_w (b : LocalLabels leftRegion ∅) : b.1 leftW = 0 := by
  have h := local_edge leftRegion ∅ b leftEdge (local_fixed_all leftRegion leftEdge)
  change b.1 leftW = b.1 leftP at h
  exact h.trans (local_fixed leftRegion ∅ b leftP (Or.inl rfl))

/-- The fixed original e2 and physical q force the entire local w label to vanish. -/
theorem right_empty_w (b : LocalLabels rightRegion ∅) : b.1 rightW = 0 := by
  have h := local_edge rightRegion ∅ b rightEdge (local_fixed_all rightRegion rightEdge)
  change b.1 rightQ = b.1 rightW at h
  exact h.symm.trans (local_fixed rightRegion ∅ b rightQ (Or.inr rfl))

/-- Every full original label on the left patch is zero under empty permission. -/
theorem left_empty_zero (b : LocalLabels leftRegion ∅) : b = 0 := by
  apply Subtype.ext
  funext v
  rcases v with ⟨v,hv⟩
  change v = vertexP ∨ v = vertexW at hv
  rcases hv with h | h
  · subst v; exact local_fixed leftRegion ∅ b leftP (Or.inl rfl)
  · subst v; exact left_empty_w b

/-- Every full original label on the right patch is zero under empty permission. -/
theorem right_empty_zero (b : LocalLabels rightRegion ∅) : b = 0 := by
  apply Subtype.ext
  funext v
  rcases v with ⟨v,hv⟩
  change v = vertexW ∨ v = vertexQ at hv
  rcases hv with h | h
  · subst v; exact right_empty_w b
  · subst v; exact local_fixed rightRegion ∅ b rightQ (Or.inr rfl)

/-- The original internal overlap vertex w keeps its selected original name. -/
def overlapW : (ClosedRegion.presentation overlap).Vertex :=
  ⟨vertexW, by change vertexW ∈ overlap.vertices; rw [overlap_vertices]; exact rfl⟩

/-- Every original overlap vertex is the same original w, with no physical fixed vertex added. -/
theorem overlap_vertex (v : (ClosedRegion.presentation overlap).Vertex) : v = overlapW := by
  apply Subtype.ext
  have h := v.2
  change v.1 ∈ overlap.vertices at h
  rw [overlap_vertices] at h
  exact h

/-- There is no physical fixed vertex in the original overlap. -/
theorem overlap_not_fixed (v : (ClosedRegion.presentation overlap).Vertex) :
    v ∉ ClosedRegion.restrictedVertices overlap fixedRegion.vertices := by
  rw [overlap_vertex v]
  exact internal_not_fixed

/-- There is no actual selected edge in the original overlap. -/
theorem overlap_no_edge (e : EdgeName (K := ClosedRegion.presentation overlap)) : False := by
  have h : (ClosedRegion.edgeNameEquiv overlap e).1 ∈
      (∅ : Set (EdgeName (K := geometry))) := by
    simpa only [overlap_edges] using (ClosedRegion.edgeNameEquiv overlap e).2
  exact h

/-- Every full original overlap value is a permitted actual label at w. -/
def overlapLabel (a : ZMod 3) : LocalLabels overlap ∅ := ⟨fun _ => a, by
  constructor
  · intro v hv; exact (overlap_not_fixed v hv).elim
  · intro e he; exact (overlap_no_edge e).elim⟩

/-- The whole original overlap label group is the entire F3, with both inverses. -/
def overlapLabelEquiv : LocalLabels overlap ∅ ≃+ ZMod 3 where
  toFun b := b.1 overlapW
  invFun := overlapLabel
  left_inv b := by
    apply Subtype.ext
    funext v
    change b.1 overlapW = b.1 v
    rw [overlap_vertex v]
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Restoring any full overlap label keeps its actual original value at w. -/
theorem overlap_label_value (a : ZMod 3) : (overlapLabel a).1 overlapW = a := rfl

end AAT.AG.RelativeRepairComposition.W2GaugeLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2GaugeLabels
