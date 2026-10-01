import ResearchLean.AG.RelativeRepairComposition.ParallelPinGeometry

/-! # Original closed incidence inside the parallel-pin presentation -/
namespace AAT.AG.RelativeRepairComposition.ParallelPinGeometry
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG})

/-- Every edge occurrence in an included word is exactly an included old occurrence. -/
theorem included_path_edges {i j : K.Vertex} (w : K.Path i j) :
    pathEdges (K := presentation K) (includePath K w) =
      oldEdgeName K '' pathEdges w := by
  induction w with
  | nil _ => simp only [includePath, pathEdges, Set.image_empty]
  | cons e w ih =>
    simp only [includePath, pathEdges, ih, Set.image_union, Set.image_singleton, oldEdgeName]

/-- The included three-cell route contains exactly its original face names. -/
theorem included_pasting_faces {i j : K.Vertex} {w z : K.Path i j}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingFaces (K := presentation K) (includePasting K p) =
      Sum.inl '' pastingFaces p := by
  induction p with
  | nil _ => simp only [includePasting, pastingFaces, Set.image_empty]
  | cons s t ih =>
    simp only [includePasting, pastingFaces, includeStep, includeFace, ih,
      Set.image_union, Set.image_singleton]

/-- Every original prefix and suffix occurrence is retained in the copied route. -/
theorem included_pasting_context {i j : K.Vertex} {w z : K.Path i j}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingContextEdges (K := presentation K) (includePasting K p) =
      oldEdgeName K '' pastingContextEdges p := by
  induction p with
  | nil _ => simp only [includePasting, pastingContextEdges, Set.image_empty]
  | cons s t ih =>
    change (pathEdges (K := presentation K) (includePath K s.face.incoming) ∪
      pathEdges (K := presentation K) (includePath K s.face.outgoing)) ∪
      pastingContextEdges (K := presentation K) (includePasting K t) = _
    rw [included_path_edges, included_path_edges, ih]
    simp only [pastingContextEdges, Set.image_union]

/-- Original fixed cells embed without fixing any new edge, face or vertex. -/
noncomputable def oldRegion (P : ClosedRegion K) : ClosedRegion (presentation K) where
  vertices := P.vertices
  edges := oldEdgeName K '' P.edges
  faces := Sum.inl '' P.faces
  triples := P.triples
  edge_closed := by
    rintro _ ⟨e, he, rfl⟩
    exact P.edge_closed e he
  face_closed := by
    rintro _ ⟨f, hf, rfl⟩
    have h := P.face_closed f hf
    refine ⟨h.1, h.2.1, ?_, ?_⟩
    · change pathEdges (K := presentation K) (includePath K (K.twoLeft f)) ⊆ _
      rw [included_path_edges]
      exact Set.image_mono h.2.2.1
    · change pathEdges (K := presentation K) (includePath K (K.twoRight f)) ⊆ _
      rw [included_path_edges]
      exact Set.image_mono h.2.2.2
  triple_closed := by
    intro f hf
    have h := P.triple_closed f hf
    refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change pathEdges (K := presentation K) (includePath K (K.threeStart f)) ⊆ _
      rw [included_path_edges]
      exact Set.image_mono h.2.2.1
    · change pathEdges (K := presentation K) (includePath K (K.threeFinish f)) ⊆ _
      rw [included_path_edges]
      exact Set.image_mono h.2.2.2.1
    · change pastingFaces (K := presentation K) (includePasting K (K.threeLeft f)) ⊆ _
      rw [included_pasting_faces]
      exact Set.image_mono h.2.2.2.2.1
    · change pastingFaces (K := presentation K) (includePasting K (K.threeRight f)) ⊆ _
      rw [included_pasting_faces]
      exact Set.image_mono h.2.2.2.2.2.1
    · change pastingContextEdges (K := presentation K) (includePasting K (K.threeLeft f)) ⊆ _
      rw [included_pasting_context]
      exact Set.image_mono h.2.2.2.2.2.2.1
    · change pastingContextEdges (K := presentation K) (includePasting K (K.threeRight f)) ⊆ _
      rw [included_pasting_context]
      exact Set.image_mono h.2.2.2.2.2.2.2

/-- A new pin never becomes physically fixed by the old closed region. -/
theorem pin_not_fixed (P : ClosedRegion K) (e : EdgeName (K := K)) :
    pinEdgeName K e ∉ (oldRegion K P).edges := by
  rintro ⟨f, _, h⟩
  exact old_ne_pin K f e h

/-- The original fixed vertices, including their full gauge condition, are unchanged. -/
theorem old_fixed_vertices (P : ClosedRegion K) :
    (oldRegion K P).vertices = P.vertices := rfl

end AAT.AG.RelativeRepairComposition.ParallelPinGeometry
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.ParallelPinGeometry
