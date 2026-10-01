import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeometry

/-!
# Exact retained incidence of original closed regions under subdivision

Closed regions avoiding the selected edge retain all their cells and no new
factor or intermediate vertex. Every path and every route context is checked.

## Implementation notes

The old-edge image uses a subtype of complete names excluding the chosen name.
This permits one map for all candidate/fixed/shared sets and handles loops and
parallel names uniformly. Extending an old region to include the new vertex
was rejected: the fixed/shared exclusions in GOAL E are essential to the full
label equivalence, and closure already rules out the replaced edge in its words.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))

/-- A single total map retains every nonselected original complete edge name. -/
def retainedEdgeName (e : {e : EdgeName (K := K) // e ≠ chosen}) :
    EdgeName (K := presentation K chosen) := oldEdgeName K chosen e.1 e.2

/-- Original retained complete names are never identified by subdivision. -/
theorem retained_injective : Function.Injective (retainedEdgeName K chosen) := by
  intro e f h
  have hn := congrArg (edgeNameEquiv K chosen) h
  change Sum.inl e = Sum.inl f at hn
  exact Sum.inl.inj hn

/-- Retain a set of old names without adding either factor name. -/
def oldEdgeSet (S : Set (EdgeName (K := K))) : Set (EdgeName (K := presentation K chosen)) :=
  retainedEdgeName K chosen '' {e | e.1 ∈ S}

/-- Retention preserves inclusion of every original edge set. -/
theorem old_set_mono {S T : Set (EdgeName (K := K))} (h : S ⊆ T) :
    oldEdgeSet K chosen S ⊆ oldEdgeSet K chosen T :=
  Set.image_mono (fun _ he => h he)

/-- No original names are introduced from the empty set. -/
theorem old_set_empty : oldEdgeSet K chosen ∅ = ∅ := by
  simp [oldEdgeSet]

/-- Retention preserves unions of named original edge sets. -/
theorem old_set_union (S T : Set (EdgeName (K := K))) :
    oldEdgeSet K chosen (S ∪ T) = oldEdgeSet K chosen S ∪ oldEdgeSet K chosen T := by
  change retainedEdgeName K chosen '' ({e | e.1 ∈ S} ∪ {e | e.1 ∈ T}) = _
  exact Set.image_union _ _ _

/-- A nonselected singleton is the singleton of its same retained complete name. -/
theorem old_set_singleton (e : EdgeName (K := K)) (he : e ≠ chosen) :
    oldEdgeSet K chosen {e} = {oldEdgeName K chosen e he} := by
  ext a
  constructor
  · rintro ⟨⟨f,hf⟩,h,rfl⟩
    have hh : f = e := h
    cases hh
    rfl
  · intro h
    have hh : a = oldEdgeName K chosen e he := h
    cases hh
    exact ⟨⟨e,he⟩,rfl,rfl⟩

/-- Each untouched original word has precisely its retained edge occurrences. -/
theorem substituted_path_edges {i j : K.Vertex} (w : K.Path i j)
    (hw : chosen ∉ pathEdges w) :
    pathEdges (K := presentation K chosen) (substitutePath K chosen w) =
      oldEdgeSet K chosen (pathEdges w) := by
  induction w with
  | nil _ => exact (old_set_empty K chosen).symm
  | @cons i j l e w ih =>
    have he : (⟨i,j,e⟩ : EdgeName (K := K)) ≠ chosen := fun h => hw (Or.inl h.symm)
    have ht : chosen ∉ pathEdges w := fun h => hw (Or.inr h)
    simp only [substitutePath,edgeWord_old K chosen _ he,PresentedPath.append,pathEdges]
    rw [ih ht,old_set_union,old_set_singleton K chosen _ he]
    rfl

/-- Substituted complete routes retain exactly the original authored face names. -/
theorem substituted_pasting_faces {i j : K.Vertex} {w z : K.Path i j}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingFaces (K := presentation K chosen) (substitutePasting K chosen p) = pastingFaces p := by
  induction p with
  | nil _ => rfl
  | cons s t ih =>
    simp only [substitutePasting,pastingFaces,substituteStep,substituteFace,ih]

/-- Every untouched prefix/suffix in both complete routes has exactly its retained original occurrences. -/
theorem substituted_pasting_context {i j : K.Vertex} {w z : K.Path i j}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z)
    (hp : chosen ∉ pastingContextEdges p) :
    pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen p) =
      oldEdgeSet K chosen (pastingContextEdges p) := by
  induction p with
  | nil _ => exact (old_set_empty K chosen).symm
  | cons s t ih =>
    have hi : chosen ∉ pathEdges s.face.incoming := fun h => hp (Or.inl (Or.inl h))
    have ho : chosen ∉ pathEdges s.face.outgoing := fun h => hp (Or.inl (Or.inr h))
    have ht : chosen ∉ pastingContextEdges t := fun h => hp (Or.inr h)
    change (pathEdges (K := presentation K chosen) (substitutePath K chosen s.face.incoming) ∪
      pathEdges (K := presentation K chosen) (substitutePath K chosen s.face.outgoing)) ∪
        pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen t) = _
    rw [substituted_path_edges K chosen _ hi,substituted_path_edges K chosen _ ho,ih ht]
    simp only [pastingContextEdges,old_set_union]

/-- An original closed region avoiding the selected edge retains all its original cells. -/
noncomputable def oldRegion (U : ClosedRegion K) (hu : chosen ∉ U.edges) :
    ClosedRegion (presentation K chosen) where
  vertices := Sum.inl '' U.vertices
  edges := oldEdgeSet K chosen U.edges
  faces := U.faces
  triples := U.triples
  edge_closed := by
    rintro _ ⟨e,he,rfl⟩
    have h := U.edge_closed e.1 he
    exact ⟨⟨e.1.1,h.1,rfl⟩,⟨e.1.2.1,h.2,rfl⟩⟩
  face_closed := by
    intro f hf
    have h := U.face_closed f hf
    refine ⟨⟨K.twoSource f,h.1,rfl⟩,⟨K.twoTarget f,h.2.1,rfl⟩,?_,?_⟩
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.twoLeft f)) ⊆ _
      rw [substituted_path_edges K chosen _ (fun he => hu (h.2.2.1 he))]
      exact old_set_mono K chosen h.2.2.1
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.twoRight f)) ⊆ _
      rw [substituted_path_edges K chosen _ (fun he => hu (h.2.2.2 he))]
      exact old_set_mono K chosen h.2.2.2
  triple_closed := by
    intro f hf
    have h := U.triple_closed f hf
    refine ⟨⟨K.threeSource f,h.1,rfl⟩,⟨K.threeTarget f,h.2.1,rfl⟩,?_,?_,?_,?_,?_,?_⟩
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.threeStart f)) ⊆ _
      rw [substituted_path_edges K chosen _ (fun he => hu (h.2.2.1 he))]
      exact old_set_mono K chosen h.2.2.1
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.threeFinish f)) ⊆ _
      rw [substituted_path_edges K chosen _ (fun he => hu (h.2.2.2.1 he))]
      exact old_set_mono K chosen h.2.2.2.1
    · change pastingFaces (K := presentation K chosen) (substitutePasting K chosen (K.threeLeft f)) ⊆ _
      rw [substituted_pasting_faces]
      exact h.2.2.2.2.1
    · change pastingFaces (K := presentation K chosen) (substitutePasting K chosen (K.threeRight f)) ⊆ _
      rw [substituted_pasting_faces]
      exact h.2.2.2.2.2.1
    · change pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen (K.threeLeft f)) ⊆ _
      rw [substituted_pasting_context K chosen _ (fun he => hu (h.2.2.2.2.2.2.1 he))]
      exact old_set_mono K chosen h.2.2.2.2.2.2.1
    · change pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen (K.threeRight f)) ⊆ _
      rw [substituted_pasting_context K chosen _ (fun he => hu (h.2.2.2.2.2.2.2 he))]
      exact old_set_mono K chosen h.2.2.2.2.2.2.2

/-- The new intermediate vertex belongs to no retained original region. -/
theorem new_vertex_not_old_region (U : ClosedRegion K) (hu : chosen ∉ U.edges) :
    (Sum.inr () : (presentation K chosen).Vertex) ∉ (oldRegion K chosen U hu).vertices := by
  rintro ⟨v,_,h⟩
  cases h

/-- The first factor belongs to no retained original region. -/
theorem first_not_old_region (U : ClosedRegion K) (hu : chosen ∉ U.edges) :
    firstEdgeName K chosen ∉ (oldRegion K chosen U hu).edges := by
  rintro ⟨e,_,h⟩
  have hn := congrArg (edgeNameEquiv K chosen) h
  change Sum.inl e = Sum.inr false at hn
  cases hn

/-- The second factor belongs to no retained original region. -/
theorem second_not_old_region (U : ClosedRegion K) (hu : chosen ∉ U.edges) :
    secondEdgeName K chosen ∉ (oldRegion K chosen U hu).edges := by
  rintro ⟨e,_,h⟩
  have hn := congrArg (edgeNameEquiv K chosen) h
  change Sum.inl e = Sum.inr true at hn
  cases hn

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
