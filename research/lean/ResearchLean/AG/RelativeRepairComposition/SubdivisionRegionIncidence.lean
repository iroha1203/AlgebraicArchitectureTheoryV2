import ResearchLean.AG.RelativeRepairComposition.SubdivisionIncidence

/-!
# Full incidence of every subdivided closed region

## Implementation notes

Both factors read the chosen complete original name; retained edges read their
own original name. Pullback of edge sets therefore replaces every occurrence.
The fresh vertex is included exactly when the region contains the chosen edge.
Restricting to regions avoiding that edge would omit the region whose private
differential is needed for the generated local comparison in GOAL E.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))

/-- The original complete name read by each retained edge or either factor. -/
def edgeOrigin (e : EdgeName (K := presentation K chosen)) : EdgeName (K := K) :=
  (edgeNameEquiv K chosen e).elim Subtype.val (fun _ => chosen)

/-- A retained edge reads exactly its original complete name. -/
theorem edgeOrigin_old (e : EdgeName (K := K)) (he : e ≠ chosen) :
    edgeOrigin K chosen (oldEdgeName K chosen e he) = e := rfl

/-- The first factor reads the chosen original name. -/
theorem edgeOrigin_first : edgeOrigin K chosen (firstEdgeName K chosen) = chosen := rfl

/-- The second factor reads the same chosen original name. -/
theorem edgeOrigin_second : edgeOrigin K chosen (secondEdgeName K chosen) = chosen := rfl

/-- Every original occurrence is replaced, including both factors. -/
def expandedEdgeSet (S : Set (EdgeName (K := K))) :
    Set (EdgeName (K := presentation K chosen)) := {e | edgeOrigin K chosen e ∈ S}

/-- Substitution of named edge sets preserves inclusion. -/
theorem expanded_set_mono {S T : Set (EdgeName (K := K))} (h : S ⊆ T) :
    expandedEdgeSet K chosen S ⊆ expandedEdgeSet K chosen T := fun _ he => h he

/-- No new edge occurs when the original set is empty. -/
theorem expanded_set_empty : expandedEdgeSet K chosen ∅ = ∅ := rfl

/-- All occurrences in a union are substituted. -/
theorem expanded_set_union (S T : Set (EdgeName (K := K))) :
    expandedEdgeSet K chosen (S ∪ T) = expandedEdgeSet K chosen S ∪ expandedEdgeSet K chosen T := rfl

/-- Substitution preserves the intersection of complete edge names. -/
theorem expanded_set_inter (S T : Set (EdgeName (K := K))) :
    expandedEdgeSet K chosen (S ∩ T) = expandedEdgeSet K chosen S ∩ expandedEdgeSet K chosen T := rfl

/-- Edge occurrences in concatenated typed paths are exactly their union. -/
theorem pathEdges_append {H : FiniteTransportPresentation.{uG}} {i j l : H.Vertex}
    (w : H.Path i j) (z : H.Path j l) : pathEdges (w.append z) = pathEdges w ∪ pathEdges z := by
  induction w with
  | nil _ => simp [PresentedPath.append,pathEdges]
  | cons _ _ ih => simp only [PresentedPath.append,pathEdges,ih,Set.union_assoc]

/-- An untouched original name has exactly one retained preimage. -/
theorem edgeOrigin_eq_old (a : EdgeName (K := presentation K chosen))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    edgeOrigin K chosen a = e ↔ a = oldEdgeName K chosen e he := by
  obtain ⟨n,rfl⟩ := (edgeNameEquiv K chosen).symm.surjective a
  cases n with
  | inl b =>
    change b.1 = e ↔ _
    constructor
    · intro h; subst e; rfl
    · intro h
      have hn := congrArg (edgeNameEquiv K chosen) h
      exact congrArg Subtype.val (Sum.inl.inj hn)
  | inr b =>
    change chosen = e ↔ _
    constructor
    · intro h; exact False.elim (he h.symm)
    · intro h
      have hn := congrArg (edgeNameEquiv K chosen) h
      cases hn

/-- The chosen original name has precisely the two factor preimages. -/
theorem edgeOrigin_eq_chosen (a : EdgeName (K := presentation K chosen)) :
    edgeOrigin K chosen a = chosen ↔
      a = firstEdgeName K chosen ∨ a = secondEdgeName K chosen := by
  obtain ⟨n,rfl⟩ := (edgeNameEquiv K chosen).symm.surjective a
  cases n with
  | inl b =>
    change b.1 = chosen ↔ _
    constructor
    · intro h; exact False.elim (b.2 h)
    · rintro (h|h) <;> have hn := congrArg (edgeNameEquiv K chosen) h <;> cases hn
  | inr b =>
    cases b
    · constructor
      · intro _; exact Or.inl rfl
      · intro _; rfl
    · constructor
      · intro _; exact Or.inr rfl
      · intro _; rfl

/-- One authored edge has its entire substituted occurrence set. -/
theorem edgeWord_edges (e : EdgeName (K := K)) :
    pathEdges (K := presentation K chosen) (edgeWord K chosen e) = expandedEdgeSet K chosen {e} := by
  classical
  by_cases he : e = chosen
  · subst e
    rw [edgeWord_chosen]
    ext a
    change (a = firstEdgeName K chosen ∨ a = secondEdgeName K chosen ∨ False) ↔
      edgeOrigin K chosen a = chosen
    simpa only [or_false] using (edgeOrigin_eq_chosen K chosen a).symm
  · rw [edgeWord_old K chosen e he]
    ext a
    change (a = oldEdgeName K chosen e he ∨ False) ↔ edgeOrigin K chosen a = e
    simpa only [or_false] using (edgeOrigin_eq_old K chosen a e he).symm

/-- Every occurrence in every original typed path is replaced. -/
theorem expanded_path_edges {i j : K.Vertex} (w : K.Path i j) :
    pathEdges (K := presentation K chosen) (substitutePath K chosen w) =
      expandedEdgeSet K chosen (pathEdges w) := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change pathEdges (K := presentation K chosen) ((edgeWord K chosen ⟨_,_,e⟩).append (substitutePath K chosen w)) = _
    rw [pathEdges_append,edgeWord_edges,ih]
    exact (expanded_set_union K chosen _ _).symm

/-- Every original prefix and suffix in both complete rewriting routes is substituted. -/
theorem expanded_pasting_context {i j : K.Vertex} {w z : K.Path i j}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen p) =
      expandedEdgeSet K chosen (pastingContextEdges p) := by
  induction p with
  | nil _ => rfl
  | cons s t ih =>
    change (pathEdges (K := presentation K chosen) (substitutePath K chosen s.face.incoming) ∪
      pathEdges (K := presentation K chosen) (substitutePath K chosen s.face.outgoing)) ∪
      pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen t) = _
    rw [expanded_path_edges,expanded_path_edges,ih]
    rfl

/-- Original vertices stay; fresh membership reads the chosen original edge. -/
def expandedVertexSet (U : ClosedRegion K) : Set (presentation K chosen).Vertex :=
  {v | match v with | .inl a => a ∈ U.vertices | .inr _ => chosen ∈ U.edges}

/-- Every original closed region generates its complete subdivided region. -/
noncomputable def expandedRegion (U : ClosedRegion K) : ClosedRegion (presentation K chosen) where
  vertices := expandedVertexSet K chosen U
  edges := expandedEdgeSet K chosen U.edges
  faces := U.faces
  triples := U.triples
  edge_closed := by
    intro e he
    obtain ⟨n,rfl⟩ := (edgeNameEquiv K chosen).symm.surjective e
    cases n with
    | inl a => exact U.edge_closed a.1 he
    | inr b =>
      have h := U.edge_closed chosen he
      cases b
      · exact ⟨h.1,he⟩
      · exact ⟨he,h.2⟩
  face_closed := by
    intro f hf
    obtain ⟨hs,ht,hl,hr⟩ := U.face_closed f hf
    refine ⟨hs,ht,?_,?_⟩
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.twoLeft f)) ⊆ _
      rw [expanded_path_edges]; exact expanded_set_mono K chosen hl
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.twoRight f)) ⊆ _
      rw [expanded_path_edges]; exact expanded_set_mono K chosen hr
  triple_closed := by
    intro t ht
    obtain ⟨hs,ht,ha,hz,hl,hr,hc,hd⟩ := U.triple_closed t ht
    refine ⟨hs,ht,?_,?_,?_,?_,?_,?_⟩
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.threeStart t)) ⊆ _
      rw [expanded_path_edges]; exact expanded_set_mono K chosen ha
    · change pathEdges (K := presentation K chosen) (substitutePath K chosen (K.threeFinish t)) ⊆ _
      rw [expanded_path_edges]; exact expanded_set_mono K chosen hz
    · change pastingFaces (K := presentation K chosen) (substitutePasting K chosen (K.threeLeft t)) ⊆ _
      rw [substituted_pasting_faces]; exact hl
    · change pastingFaces (K := presentation K chosen) (substitutePasting K chosen (K.threeRight t)) ⊆ _
      rw [substituted_pasting_faces]; exact hr
    · change pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen (K.threeLeft t)) ⊆ _
      rw [expanded_pasting_context]; exact expanded_set_mono K chosen hc
    · change pastingContextEdges (K := presentation K chosen) (substitutePasting K chosen (K.threeRight t)) ⊆ _
      rw [expanded_pasting_context]; exact expanded_set_mono K chosen hd

/-- Retained original vertices have exactly their old membership. -/
theorem expanded_vertex_old (U : ClosedRegion K) (v : K.Vertex) :
    (Sum.inl v : (presentation K chosen).Vertex) ∈ (expandedRegion K chosen U).vertices ↔
      v ∈ U.vertices := Iff.rfl

/-- Fresh membership is exactly chosen-edge membership in the original region. -/
theorem expanded_vertex_fresh (U : ClosedRegion K) :
    (Sum.inr () : (presentation K chosen).Vertex) ∈ (expandedRegion K chosen U).vertices ↔
      chosen ∈ U.edges := Iff.rfl

/-- All original face names keep their memberships and substituted paths. -/
theorem expanded_faces (U : ClosedRegion K) : (expandedRegion K chosen U).faces = U.faces := rfl

/-- All original triple names keep their memberships and complete routes. -/
theorem expanded_triples (U : ClosedRegion K) : (expandedRegion K chosen U).triples = U.triples := rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
