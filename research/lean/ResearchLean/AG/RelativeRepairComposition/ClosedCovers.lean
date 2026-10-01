import ResearchLean.AG.RelativeRepairComposition.RelativeFamilies
/-!
# Closed intersections, unions and covers of original typed cells.

## Implementation notes

Every family keeps its original index and full coefficient group. Fixed-cell
vanishing is preserved by restriction. Extension by zero is degreewise only;
no chain-map property is assumed for extension.
-/

namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}
namespace ClosedRegion
/-- Original cells closed under their full incidence in the common intersection. -/
def inter (U V : ClosedRegion K) : ClosedRegion K where
  vertices := U.vertices ∩ V.vertices
  edges := U.edges ∩ V.edges
  faces := U.faces ∩ V.faces
  triples := U.triples ∩ V.triples
  edge_closed e he := ⟨⟨(U.edge_closed e he.1).1,(V.edge_closed e he.2).1⟩,
    ⟨(U.edge_closed e he.1).2,(V.edge_closed e he.2).2⟩⟩
  face_closed f hf := by
    rcases U.face_closed f hf.1 with ⟨hus,hut,hul,hur⟩
    rcases V.face_closed f hf.2 with ⟨hvs,hvt,hvl,hvr⟩
    exact ⟨⟨hus,hvs⟩,⟨hut,hvt⟩,fun _ he => ⟨hul he,hvl he⟩,
      fun _ he => ⟨hur he,hvr he⟩⟩
  triple_closed t ht := by
    rcases U.triple_closed t ht.1 with ⟨hus,hut,hua,huz,hul,hur,huc,hud⟩
    rcases V.triple_closed t ht.2 with ⟨hvs,hvt,hva,hvz,hvl,hvr,hvc,hvd⟩
    exact ⟨⟨hus,hvs⟩,⟨hut,hvt⟩,fun _ he => ⟨hua he,hva he⟩,
      fun _ he => ⟨huz he,hvz he⟩,fun _ hf => ⟨hul hf,hvl hf⟩,
      fun _ hf => ⟨hur hf,hvr hf⟩,fun _ he => ⟨huc he,hvc he⟩,
      fun _ he => ⟨hud he,hvd he⟩⟩

/-- The union keeps every complete face path and three-cell context of each region. -/
def union (U V : ClosedRegion K) : ClosedRegion K where
  vertices := U.vertices ∪ V.vertices
  edges := U.edges ∪ V.edges
  faces := U.faces ∪ V.faces
  triples := U.triples ∪ V.triples
  edge_closed e he := by
    rcases he with hu | hv
    · exact ⟨Or.inl (U.edge_closed e hu).1,Or.inl (U.edge_closed e hu).2⟩
    · exact ⟨Or.inr (V.edge_closed e hv).1,Or.inr (V.edge_closed e hv).2⟩
  face_closed f hf := by
    rcases hf with hu | hv
    · rcases U.face_closed f hu with ⟨hs,ht,hl,hr⟩
      exact ⟨Or.inl hs,Or.inl ht,fun _ he => Or.inl (hl he),fun _ he => Or.inl (hr he)⟩
    · rcases V.face_closed f hv with ⟨hs,ht,hl,hr⟩
      exact ⟨Or.inr hs,Or.inr ht,fun _ he => Or.inr (hl he),fun _ he => Or.inr (hr he)⟩
  triple_closed t ht := by
    rcases ht with hu | hv
    · rcases U.triple_closed t hu with ⟨hs,ht,ha,hz,hl,hr,hc,hd⟩
      exact ⟨Or.inl hs,Or.inl ht,fun _ h => Or.inl (ha h),fun _ h => Or.inl (hz h),
        fun _ h => Or.inl (hl h),fun _ h => Or.inl (hr h),fun _ h => Or.inl (hc h),fun _ h => Or.inl (hd h)⟩
    · rcases V.triple_closed t hv with ⟨hs,ht,ha,hz,hl,hr,hc,hd⟩
      exact ⟨Or.inr hs,Or.inr ht,fun _ h => Or.inr (ha h),fun _ h => Or.inr (hz h),
        fun _ h => Or.inr (hl h),fun _ h => Or.inr (hr h),fun _ h => Or.inr (hc h),fun _ h => Or.inr (hd h)⟩

/-- All original cells form a closed region. -/
def all : ClosedRegion K where
  vertices := Set.univ
  edges := Set.univ
  faces := Set.univ
  triples := Set.univ
  edge_closed _ _ := ⟨trivial,trivial⟩
  face_closed _ _ := ⟨trivial,trivial,Set.subset_univ _,Set.subset_univ _⟩
  triple_closed _ _ := ⟨trivial,trivial,Set.subset_univ _,Set.subset_univ _,
    Set.subset_univ _,Set.subset_univ _,Set.subset_univ _,Set.subset_univ _⟩

/-- The empty original cell region is closed at every degree. -/
def empty : ClosedRegion K where
  vertices := ∅
  edges := ∅
  faces := ∅
  triples := ∅
  edge_closed _ he := he.elim
  face_closed _ hf := hf.elim
  triple_closed _ ht := ht.elim

/-- Inclusion retains original cells at every degree. -/
structure Inclusion (U V : ClosedRegion K) : Prop where
  vertices : U.vertices ⊆ V.vertices
  edges : U.edges ⊆ V.edges
  faces : U.faces ⊆ V.faces
  triples : U.triples ⊆ V.triples

/-- Identity inclusion on all original cells. -/
theorem Inclusion.refl (U : ClosedRegion K) : Inclusion U U :=
  ⟨Set.Subset.refl _,Set.Subset.refl _,Set.Subset.refl _,Set.Subset.refl _⟩

/-- Compose inclusions without changing original names. -/
theorem Inclusion.trans {U V W : ClosedRegion K} (h : Inclusion U V) (k : Inclusion V W) : Inclusion U W :=
  ⟨h.vertices.trans k.vertices,h.edges.trans k.edges,h.faces.trans k.faces,h.triples.trans k.triples⟩

/-- The common intersection includes into the first region. -/
theorem inter_left (U V : ClosedRegion K) : Inclusion (inter U V) U :=
  ⟨Set.inter_subset_left,Set.inter_subset_left,Set.inter_subset_left,Set.inter_subset_left⟩

/-- Deprecated compatibility name for `inter_left`. -/
@[deprecated inter_left (since := "2026-10-01")]
alias interLeft := inter_left

/-- The common intersection includes into the second region. -/
theorem inter_right (U V : ClosedRegion K) : Inclusion (inter U V) V :=
  ⟨Set.inter_subset_right,Set.inter_subset_right,Set.inter_subset_right,Set.inter_subset_right⟩

/-- Deprecated compatibility name for `inter_right`. -/
@[deprecated inter_right (since := "2026-10-01")]
alias interRight := inter_right

/-- Every original region includes into the complete original cell region. -/
theorem to_all (U : ClosedRegion K) : Inclusion U all :=
  ⟨Set.subset_univ _,Set.subset_univ _,Set.subset_univ _,Set.subset_univ _⟩

/-- Deprecated compatibility name for `to_all`. -/
@[deprecated to_all (since := "2026-10-01")]
alias toAll := to_all

/-- Two regions cover every original 0–3-cell. -/
structure Cover (U V : ClosedRegion K) : Prop where
  vertices : U.vertices ∪ V.vertices = Set.univ
  edges : U.edges ∪ V.edges = Set.univ
  faces : U.faces ∪ V.faces = Set.univ
  triples : U.triples ∪ V.triples = Set.univ

/-- A complete original region together with any region is a genuine cover. -/
theorem cover_all_left (U : ClosedRegion K) : Cover all U :=
  ⟨Set.univ_union _,Set.univ_union _,Set.univ_union _,Set.univ_union _⟩

/-- Deprecated compatibility name for `cover_all_left`. -/
@[deprecated cover_all_left (since := "2026-10-01")]
alias coverAllLeft := cover_all_left

/-- On any nonempty original vertex set, two empty regions fail the cover condition. -/
theorem not_cover_empty [Nonempty K.Vertex] : ¬ Cover (empty (K := K)) empty := by
  intro h
  obtain ⟨v⟩ := ‹Nonempty K.Vertex›
  have hv : v ∈ (empty (K := K)).vertices ∪ empty.vertices := by
    rw [h.vertices]
    trivial
  exact hv.elim False.elim False.elim

/-- The full region cannot include into the empty region on a nonempty vertex set. -/
theorem not_inclusion_all_empty [Nonempty K.Vertex] :
    ¬ Inclusion (all (K := K)) empty := by
  intro h
  obtain ⟨v⟩ := ‹Nonempty K.Vertex›
  exact h.vertices (Set.mem_univ v)

variable (M : LocalCoefficients.{uG,uA} K)
variable {U V : ClosedRegion K}

/-- Restrict degree 0 along included original cells, preserving each coefficient. -/
def r0Between (h : Inclusion V U) : C0 M U →+ C0 M V :=
  Family.inclusionRestrict M.A h.vertices

/-- Nested degree-0 restrictions are the same original-cell restriction. -/
theorem r0_between_restrict (h : Inclusion V U) (b : AbelianLiftingObstruction.C0 M) :
    r0Between M h (r0 M U b) = r0 M V b := rfl

/-- Restrict degree 1 along included original cells, preserving each coefficient. -/
def r1Between (h : Inclusion V U) : C1 M U →+ C1 M V :=
  Family.inclusionRestrict (fun e : EdgeName (K := K) => M.A e.2.1) h.edges

/-- Nested degree-1 restrictions are the same original-cell restriction. -/
theorem r1_between_restrict (h : Inclusion V U) (b : AbelianLiftingObstruction.C1 M) :
    r1Between M h (r1 M U b) = r1 M V b := rfl

/-- Restrict degree 2 along included original cells, preserving each coefficient. -/
def r2Between (h : Inclusion V U) : C2 M U →+ C2 M V :=
  Family.inclusionRestrict (fun f => M.A (K.twoTarget f)) h.faces

/-- Nested degree-2 restrictions are the same original-cell restriction. -/
theorem r2_between_restrict (h : Inclusion V U) (b : AbelianLiftingObstruction.C2 M) :
    r2Between M h (r2 M U b) = r2 M V b := rfl

/-- Restrict degree 3 along included original cells, preserving each coefficient. -/
def r3Between (h : Inclusion V U) : C3 M U →+ C3 M V :=
  Family.inclusionRestrict (fun t => M.A (K.threeTarget t)) h.triples

/-- Nested degree-3 restrictions are the same original-cell restriction. -/
theorem r3_between_restrict (h : Inclusion V U) (b : AbelianLiftingObstruction.C3 M) :
    r3Between M h (r3 M U b) = r3 M V b := rfl

/-- Inclusion restriction commutes with the full original d0 by closed incidence. -/
theorem inclusion_d0 (h : Inclusion V U) (b : C0 M U) :
    r1Between M h (d0Hom M U b) = d0Hom M V (r0Between M h b) := by
  have hi : r0Between M h b = r0 M V (e0 M U b) :=
    Family.inclusion_restrict_extend M.A h.vertices b
  have hu := r_d0 M U (e0 M U b)
  have he : r0 M U (e0 M U b) = b := Family.restrict_extend _ _ _
  rw [he] at hu
  rw [hi, ← r_d0, ← hu, r1_between_restrict]

/-- Inclusion restriction commutes with the full original d1 by closed incidence. -/
theorem inclusion_d1 (h : Inclusion V U) (b : C1 M U) :
    r2Between M h (d1Hom M U b) = d1Hom M V (r1Between M h b) := by
  have hi : r1Between M h b = r1 M V (e1 M U b) :=
    Family.inclusion_restrict_extend (fun e : EdgeName (K := K) => M.A e.2.1) h.edges b
  have hu := r_d1 M U (e1 M U b)
  have he : r1 M U (e1 M U b) = b := Family.restrict_extend _ _ _
  rw [he] at hu
  rw [hi, ← r_d1, ← hu, r2_between_restrict]

/-- Inclusion restriction commutes with the full original d2 by closed incidence. -/
theorem inclusion_d2 (h : Inclusion V U) (b : C2 M U) :
    r3Between M h (d2Hom M U b) = d2Hom M V (r2Between M h b) := by
  have hi : r2Between M h b = r2 M V (e2 M U b) :=
    Family.inclusion_restrict_extend (fun f => M.A (K.twoTarget f)) h.faces b
  have hu := r_d2 M U (e2 M U b)
  have he : r2 M U (e2 M U b) = b := Family.restrict_extend _ _ _
  rw [he] at hu
  rw [hi, ← r_d2, ← hu, r3_between_restrict]
end ClosedRegion
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
