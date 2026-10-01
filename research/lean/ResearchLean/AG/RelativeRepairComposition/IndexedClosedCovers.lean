import ResearchLean.AG.RelativeRepairComposition.IndexedFamilies
import ResearchLean.AG.RelativeRepairComposition.RelativeCoverComplex

/-!
# Indexed covers of the complete original typed presentation

Coverage names every original cell in degrees zero through three. Intersections
and unions retain all incidence paths and typed three-cell contexts. The family
isomorphisms below restore every original value, including fixed-cell zero values.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uG uA uJ
variable {K : FiniteTransportPresentation.{uG}} {J : Type uJ}
namespace ClosedRegion
/-- A family covers the original presentation at every cell degree. -/
structure IndexedCover (U : J → ClosedRegion K) : Prop where
  vertices : ∀ v, ∃ j, v ∈ (U j).vertices
  edges : ∀ e, ∃ j, e ∈ (U j).edges
  faces : ∀ f, ∃ j, f ∈ (U j).faces
  triples : ∀ t, ∃ j, t ∈ (U j).triples

/-- A nonempty family of full regions covers every original cell. -/
theorem indexed_cover_all [Nonempty J] :
    IndexedCover (fun (_ : J) => (all : ClosedRegion K)) := by
  obtain ⟨j⟩ := ‹Nonempty J›
  exact ⟨fun _ => ⟨j,Set.mem_univ _⟩,fun _ => ⟨j,Set.mem_univ _⟩,
    fun _ => ⟨j,Set.mem_univ _⟩,fun _ => ⟨j,Set.mem_univ _⟩⟩

/-- Empty regions cannot cover an existing original vertex. -/
theorem not_indexed_cover_empty [Nonempty K.Vertex] :
    ¬ IndexedCover (fun (_ : J) => (empty : ClosedRegion K)) := by
  obtain ⟨v⟩ := ‹Nonempty K.Vertex›
  intro hc
  obtain ⟨j,hj⟩ := hc.vertices v
  exact hj

/-- A union retains the original complete incidence of every member. -/
def indexedUnion (U : J → ClosedRegion K) : ClosedRegion K where
  vertices := {v | ∃ j, v ∈ (U j).vertices}
  edges := {e | ∃ j, e ∈ (U j).edges}
  faces := {f | ∃ j, f ∈ (U j).faces}
  triples := {t | ∃ j, t ∈ (U j).triples}
  edge_closed e he := by
    obtain ⟨j,hj⟩ := he
    exact ⟨⟨j,((U j).edge_closed e hj).1⟩,⟨j,((U j).edge_closed e hj).2⟩⟩
  face_closed f hf := by
    obtain ⟨j,hj⟩ := hf
    obtain ⟨hs,ht,hl,hr⟩ := (U j).face_closed f hj
    exact ⟨⟨j,hs⟩,⟨j,ht⟩,fun _ h => ⟨j,hl h⟩,fun _ h => ⟨j,hr h⟩⟩
  triple_closed t ht := by
    obtain ⟨j,hj⟩ := ht
    obtain ⟨hs,ht,ha,hz,hl,hr,hc,hd⟩ := (U j).triple_closed t hj
    exact ⟨⟨j,hs⟩,⟨j,ht⟩,fun _ h => ⟨j,ha h⟩,fun _ h => ⟨j,hz h⟩,
      fun _ h => ⟨j,hl h⟩,fun _ h => ⟨j,hr h⟩,fun _ h => ⟨j,hc h⟩,fun _ h => ⟨j,hd h⟩⟩

/-- Each member includes with the same original cell names. -/
theorem to_indexed_union (U : J → ClosedRegion K) (j : J) :
    Inclusion (U j) (indexedUnion U) :=
  ⟨fun _ h => ⟨j,h⟩,fun _ h => ⟨j,h⟩,fun _ h => ⟨j,h⟩,fun _ h => ⟨j,h⟩⟩

/-- The chosen bracket for a threefold overlap keeps all original cells. -/
def triple (U V W : ClosedRegion K) : ClosedRegion K := inter U (inter V W)

/-- The triple overlap includes into the first pair. -/
theorem triple_first_pair (U V W : ClosedRegion K) : Inclusion (triple U V W) (inter U V) :=
  ⟨fun _ h => ⟨h.1,h.2.1⟩,fun _ h => ⟨h.1,h.2.1⟩,
    fun _ h => ⟨h.1,h.2.1⟩,fun _ h => ⟨h.1,h.2.1⟩⟩

/-- The triple overlap includes into the second pair. -/
theorem triple_second_pair (U V W : ClosedRegion K) : Inclusion (triple U V W) (inter V W) :=
  inter_right U (inter V W)

/-- The triple overlap includes into the outer pair. -/
theorem triple_outer_pair (U V W : ClosedRegion K) : Inclusion (triple U V W) (inter U W) :=
  ⟨fun _ h => ⟨h.1,h.2.2⟩,fun _ h => ⟨h.1,h.2.2⟩,
    fun _ h => ⟨h.1,h.2.2⟩,fun _ h => ⟨h.1,h.2.2⟩⟩
end ClosedRegion

namespace IndexedCover
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K) (U : J → ClosedRegion K)

/-- All compatible local original values in degree 0. -/
abbrev Compatible0 := Family.indexedCompatible M.A (fun j => (U j).vertices) P.vertices

/-- All original degree-0 values restrict to the indexed family. -/
def restriction0 : RelativeCover.C0 M ClosedRegion.all P →+ Compatible0 M P U :=
  Family.indexedRestriction M.A (fun j => (U j).vertices) P.vertices

/-- All compatible degree-0 values restore to the original presentation. -/
noncomputable def glue0 (hc : ClosedRegion.IndexedCover U) :
    Compatible0 M P U →+ RelativeCover.C0 M ClosedRegion.all P :=
  Family.indexedGlue M.A (fun j => (U j).vertices) P.vertices hc.vertices

/-- Original degree-0 families are exactly all compatible local families. -/
noncomputable def familyEquiv0 (hc : ClosedRegion.IndexedCover U) :
    RelativeCover.C0 M ClosedRegion.all P ≃+ Compatible0 M P U :=
  Family.indexedEquiv M.A (fun j => (U j).vertices) P.vertices hc.vertices

/-- Indexed restriction is injective on every original degree-0 value. -/
theorem restriction0_injective (hc : ClosedRegion.IndexedCover U) :
    Function.Injective (restriction0 M P U) :=
  Family.indexed_restriction_injective M.A (fun j => (U j).vertices) P.vertices hc.vertices

/-- Restored degree-0 values agree on every local original cell. -/
theorem glue0_value (hc : ClosedRegion.IndexedCover U) (b : Compatible0 M P U)
    (j : J) (i : (U j).vertices) :
    (glue0 M P U hc b).1 ⟨i.1,Set.mem_univ i.1⟩ = (b.1 j).1 i :=
  Family.indexed_glue_on M.A (fun j => (U j).vertices) P.vertices hc.vertices b j i.1 i.2

/-- Restoration returns every full local degree-0 family. -/
theorem restrict_glue0 (hc : ClosedRegion.IndexedCover U) (b : Compatible0 M P U) :
    restriction0 M P U (glue0 M P U hc b) = b :=
  Family.indexed_restriction_glue M.A (fun j => (U j).vertices) P.vertices hc.vertices b

/-- All compatible local original values in degree 1. -/
abbrev Compatible1 := Family.indexedCompatible (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges

/-- All original degree-1 values restrict to the indexed family. -/
def restriction1 : RelativeCover.C1 M ClosedRegion.all P →+ Compatible1 M P U :=
  Family.indexedRestriction (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges

/-- All compatible degree-1 values restore to the original presentation. -/
noncomputable def glue1 (hc : ClosedRegion.IndexedCover U) :
    Compatible1 M P U →+ RelativeCover.C1 M ClosedRegion.all P :=
  Family.indexedGlue (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges hc.edges

/-- Original degree-1 families are exactly all compatible local families. -/
noncomputable def familyEquiv1 (hc : ClosedRegion.IndexedCover U) :
    RelativeCover.C1 M ClosedRegion.all P ≃+ Compatible1 M P U :=
  Family.indexedEquiv (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges hc.edges

/-- Indexed restriction is injective on every original degree-1 value. -/
theorem restriction1_injective (hc : ClosedRegion.IndexedCover U) :
    Function.Injective (restriction1 M P U) :=
  Family.indexed_restriction_injective (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges hc.edges

/-- Restored degree-1 values agree on every local original cell. -/
theorem glue1_value (hc : ClosedRegion.IndexedCover U) (b : Compatible1 M P U)
    (j : J) (i : (U j).edges) :
    (glue1 M P U hc b).1 ⟨i.1,Set.mem_univ i.1⟩ = (b.1 j).1 i :=
  Family.indexed_glue_on (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges hc.edges b j i.1 i.2

/-- Restoration returns every full local degree-1 family. -/
theorem restrict_glue1 (hc : ClosedRegion.IndexedCover U) (b : Compatible1 M P U) :
    restriction1 M P U (glue1 M P U hc b) = b :=
  Family.indexed_restriction_glue (fun e : EdgeName (K := K) => M.A e.2.1) (fun j => (U j).edges) P.edges hc.edges b

/-- All compatible local original values in degree 2. -/
abbrev Compatible2 := Family.indexedCompatible (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces

/-- All original degree-2 values restrict to the indexed family. -/
def restriction2 : RelativeCover.C2 M ClosedRegion.all P →+ Compatible2 M P U :=
  Family.indexedRestriction (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces

/-- All compatible degree-2 values restore to the original presentation. -/
noncomputable def glue2 (hc : ClosedRegion.IndexedCover U) :
    Compatible2 M P U →+ RelativeCover.C2 M ClosedRegion.all P :=
  Family.indexedGlue (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces hc.faces

/-- Original degree-2 families are exactly all compatible local families. -/
noncomputable def familyEquiv2 (hc : ClosedRegion.IndexedCover U) :
    RelativeCover.C2 M ClosedRegion.all P ≃+ Compatible2 M P U :=
  Family.indexedEquiv (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces hc.faces

/-- Indexed restriction is injective on every original degree-2 value. -/
theorem restriction2_injective (hc : ClosedRegion.IndexedCover U) :
    Function.Injective (restriction2 M P U) :=
  Family.indexed_restriction_injective (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces hc.faces

/-- Restored degree-2 values agree on every local original cell. -/
theorem glue2_value (hc : ClosedRegion.IndexedCover U) (b : Compatible2 M P U)
    (j : J) (i : (U j).faces) :
    (glue2 M P U hc b).1 ⟨i.1,Set.mem_univ i.1⟩ = (b.1 j).1 i :=
  Family.indexed_glue_on (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces hc.faces b j i.1 i.2

/-- Restoration returns every full local degree-2 family. -/
theorem restrict_glue2 (hc : ClosedRegion.IndexedCover U) (b : Compatible2 M P U) :
    restriction2 M P U (glue2 M P U hc b) = b :=
  Family.indexed_restriction_glue (fun f => M.A (K.twoTarget f)) (fun j => (U j).faces) P.faces hc.faces b

/-- All compatible local original values in degree 3. -/
abbrev Compatible3 := Family.indexedCompatible (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples

/-- All original degree-3 values restrict to the indexed family. -/
def restriction3 : RelativeCover.C3 M ClosedRegion.all P →+ Compatible3 M P U :=
  Family.indexedRestriction (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples

/-- All compatible degree-3 values restore to the original presentation. -/
noncomputable def glue3 (hc : ClosedRegion.IndexedCover U) :
    Compatible3 M P U →+ RelativeCover.C3 M ClosedRegion.all P :=
  Family.indexedGlue (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples hc.triples

/-- Original degree-3 families are exactly all compatible local families. -/
noncomputable def familyEquiv3 (hc : ClosedRegion.IndexedCover U) :
    RelativeCover.C3 M ClosedRegion.all P ≃+ Compatible3 M P U :=
  Family.indexedEquiv (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples hc.triples

/-- Indexed restriction is injective on every original degree-3 value. -/
theorem restriction3_injective (hc : ClosedRegion.IndexedCover U) :
    Function.Injective (restriction3 M P U) :=
  Family.indexed_restriction_injective (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples hc.triples

/-- Restored degree-3 values agree on every local original cell. -/
theorem glue3_value (hc : ClosedRegion.IndexedCover U) (b : Compatible3 M P U)
    (j : J) (i : (U j).triples) :
    (glue3 M P U hc b).1 ⟨i.1,Set.mem_univ i.1⟩ = (b.1 j).1 i :=
  Family.indexed_glue_on (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples hc.triples b j i.1 i.2

/-- Restoration returns every full local degree-3 family. -/
theorem restrict_glue3 (hc : ClosedRegion.IndexedCover U) (b : Compatible3 M P U) :
    restriction3 M P U (glue3 M P U hc b) = b :=
  Family.indexed_restriction_glue (fun t => M.A (K.threeTarget t)) (fun j => (U j).triples) P.triples hc.triples b

end IndexedCover
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
