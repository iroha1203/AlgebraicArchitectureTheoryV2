import ResearchLean.AG.RelativeRepairComposition.AffineEmbeddedValues
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid
import ResearchLean.AG.RelativeRepairComposition.ContextRelations

/-!
# Actual affine regions sharing the same full original W

These are primitive finite affine input data and exact geometric sharing data.
No repair, boundary range, singleton relation, gluing conclusion or vanishing
certificate is a field. A compatible range fixes only the shared candidate
permission; every other candidate in the external region is still quantified.

## Implementation notes

The record stores the whole actual affine input and the exact images of all
shared cells, with primitive word/route laws. A record containing just the
realized relation was rejected: it would assume the realization required by
GOAL E and n1017 §3.2 and lose the full external-input quantifier. Exact images
also distinguish original parallel names and preserve every shared vector.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (W : FiniteTransportPresentation.{uG})
variable (LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A)
variable (cW : W.TwoCell → A) (PW : ClosedRegion W) (CW : Set (EdgeName (K := W)))

/-- A whole actual affine input containing the specified full closed shared presentation. -/
structure AffineContextInput where
  /-- The complete original finite external or internal region. -/
  geometry : FiniteTransportPresentation.{uG}
  /-- Exact typed sharing of every original W cell and rewriting context. -/
  embedding : FinitePresentationEmbedding W geometry
  /-- The shared cells form a closed original region of this input. -/
  shared : ClosedRegion geometry
  /-- All and only the named shared original vertices occur. -/
  shared_vertices : shared.vertices = Set.range embedding.vertex
  /-- All and only the named shared original edges occur. -/
  shared_edges : shared.edges = Set.range embedding.edgeName
  /-- All and only the named shared original authored faces occur. -/
  shared_faces : shared.faces = Set.range embedding.face
  /-- All and only the named shared original three-cells occur. -/
  shared_triples : shared.triples = Set.range embedding.triple
  /-- Every arbitrary original real affine edge is retained separately. -/
  originals : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Operations k A
  /-- Every full original real reference edge is retained separately. -/
  references : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Operations k A
  /-- Original authored translation comparisons. -/
  comparisons : geometry.TwoCell → A
  /-- Actual full linear alignment of every original authored face. -/
  aligned : ∀ f : geometry.TwoCell,
    (GroupExtension.pathValue geometry references (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry references (geometry.twoRight f)).linear
  /-- Actual authored equality of both complete original three-cell routes. -/
  three_law : ∀ f : geometry.ThreeCell,
    pastingOperation geometry references comparisons (geometry.threeLeft f) =
      pastingOperation geometry references comparisons (geometry.threeRight f)
  /-- The original physical fixed part is closed on all original cells. -/
  fixed : ClosedRegion geometry
  /-- The original references agree with every authored physically fixed face. -/
  fixed_faces : ∀ f ∈ fixed.faces,
    translation (k := k) (comparisons f) * GroupExtension.pathValue geometry references (geometry.twoLeft f) =
      GroupExtension.pathValue geometry references (geometry.twoRight f)
  /-- All named original candidates of the whole input. -/
  candidates : Set (EdgeName (K := geometry))
  /-- Sharing preserves precisely the specified original reference operation. -/
  shared_reference : ∀ {i j : W.Vertex} (e : W.Edge i j), references (embedding.edge e) = RW e
  /-- Sharing preserves the specified actual original core, while keeping each original edge separate. -/
  shared_core : ∀ {i j : W.Vertex} (e : W.Edge i j),
    projection (references (embedding.edge e) * (originals (embedding.edge e))⁻¹) =
      projection (RW e * (LW e)⁻¹)
  /-- Sharing preserves every original authored comparison operation. -/
  shared_comparison : ∀ f : W.TwoCell, comparisons (embedding.face f) = cW f
  /-- No shared vertex gains or loses its physical fixed condition. -/
  shared_fixed_vertices : ∀ v : W.Vertex, embedding.vertex v ∈ fixed.vertices ↔ v ∈ PW.vertices
  /-- No shared original edge gains or loses its physical fixed condition. -/
  shared_fixed_edges : ∀ e : EdgeName (K := W), embedding.edgeName e ∈ fixed.edges ↔ e ∈ PW.edges
  /-- No shared original face gains or loses its physical fixed condition. -/
  shared_fixed_faces : ∀ f : W.TwoCell, embedding.face f ∈ fixed.faces ↔ f ∈ PW.faces
  /-- No shared original three-cell gains or loses its physical fixed condition. -/
  shared_fixed_triples : ∀ f : W.ThreeCell, embedding.triple f ∈ fixed.triples ↔ f ∈ PW.triples
  /-- Shared candidates preserve their original names and membership. -/
  shared_candidates : ∀ e : EdgeName (K := W), embedding.edgeName e ∈ candidates ↔ e ∈ CW

namespace AffineContextInput
variable {W LW RW cW PW CW}
variable (I : AffineContextInput W LW RW cW PW CW)

/-- Whole candidate permissions compatible with precisely the same shared candidate S. -/
structure Range (S : Set (EdgeName (K := W))) where
  /-- All permitted original candidates in this whole region, including internal candidates. -/
  allowed : Set (EdgeName (K := I.geometry))
  /-- Shared original candidates have precisely the same permitted names. -/
  shared_allowed : ∀ e ∈ CW, I.embedding.edgeName e ∈ allowed ↔ e ∈ S

/-- Actual whole repairs are independently specified by the original operations and faces. -/
abbrev Repairs {S : Set (EdgeName (K := W))} (a : I.Range S) :=
  Repair I.geometry I.references I.comparisons (fixedEdgesForRange I.fixed.edges I.candidates a.allowed)

/-- Exact primitive sharing and matching permissions preserve every physically forbidden shared edge. -/
theorem shared_forbidden {S : Set (EdgeName (K := W))} (a : I.Range S)
    (e : EdgeName (K := W)) (he : e ∈ fixedEdgesForRange PW.edges CW S) :
    I.embedding.edgeName e ∈ fixedEdgesForRange I.fixed.edges I.candidates a.allowed := by
  rcases he with hp | ⟨hc,hs⟩
  · exact Or.inl ((I.shared_fixed_edges e).mpr hp)
  · exact Or.inr ⟨(I.shared_candidates e).mpr hc, fun h => hs ((a.shared_allowed e hc).mp h)⟩

/-- Every actual whole repair yields a genuine shared repair from exact original operations. -/
def sharedRepair {S : Set (EdgeName (K := W))} (a : I.Range S) (s : I.Repairs a) :
    Repair W RW cW (fixedEdgesForRange PW.edges CW S) :=
  restrictEmbeddedRepair I.embedding RW I.references cW I.comparisons
    (fixedEdgesForRange PW.edges CW S) (fixedEdgesForRange I.fixed.edges I.candidates a.allowed)
    I.shared_reference I.shared_comparison (I.shared_forbidden a) s

/-- The boundary reads the actual shared correction from original affine operations. -/
def boundary {S : Set (EdgeName (K := W))} (a : I.Range S) (s : I.Repairs a) :
    EdgeName (K := W) → A :=
  realCorrection W RW cW (fixedEdgesForRange PW.edges CW S) (I.sharedRepair a s)

/-- Every boundary value is the same full actual quotient at its named original environment edge. -/
theorem boundary_value {S : Set (EdgeName (K := W))} (a : I.Range S) (s : I.Repairs a)
    (e : EdgeName (K := W)) : I.boundary a s e =
      realCorrection I.geometry I.references I.comparisons
        (fixedEdgesForRange I.fixed.edges I.candidates a.allowed) s (I.embedding.edgeName e) :=
  embedded_correction_value I.embedding RW I.references cW I.comparisons
    (fixedEdgesForRange PW.edges CW S) (fixedEdgesForRange I.fixed.edges I.candidates a.allowed)
    I.shared_reference I.shared_comparison (I.shared_forbidden a) s e

end AffineContextInput
end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine
