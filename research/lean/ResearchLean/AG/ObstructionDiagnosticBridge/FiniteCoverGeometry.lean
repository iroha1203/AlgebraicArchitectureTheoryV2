import ResearchLean.AG.ObstructionDiagnosticBridge.FaceEmptyCechNormalization
import Mathlib.Topology.Order.UpperLowerSetTopology
import Formal.Util.AssertStandardAxioms

/-!
# The selected eight-point cover geometry for G-125

This module constructs the finite topological space fixed in the G-125 paper
design.  Its points are four vertices and four edge points, ordered only from
an incident vertex to its edge point.  The upper-set topology therefore gives
the minimal open neighbourhood of a vertex as that vertex together with its
incident edge points.

The fine cover consists of the four vertex neighbourhoods.  The coarse cover
joins the two neighbourhoods at `a0` and `a1` and keeps the neighbourhoods at
`b` and `c`.  Both covers are proved to cover the same space.  Their patch and
nonempty pair-overlap supports are nonempty and preconnected.

For face provenance, `CompleteFaceIndex` is not an arbitrary supplied type: it
contains an injective ordered triple of charts together with an actual point
in their intersection.  It is therefore complete for nonempty intersections
by construction.  Exhaustive proofs show that this type is empty for both
covers.  Thus the selected face-index emptiness is derived from the concrete
geometry rather than assumed.
-/

noncomputable section

open Set TopologicalSpace

namespace AAT.AG.ObstructionDiagnosticBridge
namespace SelectedFiniteGeometry

/-- Vertices of the selected four-cycle refinement. -/
inductive Vertex where
  | a0 | a1 | b | c
  deriving DecidableEq, Fintype

/-- Edge points of the selected four-cycle refinement. -/
inductive Edge where
  | k | ab | bc | ac
  deriving DecidableEq, Fintype

/-- The two endpoints of each edge point. -/
def Edge.incident : Edge → Vertex → Prop
  | .k, v => v = .a0 ∨ v = .a1
  | .ab, v => v = .a1 ∨ v = .b
  | .bc, v => v = .b ∨ v = .c
  | .ac, v => v = .a0 ∨ v = .c

instance (e : Edge) (v : Vertex) : Decidable (e.incident v) := by
  cases e <;> cases v <;> simp only [Edge.incident] <;> infer_instance

/-- Four vertex points and four edge points. -/
inductive Point where
  | vertex : Vertex → Point
  | edge : Edge → Point
  deriving DecidableEq, Fintype

/-- Incidence order: a vertex lies below exactly its incident edge points. -/
def Point.le : Point → Point → Prop
  | .vertex v, .vertex w => v = w
  | .vertex v, .edge e => e.incident v
  | .edge _, .vertex _ => False
  | .edge e, .edge f => e = f

instance (x y : Point) : Decidable (Point.le x y) := by
  cases x <;> cases y <;> simp only [Point.le] <;> infer_instance

instance pointPartialOrder : PartialOrder Point where
  le := Point.le
  le_refl x := by cases x <;> simp [Point.le]
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp_all [Point.le, Edge.incident]
  le_antisymm := by
    intro x y hxy hyx
    cases x <;> cases y <;> simp_all [Point.le]

@[simp]
theorem vertex_le_vertex_iff (v w : Vertex) :
    Point.vertex v ≤ Point.vertex w ↔ v = w :=
  Iff.rfl

@[simp]
theorem vertex_le_edge_iff (v : Vertex) (e : Edge) :
    Point.vertex v ≤ Point.edge e ↔ e.incident v :=
  Iff.rfl

@[simp]
theorem edge_le_vertex_iff (e : Edge) (v : Vertex) :
    ¬ Point.edge e ≤ Point.vertex v := by
  intro h
  exact h

@[simp]
theorem edge_le_edge_iff (e f : Edge) :
    Point.edge e ≤ Point.edge f ↔ e = f :=
  Iff.rfl

/-- The selected finite Alexandrov space. -/
abbrev Space := Topology.WithUpperSet Point

/-- A vertex as a point of the selected space. -/
def vertexPoint (v : Vertex) : Space :=
  Topology.WithUpperSet.toUpperSet (Point.vertex v)

/-- An edge point as a point of the selected space. -/
def edgePoint (e : Edge) : Space :=
  Topology.WithUpperSet.toUpperSet (Point.edge e)

/-- Minimal open neighbourhood of a selected vertex. -/
def patch (v : Vertex) : Opens Space where
  carrier := Set.Ici (vertexPoint v)
  is_open' := by
    rw [Topology.IsUpperSet.isOpen_iff_isUpperSet]
    intro x y hxy hx
    exact le_trans hx hxy

@[simp]
theorem vertexPoint_mem_patch_iff (v w : Vertex) :
    vertexPoint w ∈ patch v ↔ v = w := by
  rfl

@[simp]
theorem edgePoint_mem_patch_iff (v : Vertex) (e : Edge) :
    edgePoint e ∈ patch v ↔ e.incident v := by
  rfl

/-- A minimal vertex neighbourhood is nonempty. -/
def patchNonempty (v : Vertex) : Nonempty (patch v) :=
  ⟨⟨vertexPoint v, show vertexPoint v ≤ vertexPoint v from le_rfl⟩⟩

/-- A minimal vertex neighbourhood is preconnected in the upper-set topology. -/
theorem patch_isPreconnected (v : Vertex) :
    IsPreconnected (patch v : Set Space) := by
  intro left right hleft hright hcover
  rintro ⟨x, hxpatch, hxleft⟩ ⟨y, hypatch, hyright⟩
  have hvpatch : vertexPoint v ∈ (patch v : Set Space) :=
    show vertexPoint v ≤ vertexPoint v from le_rfl
  have hbase : vertexPoint v ∈ left ∪ right := hcover hvpatch
  rcases hbase with hbase | hbase
  · refine ⟨y, hypatch, ?_, hyright⟩
    exact (Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hleft) hypatch hbase
  · refine ⟨x, hxpatch, hxleft, ?_⟩
    exact (Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hright) hxpatch hbase

/-- Preconnected-space package used by the locally constant coefficient API. -/
def patchPreconnectedSpace (v : Vertex) : PreconnectedSpace (patch v) :=
  Subtype.preconnectedSpace (patch_isPreconnected v)

/-- The four fine charts. -/
abbrev FineChart := Vertex

/-- Fine patch support. -/
def finePatch (v : FineChart) : Opens Space := patch v

/-- The three coarse charts. -/
inductive CoarseChart where
  | c0 | c1 | c2
  deriving DecidableEq, Fintype

/-- Coarse patch support on the same eight-point space. -/
def coarsePatch : CoarseChart → Opens Space
  | .c0 => patch .a0 ⊔ patch .a1
  | .c1 => patch .b
  | .c2 => patch .c

/-- Fine chart `a0` refines coarse chart `c0`. -/
theorem finePatch_a0_le_coarsePatch_c0 :
    finePatch .a0 ≤ coarsePatch .c0 :=
  le_sup_left

/-- Fine chart `a1` refines coarse chart `c0`. -/
theorem finePatch_a1_le_coarsePatch_c0 :
    finePatch .a1 ≤ coarsePatch .c0 :=
  le_sup_right

/-- Fine chart `b` is coarse chart `c1`. -/
@[simp]
theorem finePatch_b_eq_coarsePatch_c1 :
    finePatch .b = coarsePatch .c1 :=
  rfl

/-- Fine chart `c` is coarse chart `c2`. -/
@[simp]
theorem finePatch_c_eq_coarsePatch_c2 :
    finePatch .c = coarsePatch .c2 :=
  rfl

/-- The fine cover covers all eight points. -/
theorem fine_cover (x : Space) : ∃ v : FineChart, x ∈ finePatch v := by
  induction x using Topology.WithUpperSet.rec with
  | toUpperSet point =>
      cases point with
      | vertex v => exact ⟨v, vertexPoint_mem_patch_iff v v |>.2 rfl⟩
      | edge e =>
          cases e
          · exact ⟨.a0, edgePoint_mem_patch_iff .a0 .k |>.2 (by simp [Edge.incident])⟩
          · exact ⟨.a1, edgePoint_mem_patch_iff .a1 .ab |>.2 (by simp [Edge.incident])⟩
          · exact ⟨.b, edgePoint_mem_patch_iff .b .bc |>.2 (by simp [Edge.incident])⟩
          · exact ⟨.a0, edgePoint_mem_patch_iff .a0 .ac |>.2 (by simp [Edge.incident])⟩

/-- The coarse cover covers the same eight points. -/
theorem coarse_cover (x : Space) : ∃ v : CoarseChart, x ∈ coarsePatch v := by
  obtain ⟨v, hv⟩ := fine_cover x
  cases v
  · exact ⟨.c0, finePatch_a0_le_coarsePatch_c0 hv⟩
  · exact ⟨.c0, finePatch_a1_le_coarsePatch_c0 hv⟩
  · exact ⟨.c1, by simpa using hv⟩
  · exact ⟨.c2, by simpa using hv⟩

/-- The joined coarse patch is preconnected through the shared point `k`. -/
theorem coarsePatch_c0_isPreconnected :
    IsPreconnected (coarsePatch .c0 : Set Space) := by
  change IsPreconnected ((patch .a0 : Set Space) ∪ patch .a1)
  apply (patch_isPreconnected .a0).union' _ (patch_isPreconnected .a1)
  exact ⟨edgePoint .k, by simp [Edge.incident]⟩

/-- Every coarse patch is nonempty. -/
def coarsePatchNonempty (v : CoarseChart) : Nonempty (coarsePatch v) := by
  cases v
  · exact ⟨⟨vertexPoint .a0, by simp [coarsePatch]⟩⟩
  · exact patchNonempty .b
  · exact patchNonempty .c

/-- Every coarse patch is preconnected. -/
def coarsePatchPreconnectedSpace (v : CoarseChart) :
    PreconnectedSpace (coarsePatch v) := by
  cases v
  · exact Subtype.preconnectedSpace coarsePatch_c0_isPreconnected
  · exact patchPreconnectedSpace .b
  · exact patchPreconnectedSpace .c

/-- Left endpoint of a fine edge. -/
def fineEdgeLeft : Edge → FineChart
  | .k => .a0
  | .ab => .a1
  | .bc => .b
  | .ac => .a0

/-- Right endpoint of a fine edge. -/
def fineEdgeRight : Edge → FineChart
  | .k => .a1
  | .ab => .b
  | .bc => .c
  | .ac => .c

/-- Actual fine pair-overlap support. -/
def fineOverlap (e : Edge) : Opens Space :=
  finePatch (fineEdgeLeft e) ⊓ finePatch (fineEdgeRight e)

/-- Every selected fine pair-overlap is exactly its edge point. -/
theorem fineOverlap_eq_singleton (e : Edge) :
    (fineOverlap e : Set Space) = {edgePoint e} := by
  ext x
  induction x using Topology.WithUpperSet.rec with
  | toUpperSet point =>
      cases e <;>
        cases point with
        | vertex v => cases v <;> simp [fineOverlap, finePatch, fineEdgeLeft,
            fineEdgeRight, patch, vertexPoint, edgePoint,
            Topology.WithUpperSet.toUpperSet_le_iff]
        | edge edge => cases edge <;> simp [fineOverlap, finePatch, fineEdgeLeft,
            fineEdgeRight, patch, vertexPoint, edgePoint,
            Topology.WithUpperSet.toUpperSet_le_iff, Edge.incident]

/-- Fine pair-overlaps are nonempty. -/
def fineOverlapNonempty (e : Edge) : Nonempty (fineOverlap e) := by
  refine ⟨⟨edgePoint e, ?_⟩⟩
  change edgePoint e ∈ (fineOverlap e : Set Space)
  rw [fineOverlap_eq_singleton]
  exact Set.mem_singleton _

/-- Fine pair-overlaps are preconnected. -/
def fineOverlapPreconnectedSpace (e : Edge) :
    PreconnectedSpace (fineOverlap e) :=
  Subtype.preconnectedSpace (by
    rw [fineOverlap_eq_singleton]
    exact isPreconnected_singleton)

/-- The three nonempty coarse pair-overlaps. -/
inductive CoarseEdge where
  | ab | bc | ac
  deriving DecidableEq, Fintype

/-- Left endpoint of a coarse edge. -/
def coarseEdgeLeft : CoarseEdge → CoarseChart
  | .ab => .c0
  | .bc => .c1
  | .ac => .c0

/-- Right endpoint of a coarse edge. -/
def coarseEdgeRight : CoarseEdge → CoarseChart
  | .ab => .c1
  | .bc => .c2
  | .ac => .c2

/-- Actual coarse pair-overlap support. -/
def coarseOverlap (e : CoarseEdge) : Opens Space :=
  coarsePatch (coarseEdgeLeft e) ⊓ coarsePatch (coarseEdgeRight e)

/-- Edge point represented by each coarse pair-overlap. -/
def coarseEdgePoint : CoarseEdge → Edge
  | .ab => .ab
  | .bc => .bc
  | .ac => .ac

/-- Every selected coarse pair-overlap is exactly its named edge point. -/
theorem coarseOverlap_eq_singleton (e : CoarseEdge) :
    (coarseOverlap e : Set Space) = {edgePoint (coarseEdgePoint e)} := by
  ext x
  induction x using Topology.WithUpperSet.rec with
  | toUpperSet point =>
      cases e <;>
        cases point with
        | vertex v => cases v <;> simp [coarseOverlap, coarsePatch,
            coarseEdgeLeft, coarseEdgeRight, coarseEdgePoint, patch,
            vertexPoint, edgePoint, Topology.WithUpperSet.toUpperSet_le_iff]
        | edge edge => cases edge <;> simp [coarseOverlap, coarsePatch,
            coarseEdgeLeft, coarseEdgeRight, coarseEdgePoint, patch,
            vertexPoint, edgePoint, Topology.WithUpperSet.toUpperSet_le_iff,
            Edge.incident]

/-- Coarse pair-overlaps are nonempty. -/
def coarseOverlapNonempty (e : CoarseEdge) : Nonempty (coarseOverlap e) := by
  refine ⟨⟨edgePoint (coarseEdgePoint e), ?_⟩⟩
  change edgePoint (coarseEdgePoint e) ∈ (coarseOverlap e : Set Space)
  rw [coarseOverlap_eq_singleton]
  exact Set.mem_singleton _

/-- Coarse pair-overlaps are preconnected. -/
def coarseOverlapPreconnectedSpace (e : CoarseEdge) :
    PreconnectedSpace (coarseOverlap e) :=
  Subtype.preconnectedSpace (by
    rw [coarseOverlap_eq_singleton]
    exact isPreconnected_singleton)

/-- A complete index for nonempty intersections of three distinct patches.

The point field is the provenance: every inhabitant is an actual geometric
triple-overlap witness, while every nonempty intersection produces an
inhabitant by the constructor below.
-/
structure CompleteFaceIndex (Chart : Type) (support : Chart → Opens Space) where
  chart : Fin 3 → Chart
  chart_injective : Function.Injective chart
  point : Space
  point_mem : ∀ i, point ∈ support (chart i)

/-- Completeness is definitional: an actual distinct triple-overlap witness
produces an element of the selected face index. -/
def CompleteFaceIndex.ofWitness {Chart : Type} {support : Chart → Opens Space}
    (chart : Fin 3 → Chart) (hinjective : Function.Injective chart)
    (point : Space) (hpoint : ∀ i, point ∈ support (chart i)) :
    CompleteFaceIndex Chart support where
  chart := chart
  chart_injective := hinjective
  point := point
  point_mem := hpoint

set_option maxHeartbeats 1000000

/-- No point belongs to three distinct fine patches. -/
theorem fine_distinct_triple_empty
    (chart : Fin 3 → FineChart) (hinjective : Function.Injective chart)
    (point : Space) : ¬ ∀ i, point ∈ finePatch (chart i) := by
  intro hpoint
  have h01 : chart 0 ≠ chart 1 := fun h => by
    have := hinjective h
    omega
  have h02 : chart 0 ≠ chart 2 := fun h => by
    have := hinjective h
    omega
  have h12 : chart 1 ≠ chart 2 := fun h => by
    have := hinjective h
    omega
  have h0 := hpoint 0
  have h1 := hpoint 1
  have h2 := hpoint 2
  induction point using Topology.WithUpperSet.rec with
  | toUpperSet point =>
      cases point with
      | vertex v =>
          cases v <;>
            cases hchart0 : chart 0 <;>
            cases hchart1 : chart 1 <;>
            cases hchart2 : chart 2 <;>
            simp_all [finePatch, patch, vertexPoint,
              Topology.WithUpperSet.toUpperSet_le_iff]
      | edge e =>
          cases e <;>
            cases hchart0 : chart 0 <;>
            cases hchart1 : chart 1 <;>
            cases hchart2 : chart 2 <;>
            simp_all [finePatch, patch, vertexPoint,
              Topology.WithUpperSet.toUpperSet_le_iff, Edge.incident]

/-- The complete fine face index is empty by geometric triple-intersection
emptiness. -/
instance fineCompleteFaceIndexIsEmpty :
    IsEmpty (CompleteFaceIndex FineChart finePatch) where
  false face :=
    fine_distinct_triple_empty face.chart face.chart_injective face.point
      face.point_mem

/-- No point belongs to three distinct coarse patches. -/
theorem coarse_distinct_triple_empty
    (chart : Fin 3 → CoarseChart) (hinjective : Function.Injective chart)
    (point : Space) : ¬ ∀ i, point ∈ coarsePatch (chart i) := by
  intro hpoint
  have h01 : chart 0 ≠ chart 1 := fun h => by
    have := hinjective h
    omega
  have h02 : chart 0 ≠ chart 2 := fun h => by
    have := hinjective h
    omega
  have h12 : chart 1 ≠ chart 2 := fun h => by
    have := hinjective h
    omega
  have h0 := hpoint 0
  have h1 := hpoint 1
  have h2 := hpoint 2
  induction point using Topology.WithUpperSet.rec with
  | toUpperSet point =>
      cases point with
      | vertex v =>
          cases v <;>
            cases hchart0 : chart 0 <;>
            cases hchart1 : chart 1 <;>
            cases hchart2 : chart 2 <;>
            simp_all [coarsePatch, patch, vertexPoint,
              Topology.WithUpperSet.toUpperSet_le_iff]
      | edge e =>
          cases e <;>
            cases hchart0 : chart 0 <;>
            cases hchart1 : chart 1 <;>
            cases hchart2 : chart 2 <;>
            simp_all [coarsePatch, patch, vertexPoint,
              Topology.WithUpperSet.toUpperSet_le_iff, Edge.incident]

set_option maxHeartbeats 200000

/-- The complete coarse face index is empty by geometric triple-intersection
emptiness. -/
instance coarseCompleteFaceIndexIsEmpty :
    IsEmpty (CompleteFaceIndex CoarseChart coarsePatch) where
  false face :=
    coarse_distinct_triple_empty face.chart face.chart_injective face.point
      face.point_mem

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge.SelectedFiniteGeometry

end SelectedFiniteGeometry
end AAT.AG.ObstructionDiagnosticBridge
