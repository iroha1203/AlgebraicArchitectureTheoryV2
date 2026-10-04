import ResearchLean.AG.VisibleCycleReflection.FiniteIncidenceGeometry
import Formal.Util.AssertStandardAxioms

/-!
# The three specified primitive inputs and actual incidence covers

## Implementation notes

Point codes are vertices followed by the listed edge points. The topology lists
all upward closed subsets for the vertex-below-incident-edge order. Primitive
relation, geometry, and target columns are supplied separately. The proofs of
T0 use the generic incidence construction and finite primitive-table checks.
Using target membership to generate geometric intersections was rejected: the
fixed specification supplies these columns independently.
-/

namespace AAT.AG.VisibleCycleReflection.WitnessInputs
open FiniteInputTable

/-- Original four-source input: c has value zero; the three related sources have value one. -/
abbrev relatedPrimitive : FiniteInputTable where
  sourceCount := 4
  lawCount := 1
  targetCount := 4
  pointCount := 0
  chartCount := 0
  valueCount := fun _ => 2
  eval := fun _ s => if s = 0 then 0 else 1
  read := id
  relation := fun g h => (g.2 == 1 && h.2 == 2) || (g.2 == 2 && h.2 == 3)
  opens := ∅
  chart := Fin.elim0
  target := Fin.elim0

/-- The relation chain, identity reading, and original evaluation discharge all primitive T0 rows. -/
theorem relatedPrimitive_valid : relatedPrimitive.SurjectiveReading ∧
    relatedPrimitive.AdequateReading ∧ relatedPrimitive.LabelPreserving ∧
    relatedPrimitive.RelationReflecting := by decide

/-- Original forest input with two sources, distinct labels, and no primitive relation. -/
abbrev forestPrimitive : FiniteInputTable where
  sourceCount := 2
  lawCount := 1
  targetCount := 2
  pointCount := 0
  chartCount := 0
  valueCount := fun _ => 2
  eval := fun _ s => s
  read := id
  relation := fun _ _ => false
  opens := ∅
  chart := Fin.elim0
  target := Fin.elim0

/-- The forest's equal labels already have equal original generators, so its empty relation satisfies Rq. -/
theorem forestPrimitive_valid : forestPrimitive.SurjectiveReading ∧
    forestPrimitive.AdequateReading ∧ forestPrimitive.LabelPreserving ∧
    forestPrimitive.RelationReflecting := by decide

/-- Triangle 012 with the bridge 23, in the specified edge-point order. -/
abbrev geometryOne : FiniteIncidenceGeometry := ⟨4,4,![(0,1),(0,2),(1,2),(2,3)]⟩
/-- Two triangles sharing vertex zero, with 34 preceding 03 and 04 in the failure search. -/
abbrev geometryTwo : FiniteIncidenceGeometry := ⟨5,6,![(0,1),(0,2),(1,2),(3,4),(0,3),(0,4)]⟩
/-- The three-vertex path, in its specified edge-point order. -/
abbrev geometryThree : FiniteIncidenceGeometry := ⟨3,2,![(0,1),(1,2)]⟩

/-- W1 independent target columns. -/
def targetOne : Fin 4 → Finset (Fin 4) := ![{0,1,2},{0,1,3},{0,2,3},{0}]
/-- W2 independent target columns. -/
def targetTwo : Fin 5 → Finset (Fin 4) := ![{0,1,2},{0,1,3},{0,2,3},{0},{0}]
/-- W3 independent target columns. -/
def targetThree : Fin 3 → Finset (Fin 2) := ![{0,1},{0},{0}]

/-- W1 complete finite original primitive, geometric, and target input. -/
abbrev one : FiniteInputTable := geometryOne.table relatedPrimitive targetOne
  [(0,1),(0,2),(1,2),(2,3)]
/-- W2 complete finite original input with the specified deterministic failure order. -/
abbrev two : FiniteInputTable := geometryTwo.table relatedPrimitive targetTwo
  [(0,1),(0,2),(1,2),(3,4),(0,3),(0,4)]
/-- W3 complete finite original forest input. -/
abbrev three : FiniteInputTable := geometryThree.table forestPrimitive targetThree [(0,1),(1,2)]

/-- Public evaluation of the specified last W1 target column. -/
theorem one_target_three : one.target (3 : Fin 4) = {0} := rfl
/-- The fixed W1 geometry supplies both an incident and a nonincident pair. -/
theorem incidence_instances : geometryOne.Incident 0 0 ∧ ¬geometryOne.Incident 3 0 := by
  rw [geometryOne.incident_iff_endpoints,geometryOne.incident_iff_endpoints]
  decide
/-- The same fixed vertex/edge supplies positive and negative order instances. -/
theorem below_instances :
    geometryOne.Below (geometryOne.vertexPoint 0) (geometryOne.edgePoint 0) ∧
    ¬geometryOne.Below (geometryOne.edgePoint 0) (geometryOne.vertexPoint 0) :=
  ⟨geometryOne.below_vertex_edge 0 0 incidence_instances.1,
    geometryOne.not_below_edge_vertex 0 0⟩
/-- A full W1 chart is upward closed; the same vertex alone is not. -/
theorem upClosed_instances : geometryOne.UpClosed (geometryOne.chart 0) ∧
    ¬geometryOne.UpClosed {geometryOne.vertexPoint 0} :=
  ⟨geometryOne.chart_upClosed 0,geometryOne.singleton_not_upClosed 0 0 incidence_instances.1⟩

/-- W1 finite table constructs every primitive, topological, geometric, and target T0 condition. -/
theorem one_valid : one.Valid := by
  refine ⟨relatedPrimitive_valid.1,relatedPrimitive_valid.2.1,
    relatedPrimitive_valid.2.2.1,relatedPrimitive_valid.2.2.2,
    geometryOne.table_topology_valid _ _ _,geometryOne.table_geometry_valid _ _ _
      (by decide) (by decide) (by decide),?_⟩
  decide
/-- W2 finite table constructs every T0 condition, including all actual intersections. -/
theorem two_valid : two.Valid := by
  refine ⟨relatedPrimitive_valid.1,relatedPrimitive_valid.2.1,
    relatedPrimitive_valid.2.2.1,relatedPrimitive_valid.2.2.2,
    geometryTwo.table_topology_valid _ _ _,geometryTwo.table_geometry_valid _ _ _
      (by decide) (by decide) (by decide),?_⟩
  decide
/-- W3 finite table constructs every T0 condition despite label one having no visible edge. -/
theorem three_valid : three.Valid := by
  refine ⟨forestPrimitive_valid.1,forestPrimitive_valid.2.1,
    forestPrimitive_valid.2.2.1,forestPrimitive_valid.2.2.2,
    geometryThree.table_topology_valid _ _ _,geometryThree.table_geometry_valid _ _ _
      (by decide) (by decide) (by decide),?_⟩
  decide

/-- W1's finite validation succeeds for its actual table. -/
theorem one_validates : one.validate = true := one.validate_true_iff.mpr one_valid
/-- W2's finite validation succeeds before its reflection failure is tested. -/
theorem two_validates : two.validate = true := two.validate_true_iff.mpr two_valid
/-- W3's finite validation succeeds for its actual forest table. -/
theorem three_validates : three.validate = true := three.validate_true_iff.mpr three_valid

/-- W1 decoding gives precisely the specified upper-set Alexandrov topology. -/
theorem one_topology : one.actualTopology one_valid = geometryOne.upperTopology :=
  geometryOne.table_topology_eq_upper _ _ _ one_valid
/-- W2 decoding gives precisely the specified upper-set Alexandrov topology. -/
theorem two_topology : two.actualTopology two_valid = geometryTwo.upperTopology :=
  geometryTwo.table_topology_eq_upper _ _ _ two_valid
/-- W3 decoding gives precisely the specified upper-set Alexandrov topology. -/
theorem three_topology : three.actualTopology three_valid = geometryThree.upperTopology :=
  geometryThree.table_topology_eq_upper _ _ _ three_valid

/-- W1 complete nerve edge columns, in the stated order. -/
theorem one_edges : one.rawEdges.map Subtype.val = [(0,1),(0,2),(1,2),(2,3)] := by decide
/-- W2 complete nerve edge columns, retaining its failure search order. -/
theorem two_edges : two.rawEdges.map Subtype.val = [(0,1),(0,2),(1,2),(3,4),(0,3),(0,4)] := by decide
/-- W3 complete nerve edge columns. -/
theorem three_edges : three.rawEdges.map Subtype.val = [(0,1),(1,2)] := by decide

/-- W1 label zero is visible everywhere and label one exactly on the triangle vertices and edges. -/
theorem one_visibility :
    (∀ i, one.VertexVisible ⟨0,0⟩ i) ∧
    (∀ i, one.VertexVisible ⟨0,1⟩ i ↔ i ≠ 3) ∧
    (∀ e : one.RawEdge, one.EdgeVisible ⟨0,0⟩ e.1) ∧
    (∀ e : one.RawEdge, one.EdgeVisible ⟨0,1⟩ e.1 ↔ e.1 ≠ (2,3)) := by decide
/-- W2 label zero is visible everywhere and label one exactly on the first triangle. -/
theorem two_visibility :
    (∀ i, two.VertexVisible ⟨0,0⟩ i) ∧
    (∀ i, two.VertexVisible ⟨0,1⟩ i ↔ i < 3) ∧
    (∀ e : two.RawEdge, two.EdgeVisible ⟨0,0⟩ e.1) ∧
    (∀ e : two.RawEdge, two.EdgeVisible ⟨0,1⟩ e.1 ↔ e.1.2 < 3) := by decide
/-- W3 label zero is visible everywhere; label one is the single vertex zero and has no edge. -/
theorem three_visibility :
    (∀ i, three.VertexVisible ⟨0,0⟩ i) ∧
    (∀ i, three.VertexVisible ⟨0,1⟩ i ↔ i = 0) ∧
    (∀ e : three.RawEdge, three.EdgeVisible ⟨0,0⟩ e.1) ∧
    (∀ e : three.RawEdge, ¬ three.EdgeVisible ⟨0,1⟩ e.1) := by decide

end AAT.AG.VisibleCycleReflection.WitnessInputs
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.WitnessInputs
