import ResearchLean.AG.VisibleCycleReflection.ActualTableDecode
import Formal.Util.AssertStandardAxioms

/-!
# Concrete finite validator witnesses

## Implementation notes

The positive table has one actual point, chart, primitive Law, and primitive
source. Each negative table changes a raw column without supplying a rejection
certificate. The Boolean computations are checked by the Lean kernel.
-/

namespace AAT.AG.VisibleCycleReflection.FiniteValidationWitness
open FiniteInputTable AAT.AG.ResolutionInvariance

/-- A nonempty primitive input and nonempty one-chart geometry. -/
def onePointTable : FiniteInputTable where
  sourceCount := 1
  lawCount := 1
  targetCount := 1
  pointCount := 1
  chartCount := 1
  valueCount := fun _ => 1
  eval := fun _ _ => 0
  read := fun _ => 0
  relation := fun _ _ => false
  opens := (Finset.univ : Finset (Fin 1)).powerset
  chart := fun _ => Finset.univ
  target := fun _ => Finset.univ

/-- The actual primitive and geometric input validator succeeds by finite computation. -/
theorem onePointTable_validates : onePointTable.validate = true := by decide

/-- The positive input's T0 proof is obtained from the computed validator. -/
theorem onePointTable_valid : onePointTable.Valid :=
  onePointTable.validate_true_iff.mp onePointTable_validates

/-- A raw table with no declared open sets. -/
def missingOpens : FiniteInputTable := {onePointTable with opens := ∅}

/-- An invalid topology is rejected before actual input decoding. -/
theorem missingOpens_rejected : missingOpens.validate = false := by decide

/-- A raw table whose chart has no geometric point. -/
def emptyChart : FiniteInputTable := {onePointTable with chart := fun _ => ∅}

/-- An invalid geometric chart is rejected independently of target support. -/
theorem emptyChart_rejected : emptyChart.validate = false := by decide

/-- A raw table whose independent target column is empty. -/
def emptyTarget : FiniteInputTable := {onePointTable with target := fun _ => ∅}

/-- An empty target column is rejected independently of geometric chart support. -/
theorem emptyTarget_rejected : emptyTarget.validate = false := by decide

/-- Equal generated labels with two unrelated primitive sources. -/
def missingPrimitiveRelation : FiniteInputTable where
  sourceCount := 2
  lawCount := 1
  targetCount := 2
  pointCount := 1
  chartCount := 1
  valueCount := fun _ => 1
  eval := fun _ _ => 0
  read := id
  relation := fun _ _ => false
  opens := (Finset.univ : Finset (Fin 1)).powerset
  chart := fun _ => Finset.univ
  target := fun _ => Finset.univ

/-- Rq is computed from the raw relation and rejects unrelated equal labels. -/
theorem missingPrimitiveRelation_rejected : missingPrimitiveRelation.validate = false := by decide

/-- A target code with no reading preimage. -/
def missingReading : FiniteInputTable where
  sourceCount := 1
  lawCount := 1
  targetCount := 2
  pointCount := 1
  chartCount := 1
  valueCount := fun _ => 1
  eval := fun _ _ => 0
  read := fun _ => 0
  relation := fun _ _ => false
  opens := (Finset.univ : Finset (Fin 1)).powerset
  chart := fun _ => Finset.univ
  target := fun _ => Finset.univ

/-- Surjectivity failure is visible to the finite source search. -/
theorem missingReading_not_surjective : ¬ missingReading.SurjectiveReading := by decide

/-- Distinct Law values on one reading fiber. -/
def inadequateReading : FiniteInputTable where
  sourceCount := 2
  lawCount := 1
  targetCount := 1
  pointCount := 1
  chartCount := 1
  valueCount := fun _ => 2
  eval := fun _ s => s
  read := fun _ => 0
  relation := fun _ _ => false
  opens := (Finset.univ : Finset (Fin 1)).powerset
  chart := fun _ => Finset.univ
  target := fun _ => Finset.univ

/-- Adequacy is independently tested from finite reading fibers. -/
theorem inadequateReading_not_adequate : ¬ inadequateReading.AdequateReading := by decide

/-- A Boolean relation crossing distinct generated Law values. -/
def crossLabelRelation : FiniteInputTable :=
  {inadequateReading with relation := fun _ _ => true}

/-- Label preservation rejects raw primitive relations between distinct values. -/
theorem crossLabelRelation_not_preserving : ¬ crossLabelRelation.LabelPreserving := by decide

/-- The computed equal-label reachability test fails without primitive relations. -/
theorem missingPrimitiveRelation_not_reflecting :
    ¬ missingPrimitiveRelation.RelationReflecting := by decide

/-- Failure is already in the raw topology predicate. -/
theorem missingOpens_not_topology : ¬ missingOpens.TopologyValid := by decide

/-- Failure is already in the raw geometric predicate. -/
theorem emptyChart_not_geometry : ¬ emptyChart.GeometryValid := by decide

/-- Failure is already in the independent target predicate. -/
theorem emptyTarget_not_target : ¬ emptyTarget.TargetValid := by decide

/-- The geometric point table may have two separated points. -/
def separatedPoints : FiniteInputTable where
  sourceCount := 1
  lawCount := 1
  targetCount := 1
  pointCount := 2
  chartCount := 1
  valueCount := fun _ => 1
  eval := fun _ _ => 0
  read := fun _ => 0
  relation := fun _ _ => false
  opens := (Finset.univ : Finset (Fin 2)).powerset
  chart := fun _ => Finset.univ
  target := fun _ => Finset.univ

/-- The whole separated point set fails the finite connectedness test. -/
theorem separatedPoints_not_preconnected : ¬ separatedPoints.Preconnected Finset.univ := by decide

/-- The positive chart passes the finite connectedness test. -/
theorem onePoint_preconnected : onePointTable.Preconnected Finset.univ := by decide

/-- Vertex support has both a present and absent instance in the raw support predicates. -/
theorem vertex_support_pair : onePointTable.VertexVisible ⟨(0 : Fin 1),(0 : Fin 1)⟩ (0 : Fin 1) ∧
    ¬ emptyTarget.VertexVisible ⟨(0 : Fin 1),(0 : Fin 1)⟩ (0 : Fin 1) := by decide

/-- Same-target support has both a present and absent instance independently of geometry. -/
theorem edge_support_pair : onePointTable.EdgeVisible ⟨(0 : Fin 1),(0 : Fin 1)⟩ ((0 : Fin 1),(0 : Fin 1)) ∧
    ¬ emptyTarget.EdgeVisible ⟨(0 : Fin 1),(0 : Fin 1)⟩ ((0 : Fin 1),(0 : Fin 1)) := by decide

/-- All valid one-chart actual inputs satisfy B3 because no ordered edge exists. -/
theorem onePoint_nonbridge_visible :
    onePointTable.ActualNonbridgeVisible onePointTable_valid := by
  intro l e _
  have he := e.2.1
  have hi := e.1.1.isLt
  have hj := e.1.2.isLt
  change e.1.1.val < e.1.2.val at he
  change e.1.1.val < 1 at hi
  change e.1.2.val < 1 at hj
  omega

/-- The validator-generated actual positive input has all-input reflection. -/
theorem onePoint_reflects : onePointTable.ActualReflects onePointTable_valid :=
  (onePointTable.actual_reflection_iff_nonbridge_visible onePointTable_valid).mpr
    onePoint_nonbridge_visible

/-- Actual AAT local inputs for the computed positive table. -/
abbrev ActualData : Type := onePointTable.ActualLocalData onePointTable_valid

/-- Decoding has a local-data inhabitant, namely the actual zero transition and state. -/
theorem actualData_nonempty : Nonempty ActualData := by
  exact ⟨{transition := 0,localState := 0}⟩

/-- A triangle incidence geometry with two generated labels and all targets supported only at label zero. -/
def nonreflectingTriangle : FiniteInputTable where
  sourceCount := 2
  lawCount := 1
  targetCount := 2
  pointCount := 6
  chartCount := 3
  valueCount := fun _ => 2
  eval := fun _ s => s
  read := id
  relation := fun _ _ => false
  opens := (Finset.univ : Finset (Fin 6)).powerset.filter fun U =>
    (0 ∈ U → 3 ∈ U ∧ 4 ∈ U) ∧ (1 ∈ U → 3 ∈ U ∧ 5 ∈ U) ∧ (2 ∈ U → 4 ∈ U ∧ 5 ∈ U)
  chart := fun i => if i.val = 0 then {0,3,4} else if i.val = 1 then {1,3,5} else {2,4,5}
  target := fun _ => {0}

/-- This negative instance satisfies all T0 checks by finite computation. -/
theorem nonreflectingTriangle_valid : nonreflectingTriangle.Valid := by decide

/-- The invisible label is generated by the second primitive source. -/
def triangleLabel : LawValueLabel nonreflectingTriangle.laws := ⟨(0 : Fin 1),(1 : Fin 2),⟨(1 : Fin 2),rfl⟩⟩
/-- The chosen actual raw intersection edge, oriented zero to one. -/
abbrev triangleRawEdge : Graph.Edge nonreflectingTriangle.rawGraph := ⟨((0 : Fin 3),(1 : Fin 3)),by decide⟩
/-- Deleting the chosen raw edge leaves the other two triangle edges. -/
theorem triangleRawEdge_not_bridge :
    ¬ nonreflectingTriangle.rawGraph.IsBridge
      (Graph.unoriented nonreflectingTriangle.rawGraph triangleRawEdge) := by
  rw [Graph.unoriented_val,SimpleGraph.isBridge_iff]
  decide

/-- A valid decoded table fails B3 at a genuine invisible nonbridge edge. -/
theorem nonreflectingTriangle_not_nonbridge_visible :
    ¬ nonreflectingTriangle.ActualNonbridgeVisible nonreflectingTriangle_valid := by
  letI : TopologicalSpace nonreflectingTriangle.Point := nonreflectingTriangle.actualTopology nonreflectingTriangle_valid
  intro hv
  let e : Graph.Edge (nonreflectingTriangle.actualGeometry nonreflectingTriangle_valid).graph :=
    ⟨((0 : Fin 3),(1 : Fin 3)),by
      refine ⟨by decide,?_⟩
      rw [nonreflectingTriangle.actualGeometry_graph nonreflectingTriangle_valid]
      exact triangleRawEdge.2.2⟩
  have he : ¬ (nonreflectingTriangle.actualGeometry nonreflectingTriangle_valid).graph.IsBridge
      (Graph.unoriented (nonreflectingTriangle.actualGeometry nonreflectingTriangle_valid).graph e) := by
    have hep : e.1 = ((0 : Fin 3),(1 : Fin 3)) := rfl
    rw [Graph.unoriented_val,hep,
      nonreflectingTriangle.actualGeometry_graph nonreflectingTriangle_valid]
    simpa only [Graph.unoriented_val] using triangleRawEdge_not_bridge
  have hi := hv triangleLabel e he
  have hn : ¬ nonreflectingTriangle.EdgeVisible ⟨(0 : Fin 1),(1 : Fin 2)⟩ ((0 : Fin 3),(1 : Fin 3)) := by decide
  apply hn
  simpa only [nonreflectingTriangle.actualGraphRawEdgeEquiv_val nonreflectingTriangle_valid e] using hi

/-- The same valid table fails all-input reflection via the accepted actual counterinput API. -/
theorem nonreflectingTriangle_not_reflects :
    ¬ nonreflectingTriangle.ActualReflects nonreflectingTriangle_valid := by
  intro hr
  exact nonreflectingTriangle_not_nonbridge_visible
    ((nonreflectingTriangle.actual_reflection_iff_nonbridge_visible nonreflectingTriangle_valid).mp hr)

end AAT.AG.VisibleCycleReflection.FiniteValidationWitness
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
