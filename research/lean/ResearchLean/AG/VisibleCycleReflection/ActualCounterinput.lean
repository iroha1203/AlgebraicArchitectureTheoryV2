import ResearchLean.AG.VisibleCycleReflection.ActualReflection
import ResearchLean.AG.VisibleCycleReflection.GraphPeriods
import Formal.Util.AssertStandardAxioms

/-!
# Actual single-edge counterinputs and all-input necessity

## Implementation notes

The transition is constructed by the inverse actual-section normalization from one
original presentation basis value on one geometric edge. It is a real locally constant
section, rather than a supplied graph realization. The independent diagnostic is
proved zero pointwise. A deleted-edge simple path gives a closed walk whose original
presentation-valued period is minus the same basis. Arbitrary H1 realizability is
therefore not an input assumption. The all-input converse uses this very construction,
without restricting p or xi in the reflection statement.
-/

noncomputable section
namespace AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source] {laws : FiniteLawFamily Source} {q : Reading Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent] {P : GeneratorPresentation laws}
variable {C : GeneratorPresentation.FaceEmptyAATCechCover D G}

/-- Public quotient-generation formula for the independent diagnostic. -/
theorem diagnosticClass_generation (x : GeneratorPresentation.ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) :
    x.diagnosticClass hadequate =
      (LinearMap.range (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ
        (x.diagnosticCocycle hadequate) := rfl
/-- Public cochain value of the independent diagnostic cocycle. -/
@[simp] theorem diagnosticCocycle_value (x : GeneratorPresentation.ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) :
    (x.diagnosticCocycle hadequate).1 = x.diagnosticMismatch hadequate := rfl
/-- Diagnostic cochain zero implies diagnostic class zero. -/
theorem diagnosticClass_zero_of_mismatch_zero (x : GeneratorPresentation.ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) (h : x.diagnosticMismatch hadequate = 0) :
    x.diagnosticClass hadequate = 0 := by
  rw [diagnosticClass_generation]
  have hc : x.diagnosticCocycle hadequate = 0 := by
    apply Subtype.ext
    rw [diagnosticCocycle_value,h]
    rfl
  rw [hc,map_zero]
end AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData

namespace AAT.AG.VisibleCycleReflection.GeometricCover
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge Cohomology Classical
universe u
variable {Source X I : Type u} [Fintype Source] [TopologicalSpace X] [LinearOrder I] [Fintype I]
variable {laws : FiniteLawFamily Source} {q : Reading Source}
variable (K : GeometricCover X I) (target : I → Set q.Target) (hne : ∀ i, (target i).Nonempty)
variable (P : GeneratorPresentation laws) (hR : P.ReflectionCondition)

/-- B's real local data: one original basis transition on one actual edge, and zero state. -/
def singleEdgeData (label : LawValueLabel laws) (edge : Graph.Edge K.graph) :
    GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne) where
  transition := (P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne)).symm
    (fun e => if K.graphEdgeEquiv e = edge then labelBasis P hR label else 0)
  localState := 0

/-- The transition constructor returns the inverse actual section normalization. -/
theorem singleEdgeData_transition (label : LawValueLabel laws) (edge : Graph.Edge K.graph) :
    (K.singleEdgeData target hne P hR label edge).transition =
      (P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne)).symm
        (fun e => if K.graphEdgeEquiv e = edge then labelBasis P hR label else 0) := rfl
/-- The constructed local state is zero on every actual chart. -/
@[simp] theorem singleEdgeData_localState (label : LawValueLabel laws) (edge : Graph.Edge K.graph) :
    (K.singleEdgeData target hne P hR label edge).localState = 0 := rfl

/-- The original-valued transition is exactly the single-edge basis cochain. -/
theorem singleEdgeData_transition_value (label : LawValueLabel laws) (edge e : Graph.Edge K.graph) :
    P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne)
      (K.singleEdgeData target hne P hR label edge).transition (K.graphEdgeEquiv.symm e) =
      if e = edge then labelBasis P hR label else 0 := by
  rw [singleEdgeData_transition,AddEquiv.apply_symm_apply,K.graphEdgeEquiv.apply_symm_apply]

/-- The mismatch of the zero-state counterinput equals its actual transition. -/
theorem singleEdgeData_mismatch (label : LawValueLabel laws) (edge : Graph.Edge K.graph) :
    (K.singleEdgeData target hne P hR label edge).actualMismatch =
      (K.singleEdgeData target hne P hR label edge).transition := by
  rw [GeneratorPresentation.ActualCechAffineLocalData.actualMismatch_eq,
    singleEdgeData_localState,map_zero,add_zero]

/-- Public integral-coordinate formula for the actual single-edge mismatch. -/
theorem singleEdgeData_normalized (label current : LawValueLabel laws)
    (edge e : Graph.Edge K.graph) :
    K.graphMismatch target hne P hR (K.singleEdgeData target hne P hR label edge) e current =
      if e = edge then if current = label then 1 else 0 else 0 := by
  rw [graphMismatch_apply,singleEdgeData_mismatch,actualIntegralCochain1Equiv_apply,
    singleEdgeData_transition_value]
  by_cases he : e = edge
  · simp only [if_pos he]
    exact integralLabelEquiv_labelBasis P hR label current
  · simp only [if_neg he,map_zero,Pi.zero_apply]

/-- B necessity: an invisible selected edge makes every independent diagnostic coordinate zero. -/
theorem singleEdgeData_diagnostic_mismatch_zero (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) (edge : Graph.Edge K.graph)
    (hi : edge ∉ K.visibleEdgeSet target hne hadequate label) :
    (K.singleEdgeData target hne P hR label edge).diagnosticMismatch hadequate = 0 := by
  rw [← GeneratorPresentation.ActualCechAffineLocalData.actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch]
  ext coordinate
  rw [actualCoefficient1_apply P (K.actualCechCover P target hne) hR]
  let current := coordinate.lawValueLabel laws q hadequate
    (K.supportedNerve target hne).nerve.EdgeComponent (K.supportedNerve target hne).edgeSupport
  have hv : K.graphEdgeEquiv coordinate.cell ∈ K.visibleEdgeSet target hne hadequate current :=
    (blockCellEquiv hadequate (K.supportedNerve target hne).nerve.EdgeComponent
      (K.supportedNerve target hne).edgeSupport current ⟨coordinate,rfl⟩).2
  change (K.graphMismatch target hne P hR (K.singleEdgeData target hne P hR label edge)
    (K.graphEdgeEquiv coordinate.cell) current : ℚ) = 0
  rw [singleEdgeData_normalized]
  by_cases he : K.graphEdgeEquiv coordinate.cell = edge
  · rw [if_pos he]
    have hc : current ≠ label := by
      intro hh
      rw [hh,he] at hv
      exact hi hv
    rw [if_neg hc]
    rfl
  · rw [if_neg he]
    rfl

/-- The same actual counterinput has zero diagnostic class. -/
theorem singleEdgeData_diagnostic_zero (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) (edge : Graph.Edge K.graph)
    (hi : edge ∉ K.visibleEdgeSet target hne hadequate label) :
    (K.singleEdgeData target hne P hR label edge).diagnosticClass hadequate = 0 :=
  GeneratorPresentation.ActualCechAffineLocalData.diagnosticClass_zero_of_mismatch_zero _ hadequate
    (K.singleEdgeData_diagnostic_mismatch_zero target hne P hR hadequate label edge hi)

/-- Period of actual transition sections in the original primitive coefficient group. -/
def actualTransitionPeriod
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    {a b : I} (p : K.graph.Walk a b) : P.PresentationGroup :=
  Graph.walkPeriod K.graph (fun e => P.faceEmptyCechCochain1Equiv
    (K.actualCechCover P target hne) x.transition (K.graphEdgeEquiv.symm e)) p

omit [Fintype Source] in
/-- Public original-valued formula for an actual transition period. -/
theorem actualTransitionPeriod_apply
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    {a b : I} (p : K.graph.Walk a b) :
    K.actualTransitionPeriod target hne P x p =
      Graph.walkPeriod K.graph (fun e => P.faceEmptyCechCochain1Equiv
        (K.actualCechCover P target hne) x.transition (K.graphEdgeEquiv.symm e)) p := rfl

/-- A once-through chain with coefficient minus one has period minus the original basis. -/
theorem singleEdgeData_period (label : LawValueLabel laws) (edge : Graph.Edge K.graph)
    {a b : I} (p : K.graph.Walk a b) (hp : Graph.walkChain K.graph p edge = -1) :
    K.actualTransitionPeriod target hne P (K.singleEdgeData target hne P hR label edge) p =
      -labelBasis P hR label := by
  rw [actualTransitionPeriod_apply]
  apply P.coefficientComparison_injective hR
  ext current
  rw [map_neg]
  change P.coefficientComparison
    (Graph.walkPeriod K.graph (fun e => P.faceEmptyCechCochain1Equiv
      (K.actualCechCover P target hne)
      (K.singleEdgeData target hne P hR label edge).transition (K.graphEdgeEquiv.symm e)) p) current = _
  have h := Graph.map_walkPeriod K.graph
    ((Pi.evalAddMonoidHom (fun _ : LawValueLabel laws => ℚ) current).comp P.coefficientComparison)
    (fun e => P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne)
      (K.singleEdgeData target hne P hR label edge).transition (K.graphEdgeEquiv.symm e)) p
  change P.coefficientComparison _ current = _ at h
  rw [h]
  simp_rw [singleEdgeData_transition_value]
  simp only [AddMonoidHom.comp_apply,Pi.evalAddMonoidHom_apply] at *
  change (∑ e, Graph.walkChain K.graph p e *
    P.coefficientComparison (if e = edge then labelBasis P hR label else 0) current) = _
  have hf : ∀ e : Graph.Edge K.graph,
      P.coefficientComparison (if e = edge then labelBasis P hR label else 0) current =
        if e = edge then if current = label then 1 else 0 else 0 := by
    intro e
    by_cases he : e = edge <;> simp [he,coefficientComparison_labelBasis]
  simp_rw [hf]
  by_cases hc : current = label
  · subst current
    simp [coefficientComparison_labelBasis,hp]
  · simp [coefficientComparison_labelBasis,hc]

/-- B necessity: a nonbridge single-edge counterinput has nonzero existing obstruction. -/
theorem singleEdgeData_existing_nonzero (label : LawValueLabel laws) (edge : Graph.Edge K.graph)
    (he : ¬K.graph.IsBridge (Graph.unoriented K.graph edge)) :
    (K.singleEdgeData target hne P hR label edge).existingDescentAdditiveClass ≠ 0 := by
  intro hx
  obtain ⟨n,hn⟩ := (GeneratorPresentation.ActualCechAffineLocalData.existingDescent_zero_iff_correction _).mp hx
  obtain ⟨p,hcycle,honce,hcoeff⟩ := Graph.exists_once_cycle K.graph edge he
  let b : I → ℚ := fun i => (actualIntegralCochain0Equiv P (K.actualCechCover P target hne) hR n i label : ℚ)
  have hb : Graph.d0 K.graph b = Graph.edgeUnit K.graph edge := by
    ext e
    have hh := congrArg (fun c => actualIntegralCochain1Equiv P (K.actualCechCover P target hne) hR
      c (K.graphEdgeEquiv.symm e) label) hn
    dsimp only at hh
    rw [actualIntegral_d0] at hh
    change actualIntegralCochain0Equiv P (K.actualCechCover P target hne) hR n
      (Graph.right (V := I) K.graph e) label - actualIntegralCochain0Equiv P (K.actualCechCover P target hne) hR n
      (Graph.left (V := I) K.graph e) label =
        K.graphMismatch target hne P hR (K.singleEdgeData target hne P hR label edge) e label at hh
    rw [singleEdgeData_normalized,if_pos rfl] at hh
    rw [Graph.d0_apply,Graph.edgeUnit_apply]
    dsimp only [b]
    rw [← Int.cast_sub,hh]
    split_ifs <;> rfl
  have hc := Graph.cycle_pairing_d0 K.graph (Graph.closedWalkH1 K.graph p) b
  rw [hb] at hc
  simp only [Graph.edgeUnit_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at hc
  change Graph.walkChain K.graph p edge = 0 at hc
  rw [hcoeff] at hc
  norm_num at hc

/-- B's complete failure construction from any invisible nonbridge edge and label. -/
theorem exists_actual_counterinput (hadequate : laws.Adequate q)
    (label : LawValueLabel laws) (edge : Graph.Edge K.graph)
    (hi : edge ∉ K.visibleEdgeSet target hne hadequate label)
    (he : ¬K.graph.IsBridge (Graph.unoriented K.graph edge)) :
    ∃ p : K.graph.Walk (Graph.right K.graph edge) (Graph.right K.graph edge),
      p.IsCycle ∧ p.edges.count (Graph.unoriented K.graph edge) = 1 ∧
      (K.singleEdgeData target hne P hR label edge).diagnosticMismatch hadequate = 0 ∧
      (K.singleEdgeData target hne P hR label edge).diagnosticClass hadequate = 0 ∧
      K.actualTransitionPeriod target hne P (K.singleEdgeData target hne P hR label edge) p =
        -labelBasis P hR label ∧
      K.actualTransitionPeriod target hne P (K.singleEdgeData target hne P hR label edge) p ≠ 0 ∧
      (K.singleEdgeData target hne P hR label edge).existingDescentAdditiveClass ≠ 0 := by
  obtain ⟨p,hcycle,honce,hcoeff⟩ := Graph.exists_once_cycle K.graph edge he
  have hp := K.singleEdgeData_period target hne P hR label edge p hcoeff
  refine ⟨p,hcycle,honce,
    K.singleEdgeData_diagnostic_mismatch_zero target hne P hR hadequate label edge hi,
    K.singleEdgeData_diagnostic_zero target hne P hR hadequate label edge hi,hp,?_,
    K.singleEdgeData_existing_nonzero target hne P hR label edge he⟩
  rw [hp]
  exact neg_ne_zero.mpr (labelBasis_ne_zero P hR label)

include hR in
/-- The all-input reflection condition is exactly visibility of every nonbridge edge. -/
theorem input_reflection_iff_nonbridge_visible (hadequate : laws.Adequate q) :
    (∀ x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne),
      x.diagnosticClass hadequate = 0 ↔ x.existingDescentAdditiveClass = 0) ↔
    ∀ label e, ¬K.graph.IsBridge (Graph.unoriented K.graph e) →
      e ∈ K.visibleEdgeSet target hne hadequate label := by
  constructor
  · intro h label edge he
    by_contra hi
    have hx := (h (K.singleEdgeData target hne P hR label edge)).mp
      (K.singleEdgeData_diagnostic_zero target hne P hR hadequate label edge hi)
    exact K.singleEdgeData_existing_nonzero target hne P hR label edge he hx
  · intro h x
    exact K.input_reflection_of_nonbridge_visible target hne hadequate P hR h x

include hR in
/-- B1 iff B2, together with B2 iff B3 on the same actual input. -/
theorem input_reflection_iff_homology_surjective (hadequate : laws.Adequate q) :
    (∀ x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne),
      x.diagnosticClass hadequate = 0 ↔ x.existingDescentAdditiveClass = 0) ↔
    (∀ label, Function.Surjective (Graph.h1Inclusion K.graph
      (K.visibleVertexSet target hne hadequate label) (K.visibleEdgeSet target hne hadequate label)
      (K.visibleEdge_left target hne hadequate label) (K.visibleEdge_right target hne hadequate label))) :=
  (K.input_reflection_iff_nonbridge_visible target hne P hR hadequate).trans
    (K.input_homology_iff_nonbridge_visible target hne hadequate).symm

end AAT.AG.VisibleCycleReflection.GeometricCover
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
