import ResearchLean.AG.VisibleCycleReflection.IntegralVisibleReflection
import Formal.Util.AssertStandardAxioms

/-!
# Visible-cycle reflection on the same primitive actual AAT input

## Implementation notes

The graph subsets use the existing target-supported nerve's supports, then transport
its complete geometric edge index. They are not selected from a desired vanishing
claim. The rational witnesses are obtained from the independent diagnostic quotient
through the accepted factorization. Integer corrections return through the inverse
actual-section equivalence, so the output consists of real locally constant sections.
Starting with arbitrary graph cochains without this return to the actual input would
not establish B. Common target representatives are never required.
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

omit [Fintype Source] in
/-- Public class-generation formula for arbitrary actual affine data. -/
theorem actualClass_generation (x : GeneratorPresentation.ActualCechAffineLocalData P C) :
    x.actualClass = (P.faceEmptyCechComplex C).additiveH1Class x.actualCocycle := rfl

omit [Fintype Source] in
/-- Public cochain value of the independently generated actual cocycle. -/
@[simp] theorem actualCocycle_value (x : GeneratorPresentation.ActualCechAffineLocalData P C) :
    x.actualCocycle.1 = x.actualMismatch := rfl

omit [Fintype Source] in
/-- Public coordinate-change constructor formula. -/
theorem adjustLocalState_generation (x : GeneratorPresentation.ActualCechAffineLocalData P C)
    (n : (P.faceEmptyCechComplex C).Cn 0) :
    x.adjustLocalState n = ⟨x.transition,x.localState + n⟩ := rfl

omit [Fintype Source] in
/-- Zero of the existing descent class is exactly existence of an actual integer correction. -/
theorem existingDescent_zero_iff_correction (x : GeneratorPresentation.ActualCechAffineLocalData P C) :
    x.existingDescentAdditiveClass = 0 ↔
      ∃ n : (P.faceEmptyCechComplex C).Cn 0, (P.faceEmptyCechComplex C).d 0 n = x.actualMismatch := by
  rw [x.existingDescentAdditiveClass_eq_actualClass,x.actualClass_generation,
    (P.faceEmptyCechComplex C).additiveH1Class_eq_zero_iff,x.actualCocycle_value]
  exact exists_congr (fun _ => eq_comm)

omit [Fintype Source] in
/-- Changing only p preserves the existing descent class, for any two actual chart states. -/
theorem existingDescent_eq_of_transition_eq (x y : GeneratorPresentation.ActualCechAffineLocalData P C)
    (h : y.transition = x.transition) : y.existingDescentAdditiveClass = x.existingDescentAdditiveClass := by
  have hy : y = x.adjustLocalState (y.localState - x.localState) := by
    rw [adjustLocalState_generation]
    cases x with
    | mk tx px =>
      cases y with
      | mk ty py =>
        dsimp at h ⊢
        subst ty
        congr 1
        abel
  rw [y.existingDescentAdditiveClass_eq_actualClass,x.existingDescentAdditiveClass_eq_actualClass,hy]
  exact x.actual_class_adjust_local_state _

/-- Changing only p also preserves the independently generated diagnostic class. -/
theorem diagnostic_eq_of_transition_eq (x y : GeneratorPresentation.ActualCechAffineLocalData P C)
    (h : y.transition = x.transition) (hadequate : laws.Adequate q) :
    y.diagnosticClass hadequate = x.diagnosticClass hadequate := by
  rw [← y.h1_map_actual_class_eq_diagnostic_class hadequate,
    ← x.h1_map_actual_class_eq_diagnostic_class hadequate,
    ← y.existingDescentAdditiveClass_eq_actualClass,← x.existingDescentAdditiveClass_eq_actualClass,
    existingDescent_eq_of_transition_eq x y h]

end AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData

namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge Cohomology Classical
universe u

namespace GeometricCover
variable {Source X I : Type u} [Fintype Source] [TopologicalSpace X]
    [LinearOrder I] [Fintype I]
variable {laws : FiniteLawFamily Source} {q : Reading Source}
variable (K : GeometricCover X I) (target : I → Set q.Target)
    (hne : ∀ i, (target i).Nonempty) (hadequate : laws.Adequate q)

/-- B's visible vertices are exactly the supplied chart-support occurrences. -/
def visibleVertexSet (label : LawValueLabel laws) : Set I :=
  {i | ∃ t, t ∈ (K.supportedNerve target hne).chartSupport i ∧
    lawDescend laws q hadequate label.law t = label.value}

/-- B's visible edges use the same target in the existing edge support. -/
def visibleEdgeSet (label : LawValueLabel laws) : Set (Graph.Edge K.graph) :=
  {e | ∃ t, t ∈ (K.supportedNerve target hne).edgeSupport (K.graphEdgeEquiv.symm e) ∧
    lawDescend laws q hadequate label.law t = label.value}

omit [Fintype Source] in
/-- B's subgraph closure at the source, derived from the same edge witness. -/
theorem visibleEdge_left (label : LawValueLabel laws) (e : Graph.Edge K.graph)
    (he : e ∈ K.visibleEdgeSet target hne hadequate label) :
    Graph.left K.graph e ∈ K.visibleVertexSet target hne hadequate label := by
  obtain ⟨t,ht,hvalue⟩ := he
  exact ⟨t, ((K.supportedNerve target hne).mem_edgeSupport_iff _ t).mp ht |>.1,hvalue⟩

omit [Fintype Source] in
/-- B's subgraph closure at the target, derived from the same edge witness. -/
theorem visibleEdge_right (label : LawValueLabel laws) (e : Graph.Edge K.graph)
    (he : e ∈ K.visibleEdgeSet target hne hadequate label) :
    Graph.right K.graph e ∈ K.visibleVertexSet target hne hadequate label := by
  obtain ⟨t,ht,hvalue⟩ := he
  exact ⟨t, ((K.supportedNerve target hne).mem_edgeSupport_iff _ t).mp ht |>.2,hvalue⟩

/-- Exact visible-edge identification with the accepted actual diagnostic cells. -/
def actualVisibleEdgeEquiv (label : LawValueLabel laws) :
    VisibleEdge (K.supportedNerve target hne) hadequate label ≃
      K.visibleEdgeSet target hne hadequate label where
  toFun e := ⟨K.graphEdgeEquiv e.1,e.2⟩
  invFun e := ⟨K.graphEdgeEquiv.symm e.1,e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype Source] in
/-- The visible edge equivalence retains the oriented geometric edge. -/
@[simp] theorem actualVisibleEdgeEquiv_val (label : LawValueLabel laws)
    (e : VisibleEdge (K.supportedNerve target hne) hadequate label) :
    (K.actualVisibleEdgeEquiv target hne hadequate label e).1 = K.graphEdgeEquiv e.1 := rfl

omit [Fintype Source] in
/-- Public transport of visible vertex differences to the actual diagnostic differential. -/
theorem visible_d0_actual (label : LawValueLabel laws)
    (b : K.visibleVertexSet target hne hadequate label → ℚ)
    (e : K.visibleEdgeSet target hne hadequate label) :
    Graph.visibleD0 K.graph (K.visibleVertexSet target hne hadequate label)
      (K.visibleEdgeSet target hne hadequate label)
      (K.visibleEdge_left target hne hadequate label)
      (K.visibleEdge_right target hne hadequate label) b e =
      visibleD0 (K.supportedNerve target hne) hadequate label b
        ((K.actualVisibleEdgeEquiv target hne hadequate label).symm e) := rfl

variable (P : GeneratorPresentation laws) (hR : P.ReflectionCondition)

/-- The specified actual mismatch in the complete graph's integral coordinates. -/
def graphMismatch (x : GeneratorPresentation.ActualCechAffineLocalData P
    (K.actualCechCover P target hne)) : Graph.Edge K.graph → LawValueLabel laws → ℤ :=
  fun e => actualIntegralCochain1Equiv P (K.actualCechCover P target hne) hR
    x.actualMismatch (K.graphEdgeEquiv.symm e)

/-- Public normalization of the specified graph mismatch. -/
theorem graphMismatch_apply (x : GeneratorPresentation.ActualCechAffineLocalData P
    (K.actualCechCover P target hne)) (e : Graph.Edge K.graph) (label : LawValueLabel laws) :
    K.graphMismatch target hne P hR x e label =
      actualIntegralCochain1Equiv P (K.actualCechCover P target hne) hR
        x.actualMismatch (K.graphEdgeEquiv.symm e) label := rfl

/-- Diagnostic zero provides rational potential witnesses on every specified visible graph. -/
theorem visible_potentials_of_diagnostic_zero
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (hx : x.diagnosticClass hadequate = 0) (label : LawValueLabel laws) :
    ∃ b : K.visibleVertexSet target hne hadequate label → ℚ,
      ∀ e : K.visibleEdgeSet target hne hadequate label,
        (K.graphMismatch target hne P hR x e.1 label : ℚ) =
          Graph.visibleD0 K.graph (K.visibleVertexSet target hne hadequate label)
            (K.visibleEdgeSet target hne hadequate label)
            (K.visibleEdge_left target hne hadequate label)
            (K.visibleEdge_right target hne hadequate label) b e := by
  have h := input_local_data_factorization (K := K) (target := target) (hne := hne)
    (P := P) (hR := hR) (hadequate := hadequate) (x := x) (current := label)
  rw [hx,map_zero,map_zero] at h
  rw [existingDescent_graph_representative,integerToRationalH1_mk,rationalRestrictionH1_mk] at h
  have hz : (LinearMap.range (visibleD0 (K.supportedNerve target hne) hadequate label)).mkQ
      (rationalRestriction1 (K.supportedNerve target hne) hadequate label
        (graphCoefficientCast (K.supportedNerve target hne).nerve (LawValueLabel laws)
          (actualIntegralCochain1Equiv P (K.actualCechCover P target hne) hR x.actualMismatch))) = 0 := h.symm
  obtain ⟨b,hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  refine ⟨b,?_⟩
  intro e
  rw [K.visible_d0_actual]
  have he := congrFun hb ((K.actualVisibleEdgeEquiv target hne hadequate label).symm e)
  exact he.symm

include hR in
/-- B3 and diagnostic zero give an actual integral chart correction on the generated AAT cover. -/
theorem exists_actual_integral_correction
    (hvisible : ∀ label e, ¬K.graph.IsBridge (Graph.unoriented K.graph e) →
      e ∈ K.visibleEdgeSet target hne hadequate label)
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (hx : x.diagnosticClass hadequate = 0) :
    ∃ n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0,
      (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch := by
  obtain ⟨n,hn⟩ := Graph.exists_integral_correction K.graph
    (K.visibleVertexSet target hne hadequate) (K.visibleEdgeSet target hne hadequate)
    (K.visibleEdge_left target hne hadequate) (K.visibleEdge_right target hne hadequate)
    hvisible (K.graphMismatch target hne P hR x)
    (K.visible_potentials_of_diagnostic_zero target hne hadequate P hR x hx)
  refine ⟨(actualIntegralCochain0Equiv P (K.actualCechCover P target hne) hR).symm n,?_⟩
  apply (actualIntegralCochain1Equiv P (K.actualCechCover P target hne) hR).injective
  rw [actualIntegral_d0,AddEquiv.apply_symm_apply]
  ext e label
  exact hn (K.graphEdgeEquiv e) label

include hR in
/-- B3 reflects diagnostic zero to existing obstruction zero for all actual ξ,p. -/
theorem input_reflection_of_nonbridge_visible
    (hvisible : ∀ label e, ¬K.graph.IsBridge (Graph.unoriented K.graph e) →
      e ∈ K.visibleEdgeSet target hne hadequate label)
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne)) :
    x.diagnosticClass hadequate = 0 ↔ x.existingDescentAdditiveClass = 0 := by
  constructor
  · intro hx
    apply x.existingDescent_zero_iff_correction.mpr
    exact K.exists_actual_integral_correction target hne hadequate P hR hvisible x hx
  · intro hx
    rw [← existingDescent_comparison P (K.actualCechCover P target hne) hadequate x,hx,map_zero]

omit [Fintype Source] in
/-- B2 is the full chain inclusion for the same visible subsets, and equals B3. -/
theorem input_homology_iff_nonbridge_visible :
    (∀ label, Function.Surjective (Graph.h1Inclusion K.graph
      (K.visibleVertexSet target hne hadequate label) (K.visibleEdgeSet target hne hadequate label)
      (K.visibleEdge_left target hne hadequate label) (K.visibleEdge_right target hne hadequate label))) ↔
    ∀ label e, ¬K.graph.IsBridge (Graph.unoriented K.graph e) →
      e ∈ K.visibleEdgeSet target hne hadequate label := by
  apply forall_congr'
  intro label
  exact Graph.h1Inclusion_surjective_iff_nonbridge_visible K.graph
    (K.visibleVertexSet target hne hadequate label) (K.visibleEdgeSet target hne hadequate label)
    (K.visibleEdge_left target hne hadequate label) (K.visibleEdge_right target hne hadequate label)

end GeometricCover
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
