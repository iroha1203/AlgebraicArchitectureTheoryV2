import ResearchLean.AG.VisibleCycleReflection.ActualStateGluing
import Formal.Util.AssertStandardAxioms

/-!
# Returning affine global states to actual integer repairs

## Implementation notes

The chart coordinates below are normalized actual sections and are proved
equal to the original section at every point. Correction compatibility is
derived from the actual differential, rather than accepted as input. In the
reverse direction a global affine state gives locally constant chart states;
connectedness makes their primitive values constant, and the inverse actual
Cech equivalence returns them to integer chart sections.
-/

noncomputable section
open CategoryTheory TopologicalSpace Opposite
namespace AAT.AG.VisibleCycleReflection.GeometricCover
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge
universe u
variable {Source X I : Type u} [TopologicalSpace X] [LinearOrder I] [Fintype I]
variable {laws : FiniteLawFamily Source} {q : Reading Source}
variable (K : GeometricCover X I) (P : GeneratorPresentation laws)
    (target : I → Set q.Target) (hne : ∀ i, (target i).Nonempty)

/-- The actual chart support is its original geometric chart. -/
theorem actualChartSupport_eq (i : I) :
    (OpenSupport.contextOpenSupport (Space := X) P).support.obj
      ((K.actualCechCover P target hne).chartContext i) = K.patch i :=
  OpenSupport.contextOpenSupport_obj_openContext P _

/-- The actual edge support is its original geometric overlap. -/
theorem actualOverlapSupport_eq (e : K.Edge) :
    (OpenSupport.contextOpenSupport (Space := X) P).support.obj
      ((K.actualCechCover P target hne).edgeContext e) = K.overlap e :=
  OpenSupport.contextOpenSupport_obj_openContext P _

/-- Every chart point lands in the same actual AAT chart support. -/
def actualChartPoint (i : I) (x : K.patch i) :
    (OpenSupport.contextOpenSupport (Space := X) P).support.obj
      ((K.actualCechCover P target hne).chartContext i) :=
  ⟨x.1,by rw [K.actualChartSupport_eq P target hne]; exact x.2⟩

/-- Every overlap point lands in the same actual AAT overlap support. -/
def actualOverlapPoint (e : K.Edge) (x : K.overlap e) :
    (OpenSupport.contextOpenSupport (Space := X) P).support.obj
      ((K.actualCechCover P target hne).edgeContext e) :=
  ⟨x.1,by rw [K.actualOverlapSupport_eq P target hne]; exact x.2⟩

/-- Primitive chart coordinates of arbitrary actual locally constant integer states. -/
def actualChartCoordinates (c : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0)
    (i : I) : LocallyConstant (K.patch i) P.PresentationGroup :=
  LocallyConstant.const _ (P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne) c i)

/-- Public primitive value of the chart coordinate section. -/
@[simp] theorem actualChartCoordinates_apply
    (c : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0) (i : I) (x : K.patch i) :
    K.actualChartCoordinates P target hne c i x =
      P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne) c i := rfl

/-- The chart coordinates equal the original actual section at every chart point. -/
theorem actualChartCoordinates_actual_value
    (c : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0) (i : I) (x : K.patch i) :
    K.actualChartCoordinates P target hne c i x =
      P.actualSectionEquiv (OpenSupport.contextOpenSupport (Space := X) P)
        ((K.actualCechCover P target hne).chartContext i) (c i)
          (K.actualChartPoint P target hne i x) :=
  P.faceEmptyCechCochain0Equiv_value (K.actualCechCover P target hne) c i _

/-- Atlas translations are the original actual transition section at every overlap point. -/
theorem actualAffineAtlas_actual_transition_value
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (e : K.Edge) (x : K.overlap e) :
    (K.actualAffineAtlas P target hne ξ).transition e.1.1 e.1.2 =
      P.actualSectionEquiv (OpenSupport.contextOpenSupport (Space := X) P)
        ((K.actualCechCover P target hne).edgeContext e) (ξ e)
          (K.actualOverlapPoint P target hne e x) := by
  rw [K.actualAffineAtlas_transition]
  exact P.faceEmptyCechCochain1Equiv_value (K.actualCechCover P target hne) ξ e _

/-- The corrected primitive chart values obey the original affine equation on every edge. -/
theorem actual_corrected_edge
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (c : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0)
    (hc : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 c = -ξ) (e : K.Edge) :
    P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne) c e.1.1 =
      (K.actualAffineAtlas P target hne ξ).transition e.1.1 e.1.2 +
        P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne) c e.1.2 := by
  have h := P.faceEmptyCech_d0_normalizes (K.actualCechCover P target hne) c
  rw [hc,map_neg] at h
  have he := congrFun h e
  rw [P.presentationD0_apply] at he
  rw [K.actualAffineAtlas_transition]
  change -(P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne) ξ e) =
    P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne) c e.1.2 -
      P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne) c e.1.1 at he
  rw [(sub_eq_iff_eq_add).mp he.symm]
  abel

/-- Corrected actual chart sections match through the generated affine translations. -/
theorem actual_corrected_compatibility
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (c : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0)
    (hc : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 c = -ξ)
    (i j : I) (x : X) (hi : x ∈ K.patch i) (hj : x ∈ K.patch j) :
    K.actualChartCoordinates P target hne c i ⟨x,hi⟩ =
      (K.actualAffineAtlas P target hne ξ).transition i j +
        K.actualChartCoordinates P target hne c j ⟨x,hj⟩ := by
  rw [actualChartCoordinates_apply,actualChartCoordinates_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · exact K.actual_corrected_edge P target hne ξ c hc ⟨(i,j),h,⟨x,hi,hj⟩⟩
  · rw [(K.actualAffineAtlas P target hne ξ).self,zero_add]
  · have he := K.actual_corrected_edge P target hne ξ c hc ⟨(j,i),h,⟨x,hj,hi⟩⟩
    rw [(K.actualAffineAtlas P target hne ξ).reverse i j] at he
    rw [he]
    abel

/-- Read a global affine state in each original chart trivialization. -/
def stateChartCoordinates
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) (i : I) :
    LocallyConstant (K.patch i) P.PresentationGroup :=
  (K.actualAffineAtlas P target hne ξ).localTrivialization i le_rfl
    ((K.actualAffineAtlas P target hne ξ).restrict le_top s)

/-- Chart coordinates of a global state are its original fiber coordinates. -/
@[simp] theorem stateChartCoordinates_value
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) (i : I) (x : K.patch i) :
    K.stateChartCoordinates P target hne ξ s i x =
      (K.actualAffineAtlas P target hne ξ).coordinate x.1 i x.2 (s.1 ⟨x.1,trivial⟩) := rfl

/-- Connected actual charts determine one primitive coefficient for every global state. -/
def stateChartValue
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) (i : I) :
    P.PresentationGroup :=
  K.stateChartCoordinates P target hne ξ s i
    ⟨(K.chartNonempty i).choose,(K.chartNonempty i).choose_spec⟩

/-- The primitive chart value equals the global state's chart section at every point. -/
theorem stateChartValue_eq
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) (i : I) (x : K.patch i) :
    K.stateChartValue P target hne ξ s i = K.stateChartCoordinates P target hne ξ s i x := by
  letI := Subtype.preconnectedSpace (K.chartPreconnected i)
  exact (K.stateChartCoordinates P target hne ξ s i).apply_eq_of_preconnectedSpace _ _

/-- The primitive chart values retain the original actual transition on every edge. -/
theorem stateChartValue_edge
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) (e : K.Edge) :
    K.stateChartValue P target hne ξ s e.1.1 =
      P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne) ξ e +
        K.stateChartValue P target hne ξ s e.1.2 := by
  obtain ⟨x,hi,hj⟩ := e.2.2
  rw [K.stateChartValue_eq P target hne ξ s e.1.1 ⟨x,hi⟩,
    K.stateChartValue_eq P target hne ξ s e.1.2 ⟨x,hj⟩,
    stateChartCoordinates_value,stateChartCoordinates_value,
    ← K.actualAffineAtlas_transition P target hne ξ e]
  exact (K.actualAffineAtlas P target hne ξ).coordinate_change x e.1.1 e.1.2 hi hj _

/-- Return global state coordinates to the original actual integer chart cochain. -/
def actualStateFromGlobal
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) :
    (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0 :=
  (P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne)).symm
    (K.stateChartValue P target hne ξ s)

/-- The inverse actual normalization retains precisely the chart values of the given state. -/
@[simp] theorem actualStateFromGlobal_coordinates
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) :
    P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne)
      (K.actualStateFromGlobal P target hne ξ s) = K.stateChartValue P target hne ξ s :=
  (P.faceEmptyCechCochain0Equiv (K.actualCechCover P target hne)).apply_symm_apply _

/-- A global state has the original actual differential minus its original transition. -/
theorem actualStateFromGlobal_d0
    (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)
    (s : (K.actualAffineAtlas P target hne ξ).StateSection ⊤) :
    (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0
      (K.actualStateFromGlobal P target hne ξ s) = -ξ := by
  apply (P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne)).injective
  rw [P.faceEmptyCech_d0_normalizes,K.actualStateFromGlobal_coordinates,map_neg]
  funext e
  rw [P.presentationD0_apply]
  change K.stateChartValue P target hne ξ s e.1.2 -
    K.stateChartValue P target hne ξ s e.1.1 =
      -(P.faceEmptyCechCochain1Equiv (K.actualCechCover P target hne) ξ e)
  rw [K.stateChartValue_edge P target hne ξ s e]
  abel

variable [Fintype Source]

/-- Any actual correction makes the actual state p-n have differential minus the transition. -/
theorem actual_corrected_d0
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0)
    (hn : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch) :
    (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 (x.localState-n) = -x.transition := by
  rw [map_sub,hn,x.actualMismatch_eq]
  abel

/-- Every actual repair glues the actual p-n chart states uniquely. -/
theorem actual_corrected_gluing
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0)
    (hn : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch) :
    ∃! s : (K.actualAffineAtlas P target hne x.transition).StateSection ⊤,
      ∀ i, K.stateChartCoordinates P target hne x.transition s i =
        K.actualChartCoordinates P target hne (x.localState-n) i :=
  (K.actualAffineAtlas P target hne x.transition).existsUnique_gluing_chart_coordinates
    (K.actualChartCoordinates P target hne (x.localState-n))
    (K.actual_corrected_compatibility P target hne x.transition (x.localState-n)
      (K.actual_corrected_d0 P target hne x n hn))

/-- A global state yields a correction of the same actual affine input. -/
def actualCorrectionFromGlobal
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (s : (K.actualAffineAtlas P target hne x.transition).StateSection ⊤) :
    (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0 :=
  x.localState - K.actualStateFromGlobal P target hne x.transition s

/-- The generated correction satisfies the original actual mismatch equation. -/
theorem actualCorrectionFromGlobal_d0
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (s : (K.actualAffineAtlas P target hne x.transition).StateSection ⊤) :
    (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0
      (K.actualCorrectionFromGlobal P target hne x s) = x.actualMismatch := by
  change (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0
    (x.localState - K.actualStateFromGlobal P target hne x.transition s) = x.actualMismatch
  rw [map_sub,K.actualStateFromGlobal_d0,x.actualMismatch_eq]
  abel

/-- Actual correction existence is exactly nonemptiness of generated global affine states. -/
theorem correction_iff_global_state
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne)) :
    (∃ n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0,
      (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch) ↔
        Nonempty ((K.actualAffineAtlas P target hne x.transition).StateSection ⊤) := by
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨s,_,_⟩ := K.actual_corrected_gluing P target hne x n hn
    exact ⟨s⟩
  · rintro ⟨s⟩
    exact ⟨K.actualCorrectionFromGlobal P target hne x s,
      K.actualCorrectionFromGlobal_d0 P target hne x s⟩

/-- Zero of the original descent obstruction is equivalent to a generated global affine state. -/
theorem existingDescent_zero_iff_global_state
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne)) :
    x.existingDescentAdditiveClass = 0 ↔
      Nonempty ((K.actualAffineAtlas P target hne x.transition).StateSection ⊤) :=
  x.existingDescent_zero_iff_correction.trans (K.correction_iff_global_state P target hne x)

end AAT.AG.VisibleCycleReflection.GeometricCover
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
