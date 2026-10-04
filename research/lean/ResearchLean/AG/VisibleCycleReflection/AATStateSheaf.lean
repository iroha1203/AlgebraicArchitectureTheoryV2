import ResearchLean.AG.VisibleCycleReflection.ActualStateRepair
import Formal.AG.Site.Sheaf
import Formal.Util.AssertStandardAxioms

/-!
# Pulling the generated affine state sheaf to the same AAT site

## Implementation notes

The support functor is the one generated from the point and primitive generator
Atoms in cycle 1. Its proved continuity pulls back the geometric affine sheaf.
This is a generic sheaf transport applied to an independently constructed state
sheaf; neither continuity nor the affine sheaf condition is supplied by the
caller. Objects and restrictions retain the actual open support, and the
chart trivialization has the existing primitive coefficient sheaf as its target.
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
variable (ξ : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 1)

/-- Affine states on the same primitive-input AAT contexts. -/
def aatStatePresheaf : Site.AATPresheaf (OpenSupport.site (X := X) P) :=
  (OpenSupport.contextOpenSupport (Space := X) P).support.op ⋙
    (K.actualAffineAtlas P target hne ξ).stateSheaf.presheaf

/-- The generated support's continuity proves the actual AAT affine sheaf condition. -/
theorem aatStatePresheaf_isSheaf :
    Site.AATSheafCondition (OpenSupport.site (X := X) P)
      (K.aatStatePresheaf P target hne ξ) := by
  rw [Site.AATSheafCondition.iff_presieve_isSheaf]
  let G := OpenSupport.contextOpenSupport (Space := X) P
  letI : Functor.IsContinuous.{u} G.support (OpenSupport.site (X := X) P).topology
      (Opens.grothendieckTopology G.space) := G.continuous
  exact G.support.op_comp_isSheaf_of_types
    (OpenSupport.site (X := X) P).topology (Opens.grothendieckTopology G.space)
    (K.actualAffineAtlas P target hne ξ).stateSheaf

/-- The affine state sheaf constructed on the actual point/generator AAT site. -/
def aatStateSheaf : Site.AATSheaf (OpenSupport.site (X := X) P) where
  carrier := K.aatStatePresheaf P target hne ξ
  isSheaf := K.aatStatePresheaf_isSheaf P target hne ξ

/-- States over an AAT context are affine states on its original open support. -/
theorem aatStateSheaf_obj (W : (OpenSupport.site (X := X) P).category) :
    (K.aatStateSheaf P target hne ξ).carrier.obj (op W) =
      (K.actualAffineAtlas P target hne ξ).StateSection
        ((OpenSupport.contextOpenSupport (Space := X) P).support.obj W) := rfl

/-- AAT restriction uses exactly the generated open-support restriction. -/
theorem aatStateSheaf_map {W V : (OpenSupport.site (X := X) P).category}
    (f : W ⟶ V) (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op V)) :
    (K.aatStateSheaf P target hne ξ).carrier.map f.op s =
      (K.actualAffineAtlas P target hne ξ).restrict
        ((OpenSupport.contextOpenSupport (Space := X) P).support.map f).le s :=
  (K.actualAffineAtlas P target hne ξ).stateSheaf_map _ s

/-- On any supported context inside a chart, the actual coefficient sheaf trivializes states. -/
def aatLocalTrivialization (W : (OpenSupport.site (X := X) P).category)
    (i : I) (h : (OpenSupport.contextOpenSupport (Space := X) P).support.obj W ≤ K.patch i) :
    (K.aatStateSheaf P target hne ξ).carrier.obj (op W) ≃
      (P.aatLocallyConstantObstructionSheaf
        (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.obj (op W) :=
  (K.actualAffineAtlas P target hne ξ).localTrivialization i h

/-- The original primitive coefficient sheaf acts on the generated actual AAT state sheaf. -/
def aatTranslateSection (W : (OpenSupport.site (X := X) P).category)
    (g : (P.aatLocallyConstantObstructionSheaf
      (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.obj (op W))
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op W)) :
    (K.aatStateSheaf P target hne ξ).carrier.obj (op W) :=
  (K.actualAffineAtlas P target hne ξ).translateSection
    (P.actualSectionEquiv (OpenSupport.contextOpenSupport (Space := X) P) W g) s

/-- The original coefficient translation satisfies the zero action law on actual contexts. -/
theorem aatTranslateSection_zero (W : (OpenSupport.site (X := X) P).category)
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op W)) :
    K.aatTranslateSection P target hne ξ W 0 s = s :=
  (K.actualAffineAtlas P target hne ξ).translateSection_zero s

/-- Original coefficient addition composes the actual affine translations. -/
theorem aatTranslateSection_add (W : (OpenSupport.site (X := X) P).category)
    (g h : (P.aatLocallyConstantObstructionSheaf
      (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.obj (op W))
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op W)) :
    K.aatTranslateSection P target hne ξ W (g+h) s =
      K.aatTranslateSection P target hne ξ W g (K.aatTranslateSection P target hne ξ W h s) :=
  (K.actualAffineAtlas P target hne ξ).translateSection_add g h s

/-- The local trivialization intertwines the original coefficient sheaf action and addition. -/
theorem aatLocalTrivialization_translate (W : (OpenSupport.site (X := X) P).category)
    (i : I) (h : (OpenSupport.contextOpenSupport (Space := X) P).support.obj W ≤ K.patch i)
    (g : (P.aatLocallyConstantObstructionSheaf
      (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.obj (op W))
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op W)) :
    K.aatLocalTrivialization P target hne ξ W i h (K.aatTranslateSection P target hne ξ W g s) =
      K.aatLocalTrivialization P target hne ξ W i h s + g :=
  (K.actualAffineAtlas P target hne ξ).localTrivialization_translate i h g s

/-- The existing primitive coefficient sheaf acts freely and transitively inside every chart. -/
theorem existsUnique_aatTranslateSection (W : (OpenSupport.site (X := X) P).category)
    (i : I) (h : (OpenSupport.contextOpenSupport (Space := X) P).support.obj W ≤ K.patch i)
    (s t : (K.aatStateSheaf P target hne ξ).carrier.obj (op W)) :
    ∃! g : (P.aatLocallyConstantObstructionSheaf
      (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.obj (op W),
        K.aatTranslateSection P target hne ξ W g s = t :=
  (K.actualAffineAtlas P target hne ξ).existsUnique_translateSection i h s t

/-- The coefficient action commutes with the original actual AAT restrictions. -/
theorem aatTranslateSection_restriction {W V : (OpenSupport.site (X := X) P).category}
    (f : W ⟶ V)
    (g : (P.aatLocallyConstantObstructionSheaf
      (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.obj (op V))
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op V)) :
    (K.aatStateSheaf P target hne ξ).carrier.map f.op
      (K.aatTranslateSection P target hne ξ V g s) =
        K.aatTranslateSection P target hne ξ W
          ((P.aatLocallyConstantObstructionSheaf
            (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.map f.op g)
          ((K.aatStateSheaf P target hne ξ).carrier.map f.op s) := by
  rw [K.aatStateSheaf_map,K.aatStateSheaf_map]
  change (K.actualAffineAtlas P target hne ξ).restrict _
    ((K.actualAffineAtlas P target hne ξ).translateSection _ s) =
      (K.actualAffineAtlas P target hne ξ).translateSection _ _
  rw [P.actualSectionEquiv_restriction]
  exact (K.actualAffineAtlas P target hne ξ).translateSection_restrict _ _ s

/-- Local trivializations commute with the original actual coefficient and state restrictions. -/
theorem aatLocalTrivialization_restriction {W V : (OpenSupport.site (X := X) P).category}
    (f : W ⟶ V) (i : I)
    (hV : (OpenSupport.contextOpenSupport (Space := X) P).support.obj V ≤ K.patch i)
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op V)) :
    K.aatLocalTrivialization P target hne ξ W i
      (le_trans ((OpenSupport.contextOpenSupport (Space := X) P).support.map f).le hV)
      ((K.aatStateSheaf P target hne ξ).carrier.map f.op s) =
        (P.aatLocallyConstantObstructionSheaf
          (OpenSupport.contextOpenSupport (Space := X) P)).carrier.toPresheaf.map f.op
          (K.aatLocalTrivialization P target hne ξ V i hV s) := by
  apply (P.actualSectionEquiv (OpenSupport.contextOpenSupport (Space := X) P) W).injective
  rw [K.aatStateSheaf_map,P.actualSectionEquiv_restriction]
  exact (K.actualAffineAtlas P target hne ξ).localTrivialization_restrict i hV _ s

/-- The actual AAT base context has the original whole-space support. -/
theorem actualBaseSupport_eq :
    (OpenSupport.contextOpenSupport (Space := X) P).support.obj
      (K.actualCechCover P target hne).base = ⊤ :=
  OpenSupport.contextOpenSupport_obj_openContext P _

/-- AAT sections of the original base context are the same generated global affine states. -/
def aatGlobalStateEquiv :
    (K.aatStateSheaf P target hne ξ).carrier.obj (op (K.actualCechCover P target hne).base) ≃
      (K.actualAffineAtlas P target hne ξ).StateSection ⊤ :=
  (K.actualAffineAtlas P target hne ξ).sectionEquivOfEq (K.actualBaseSupport_eq P target hne)

/-- Actual AAT chart sections retain their original geometric support. -/
def aatChartStateEquiv (i : I) :
    (K.aatStateSheaf P target hne ξ).carrier.obj
      (op ((K.actualCechCover P target hne).chartContext i)) ≃
        (K.actualAffineAtlas P target hne ξ).StateSection (K.patch i) :=
  (K.actualAffineAtlas P target hne ξ).sectionEquivOfEq (K.actualChartSupport_eq P target hne i)

/-- Global support identification commutes with the original AAT chart inclusions. -/
theorem aatGlobalStateEquiv_restriction (i : I)
    (s : (K.aatStateSheaf P target hne ξ).carrier.obj (op (K.actualCechCover P target hne).base)) :
    K.aatChartStateEquiv P target hne ξ i
      ((K.aatStateSheaf P target hne ξ).carrier.map
        ((K.actualCechCover P target hne).inclusion i).op s) =
      (K.actualAffineAtlas P target hne ξ).restrict le_top
        (K.aatGlobalStateEquiv P target hne ξ s) := by
  rw [K.aatStateSheaf_map]
  exact (K.actualAffineAtlas P target hne ξ).sectionEquivOfEq_restrict
    (K.actualBaseSupport_eq P target hne) (K.actualChartSupport_eq P target hne i) _ s

variable [Fintype Source]

/-- Every original repair uniquely glues the same p-n sections through the original AAT inclusions. -/
theorem aat_corrected_gluing
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0)
    (hn : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch) :
    ∃! s : (K.aatStateSheaf P target hne x.transition).carrier.obj
      (op (K.actualCechCover P target hne).base),
      ∀ i, (K.actualAffineAtlas P target hne x.transition).localTrivialization i le_rfl
        (K.aatChartStateEquiv P target hne x.transition i
          ((K.aatStateSheaf P target hne x.transition).carrier.map
            ((K.actualCechCover P target hne).inclusion i).op s)) =
          K.actualChartCoordinates P target hne (x.localState-n) i := by
  obtain ⟨g,hg,hu⟩ := K.actual_corrected_gluing P target hne x n hn
  refine ⟨(K.aatGlobalStateEquiv P target hne x.transition).symm g,?_,?_⟩
  · intro i
    rw [K.aatGlobalStateEquiv_restriction,Equiv.apply_symm_apply]
    exact hg i
  · intro s hs
    apply (K.aatGlobalStateEquiv P target hne x.transition).injective
    rw [Equiv.apply_symm_apply]
    apply hu
    intro i
    have hi := hs i
    rw [K.aatGlobalStateEquiv_restriction] at hi
    exact hi

/-- Zero original descent obstruction is exactly nonemptiness of actual AAT global affine states. -/
theorem existingDescent_zero_iff_aat_global_state
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne)) :
    x.existingDescentAdditiveClass = 0 ↔
      Nonempty ((K.aatStateSheaf P target hne x.transition).carrier.obj
        (op (K.actualCechCover P target hne).base)) := by
  rw [K.existingDescent_zero_iff_global_state P target hne x]
  constructor
  · rintro ⟨s⟩
    exact ⟨(K.aatGlobalStateEquiv P target hne x.transition).symm s⟩
  · rintro ⟨s⟩
    exact ⟨K.aatGlobalStateEquiv P target hne x.transition s⟩

/-- Correction existence and actual AAT global state nonemptiness are equivalent for every input. -/
theorem correction_iff_aat_global_state
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne)) :
    (∃ n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0,
      (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch) ↔
        Nonempty ((K.aatStateSheaf P target hne x.transition).carrier.obj
          (op (K.actualCechCover P target hne).base)) :=
  x.existingDescent_zero_iff_correction.symm.trans
    (K.existingDescent_zero_iff_aat_global_state P target hne x)

/-- B3 and diagnostic zero construct a repair and its actual unique AAT gluing of p-n. -/
theorem exists_actual_repair_and_aat_gluing
    (hadequate : laws.Adequate q) (hR : P.ReflectionCondition)
    (hvisible : ∀ label e, ¬K.graph.IsBridge (Graph.unoriented K.graph e) →
      e ∈ K.visibleEdgeSet target hne hadequate label)
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne))
    (hx : x.diagnosticClass hadequate = 0) :
    ∃ n : (P.faceEmptyCechComplex (K.actualCechCover P target hne)).Cn 0,
      (P.faceEmptyCechComplex (K.actualCechCover P target hne)).d 0 n = x.actualMismatch ∧
        ∃! s : (K.aatStateSheaf P target hne x.transition).carrier.obj
          (op (K.actualCechCover P target hne).base),
          ∀ i, (K.actualAffineAtlas P target hne x.transition).localTrivialization i le_rfl
            (K.aatChartStateEquiv P target hne x.transition i
              ((K.aatStateSheaf P target hne x.transition).carrier.map
                ((K.actualCechCover P target hne).inclusion i).op s)) =
                  K.actualChartCoordinates P target hne (x.localState-n) i := by
  obtain ⟨n,hn⟩ := K.exists_actual_integral_correction target hne hadequate P hR hvisible x hx
  exact ⟨n,hn,K.aat_corrected_gluing P target hne x n hn⟩

/-- Under B3, diagnostic zero is equivalent to actual AAT global affine state nonemptiness. -/
theorem diagnostic_zero_iff_aat_global_state
    (hadequate : laws.Adequate q) (hR : P.ReflectionCondition)
    (hvisible : ∀ label e, ¬K.graph.IsBridge (Graph.unoriented K.graph e) →
      e ∈ K.visibleEdgeSet target hne hadequate label)
    (x : GeneratorPresentation.ActualCechAffineLocalData P (K.actualCechCover P target hne)) :
    x.diagnosticClass hadequate = 0 ↔
      Nonempty ((K.aatStateSheaf P target hne x.transition).carrier.obj
        (op (K.actualCechCover P target hne).base)) :=
  (K.input_reflection_of_nonbridge_visible target hne hadequate P hR hvisible x).trans
    (K.existingDescent_zero_iff_aat_global_state P target hne x)

end AAT.AG.VisibleCycleReflection.GeometricCover
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
