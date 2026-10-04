import ResearchLean.AG.VisibleCycleReflection.AffineStateSheaf
import Formal.Util.AssertStandardAxioms

/-!
# Actual chart states and unique affine gluing

## Implementation notes

Compatible coefficient sections are sent through the inverse local
trivializations. Mathlib's actual sheaf gluing theorem then constructs their
unique global affine state. The equation uses the original transition and
original primitive coefficients. Actual Cech normalization is evaluated on
every chart point, so a normalized coordinate does not replace the real
locally constant section without an equality theorem.
-/

noncomputable section
open CategoryTheory TopologicalSpace Opposite
namespace AAT.AG.VisibleCycleReflection.AffineAtlas
universe u
variable {X I M : Type u} [TopologicalSpace X] [AddCommGroup M]
variable (A : AffineAtlas X I M)

/-- Compatible coefficient sections on the chart intersections glue uniquely as affine states. -/
theorem existsUnique_gluing_coordinates (U : Opens X)
    (r : ∀ i, LocallyConstant (U ⊓ A.patch i : Opens X) M)
    (hr : ∀ i j (x : U) (hi : x.1 ∈ A.patch i) (hj : x.1 ∈ A.patch j),
      r i ⟨x.1,⟨x.2,hi⟩⟩ = A.transition i j + r j ⟨x.1,⟨x.2,hj⟩⟩) :
    ∃! s : A.StateSection U, ∀ i,
      A.localTrivialization i inf_le_right (A.restrict inf_le_left s) = r i := by
  let W (i : I) : Opens X := U ⊓ A.patch i
  let sf (i : I) : A.StateSection (W i) :=
    (A.localTrivialization i inf_le_right).symm (r i)
  have hcover : U ≤ iSup W := by
    intro x hx
    obtain ⟨i,hi⟩ := A.covers x
    exact Opens.mem_iSup.mpr ⟨i,⟨hx,hi⟩⟩
  have hsf : TopCat.Presheaf.IsCompatible A.stateSheaf.presheaf W sf := by
    intro i j
    -- This changes only the concrete Type-category morphism notation.
    change A.stateSheaf.presheaf.map (homOfLE (show W i ⊓ W j ≤ W i from inf_le_left)).op (sf i) =
      A.stateSheaf.presheaf.map (homOfLE (show W i ⊓ W j ≤ W j from inf_le_right)).op (sf j)
    rw [A.stateSheaf_map,A.stateSheaf_map]
    apply Subtype.ext
    funext x
    apply A.fiber_ext x.1 i x.2.1.2
    rw [restrict_value,restrict_value]
    dsimp only [sf]
    rw [localTrivialization_symm,localTrivialization_symm,
      sectionFromCoordinates_value,sectionFromCoordinates_value,
      coordinate_fiberFromCoordinate,coordinate_fiberFromCoordinate,A.self,zero_add]
    exact hr i j ⟨x.1,x.2.1.1⟩ x.2.1.2 x.2.2.2
  obtain ⟨s,hs,hunique⟩ := A.stateSheaf.existsUnique_gluing' W U
    (fun _ => homOfLE inf_le_left) hcover sf hsf
  refine ⟨s,?_,?_⟩
  · intro i
    have h := hs i
    change A.stateSheaf.presheaf.map (homOfLE (show W i ≤ U from inf_le_left)).op s = sf i at h
    rw [A.stateSheaf_map] at h
    rw [h]
    exact (A.localTrivialization i inf_le_right).apply_symm_apply (r i)
  · intro t ht
    apply hunique
    intro i
    change A.stateSheaf.presheaf.map (homOfLE (show W i ≤ U from inf_le_left)).op t = sf i
    rw [A.stateSheaf_map]
    apply (A.localTrivialization i inf_le_right).injective
    rw [ht i]
    exact ((A.localTrivialization i inf_le_right).apply_symm_apply (r i)).symm

/-- Chart coefficient sections satisfying the original affine transitions have a unique global state. -/
theorem existsUnique_gluing_chart_coordinates
    (r : ∀ i, LocallyConstant (A.patch i) M)
    (hr : ∀ i j (x : X) (hi : x ∈ A.patch i) (hj : x ∈ A.patch j),
      r i ⟨x,hi⟩ = A.transition i j + r j ⟨x,hj⟩) :
    ∃! s : A.StateSection ⊤, ∀ i,
      A.localTrivialization i le_rfl (A.restrict le_top s) = r i := by
  let r' (i : I) : LocallyConstant (⊤ ⊓ A.patch i : Opens X) M :=
    LocallyConstant.comap
      ⟨Set.inclusion inf_le_right,(Opens.isOpenEmbedding_of_le inf_le_right).continuous⟩ (r i)
  have hr' : ∀ i j (x : (⊤ : Opens X)) (hi : x.1 ∈ A.patch i) (hj : x.1 ∈ A.patch j),
      r' i ⟨x.1,⟨x.2,hi⟩⟩ = A.transition i j + r' j ⟨x.1,⟨x.2,hj⟩⟩ := by
    intro i j x hi hj
    exact hr i j x.1 hi hj
  obtain ⟨s,hs,hunique⟩ := A.existsUnique_gluing_coordinates ⊤ r' hr'
  refine ⟨s,?_,?_⟩
  · intro i
    apply LocallyConstant.ext
    intro x
    have h := congrArg (fun g => g (⟨x.1,⟨trivial,x.2⟩⟩ : (⊤ ⊓ A.patch i : Opens X))) (hs i)
    dsimp only at h
    rw [localTrivialization_apply,restrict_value] at h
    rw [localTrivialization_apply,restrict_value]
    exact h
  · intro t ht
    apply hunique
    intro i
    apply LocallyConstant.ext
    intro x
    have h := congrArg (fun g => g (⟨x.1,x.2.2⟩ : A.patch i)) (ht i)
    dsimp only at h
    rw [localTrivialization_apply,restrict_value] at h
    rw [localTrivialization_apply,restrict_value]
    exact h

end AAT.AG.VisibleCycleReflection.AffineAtlas

namespace AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}

/-- Public section identification on every actual context, including empty supports. -/
def actualSectionEquiv (P : GeneratorPresentation laws) (G : ContextOpenSupport S) (W : S.category) :
    (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.obj (op W) ≃+
      LocallyConstant (G.support.obj W) P.PresentationGroup := AddEquiv.refl _

/-- Original coefficient restrictions are the same locally constant open-support restrictions. -/
theorem actualSectionEquiv_restriction (P : GeneratorPresentation laws)
    (G : ContextOpenSupport S) {W V : S.category} (f : W ⟶ V)
    (g : (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.obj (op V)) :
    P.actualSectionEquiv G W
      ((P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map f.op g) =
        LocallyConstant.comap
          ⟨Set.inclusion (G.support.map f).le,
            (Opens.isOpenEmbedding_of_le (G.support.map f).le).continuous⟩
          (P.actualSectionEquiv G V g) := rfl

/-- Public evaluation formula for the connected-support actual coefficient coordinates. -/
theorem aatLocallyConstantObstructionSectionEquiv_value (P : GeneratorPresentation laws)
    (G : ContextOpenSupport S) (W : S.category)
    [Nonempty (G.support.obj W)] [PreconnectedSpace (G.support.obj W)]
    (s : (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.obj (op W))
    (x : G.support.obj W) :
    P.aatLocallyConstantObstructionSectionEquiv G W s = P.actualSectionEquiv G W s x := by
  change P.actualSectionEquiv G W s (Classical.choice inferInstance) = P.actualSectionEquiv G W s x
  exact (P.actualSectionEquiv G W s).apply_eq_of_preconnectedSpace _ _

variable {q : Reading Source} {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent] (P : GeneratorPresentation laws)
variable (C : GeneratorPresentation.FaceEmptyAATCechCover D G)

omit [IsEmpty D.nerve.FaceComponent] in
/-- Public evaluation of the original primitive-coordinate differential. -/
@[simp] theorem presentationD0_apply (c : P.PresentationCochain0 D) (e : D.nerve.EdgeComponent) :
    P.presentationD0 D c e = c (D.nerve.edgeRight e) - c (D.nerve.edgeLeft e) := rfl

/-- Normalized chart coordinates equal the actual section at every chart point. -/
theorem faceEmptyCechCochain0Equiv_value (c : (P.faceEmptyCechComplex C).Cn 0)
    (i : D.nerve.Chart) (x : G.support.obj (C.chartContext i)) :
    P.faceEmptyCechCochain0Equiv C c i = P.actualSectionEquiv G (C.chartContext i) (c i) x := by
  letI := C.chartSupportNonempty i
  letI := C.chartSupportPreconnected i
  exact P.aatLocallyConstantObstructionSectionEquiv_value G (C.chartContext i) (c i) x

/-- Normalized transition coordinates equal the actual section at every overlap point. -/
theorem faceEmptyCechCochain1Equiv_value (c : (P.faceEmptyCechComplex C).Cn 1)
    (e : D.nerve.EdgeComponent) (x : G.support.obj (C.edgeContext e)) :
    P.faceEmptyCechCochain1Equiv C c e = P.actualSectionEquiv G (C.edgeContext e) (c e) x := by
  letI := C.edgeSupportNonempty e
  letI := C.edgeSupportPreconnected e
  exact P.aatLocallyConstantObstructionSectionEquiv_value G (C.edgeContext e) (c e) x

end AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation
