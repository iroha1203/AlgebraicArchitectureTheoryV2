import Mathlib.CategoryTheory.Adjunction.Whiskering
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentSheafAlgebras
import Formal.SHIGURE.Part2.Schemes.RelativeSpecAlgebraBaseChange

/-! # Affine presentations of algebra sheaves

On an affine open, the restriction as an algebra is the algebra sheaf
associated to its section ring. Conversely, the underlying module of
any such local algebra presentation has a tilde presentation.

## Implementation notes

We use the actual algebra pullback from the relative spectrum. On an
open immersion it agrees with restriction along the open image functor;
the latter computes the underlying module restriction on each open.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

section OpenImmersion

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

private abbrev restrictRingSheaf : (X : TopCat).Sheaf CommRingCat.{u} ⥤ (Y : TopCat).Sheaf CommRingCat.{u} :=
  f.opensFunctor.sheafPushforwardContinuous CommRingCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

private def restrictRingAdjunction :
    restrictRingSheaf f ⊣ TopCat.Sheaf.pushforward CommRingCat f.base :=
  ((f.isOpenEmbedding.isOpenMap.adjunction).op.whiskerLeft CommRingCat.{u}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) _)
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) _)
    (Iso.refl _) (Iso.refl _)

private def restrictStructureIso :
    Y.sheaf ≅ (restrictRingSheaf f).obj X.sheaf :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U => (f.appIso U.unop).symm)
      (fun i => f.appIso_inv_naturality i))

private def restrictOpenAlgebra : Under X.sheaf ⥤ Under Y.sheaf :=
  Under.post (restrictRingSheaf f) ⋙ Under.map (restrictStructureIso f).hom

private theorem restrictRing_unit_comp (U : X.Opens) :
    ((restrictRingAdjunction f).unit.app X.sheaf).val.app (op U) ≫
      (restrictStructureIso f).inv.val.app (op (f ⁻¹ᵁ U)) = f.app U := by
  have h := (f.app_appIso_inv U).symm
  change ((restrictRingAdjunction f).unit.app X.sheaf).val.app (op U) ≫
    (f.appIso (f ⁻¹ᵁ U)).hom = f.app U
  have same : ((restrictRingAdjunction f).unit.app X.sheaf).val.app (op U) =
      X.presheaf.map (homOfLE (f.image_preimage_le U)).op := by
    rfl
  calc
    _ = (f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv) ≫ (f.appIso (f ⁻¹ᵁ U)).hom :=
      congrArg (· ≫ (f.appIso (f ⁻¹ᵁ U)).hom) (same.trans h)
    _ = _ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def restrictOpenAlgebraAdjunction : restrictOpenAlgebra f ⊣ pushforwardAlgebra f := by
  let a := (Under.postAdjunctionLeft (restrictRingAdjunction f)).comp
    (Under.mapIso (restrictStructureIso f)).toAdjunction
  refine a.ofNatIsoRight (NatIso.ofComponents (fun B => Under.isoMk (.refl _) ?_) ?_)
  · apply Sheaf.hom_ext
    ext1
    funext U
    change (((restrictRingAdjunction f).unit.app X.sheaf).val.app U ≫
      ((restrictStructureIso f).inv.val.app (op (f ⁻¹ᵁ U.unop)) ≫ B.hom.val.app _)) ≫
      𝟙 _ = f.app U.unop ≫ B.hom.val.app _
    rw [Category.comp_id, ← Category.assoc, restrictRing_unit_comp]
  · intro A B g
    ext
    simp [pushforwardAlgebra]

private def restrictOpenAlgebraIsoPullback : restrictOpenAlgebra f ≅ pullbackAlgebra f :=
  (restrictOpenAlgebraAdjunction f).leftAdjointUniq (pullbackAlgebraAdjunction f)

private def restrictOpenUnderlying (C : Under X.sheaf) :
    algebraUnderlyingModule ((restrictOpenAlgebra f).obj C) ≅
      (algebraUnderlyingModule C).restrict f :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => .refl _) (fun _ _ _ => by simp; rfl))

end OpenImmersion

section Underlying

variable {X : Scheme.{u}}

private def algebraUnderlyingModuleIso {C D : Under X.sheaf} (e : C ≅ D) :
    algebraUnderlyingModule C ≅ algebraUnderlyingModule D := by
  let F := Under.forget X.sheaf ⋙ sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat
  let presheafIso := F.mapIso e
  let components (U : X.Opensᵒᵖ) :
      (algebraUnderlyingModule C).val.obj U ≅ (algebraUnderlyingModule D).val.obj U := by
    let eU : C.right.val.obj U ≃+* D.right.val.obj U :=
      (presheafIso.app U).commRingCatIsoToRingEquiv
    let c : X.presheaf.obj U ⟶ C.right.val.obj U := C.hom.val.app U
    let d : X.presheaf.obj U ⟶ D.right.val.obj U := D.hom.val.app U
    let toLinear : (algebraUnderlyingModule C).val.obj U ≃ₗ[X.ringCatSheaf.val.obj U]
        (algebraUnderlyingModule D).val.obj U :=
      { eU.toAddEquiv with
        map_smul' := fun r x => by
          let r' : X.presheaf.obj U := r
          let x' : C.right.val.obj U := x
          change eU (c r' * x') = d r' * eU x'
          rw [map_mul]
          have scalar := congrArg (fun t : X.sheaf ⟶ D.right => t.val.app U r') (Under.w e.hom)
          exact congrArg (· * eU x') scalar }
    exact toLinear.toModuleIso
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk components ?_
  intro U V j
  ext x
  change e.hom.right.val.app V (C.right.val.map j x) =
    D.right.val.map j (e.hom.right.val.app U x)
  exact congrArg (fun t : C.right.val.obj U ⟶ D.right.val.obj V => t x) (e.hom.right.val.naturality j)

private def directImageUnderlyingIso {Y : Scheme.{u}} (f : Y ⟶ X) :
    algebraUnderlyingModule (directImageStructure f) ≅
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => .refl _) (fun _ _ _ => by simp; rfl))

end Underlying

section Presentations

variable {X : Scheme.{u}}

/-- On an affine open, the actual algebra restriction is the direct image
from the spectrum of its section algebra, over the spectrum of the base ring.
This is the identification of the restriction with the algebra of sections in Lemma B.7. The
quasi-coherence hypothesis supplies its affine chart through ofSheaf. -/
def quasiCoherentAlgebra_affinePresentation (C : Under X.sheaf)
    (coherent : IsQuasiCoherentSheafAlgebra C) {U : X.Opens} (hU : IsAffineOpen U) :
    (pullbackAlgebra hU.fromSpec).obj C ≅
      directImageStructure (Spec.map (C.hom.val.app (op U))) := by
  let Q := QuasiCoherentAlgebra.ofSheaf C coherent
  let W : X.AffineZariskiSite := ⟨U, hU⟩
  let a := C.hom.val.app (op U)
  have square : IsPullback (Q.chart W) (Spec.map a) Q.projection hU.fromSpec := by
    refine ((Q.isPullback_chart W).flip).of_iso (Iso.refl _) (Iso.refl _)
      hU.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · change (Spec.map a ≫ hU.isoSpec.inv) ≫ hU.isoSpec.hom = 𝟙 _ ≫ Spec.map a
      simp
    · simp
    · change U.ι ≫ 𝟙 X = hU.isoSpec.hom ≫ hU.fromSpec
      rw [IsAffineOpen.fromSpec, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  let p := affinePullbackAlgebra_isPushout square
  letI := p.hasPushout
  have comparison : (pullbackAlgebra hU.fromSpec).obj Q.algebraSheaf ≅
      directImageStructure (Spec.map a) := by
    refine Under.isoMk p.isoPushout.symm ?_
    change _ ≫ p.isoPushout.inv = _
    exact p.inr_isoPushout_inv
  exact (pullbackAlgebra hU.fromSpec).mapIso (QuasiCoherentAlgebra.ofSheaf_algebraSheafIso C coherent).symm ≪≫ comparison

/-- The actual algebra restriction is associated to an algebra over the section ring
of the affine open. The comparison preserves the structure morphism.
This is the form of the local presentation in Lemma B.7 that records the algebra isomorphism
over the affine base. -/
def HasAlgebraTildeOn (C : Under X.sheaf) {U : X.Opens} (hU : IsAffineOpen U) : Prop :=
  ∃ (A : CommRingCat.{u}) (a : Γ(X, U) ⟶ A),
    Nonempty ((pullbackAlgebra hU.fromSpec).obj C ≅ directImageStructure (Spec.map a))

/-- Presentations as algebras on an affine open cover.
This applies the module cover condition in the opening of Appendix B to the actual algebra
presentations in Lemma B.7. -/
def HasAffineAlgebraTildeCover (C : Under X.sheaf) : Prop :=
  ∃ (I : Type u) (U : I → X.affineOpens), (⨆ i, (U i : X.Opens)) = ⊤ ∧
    ∀ i, HasAlgebraTildeOn C (U i).property

private theorem HasAlgebraTildeOn.underlying {C : Under X.sheaf} {U : X.Opens}
    {hU : IsAffineOpen U} (localTilde : HasAlgebraTildeOn C hU) :
    HasTildeOn (algebraUnderlyingModule C) hU := by
  obtain ⟨A, a, ⟨e⟩⟩ := localTilde
  let comparison := (restrictOpenUnderlying hU.fromSpec C).symm ≪≫
    algebraUnderlyingModuleIso ((restrictOpenAlgebraIsoPullback hU.fromSpec).app C ≪≫ e) ≪≫
    directImageUnderlyingIso (Spec.map a)
  have represented : (tilde.functor A).essImage (SheafOfModules.unit (Spec A).ringCatSheaf) :=
    ⟨ModuleCat.of A A, ⟨tildeSelf⟩⟩
  obtain ⟨N, ⟨iso⟩⟩ := affinePushforward_essImage a _ represented
  exact ⟨N, ⟨iso ≪≫ comparison.symm⟩⟩

/-- Quasi-coherence is equivalent to a presentation as an algebra sheaf on every affine open.
This compares the all-affine algebra presentations of Lemma B.7 with quasi-coherence of the
underlying module. The two directions use the given quasi-coherence or the given algebra
presentations on each affine open. -/
theorem isQuasiCoherentSheafAlgebra_iff_eachAlgebraPresentation (C : Under X.sheaf) :
    IsQuasiCoherentSheafAlgebra C ↔ ∀ U : X.affineOpens, HasAlgebraTildeOn C U.property := by
  constructor
  · intro coherent U
    exact ⟨C.right.val.obj (op U.1), C.hom.val.app (op U.1),
      ⟨quasiCoherentAlgebra_affinePresentation C coherent U.property⟩⟩
  · intro presentations U
    exact (presentations U).underlying

/-- The presentations as algebra sheaves on any affine open cover extend to all affine opens.
This is the main algebra cover criterion, obtained by applying the module criterion in the
opening of Appendix B to the algebra presentations in Lemma B.7. The reverse direction starts
from an arbitrary affine covering family and its given algebra presentations. -/
theorem isQuasiCoherentSheafAlgebra_iff_affineAlgebraTildeCover (C : Under X.sheaf) :
    IsQuasiCoherentSheafAlgebra C ↔ HasAffineAlgebraTildeCover C := by
  constructor
  · intro coherent
    exact ⟨X.affineOpens, id, iSup_affineOpens_eq_top X,
      (isQuasiCoherentSheafAlgebra_iff_eachAlgebraPresentation C).mp coherent⟩
  · rintro ⟨I, U, cover, presentations⟩
    exact (isQuasiCoherentSheafAlgebra_iff_affineCover C).mpr
      ⟨I, U, cover, fun i => (presentations i).underlying⟩

end Presentations

end

end SHIGURE.SchemeDescent
