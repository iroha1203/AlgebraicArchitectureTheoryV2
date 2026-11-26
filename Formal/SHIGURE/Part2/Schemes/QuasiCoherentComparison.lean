import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentModules

/-! # Comparison with mathlib's quasi-coherent sheaves

## Implementation notes

The affine tilde criterion directly expresses the local descriptions in
Appendix B. Mathlib uses local presentations by generators and relations on
a general ringed site. We identify the two definitions on schemes by using
the actual equivalence between opens of an open subscheme and the slice site
over its image, with the structure rings identified by the open immersion.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open SheafOfModules

noncomputable section

universe u

section OpenImmersion

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {U : X.Opens}

/-- The image functor of an open immersion factors through the opens over its image. -/
private def imageOver (inside : f.opensRange ≤ U) : Y.Opens ⥤ Over U :=
  Over.lift f.opensFunctor
    { app := fun V => homOfLE ((f.image_le_opensRange V).trans inside) }

private abbrev preimageOver (U : X.Opens) : Over U ⥤ Y.Opens :=
  Over.forget U ⋙ Opens.map f.base

private def imageOverEquivalence (range : f.opensRange = U) : Y.Opens ≌ Over U where
  functor := imageOver f range.le
  inverse := preimageOver f U
  unitIso := NatIso.ofComponents (fun V => eqToIso (f.preimage_image_eq V).symm)
  counitIso := NatIso.ofComponents (fun V => Over.isoMk (eqToIso (by
    change f ''ᵁ (f ⁻¹ᵁ V.left) = V.left
    rw [f.image_preimage_eq_opensRange_inf, range]
    exact inf_eq_right.mpr V.hom.le)) (Subsingleton.elim _ _))

private theorem imageOver_coverPreserving (inside : f.opensRange ≤ U) :
    CoverPreserving (Opens.grothendieckTopology Y) ((Opens.grothendieckTopology X).over U)
      (imageOver f inside) := by
  constructor
  intro V S covering
  rw [GrothendieckTopology.mem_over_iff]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨W, i, hi, hyW⟩ := covering y hy
  refine ⟨f ''ᵁ W, f.opensFunctor.map i, ?_, Set.mem_image_of_mem f hyW⟩
  exact ⟨(imageOver f inside).obj W, (imageOver f inside).map i, 𝟙 _, ⟨W, i, 𝟙 _, hi, rfl⟩, rfl⟩

private theorem imageOver_isContinuous (range : f.opensRange = U) :
    (imageOver f range.le).IsContinuous (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over U) := by
  letI : (imageOver f range.le).IsEquivalence := (imageOverEquivalence f range).isEquivalence_functor
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) (imageOver_coverPreserving f range.le)

private instance : (preimageOver f U).IsContinuous ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology Y) :=
  Functor.isContinuous_comp (Over.forget U) (Opens.map f.base)
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)

private def ringImageOverIso (range : f.opensRange = U) :
    Y.ringCatSheaf.val ≅ (imageOver f range.le).op ⋙ (X.ringCatSheaf.over U).val :=
  NatIso.ofComponents
    (fun V => (forget₂ CommRingCat RingCat).mapIso (f.appIso V.unop).symm)
    (fun a => congrArg ((forget₂ CommRingCat RingCat).map) (f.appIso_inv_naturality a))

private def moduleOverEquivalence (range : f.opensRange = U) :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ≌ Y.Modules := by
  let e := imageOverEquivalence f range
  letI : e.functor.IsContinuous (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over U) :=
    imageOver_isContinuous f range
  letI : e.inverse.IsContinuous ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology Y) :=
    inferInstanceAs ((preimageOver f U).IsContinuous _ _)
  let a := ringImageOverIso f range
  let b := Functor.whiskerRight (NatTrans.op e.counit) (X.ringCatSheaf.over U).val ≫
    Functor.whiskerLeft e.inverse.op a.inv
  refine pushforwardPushforwardEquivalence e ⟨a.hom⟩ ⟨b⟩ ?_ ?_
  · ext1
    funext V
    change _ = _ ≫ a.inv.app (op (e.inverse.obj V.unop)) ≫ a.hom.app (op (e.inverse.obj V.unop))
    simp
  · ext1
    funext V
    let R := (X.ringCatSheaf.over U).val
    let S := Y.ringCatSheaf.val
    let t := (e.unit.app V.unop).op
    change a.hom.app V ≫ R.map (e.counit.app (e.functor.obj V.unop)).op ≫
      a.inv.app _ ≫ S.map t = 𝟙 _
    have natural := a.inv.naturality t
    change R.map (e.functor.map (e.unit.app V.unop)).op ≫ a.inv.app V =
      a.inv.app (op (e.inverse.obj (e.functor.obj V.unop))) ≫ S.map t at natural
    rw [← natural]
    change a.hom.app V ≫ R.map (e.counit.app (e.functor.obj V.unop)).op ≫
      R.map (e.functor.map (e.unit.app V.unop)).op ≫ a.inv.app V = 𝟙 _
    rw [← Category.assoc (R.map _), ← Functor.map_comp, ← op_comp, e.functor_unit_comp]
    change a.hom.app V ≫ R.map (𝟙 (op (e.functor.obj V.unop))) ≫ a.inv.app V = 𝟙 _
    have same := congrArg
      (fun m : R.obj (op (e.functor.obj V.unop)) ⟶ R.obj (op (e.functor.obj V.unop)) =>
        a.hom.app V ≫ m ≫ a.inv.app V) (R.map_id (op (e.functor.obj V.unop)))
    exact same.trans ((congrArg (a.hom.app V ≫ ·) (Category.id_comp _)).trans (a.hom_inv_id_app V))

private def restrictOverIso (range : f.opensRange = U) (M : X.Modules) :
    (moduleOverEquivalence f range).functor.obj (M.over U) ≅ M.restrict f :=
  (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => by simp; rfl))

end OpenImmersion

set_option maxHeartbeats 600000 in
private def unitPushforwardIso {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (isIsoApp : ∀ V, IsIso (a.val.app V)) :
    (pushforward.{u} a).obj (unit.{u} R) ≅ unit.{u} S := by
  let m : unit.{u} S ⟶ (pushforward.{u} a).obj (unit.{u} R) := unitToPushforwardObjUnit a
  let components (V : Cᵒᵖ) : (unit.{u} S).val.obj V ≅ ((pushforward.{u} a).obj (unit.{u} R)).val.obj V := by
    letI := isIsoApp V
    exact (LinearEquiv.ofBijective (m.val.app V).hom
      (ConcreteCategory.bijective_of_isIso (a.val.app V))).toModuleIso
  refine ((fullyFaithfulForget S).preimageIso (X := unit.{u} S)
    (Y := (pushforward.{u} a).obj (unit.{u} R))
    (PresheafOfModules.isoMk components ?_)).symm
  intro V W i
  exact m.val.naturality i

private def restrictUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).obj (unit X.ringCatSheaf) ≅ unit Y.ringCatSheaf := by
  let comparison : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app U := (f.appIso U.unop).inv
      naturality _ _ i := f.appIso_inv_naturality i }
  let a : Y.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight comparison (forget₂ CommRingCat RingCat)⟩
  exact unitPushforwardIso a (fun V =>
    inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso V.unop).inv)))

private def overUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {U : X.Opens}
    (range : f.opensRange = U) :
    (moduleOverEquivalence f range).functor.obj (unit (X.ringCatSheaf.over U)) ≅
      unit Y.ringCatSheaf := by
  letI := imageOver_isContinuous f range
  let a : Y.ringCatSheaf ⟶ ((imageOver f range.le).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology Y) ((Opens.grothendieckTopology X).over U)).obj (X.ringCatSheaf.over U) :=
    ⟨(ringImageOverIso f range).hom⟩
  exact unitPushforwardIso a (fun V => inferInstanceAs (IsIso ((ringImageOverIso f range).hom.app V)))

set_option maxHeartbeats 1000000 in
private theorem tilde_of_presentation {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (p : M.Presentation) : (tilde.functor R).essImage M := by
  let F := tilde.functor R
  let a := (freeHomEquiv (kernel p.generators.π)).symm p.relations.s ≫ kernel.ι p.generators.π
  let b := p.generators.π
  let e₁ := tildeFinsupp (R := R) p.relations.I
  let e₂ := tildeFinsupp (R := R) p.generators.I
  let d := (tilde.fullyFaithfulFunctor (R := R)).preimage (e₁.hom ≫ a ≫ e₂.inv)
  have compat : F.map d ≫ e₂.hom = e₁.hom ≫ a := by
    change (tilde.functor R).map ((tilde.fullyFaithfulFunctor (R := R)).preimage _) ≫ _ = _
    have comparison := (tilde.fullyFaithfulFunctor (R := R)).map_preimage (e₁.hom ≫ a ≫ e₂.inv)
    rw [comparison]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have vanishes : F.map d ≫ (e₂.hom ≫ b) = 0 := by
    calc
      _ = e₁.hom ≫ (a ≫ b) := by
        simpa only [Category.assoc] using congrArg (fun h => h ≫ b) compat
      _ = 0 := by simp only [a, b, Category.assoc, kernel.condition, comp_zero]
  let c := CokernelCofork.ofπ (f := F.map d) (e₂.hom ≫ b) vanishes
  have isColimit : IsColimit c := by
    refine IsCokernel.ofIso a p.isColimit c e₁.symm e₂.symm (.refl _) ?_ ?_
    · rw [← cancel_mono e₂.hom]
      simp [compat]
    · simp [c, b]
  refine ⟨cokernel d, ⟨?_⟩⟩
  exact (CokernelCofork.mapIsColimit _ (colimit.isColimit (parallelPair d 0)) F)
    |>.coconePointUniqueUpToIso isColimit

private theorem coversTop_iff_iSup {X : Scheme.{u}} {I : Type u} (U : I → X.Opens) :
    (Opens.grothendieckTopology X).CoversTop U ↔ (⨆ i, U i) = ⊤ := by
  constructor
  · intro covering
    apply top_le_iff.mp
    intro x hx
    obtain ⟨W, i, hi, hxW⟩ := covering ⊤ x hx
    obtain ⟨j, ⟨incl⟩⟩ := (Sieve.mem_ofObjects_iff U i).mp hi
    exact Opens.mem_iSup.mpr ⟨j, incl.le hxW⟩
  · intro covering V x hx
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (covering.ge (Set.mem_univ x))
    refine ⟨V ⊓ U j, homOfLE inf_le_left, ?_, ⟨hx, hxj⟩⟩
    exact (Sieve.mem_ofObjects_iff U _).mpr ⟨j, ⟨homOfLE inf_le_right⟩⟩

variable {X : Scheme.{u}}

private def restrictedPresentation {M : X.Modules} {U V : X.Opens}
    (inside : V ≤ U) (hV : IsAffineOpen V) (p : (M.over U).Presentation) :
    (M.restrict hV.fromSpec).Presentation := by
  let E := moduleOverEquivalence U.ι (Scheme.Opens.opensRange_ι U)
  let base : (M.restrict U.ι).Presentation := Presentation.of_isIso.{u,u,u}
    (restrictOverIso U.ι (Scheme.Opens.opensRange_ι U) M).hom
    (p.map E.functor (overUnitIso U.ι (Scheme.Opens.opensRange_ι U)))
  let g : Spec Γ(X, V) ⟶ U := hV.isoSpec.inv ≫ X.homOfLE inside
  letI : IsOpenImmersion g := by dsimp [g]; infer_instance
  have composite : g ≫ U.ι = hV.fromSpec := by
    simp [g, Category.assoc]
  let e := ((Scheme.Modules.restrictFunctorComp g U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr composite).app M
  letI : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor g) :=
    (Scheme.Modules.restrictAdjunction g).leftAdjoint_preservesColimits
  exact Presentation.of_isIso.{u,u,u} e.hom
    (base.map (Scheme.Modules.restrictFunctor g) (restrictUnitIso g))

private def overPresentation {M : X.Modules} {U : X.Opens}
    (hU : IsAffineOpen U) (N : ModuleCat Γ(X, U))
    (e : tilde N ≅ M.restrict hU.fromSpec) : (M.over U).Presentation := by
  let F := moduleOverEquivalence hU.fromSpec hU.opensRange_fromSpec
  let unitIso := overUnitIso hU.fromSpec hU.opensRange_fromSpec
  let base : (F.functor.obj (M.over U)).Presentation := Presentation.of_isIso.{u,u,u}
    (e ≪≫ (restrictOverIso hU.fromSpec hU.opensRange_fromSpec M).symm).hom
    (presentationTilde N Set.univ (by simp) _ (Submodule.span_eq _))
  let inverseUnit := (F.unitIso.app (unit (X.ringCatSheaf.over U))).symm
  let eUnit := F.inverse.mapIso unitIso.symm ≪≫ inverseUnit
  exact Presentation.of_isIso.{u,u,u} (F.unitIso.app (M.over U)).inv (base.map F.inverse eUnit)

/-- The affine tilde criterion is equivalent to mathlib's site-theoretic
quasi-coherence, given by local presentations by generators and relations. -/
theorem isQuasiCoherentModule_iff_mathlib (M : X.Modules) :
    IsQuasiCoherentModule M ↔ M.IsQuasicoherent := by
  constructor
  · intro coherent
    classical
    let opens (U : X.affineOpens) : X.Opens := U.1
    let q : M.QuasicoherentData :=
      { I := X.affineOpens
        X := opens
        coversTop := (coversTop_iff_iSup opens).mpr (iSup_affineOpens_eq_top X)
        presentation := fun U =>
          let witness := coherent U
          overPresentation U.property witness.choose witness.choose_spec.some }
    exact q.isQuasicoherent
  · intro coherent
    obtain ⟨q⟩ := coherent.nonempty_quasicoherentData
    let I := {V : X.affineOpens // ∃ i, V.1 ≤ q.X i}
    apply (isQuasiCoherentModule_iff_affineCover M).mpr
    refine ⟨I, Subtype.val, ?_, ?_⟩
    · apply top_le_iff.mp
      intro x hx
      have covering := (coversTop_iff_iSup q.X).mp q.coversTop
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (covering.ge hx)
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxi (q.X i).isOpen
      exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩
    · rintro ⟨V, i, inside⟩
      exact tilde_of_presentation _ (restrictedPresentation inside V.property (q.presentation i))

end

end SHIGURE.SchemeDescent
