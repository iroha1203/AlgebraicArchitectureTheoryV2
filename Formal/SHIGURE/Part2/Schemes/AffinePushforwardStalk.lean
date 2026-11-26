import Formal.SHIGURE.Part2.Schemes.RelativeSpecBaseChange
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Stalks of affine direct image algebras

The stalk over an affine open is obtained by localizing the ring of
functions on its inverse image at the denominators from the base point.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {X Z : Scheme.{u}} (h : Z ⟶ X) [IsAffineHom h]
  (U : X.AffineZariskiSite) (x : U.1)

private theorem denominator_of_mem_basicOpen (r : Γ(X, U.1))
    (hr : x.val ∈ X.basicOpen r) : r ∈ (U.2.primeIdealOf x).asIdeal.primeCompl := by
  rw [U.2.primeIdealOf_eq_map_closedPoint]
  change X.presheaf.germ U.1 x.val x.property r ∉ IsLocalRing.maximalIdeal _
  exact IsLocalRing.notMem_maximalIdeal.mpr ((X.mem_basicOpen' r x).mp hr)

private theorem mem_basicOpen_of_denominator (r : Γ(X, U.1))
    (hr : r ∈ (U.2.primeIdealOf x).asIdeal.primeCompl) : x.val ∈ X.basicOpen r := by
  rw [U.2.primeIdealOf_eq_map_closedPoint] at hr
  change X.presheaf.germ U.1 x.val x.property r ∉ IsLocalRing.maximalIdeal _ at hr
  exact (X.mem_basicOpen' r x).mpr (IsLocalRing.notMem_maximalIdeal.mp hr)

private abbrev affineDirectImage : (X : TopCat).Presheaf CommRingCat := (directImageStructure h).right.val

private theorem affinePushforwardStalk_isLocalization :
    let F := affineDirectImage h
    letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.stalk x.val) :=
      (F.germ U.1 x.val x.property).hom.toAlgebra
    IsLocalization ((U.2.primeIdealOf x).asIdeal.primeCompl.map (h.app U.1).hom)
      (F.stalk x.val) := by
  let F := affineDirectImage h
  let M := (U.2.primeIdealOf x).asIdeal.primeCompl
  letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.stalk x.val) :=
    (F.germ U.1 x.val x.property).hom.toAlgebra
  let f := (h.app U.1).hom
  let basicRes (r : Γ(X, U.1)) : F.obj (.op U.1) ⟶ F.obj (.op (X.basicOpen r)) :=
    F.map (homOfLE (X.basicOpen_le r)).op
  have localization (r : Γ(X, U.1)) :
      letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.obj (.op (X.basicOpen r))) := (basicRes r).hom.toAlgebra
      IsLocalization.Away (f r) (F.obj (.op (X.basicOpen r))) :=
    (QuasiCoherentAlgebra.ofAffine h).localization U r
  change IsLocalization (M.map f) (F.stalk x.val)
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨d, hd⟩
    obtain ⟨r, hr, hrEq⟩ := Submonoid.mem_map.mp hd
    have hx := mem_basicOpen_of_denominator U x r hr
    letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.obj (.op (X.basicOpen r))) := (basicRes r).hom.toAlgebra
    haveI := localization r
    have unit := IsLocalization.map_units (F.obj (.op (X.basicOpen r)))
      (⟨f r, Submonoid.mem_powers _⟩ : Submonoid.powers (f r))
    change IsUnit (basicRes r (f r)) at unit
    have restricted := unit.map (F.germ (X.basicOpen r) x.val hx).hom
    change IsUnit (F.germ U.1 x.val x.property d)
    rw [← hrEq]
    simpa [basicRes, TopCat.Presheaf.germ_res_apply] using restricted
  · intro z
    obtain ⟨W, hxW, s, hs⟩ := F.germ_exist x.val z
    obtain ⟨r, inside, hx⟩ := U.2.exists_basicOpen_le ⟨x.val, hxW⟩ x.property
    letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.obj (.op (X.basicOpen r))) := (basicRes r).hom.toAlgebra
    haveI := localization r
    let s' := F.map (homOfLE inside).op s
    have germ_s : F.germ (X.basicOpen r) x.val hx s' = z :=
      (F.germ_res_apply (homOfLE inside) x.val hx s).trans hs
    obtain ⟨⟨b, d⟩, eq⟩ := IsLocalization.surj (Submonoid.powers (f r)) s'
    obtain ⟨n, hn⟩ := d.property
    have denom : d.val ∈ M.map f :=
      Submonoid.mem_map.mpr ⟨r ^ n, M.pow_mem (denominator_of_mem_basicOpen U x r hx) n,
        (map_pow f r n).trans hn⟩
    refine ⟨⟨b, ⟨d, denom⟩⟩, ?_⟩
    change s' * basicRes r d.val = basicRes r b at eq
    simpa only [map_mul, germ_s, basicRes, TopCat.Presheaf.germ_res_apply,
      RingHom.algebraMap_toAlgebra] using congrArg (F.germ (X.basicOpen r) x.val hx) eq
  · intro b b' eq
    change F.germ U.1 x.val x.property b = F.germ U.1 x.val x.property b' at eq
    obtain ⟨W, hxW, a, a', eqW⟩ := F.germ_eq x.val x.property x.property b b' eq
    obtain ⟨r, inside, hx⟩ := U.2.exists_basicOpen_le ⟨x.val, hxW⟩ x.property
    letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.obj (.op (X.basicOpen r))) := (basicRes r).hom.toAlgebra
    haveI := localization r
    have eqB : basicRes r b = basicRes r b' := by
      have same : a = a' := Subsingleton.elim _ _
      subst a'
      simpa only [basicRes, ← CommRingCat.comp_apply, ← Functor.map_comp] using
        congrArg (F.map (homOfLE inside).op) eqW
    obtain ⟨d, equal⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f r))
      (F.obj (.op (X.basicOpen r)))).mp eqB
    obtain ⟨n, hn⟩ := d.property
    exact ⟨⟨d, Submonoid.mem_map.mpr ⟨r ^ n,
      M.pow_mem (denominator_of_mem_basicOpen U x r hx) n, (map_pow f r n).trans hn⟩⟩, equal⟩

/-- The germ square of an affine direct-image algebra is a pushout of rings. -/
theorem affinePushforwardStalk_isPushout :
    let F := affineDirectImage h
    IsPushout (h.app U.1) (X.presheaf.germ U.1 x.val x.property)
      (F.germ U.1 x.val x.property)
      ((TopCat.Presheaf.stalkFunctor CommRingCat x.val).map (directImageStructure h).hom.val) := by
  let F := affineDirectImage h
  letI : Algebra Γ(Z, h ⁻¹ᵁ U.1) (F.stalk x.val) :=
    (F.germ U.1 x.val x.property).hom.toAlgebra
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x.val) :=
    (X.presheaf.germ U.1 x.val x.property).hom.toAlgebra
  haveI := affinePushforwardStalk_isLocalization h U x
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x.val) (U.2.primeIdealOf x).asIdeal :=
    U.2.isLocalization_stalk x
  let stalkMap : X.presheaf.stalk x.val ⟶ F.stalk x.val :=
    (TopCat.Presheaf.stalkFunctor CommRingCat x.val).map (directImageStructure h).hom.val
  have commute : stalkMap.hom.comp (X.presheaf.germ U.1 x.val x.property).hom =
      (F.germ U.1 x.val x.property).hom.comp (h.app U.1).hom := by
    have commute : X.presheaf.germ U.1 x.val x.property ≫ stalkMap =
        h.app U.1 ≫ F.germ U.1 x.val x.property :=
      TopCat.Presheaf.stalkFunctor_map_germ U.1 x.val x.property (directImageStructure h).hom.val
    simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom commute
  exact CommRingCat.isPushout_of_isLocalization (h.app U.1).hom stalkMap.hom commute
    (U.2.primeIdealOf x).asIdeal.primeCompl

section Pullback

variable {Y W : Scheme.{u}} {f : Y ⟶ X} {left : W ⟶ Z} {down : W ⟶ Y}
  (square : IsPullback left down h f)

include square in
omit [IsAffineHom h] in
private theorem pullbackPreimage_le {U : X.Opens} {V : Y.Opens} (inside : V ≤ f ⁻¹ᵁ U) :
    down ⁻¹ᵁ V ≤ left ⁻¹ᵁ (h ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, square.w, Scheme.Hom.comp_preimage]
  exact down.preimage_mono inside

/-- A chart in the pullback of an affine morphism gives a pushout with both canonical functions maps. -/
theorem affinePullbackSections_isPushout (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ f ⁻¹ᵁ U.1) :
    IsPushout (h.app U.1) (f.appLE U.1 V.1 inside)
      (left.appLE (h ⁻¹ᵁ U.1) (down ⁻¹ᵁ V.1) (pullbackPreimage_le h square inside))
      (down.app V.1) := by
  let PU := h ⁻¹ᵁ U.1
  let PV := down ⁻¹ᵁ V.1
  let lowerLeft := pullbackPreimage_le h square inside
  haveI : IsAffineHom down := MorphismProperty.of_isPullback square inferInstance
  haveI : IsAffine U.1.toScheme := U.2
  haveI : IsAffine V.1.toScheme := V.2
  haveI : IsAffine PU.toScheme := U.2.preimage h
  haveI : IsAffine PV.toScheme := V.2.preimage down
  have pullback : IsPullback (left.resLE PU PV lowerLeft) (down.resLE V.1 PV le_rfl)
      (h.resLE U.1 PU le_rfl) (f.resLE U.1 V.1 inside) :=
    Scheme.Hom.isPullback_resLE square inside le_rfl (inf_eq_right.mpr lowerLeft).symm
  letI (i : WalkingCospan) : IsAffine ((cospan (h.resLE U.1 PU le_rfl) (f.resLE U.1 V.1 inside)).obj i) := by
    cases i with
    | none => exact U.2
    | some j =>
      cases j with
      | left => exact U.2.preimage h
      | right => exact V.2
  have rings := (pullback.map Scheme.Γ.rightOp).unop.flip
  have ringSquare : IsPushout (h.resLE U.1 PU le_rfl).appTop (f.resLE U.1 V.1 inside).appTop
      (left.resLE PU PV lowerLeft).appTop (down.resLE V.1 PV le_rfl).appTop := rings
  rw [h.app_eq_appLE (U := U.1), down.app_eq_appLE (U := V.1)]
  exact ringSquare.of_iso U.1.topIso PU.topIso V.1.topIso PV.topIso
    (arrowResLEAppIso h U.1 PU le_rfl).hom.w.symm
    (arrowResLEAppIso f U.1 V.1 inside).hom.w.symm
    (arrowResLEAppIso left PU PV lowerLeft).hom.w.symm
    (arrowResLEAppIso down V.1 PV le_rfl).hom.w.symm

end Pullback

end

end SHIGURE.SchemeDescent
