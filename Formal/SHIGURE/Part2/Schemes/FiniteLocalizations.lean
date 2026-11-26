import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.FinCategory.Basic

/-! # Localization of finite limit diagrams of modules

If the components of a natural transformation are localizations at one
submonoid, the induced map on its finite limits is also that localization.
This applies to a sheaf's finite cover and pairwise intersection diagram.

## Implementation notes

We use the existing exact localization functor and restrict scalars
back to the coefficient ring. This transports finite limits while
keeping every comparison linear over the original ring. A direct
fraction proof would repeat the common-denominator argument in each
diagram shape.
-/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)

private abbrev localizedOverR : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ModuleCat.localizedModule_functor S ⋙ ModuleCat.restrictScalars (algebraMap R (Localization S))

private def localizedScalarsIso (M : ModuleCat.{u} R) :
    ModuleCat.of R (M.localizedModule S) ≅ (localizedOverR S).obj M :=
  LinearEquiv.toModuleIso (X₁ := ModuleCat.of R (M.localizedModule S))
    (X₂ := (localizedOverR S).obj M)
    { AddEquiv.refl _ with
      map_smul' := fun r x => (IsScalarTower.algebraMap_smul (Localization S) r x).symm }

private def localizationUnit : 𝟭 (ModuleCat.{u} R) ⟶ localizedOverR S where
  app M := ModuleCat.ofHom (M.localizedModuleMkLinearMap S) ≫ (localizedScalarsIso S M).hom
  naturality {M N} f := by
    ext x
    change N.localizedModuleMkLinearMap S (f x) =
      IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
        (N.localizedModuleMkLinearMap S) (Localization S) f.hom (M.localizedModuleMkLinearMap S x)
    simp [IsLocalizedModule.mapExtendScalars, IsLocalizedModule.map_apply]

private instance localizationUnit_localizes (M : ModuleCat.{u} R) :
    IsLocalizedModule S ((localizationUnit S).app M).hom :=
  IsLocalizedModule.of_linearEquiv S (M.localizedModuleMkLinearMap S) (localizedScalarsIso S M).toLinearEquiv

variable {J : Type u} [SmallCategory J] [FinCategory J] {F G : J ⥤ ModuleCat.{u} R}

/-- A comparison between finite diagrams that locally inverts one submonoid
localizes their limit at the same submonoid.
This proves the localization step for compatible sections in Appendix B.3. The finite diagram is
supplied by the principal-open refinement. -/
theorem isLocalizedModule_limitMap (a : F ⟶ G)
    (h : ∀ j, IsLocalizedModule S (a.app j).hom) :
    IsLocalizedModule S (limMap a).hom := by
  let L := localizedOverR S
  letI : (ModuleCat.restrictScalars (algebraMap R (Localization S))).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R (Localization S))).isRightAdjoint
  letI : PreservesFiniteLimits L := comp_preservesFiniteLimits _ _
  letI (j : J) : IsLocalizedModule S (a.app j).hom := h j
  let e (j : J) : L.obj (F.obj j) ≅ G.obj j :=
    (IsLocalizedModule.linearEquiv S ((localizationUnit S).app (F.obj j)).hom (a.app j).hom).toModuleIso
  have unit_eq (j : J) : (localizationUnit S).app (F.obj j) ≫ (e j).hom = a.app j := by
    ext x
    exact IsLocalizedModule.linearEquiv_apply S ((localizationUnit S).app (F.obj j)).hom (a.app j).hom x
  let d : F ⋙ L ≅ G := NatIso.ofComponents e (fun {i j} f => by
    apply ModuleCat.hom_ext
    apply IsLocalizedModule.linearMap_ext S ((localizationUnit S).app (F.obj i)).hom (a.app j).hom
    have eq : (localizationUnit S).app (F.obj i) ≫ ((F ⋙ L).map f ≫ (e j).hom) =
        (localizationUnit S).app (F.obj i) ≫ ((e i).hom ≫ G.map f) := by
      rw [Functor.comp_map, ← Category.assoc, ← (localizationUnit S).naturality (F.map f)]
      simp only [Functor.id_map, Category.assoc, unit_eq, a.naturality]
      rw [← Category.assoc, unit_eq]
    exact congrArg ModuleCat.Hom.hom eq)
  let comparison : L.obj (limit F) ≅ limit G :=
    preservesLimitIso L F ≪≫ HasLimit.isoOfNatIso d
  have equal : (localizationUnit S).app (limit F) ≫ comparison.hom = limMap a := by
    apply limit.hom_ext
    intro j
    simp only [comparison, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
      preservesLimitIso_hom_π_assoc, limMap_π]
    rw [← Category.assoc, ← (localizationUnit S).naturality (limit.π F j)]
    simp only [Functor.id_map, Category.assoc, d, NatIso.ofComponents_hom_app, unit_eq]
  rw [← equal]
  exact IsLocalizedModule.of_linearEquiv S ((localizationUnit S).app (limit F)).hom comparison.toLinearEquiv

/-- Localizing at the images of a submonoid continues to localize at the
original submonoid after restricting scalars.
This is the scalar comparison used for principal opens in Appendix B.3. The two scalar towers
and localization at the image monoid are supplied by the local presentations. -/
theorem isLocalizedModule_restrictScalars_of_map {A M N : Type u} [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] (f : M →ₗ[A] N)
    [h : IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f] :
    IsLocalizedModule S (f.restrictScalars R) where
  map_units s := by
    let t : Algebra.algebraMapSubmonoid A S := ⟨algebraMap R A s, ⟨s, s.property, rfl⟩⟩
    have unit := h.map_units t
    rw [Module.End.isUnit_iff] at unit ⊢
    change Function.Bijective (fun x : N => (algebraMap R A (s : R)) • x) at unit
    change Function.Bijective (fun x : N => (s : R) • x)
    have same := funext (fun x : N => IsScalarTower.algebraMap_smul A (s : R) x)
    rw [← same]
    exact unit
  surj y := by
    obtain ⟨⟨x, t⟩, equal⟩ := h.surj y
    obtain ⟨s, hs, hs'⟩ := t.property
    refine ⟨⟨x, ⟨s, hs⟩⟩, ?_⟩
    change (s : R) • y = f x
    change (t : A) • y = f x at equal
    rw [← IsScalarTower.algebraMap_smul A, hs']
    exact equal
  exists_of_eq {x y} equal := by
    obtain ⟨t, ht⟩ := h.exists_of_eq equal
    obtain ⟨s, hs, hs'⟩ := t.property
    refine ⟨⟨s, hs⟩, ?_⟩
    change (t : A) • x = (t : A) • y at ht
    change s • x = s • y
    rw [← IsScalarTower.algebraMap_smul A s x, ← IsScalarTower.algebraMap_smul A s y, hs']
    exact ht

end

end SHIGURE.SchemeDescent
