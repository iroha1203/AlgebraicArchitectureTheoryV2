import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Image exactness for affine module sheaves

This file supplies the localization-exactness infrastructure needed to compare
the generated allowed-operation image sheaf with the module sheaf associated
to its sections on a selected affine chart.

Open restriction and `tilde` are left adjoints, so they preserve the canonical
epimorphism onto an abelian image. Their preservation of the corresponding
monomorphism is established directly: restriction reuses injective presheaf
components, while `tilde` localizes an injective module map at every prime.
The image comparisons are then the canonical isomorphisms determined by these
strong-epi/mono factorizations.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent
namespace AffineImageExactness

universe u

/-- The map on localized modules induced by an injective linear map is
injective. This is the pointwise input for `tildeMap_mono`. -/
private theorem localizationsComapFun_injective
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (x : PrimeSpectrum.Top R) :
    Function.Injective
      (AlgebraicGeometry.StructureSheaf.Localizations.comapFun f x) := by
  change Function.Injective
    (IsLocalizedModule.map x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N) f)
  exact IsLocalizedModule.map_injective _ _ _ f hf

/-- Restriction along an open immersion preserves monomorphisms of module
sheaves. The restricted component is the original injective component on the
image open, with scalars restricted along the canonical ring isomorphism. -/
theorem restrictMap_mono
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (f : M ⟶ N) [Mono f] :
    Mono ((Scheme.Modules.restrictFunctor j).map f) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget Y.ringCatSheaf).map f)
    (Opposite.op (j.opensFunctor.obj U.unop))

/-- The affine `tilde` functor preserves monomorphisms. Injectivity is checked
on locally fractional sections, point by point, using localization of the
underlying injective module map. -/
theorem tildeMap_mono
    {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] :
    Mono (AlgebraicGeometry.tilde.map f) := by
  apply (SheafOfModules.forget (AlgebraicGeometry.Spec R).ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  change Function.Injective ((AlgebraicGeometry.tilde.map f).val.app U)
  dsimp [AlgebraicGeometry.tilde.map,
    AlgebraicGeometry.SpecModulesToSheafFullyFaithful]
  have hcentral : Function.Injective
      (AlgebraicGeometry.StructureSheaf.comapₗ f.hom U.unop U.unop .rfl) :=
    fun s t h ↦ Subtype.ext <| funext fun x ↦
      localizationsComapFun_injective f.hom
        ((ModuleCat.mono_iff_injective _).mp inferInstance) x
        (congrFun (congrArg Subtype.val h) x)
  exact ((ModuleCat.mono_iff_injective _).mp
      (show Mono ((AlgebraicGeometry.tilde.modulesSpecToSheafIso N).inv.app U) from
        inferInstance)).comp
    (hcentral.comp
      ((ModuleCat.mono_iff_injective _).mp
        (show Mono ((AlgebraicGeometry.tilde.modulesSpecToSheafIso M).hom.app U) from
          inferInstance)))

/-- Open restriction carries the canonical abelian image to the abelian image
of the restricted morphism. The isomorphism is characterized by the mapped
canonical epimorphism and monomorphism. -/
noncomputable def restrictAbelianImageIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (f : M ⟶ N) :
    (Abelian.image f).restrict j ≅
      Abelian.image ((Scheme.Modules.restrictFunctor j).map f) := by
  let F := Scheme.Modules.restrictFunctor j
  let e := F.map (Abelian.factorThruImage f)
  let m := F.map (Abelian.image.ι f)
  have comm : e ≫ m = F.map f := by
    dsimp [e, m]
    rw [← F.map_comp, Abelian.image.fac]
  letI : Epi e := preserves_epi_of_preservesColimit F _
  letI : StrongEpi e := strongEpi_of_epi e
  letI : Mono m := restrictMap_mono j (Abelian.image.ι f)
  exact Limits.image.isoStrongEpiMono e m comm ≪≫
    (Abelian.imageIsoImage (F.map f)).symm

/-- `tilde` carries a module-category abelian image to the abelian image of
the induced morphism of module sheaves. The comparison uses the canonical
strong-epi/mono factorization and no supplied exactness certificate. -/
noncomputable def tildeAbelianImageIso
    {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) :
    AlgebraicGeometry.tilde (Abelian.image f) ≅
      Abelian.image (AlgebraicGeometry.tilde.map f) := by
  let F := AlgebraicGeometry.tilde.functor R
  let e := F.map (Abelian.factorThruImage f)
  let m := F.map (Abelian.image.ι f)
  have comm : e ≫ m = F.map f := by
    dsimp [e, m]
    rw [← F.map_comp, Abelian.image.fac]
  letI : Epi e := preserves_epi_of_preservesColimit F _
  letI : StrongEpi e := strongEpi_of_epi e
  letI : Mono m := tildeMap_mono (Abelian.image.ι f)
  exact Limits.image.isoStrongEpiMono e m comm ≪≫
    (Abelian.imageIsoImage (F.map f)).symm

end AffineImageExactness
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface
