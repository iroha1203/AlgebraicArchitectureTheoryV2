import Formal.SHIGURE.Part2.Schemes.ModuleTensor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.BaseChange

/-! # Affine comparison for tensor products of scheme modules

The tensor sheaf of the associated sheaves of two coefficient modules is
canonically the associated sheaf of their tensor product (Appendix B.3).

## Implementation notes

The comparison is constructed on distinguished opens using localization of
tensor products, extended into the target sheaf using the basis universal
property, and then factored through module sheafification. Thus the comparison
uses the actual sectionwise tensor product, rather than global sections.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct
noncomputable section

universe u

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) (r : R)

/-- The existing associated-sheaf sections on a distinguished open. -/
private abbrev localSections (R : CommRingCat.{u}) (M : ModuleCat R) (r : R) :=
  (structureSheafInType R M).val.obj (.op (PrimeSpectrum.basicOpen r))

/-- Localization identifies the tensor of the two localized modules with
the localization of their tensor. -/
private def localizedTensorIso :
    (localSections R M r ⊗[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R N r) ≃ₗ[R]
      localSections R (ModuleCat.of R (M ⊗[R] N)) r :=
  ((IsLocalization.moduleTensorEquiv (.powers r) ((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))
    (localSections R M r) (localSections R N r)).restrictScalars R).trans
    (IsLocalizedModule.linearEquiv (.powers r)
      (TensorProduct.map (StructureSheaf.toOpenₗ R M _) (StructureSheaf.toOpenₗ R N _))
      (StructureSheaf.toOpenₗ R (M ⊗[R] N) _))

/-- The localization comparison is linear over the actual local section ring. -/
private def localizedTensorIso' :
    (localSections R M r ⊗[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R N r) ≃ₗ[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))]
      localSections R (ModuleCat.of R (M ⊗[R] N)) r :=
  (localizedTensorIso R M N r).extendScalarsOfIsLocalization (.powers r) _

/-- The local comparison preserves pure tensors of coefficient elements. -/
@[simp] private theorem localizedTensorIso_apply_toOpen (m : M) (n : N) :
    localizedTensorIso' R M N r
      (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N) _ (m ⊗ₜ[R] n) := by
  change (IsLocalizedModule.linearEquiv (.powers r)
    (TensorProduct.map (StructureSheaf.toOpenₗ R M _) (StructureSheaf.toOpenₗ R N _))
    (StructureSheaf.toOpenₗ R (M ⊗[R] N) _))
      ((StructureSheaf.toOpenₗ R M _) m ⊗ₜ[R] (StructureSheaf.toOpenₗ R N _) n) = _
  exact IsLocalizedModule.linearEquiv_apply _ _ _ (m ⊗ₜ[R] n)

/-- The local comparison on the actual additive presheaf objects. -/
private def basicTensorAddIso :
    (tensorPresheaf (tilde M) (tilde N)).presheaf.obj (.op (PrimeSpectrum.basicOpen r)) ≅
      (tilde (ModuleCat.of R (M ⊗[R] N))).presheaf.obj (.op (PrimeSpectrum.basicOpen r)) :=
  (localizedTensorIso' R M N r).toAddEquiv.toAddCommGrpIso

/-- The tensor restriction map is linear over the coefficient ring. -/
private def tensorRes {U V : (Spec R).Opens} (i : V ⟶ U) :
    ((structureSheafInType R M).val.obj (.op U) ⊗[((structureSheafInType R R).val.obj (.op U))]
      (structureSheafInType R N).val.obj (.op U)) →ₗ[R]
    ((structureSheafInType R M).val.obj (.op V) ⊗[((structureSheafInType R R).val.obj (.op V))]
      (structureSheafInType R N).val.obj (.op V)) where
  toFun := ((tensorPresheaf (tilde M) (tilde N)).map i.op)
  map_add' := map_add _
  map_smul' a x := by
    rw [← IsScalarTower.algebraMap_smul ((structureSheafInType R R).val.obj (.op U)) a x]
    change (tensorPresheaf (tilde M) (tilde N)).map i.op ((algebraMap R ((structureSheafInType R R).val.obj (.op U))) a • x) = _
    rw [PresheafOfModules.map_smul]
    change (algebraMap R ((structureSheafInType R R).val.obj (.op V))) a • _ = _
    let y : ((structureSheafInType R M).val.obj (.op V) ⊗[((structureSheafInType R R).val.obj (.op V))] (structureSheafInType R N).val.obj (.op V)) := (tensorPresheaf (tilde M) (tilde N)).map i.op x
    exact IsScalarTower.algebraMap_smul ((structureSheafInType R R).val.obj (.op V)) a y

/-- The tensor of the localization maps, with the section-ring tensor coefficients. -/
private abbrev localTensorToOpen : (M ⊗[R] N) →ₗ[R]
    (localSections R M r ⊗[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R N r) :=
  ((IsLocalization.moduleTensorEquiv (.powers r) ((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))
    (localSections R M r) (localSections R N r)).symm.restrictScalars R).toLinearMap ∘ₗ
      TensorProduct.map (StructureSheaf.toOpenₗ R M _) (StructureSheaf.toOpenₗ R N _)

/-- The tensor of localization maps is a localization. -/
private instance : IsLocalizedModule (.powers r) (localTensorToOpen R M N r) :=
  IsLocalizedModule.of_linearEquiv (.powers r) _ _

/-- The canonical tensor localization map preserves pure tensors. -/
@[simp] private theorem localTensorToOpen_tmul (m : M) (n : N) :
    localTensorToOpen R M N r (m ⊗ₜ[R] n) =
      StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n := rfl

/-- A function invertible on a distinguished open acts invertibly after restriction. -/
private lemma localUnit (P : ModuleCat R) {r s : R}
    (i : PrimeSpectrum.basicOpen (R := R) s ⟶ PrimeSpectrum.basicOpen r) :
    ∀ x : Submonoid.powers r, IsUnit ((algebraMap R (Module.End R (localSections R P s))) x) := by
  intro x
  have hr : IsUnit ((algebraMap R ((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen s)))) r) := by
    exact (IsLocalization.Away.algebraMap_isUnit (S := ((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))) r).map ((structurePresheafInCommRingCat R).map i.op).hom
  obtain ⟨n, hn⟩ := x.property
  rw [← hn, map_pow]
  apply IsUnit.pow
  have h := hr.map (algebraMap _ (Module.End ((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen s))) (localSections R P s)))
  rw [Module.End.isUnit_iff] at h ⊢
  convert h using 1
  ext a
  exact (IsScalarTower.algebraMap_smul ((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen s))) r a).symm

/-- The localization comparison commutes with restrictions between distinguished opens. -/
private lemma localTensorNaturality {r s : R}
    (i : PrimeSpectrum.basicOpen (R := R) s ⟶ PrimeSpectrum.basicOpen r) :
    ((structurePresheafInModuleCat R (M ⊗[R] N)).map i.op).hom ∘ₗ
      (localizedTensorIso R M N r).toLinearMap =
    (localizedTensorIso R M N s).toLinearMap ∘ₗ tensorRes R M N i := by
  apply IsLocalizedModule.ext (.powers r) (localTensorToOpen R M N r)
    (localUnit R (ModuleCat.of R (M ⊗[R] N)) i)
  apply TensorProduct.ext'
  intro m n
  change ((structurePresheafInModuleCat R (M ⊗[R] N)).map i.op)
    (localizedTensorIso R M N r (localTensorToOpen R M N r (m ⊗ₜ[R] n))) =
      localizedTensorIso R M N s (tensorRes R M N i (localTensorToOpen R M N r (m ⊗ₜ[R] n)))
  rw [localTensorToOpen_tmul]
  rw [show localizedTensorIso R M N r
    (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N) _ (m ⊗ₜ[R] n) from
    localizedTensorIso_apply_toOpen R M N r m n]
  change StructureSheaf.toOpenₗ R (M ⊗[R] N) _ (m ⊗ₜ[R] n) =
    localizedTensorIso R M N s
      (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n)
  exact (localizedTensorIso_apply_toOpen R M N s m n).symm

/-- The local comparison extends uniquely to the underlying additive presheaves. -/
private def tensorComparisonAdd :
    (tensorPresheaf (tilde M) (tilde N)).presheaf ⟶ (tilde (ModuleCat.of R (M ⊗[R] N))).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _
    ((SheafOfModules.toSheaf _).obj (tilde (ModuleCat.of R (M ⊗[R] N))))
      PrimeSpectrum.isBasis_basic_opens
      { app (f : Rᵒᵖ) := (basicTensorAddIso R M N f.unop).hom
        naturality {f g : Rᵒᵖ} i := by
          ext x
          exact LinearMap.congr_fun (localTensorNaturality R M N
            i.1.hom).symm x }

/-- The basis extension recovers the prescribed local comparison. -/
@[simp] private theorem tensorComparisonAdd_basicOpen (r : R) :
    (tensorComparisonAdd R M N).app (.op (PrimeSpectrum.basicOpen r)) =
      (basicTensorAddIso R M N r).hom :=
  TopCat.Sheaf.extend_hom_app _ _ PrimeSpectrum.isBasis_basic_opens _ r

/-- The additive basis extension respects the structure-sheaf action. -/
private def tensorComparison :
    tensorPresheaf (tilde M) (tilde N) ⟶ (tilde (ModuleCat.of R (M ⊗[R] N))).val where
  app U := ModuleCat.ofHom (X := (tensorPresheaf (tilde M) (tilde N)).obj U) (Y := (tilde (ModuleCat.of R (M ⊗[R] N))).val.obj U) (show (tensorPresheaf (tilde M) (tilde N)).obj U →ₗ[((Spec R).ringCatSheaf.val.obj U)]
      (tilde (ModuleCat.of R (M ⊗[R] N))).val.obj U from
    { toAddHom := ((tensorComparisonAdd R M N).app U).hom.toAddHom
      map_smul' := by
        intro a m
        letI := ((tilde (ModuleCat.of R (M ⊗[R] N))).val.obj U).isModule
        apply TopCat.Presheaf.IsSheaf.section_ext (tilde (ModuleCat.of R (M ⊗[R] N))).isSheaf
        intro x hxU
        obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen r ≤ _⟩ :=
          PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
        refine ⟨_, hrU, hxr, ?_⟩
        let i := homOfLE hrU
        have h (z : (tensorPresheaf (tilde M) (tilde N)).obj U) :
            (tensorComparisonAdd R M N).app (.op (PrimeSpectrum.basicOpen r))
                ((tensorPresheaf (tilde M) (tilde N)).map i.op z) =
              (tilde (ModuleCat.of R (M ⊗[R] N))).val.map i.op
                ((tensorComparisonAdd R M N).app U z) :=
          congr($( (tensorComparisonAdd R M N).naturality i.op).hom z)
        change (tilde (ModuleCat.of R (M ⊗[R] N))).val.map i.op
          ((tensorComparisonAdd R M N).app U (a • m)) = _
        change _ = (tilde (ModuleCat.of R (M ⊗[R] N))).val.map i.op
          (@SMul.smul ((Spec R).ringCatSheaf.val.obj U) ((tilde (ModuleCat.of R (M ⊗[R] N))).val.obj U) (by infer_instance) a ((tensorComparisonAdd R M N).app U m))
        rw [← h, (tensorPresheaf (tilde M) (tilde N)).map_smul i.op]
        erw [(tilde (ModuleCat.of R (M ⊗[R] N))).val.map_smul i.op a ((tensorComparisonAdd R M N).app U m)]
        rw [← h]
        rw [tensorComparisonAdd_basicOpen]
        exact (localizedTensorIso' R M N r).map_smul _ _ })
  naturality i := by
    ext x
    exact congr($( (tensorComparisonAdd R M N).naturality i).hom x)

/-- The comparison is locally injective since its basis components are isomorphisms. -/
private instance tensorComparisonAdd_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R)) (tensorComparisonAdd R M N) where
  equalizerSieve_mem {U} x y h := by
    intro p hp
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hrU : PrimeSpectrum.basicOpen r ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.unop.2
    refine ⟨_, homOfLE hrU, ?_, hpr⟩
    change (tensorPresheaf (tilde M) (tilde N)).presheaf.map (homOfLE hrU).op x =
      (tensorPresheaf (tilde M) (tilde N)).presheaf.map (homOfLE hrU).op y
    apply (localizedTensorIso' R M N r).toAddEquiv.injective
    change (basicTensorAddIso R M N r).hom ((tensorPresheaf (tilde M) (tilde N)).presheaf.map (homOfLE hrU).op x) =
      (basicTensorAddIso R M N r).hom ((tensorPresheaf (tilde M) (tilde N)).presheaf.map (homOfLE hrU).op y)
    rw [← tensorComparisonAdd_basicOpen]
    exact ((tensorComparisonAdd R M N).naturality_apply (homOfLE hrU).op x).trans
      ((congrArg ((tilde (ModuleCat.of R (M ⊗[R] N))).presheaf.map (homOfLE hrU).op) h).trans
        ((tensorComparisonAdd R M N).naturality_apply (homOfLE hrU).op y).symm)

/-- The comparison is locally surjective since its basis components are isomorphisms. -/
private instance tensorComparisonAdd_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R)) (tensorComparisonAdd R M N) where
  imageSieve_mem {U} x := by
    intro p hp
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hrU : PrimeSpectrum.basicOpen r ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.2
    refine ⟨_, homOfLE hrU, ?_, hpr⟩
    refine ⟨(basicTensorAddIso R M N r).inv
      ((tilde (ModuleCat.of R (M ⊗[R] N))).presheaf.map (homOfLE hrU).op x), ?_⟩
    rw [tensorComparisonAdd_basicOpen]
    exact (localizedTensorIso' R M N r).toAddEquiv.apply_symm_apply _

/-- The canonical B.3 tensor comparison on an affine scheme, obtained from
localization and module sheafification. The coefficient ring is its only input. -/
def tildeTensorMap :
    tensorModule (tilde M) (tilde N) ⟶
      tilde (ModuleCat.of R (M ⊗[R] N)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (Spec R).ringCatSheaf.val)).symm
    (tensorComparison R M N)

/-- The canonical affine tensor comparison is an isomorphism, because it
is locally the localization tensor isomorphism. -/
instance tildeTensorMap_isIso : IsIso (tildeTensorMap R M N) := by
  suffices h : IsIso ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map (tildeTensorMap R M N)) by
    letI := h
    exact (inferInstance : (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).ReflectsIsomorphisms).reflects (tildeTensorMap R M N)
  dsimp only [tildeTensorMap]
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
    Adjunction.homEquiv_counit]
  have h := (Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective (tensorComparisonAdd R M N)
  haveI : IsIso ((presheafToSheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).map
      (tensorComparisonAdd R M N)) :=
    ((Opens.grothendieckTopology (Spec R)).W_iff _).mp h
  change IsIso (((presheafToSheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).map
      (tensorComparisonAdd R M N)) ≫ _)
  infer_instance

/-- The associated-sheaf map commutes with the localization maps. -/
private lemma toOpen_tilde_map {M M' : ModuleCat R} (f : M ⟶ M') (r : R) (m : M) :
    (tilde.map f).val.app (.op (PrimeSpectrum.basicOpen r)) (StructureSheaf.toOpenₗ R M _ m) =
      StructureSheaf.toOpenₗ R M' _ (f m) := by
  exact congr($(tilde.toOpen_map_app f (PrimeSpectrum.basicOpen r)).hom m)

/-- The associated-sheaf map on local sections is coefficient-ring linear. -/
private def localCoefficientMap {M M' : ModuleCat R} (f : M ⟶ M') (r : R) :
    localSections R M r →ₗ[R] localSections R M' r :=
  (show localSections R M r →ₗ[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R M' r from
    ((tilde.map f).val.app (.op (PrimeSpectrum.basicOpen r))).hom).restrictScalars R

/-- The tensor of two coefficient-module maps on a distinguished open. -/
private def localTensorCoefficientMap {M M' N N' : ModuleCat R} (f : M ⟶ M') (g : N ⟶ N') (r : R) :
    (localSections R M r ⊗[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R N r) →ₗ[R]
      (localSections R M' r ⊗[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R N' r) :=
  (TensorProduct.map
    (show localSections R M r →ₗ[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R M' r from
      ((tilde.map f).val.app (.op (PrimeSpectrum.basicOpen r))).hom)
    (show localSections R N r →ₗ[((structureSheafInType R R).val.obj (.op (PrimeSpectrum.basicOpen r)))] localSections R N' r from
      ((tilde.map g).val.app (.op (PrimeSpectrum.basicOpen r))).hom)).restrictScalars R

/-- The local comparison commutes with maps in the coefficient modules. -/
private lemma localTensorMapNaturality {M M' N N' : ModuleCat R} (f : M ⟶ M') (g : N ⟶ N') (r : R) :
    (localizedTensorIso R M' N' r).toLinearMap ∘ₗ
      localTensorCoefficientMap R f g r =
    localCoefficientMap R (ModuleCat.ofHom (TensorProduct.map f.hom g.hom)) r ∘ₗ
      (localizedTensorIso R M N r).toLinearMap := by
  apply IsLocalizedModule.ext (.powers r) (localTensorToOpen R M N r)
    (IsLocalizedModule.map_units (StructureSheaf.toOpenₗ R (M' ⊗[R] N') _))
  apply TensorProduct.ext'
  intro m n
  change localizedTensorIso R M' N' r
    (TensorProduct.map ((tilde.map f).val.app (.op (PrimeSpectrum.basicOpen r))).hom
      ((tilde.map g).val.app (.op (PrimeSpectrum.basicOpen r))).hom
        (localTensorToOpen R M N r (m ⊗ₜ[R] n))) =
    (tilde.map (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))).val.app
      (.op (PrimeSpectrum.basicOpen r))
      (localizedTensorIso R M N r (localTensorToOpen R M N r (m ⊗ₜ[R] n)))
  rw [localTensorToOpen_tmul, TensorProduct.map_tmul]
  erw [toOpen_tilde_map, toOpen_tilde_map]
  erw [localizedTensorIso_apply_toOpen, localizedTensorIso_apply_toOpen, toOpen_tilde_map]
  rfl

/-- The presheaf comparison is natural in both coefficient modules. -/
private lemma tensorComparison_naturality {M M' N N' : ModuleCat R} (f : M ⟶ M') (g : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom (R := (Spec R).presheaf) (tilde.map f).val (tilde.map g).val ≫
        tensorComparison R M' N' =
      tensorComparison R M N ≫
        (tilde.map (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))).val := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply TopCat.Sheaf.hom_ext _
    ((SheafOfModules.toSheaf _).obj (tilde (ModuleCat.of R (M' ⊗[R] N'))))
    PrimeSpectrum.isBasis_basic_opens
  intro r
  ext x
  change (tensorComparisonAdd R M' N').app (.op (PrimeSpectrum.basicOpen r))
      ((PresheafOfModules.Monoidal.tensorHom (R := (Spec R).presheaf)
        (tilde.map f).val (tilde.map g).val).app (.op (PrimeSpectrum.basicOpen r)) x) =
    (tilde.map (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))).val.app (.op (PrimeSpectrum.basicOpen r))
      ((tensorComparisonAdd R M N).app (.op (PrimeSpectrum.basicOpen r)) x)
  rw [tensorComparisonAdd_basicOpen, tensorComparisonAdd_basicOpen]
  exact LinearMap.congr_fun (localTensorMapNaturality R f g r) x

/-- The canonical sheaf map factors the constructed presheaf comparison. -/
private lemma tildeTensorMap_homEquiv :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (Spec R).ringCatSheaf.val)) (tildeTensorMap R M N) =
      tensorComparison R M N := by
  exact Equiv.apply_symm_apply _ _

/-- The affine tensor comparison sends the canonical local pure tensors to
those of the coefficient tensor; this fixes its choice for later coherence. -/
theorem tildeTensorMap_toOpen (m : M) (n : N) (r : R) :
    (tildeTensorMap R M N).val.app (.op (PrimeSpectrum.basicOpen r))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).unit.app
        (tensorPresheaf (tilde M) (tilde N))).app (.op (PrimeSpectrum.basicOpen r))
        (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n)) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N) _ (m ⊗ₜ[R] n) := by
  have h := congrArg
    (fun k => (k.app (.op (PrimeSpectrum.basicOpen r)))
      (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n))
    (tildeTensorMap_homEquiv R M N)
  change (tildeTensorMap R M N).val.app (.op (PrimeSpectrum.basicOpen r))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).unit.app
        (tensorPresheaf (tilde M) (tilde N))).app (.op (PrimeSpectrum.basicOpen r))
        (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n)) =
      (tensorComparison R M N).app (.op (PrimeSpectrum.basicOpen r))
        (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n) at h
  rw [h]
  change (tensorComparisonAdd R M N).app (.op (PrimeSpectrum.basicOpen r))
      (StructureSheaf.toOpenₗ R M _ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N _ n) = _
  rw [tensorComparisonAdd_basicOpen]
  exact localizedTensorIso_apply_toOpen R M N r m n

/-- Naturality of the canonical affine tensor comparison in both coefficient
modules, inherited from the localization maps and module sheafification. -/
theorem tildeTensorMap_naturality {M M' N N' : ModuleCat R} (f : M ⟶ M') (g : N ⟶ N') :
    tensorModuleMap (tilde.map f) (tilde.map g) ≫ tildeTensorMap R M' N' =
      tildeTensorMap R M N ≫ tilde.map (ModuleCat.ofHom (TensorProduct.map f.hom g.hom)) := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).homEquiv
    (tensorPresheaf (tilde M) (tilde N)) (tilde (ModuleCat.of R (M' ⊗[R] N')))).injective
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).homEquiv _ _)
    ((PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.val)).map
      (PresheafOfModules.Monoidal.tensorHom (R := (Spec R).presheaf) (tilde.map f).val (tilde.map g).val) ≫
        tildeTensorMap R M' N') = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  erw [tildeTensorMap_homEquiv R M' N', tildeTensorMap_homEquiv R M N]
  exact tensorComparison_naturality R f g

/-- On an affine scheme the actual tensor sheaf agrees naturally with the
associated sheaf of the coefficient tensor product, as required by B.3. -/
@[simps! hom_app]
def tildeTensorIso (R : CommRingCat.{u}) :
    (tilde.functor R).prod (tilde.functor R) ⋙ moduleTensorFunctor (Spec R) ≅
      MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ tilde.functor R :=
  NatIso.ofComponents (fun MN => asIso (tildeTensorMap R MN.1 MN.2))
    (fun fg => tildeTensorMap_naturality R fg.1 fg.2)

end

end SHIGURE.SchemeDescent
