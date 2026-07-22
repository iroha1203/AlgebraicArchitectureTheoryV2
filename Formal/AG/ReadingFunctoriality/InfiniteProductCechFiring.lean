import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.FiniteExamples
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Infinite-product Čech incompatibility firing

This module realizes the R9i negative firing for canonical coefficient base
change.  A countably duplicated cover makes degree-zero Čech cochains an
infinite product.  For `ℤ → ℚ`, the canonical map from the scalar extension
of that product to the product of scalar extensions is not surjective.

## Implementation notes

The coefficient is a constant large `ℤ`-module sheaf.  Its carrier is
universe-lifted because `LinearCoefficientSheaf` deliberately uses
`ModuleCat.{1}`.  The cover alternates the two actual charts of `coarseCover`
by parity, so it remains admissible while retaining `Nat` as its index type.

Non-surjectivity is detected by the family whose `n`th component is
`1 / (n + 1)`.  Tensor induction proves that every element in the image has a
single common denominator, while this family does not.  This direct
degree-zero calculation was chosen instead of a finite subcover or an
abstract failure certificate, because either alternative would lose the
required infinite-product phenomenon.
-/

noncomputable section

namespace AAT.AG.ReadingFunctorialityFinite

open CategoryTheory Opposite
open scoped TensorProduct

/-- The canonical flat coefficient change from integers to rationals. -/
noncomputable def intRationalFlatChange :
    FlatCoefficientChange Int Rat where
  hom := algebraMap Int Rat
  flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance

/-- The selected coefficient homomorphism is the canonical integer cast. -/
@[simp] theorem intRationalFlatChange_hom :
    intRationalFlatChange.hom = algebraMap Int Rat :=
  rfl

private def infiniteIndexToCoarse (n : Nat) : coarseCover.Index :=
  if Even n then FiniteModel.TwoPatchCoverIndex.left
  else FiniteModel.TwoPatchCoverIndex.right

private lemma infiniteIndexToCoarse_zero :
    infiniteIndexToCoarse 0 = FiniteModel.TwoPatchCoverIndex.left := by
  simp [infiniteIndexToCoarse]

private lemma infiniteIndexToCoarse_one :
    infiniteIndexToCoarse 1 = FiniteModel.TwoPatchCoverIndex.right := by
  simp [infiniteIndexToCoarse, Nat.not_even_one]

/-- The countably indexed cover alternating duplicated left and right charts. -/
noncomputable def infiniteDuplicatedCover :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase where
  Index := Nat
  patch n := coarseCover.patch (infiniteIndexToCoarse n)
  inclusion n := coarseCover.inclusion (infiniteIndexToCoarse n)
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases hreq with rfl | rfl
      · refine ⟨0, ?_⟩
        simp [infiniteIndexToCoarse_zero,
          coarseCover, finiteSite, FiniteModel.twoPatchSite,
          FiniteModel.twoPatchSelectedGeometryReading,
          FiniteModel.twoPatchCoverPatch,
          FiniteModel.twoPatchCoverContextIndex,
          FiniteModel.twoPatchCoverageRequirements,
          FiniteModel.twoPatchSupportVisibleOn]
      · refine ⟨1, ?_⟩
        simp [infiniteIndexToCoarse_one,
          coarseCover, finiteSite, FiniteModel.twoPatchSite,
          FiniteModel.twoPatchSelectedGeometryReading,
          FiniteModel.twoPatchCoverPatch,
          FiniteModel.twoPatchCoverContextIndex,
          FiniteModel.twoPatchCoverageRequirements,
          FiniteModel.twoPatchSupportVisibleOn]
    equationCoordinateCoverage := by
      intro _coordinate _hreq
      exact Or.inl ⟨0, trivial⟩
    violationWitnessCoverage := by
      intro _witness _hreq
      exact Or.inl ⟨0, trivial⟩
    signatureAxisCoverage := by
      intro _axis _hreq
      refine ⟨0, ?_⟩
      simp [infiniteIndexToCoarse_zero,
        coarseCover, finiteSite, FiniteModel.twoPatchSite,
        FiniteModel.twoPatchSelectedGeometryReading,
        FiniteModel.twoPatchCoverPatch,
        FiniteModel.twoPatchCoverContextIndex,
        FiniteModel.twoPatchCoverageRequirements]
    boundaryCoverage := by
      intro i j
      exact coarseCover.admissible.boundaryCoverage
        (infiniteIndexToCoarse i) (infiniteIndexToCoarse j)
    nonGeneration := by
      intro i support atom hselected
      exact coarseCover.admissible.nonGeneration
        (infiniteIndexToCoarse i) hselected
  }

/-- Identification of the actual cover index with `Nat`. -/
noncomputable def infiniteDuplicatedCoverIndexEquiv :
    infiniteDuplicatedCover.Index ≃ Nat :=
  Equiv.refl Nat

private noncomputable def infiniteProductConstantModulePresheaf :
    finiteSite.categoryᵒᵖ ⥤ ModuleCat.{1} Int where
  obj _ := ModuleCat.of Int (ULift.{1} Int)
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := by simp

private def infiniteProductObject
    (X Y : finiteSite.category) : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def infiniteProductLeft
    (X Y : finiteSite.category) : infiniteProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def infiniteProductRight
    (X Y : finiteSite.category) : infiniteProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem finiteSitePresheaf_isSheaf_of_bijective
    (P : finiteSite.categoryᵒᵖ ⥤ Type 1)
    (hbij : ∀ {X Y : finiteSite.category} (f : X ⟶ Y),
      Function.Bijective (P.map f.op)) :
    Presieve.IsSheaf finiteSite.topology P := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  let patchObject := Site.ContextCategoryObject.of finiteSite.contextPreorder
    (F.patch i)
  let Q := infiniteProductObject Y patchObject
  let q : Q ⟶ Y := infiniteProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := infiniteProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  rcases (hbij q).2 (family q hq) with ⟨global, hglobal⟩
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    let PQ := infiniteProductObject Z Q
    let pz : PQ ⟶ Z := infiniteProductLeft Z Q
    let pq : PQ ⟶ Q := infiniteProductRight Z Q
    apply (hbij pz).1
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    calc
      P.map pz.op (P.map g.op global) =
          P.map pq.op (P.map q.op global) := by
            rw [← FunctorToTypes.map_comp_apply,
              ← FunctorToTypes.map_comp_apply]
            congr 2
      _ = P.map pq.op (family q hq) := by rw [hglobal]
      _ = P.map pz.op (family g hg) := hcompat.symm
  · intro other hother
    apply (hbij q).1
    rw [hglobal]
    exact hother q hq

private theorem infiniteProductConstantModulePresheaf_isSheaf :
    Presheaf.IsSheaf finiteSite.topology
      (infiniteProductConstantModulePresheaf ⋙
        forget₂ (ModuleCat.{1} Int) AddCommGrpCat.{1}) := by
  apply Presheaf.isSheaf_of_isSheaf_comp
    (P := infiniteProductConstantModulePresheaf ⋙
      forget₂ (ModuleCat.{1} Int) AddCommGrpCat.{1})
    (s := forget AddCommGrpCat.{1})
  rw [isSheaf_iff_isSheaf_of_type]
  apply finiteSitePresheaf_isSheaf_of_bijective
  intro X Y f
  simpa [infiniteProductConstantModulePresheaf] using
    (Function.bijective_id :
      Function.Bijective (id : ULift.{1} Int → ULift.{1} Int))

/-- The constant integer-module coefficient sheaf used by the product firing. -/
noncomputable def infiniteProductLinearCoefficientSheaf :
    Cohomology.LinearCoefficientSheaf Int finiteSite where
  modulePresheaf := infiniteProductConstantModulePresheaf
  isSheaf := infiniteProductConstantModulePresheaf_isSheaf

private theorem infiniteProductRawRationalPresheaf_isSheaf :
    Presheaf.IsSheaf finiteSite.topology
      (infiniteProductLinearCoefficientSheaf.rawBaseChangePresheaf
          intRationalFlatChange ⋙
        forget₂ (ModuleCat.{1} Rat) AddCommGrpCat.{1}) := by
  apply Presheaf.isSheaf_of_isSheaf_comp
    (P := infiniteProductLinearCoefficientSheaf.rawBaseChangePresheaf
      intRationalFlatChange ⋙
      forget₂ (ModuleCat.{1} Rat) AddCommGrpCat.{1})
    (s := forget AddCommGrpCat.{1})
  rw [isSheaf_iff_isSheaf_of_type]
  apply finiteSitePresheaf_isSheaf_of_bijective
  intro X Y f
  change Function.Bijective
    (((ModuleCat.extendScalars intRationalFlatChange.hom).map
      (infiniteProductConstantModulePresheaf.map f.op)).hom)
  rw [← ConcreteCategory.isIso_iff_bijective]
  rw [show infiniteProductConstantModulePresheaf.map f.op = 𝟙 _ by
    rfl]
  infer_instance

private noncomputable instance infiniteProductBaseChangeSectionMap_isIso
    (W : finiteSite.category) :
    IsIso (infiniteProductLinearCoefficientSheaf.baseChangeSectionMap
      intRationalFlatChange W) := by
  exact Cohomology.LinearCoefficientSheaf.baseChangeSectionMap_isIso_of_raw_isSheaf
    infiniteProductLinearCoefficientSheaf intRationalFlatChange
      infiniteProductRawRationalPresheaf_isSheaf W

private abbrev InfiniteProductSimplexZero :=
  (Cohomology.canonicalCoverRelative infiniteDuplicatedCover).simplex 0

private noncomputable def infiniteProductPiDown :
    (InfiniteProductSimplexZero → ULift.{1} Int) →ₗ[Int]
      (InfiniteProductSimplexZero → Int) :=
  (LinearEquiv.piCongrRight fun _ : InfiniteProductSimplexZero =>
    ULift.moduleEquiv).toLinearMap

private noncomputable def infiniteProductRawMap :
    Rat ⊗[Int] (InfiniteProductSimplexZero → ULift.{1} Int) →ₗ[Rat]
      (InfiniteProductSimplexZero → Rat) :=
  (TensorProduct.piScalarRightHom Int Rat Rat InfiniteProductSimplexZero).comp
    (TensorProduct.AlgebraTensorModule.map LinearMap.id infiniteProductPiDown)

private noncomputable def infiniteProductComponentDown :
    Rat ⊗[Int] ULift.{1} Int →ₗ[Rat] Rat :=
  (TensorProduct.AlgebraTensorModule.rid Int Rat Rat).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.map LinearMap.id
      ULift.moduleEquiv.toLinearMap)

@[simp] private theorem infiniteProductComponentDown_tmul
    (q : Rat) (m : ULift.{1} Int) :
    infiniteProductComponentDown (q ⊗ₜ[Int] m) = (m.down : Rat) * q := by
  simp [infiniteProductComponentDown]

@[simp] private theorem infiniteProductRawMap_tmul
    (q : Rat) (m : InfiniteProductSimplexZero → ULift.{1} Int) :
    infiniteProductRawMap (q ⊗ₜ[Int] m) =
      fun σ => (m σ).down • q := by
  ext σ
  simp [infiniteProductRawMap, infiniteProductPiDown]

private theorem infiniteProductRawMap_apply
    (z : Rat ⊗[Int] (InfiniteProductSimplexZero → ULift.{1} Int))
    (σ : InfiniteProductSimplexZero) :
    infiniteProductRawMap z σ =
      infiniteProductComponentDown
        (((ModuleCat.extendScalars intRationalFlatChange.hom).map
          (ModuleCat.ofHom (LinearMap.proj σ))).hom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul q m =>
      rw [show infiniteProductRawMap (q ⊗ₜ[Int] m) σ =
        (m σ).down • q from congrFun (infiniteProductRawMap_tmul q m) σ]
      rw [ModuleCat.ExtendScalars.map_tmul]
      simp [zsmul_eq_mul]
  | add x y hx hy =>
      rw [infiniteProductRawMap.map_add, Pi.add_apply,
        map_add, infiniteProductComponentDown.map_add, hx, hy]

private theorem infiniteProductRawMap_has_common_denominator
    (z : Rat ⊗[Int] (InfiniteProductSimplexZero → ULift.{1} Int)) :
    ∃ d : Nat, 0 < d ∧ ∃ k : InfiniteProductSimplexZero → Int,
      ∀ σ, (d : Rat) * infiniteProductRawMap z σ = k σ := by
  induction z using TensorProduct.induction_on with
  | zero =>
      exact ⟨1, by omega, 0, by simp⟩
  | tmul q m =>
      refine ⟨q.den, q.den_pos, fun σ => q.num * (m σ).down, ?_⟩
      intro σ
      rw [show infiniteProductRawMap (q ⊗ₜ[Int] m) σ =
        (m σ).down • q from congrFun (infiniteProductRawMap_tmul q m) σ]
      rw [zsmul_eq_mul]
      have hcalc :
          (q.den : Rat) * (((m σ).down : Rat) * q) =
            ((q.num * (m σ).down : Int) : Rat) := by
        calc
          _ = ((m σ).down : Rat) * ((q.den : Rat) * q) := by ring
          _ = ((m σ).down : Rat) * (q.num : Rat) := by
            rw [Rat.den_mul_eq_num]
          _ = ((q.num * (m σ).down : Int) : Rat) := by
            norm_cast
            ring
      simpa using hcalc
  | add x y hx hy =>
      rcases hx with ⟨dx, hdx, kx, hkx⟩
      rcases hy with ⟨dy, hdy, ky, hky⟩
      refine ⟨dx * dy, Nat.mul_pos hdx hdy,
        fun σ => (dy : Int) * kx σ + (dx : Int) * ky σ, ?_⟩
      intro σ
      rw [map_add, Pi.add_apply]
      have hxσ := hkx σ
      have hyσ := hky σ
      rw [Nat.cast_mul]
      calc
        ((dx : Rat) * dy) *
            (infiniteProductRawMap x σ + infiniteProductRawMap y σ) =
          (dy : Rat) * ((dx : Rat) * infiniteProductRawMap x σ) +
            (dx : Rat) * ((dy : Rat) * infiniteProductRawMap y σ) := by ring
        _ = (dy : Rat) * (kx σ : Rat) +
            (dx : Rat) * (ky σ : Rat) := by rw [hxσ, hyσ]
        _ = (((dy : Int) * kx σ + (dx : Int) * ky σ : Int) : Rat) := by
          norm_cast

private noncomputable def unboundedDenominatorFamily
    (σ : InfiniteProductSimplexZero) : Rat :=
  1 / ((infiniteDuplicatedCoverIndexEquiv (σ 0) + 1 : Nat) : Rat)

private theorem unboundedDenominatorFamily_not_mem_range :
    unboundedDenominatorFamily ∉ LinearMap.range infiniteProductRawMap := by
  rintro ⟨z, hz⟩
  rcases infiniteProductRawMap_has_common_denominator z with
    ⟨d, hd, k, hk⟩
  let σ : InfiniteProductSimplexZero := fun _ =>
    infiniteDuplicatedCoverIndexEquiv.symm d
  have hσ := hk σ
  rw [hz] at hσ
  simp only [unboundedDenominatorFamily, σ,
    Equiv.apply_symm_apply] at hσ
  have hpos : (0 : Rat) < (d : Rat) * (1 / ((d + 1 : Nat) : Rat)) := by
    positivity
  have hlt : (d : Rat) * (1 / ((d + 1 : Nat) : Rat)) < 1 := by
    rw [one_div, ← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).2 (by exact_mod_cast Nat.lt_succ_self d)
  have hkpos : 0 < k σ := by
    exact_mod_cast hσ ▸ hpos
  have hklt : k σ < 1 := by
    exact_mod_cast hσ ▸ hlt
  omega

private noncomputable def infiniteProductTargetCochain :
    ((infiniteProductLinearCoefficientSheaf.baseChange
      intRationalFlatChange).canonicalLinearCech
        infiniteDuplicatedCover).complex.X 0 :=
  fun σ =>
    (infiniteProductLinearCoefficientSheaf.baseChangeSectionMap
      intRationalFlatChange
      ((Cohomology.canonicalCoverRelative
        infiniteDuplicatedCover).overlap 0 σ)).hom
      (unboundedDenominatorFamily σ ⊗ₜ[Int] ULift.up 1)

private theorem infiniteProductCanonicalBaseChangeCochain_not_surjective :
    ¬ Function.Surjective
      (Cohomology.LinearCoefficientSheaf.canonicalBaseChangeCochain
        infiniteProductLinearCoefficientSheaf
        intRationalFlatChange infiniteDuplicatedCover 0) := by
  intro hsurjective
  rcases hsurjective infiniteProductTargetCochain with ⟨x, hx⟩
  let z : Rat ⊗[Int] (InfiniteProductSimplexZero → ULift.{1} Int) :=
    ((infiniteProductLinearCoefficientSheaf.canonicalLinearCech
      infiniteDuplicatedCover).scalarExtensionObjIso
        intRationalFlatChange 0).hom x
  apply unboundedDenominatorFamily_not_mem_range
  refine ⟨z, ?_⟩
  funext σ
  have hcomponent := congrFun hx σ
  rw [Cohomology.LinearCoefficientSheaf.canonicalBaseChangeCochain_apply]
    at hcomponent
  change
    (infiniteProductLinearCoefficientSheaf.baseChangeSectionMap
      intRationalFlatChange
      ((Cohomology.canonicalCoverRelative
        infiniteDuplicatedCover).overlap 0 σ)).hom
      (((ModuleCat.extendScalars intRationalFlatChange.hom).map
        (ModuleCat.ofHom (LinearMap.proj σ))).hom z) =
    (infiniteProductLinearCoefficientSheaf.baseChangeSectionMap
      intRationalFlatChange
      ((Cohomology.canonicalCoverRelative
        infiniteDuplicatedCover).overlap 0 σ)).hom
      (unboundedDenominatorFamily σ ⊗ₜ[Int] ULift.up 1)
      at hcomponent
  have hinjective : Function.Injective
      (infiniteProductLinearCoefficientSheaf.baseChangeSectionMap
        intRationalFlatChange
        ((Cohomology.canonicalCoverRelative
          infiniteDuplicatedCover).overlap 0 σ)).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)).1
  have hraw := hinjective hcomponent
  rw [infiniteProductRawMap_apply, hraw]
  simp [unboundedDenominatorFamily, infiniteProductComponentDown]

/-- The degree-zero canonical coefficient map is not an isomorphism. -/
theorem infiniteProductCech_degreeZero_not_isIso :
    ¬ IsIso
      (Cohomology.LinearCoefficientSheaf.canonicalBaseChangeCochain
        infiniteProductLinearCoefficientSheaf
        intRationalFlatChange infiniteDuplicatedCover 0) := by
  intro h
  haveI := h
  apply infiniteProductCanonicalBaseChangeCochain_not_surjective
  exact ((ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)).2

/-- The infinite cover does not satisfy Čech coefficient base-change compatibility. -/
theorem infiniteProductCech_not_compatible :
    ¬ Cohomology.LinearCoefficientSheaf.CechCoefficientBaseChangeCompatible
      infiniteProductLinearCoefficientSheaf intRationalFlatChange
        infiniteDuplicatedCover := by
  intro h
  exact infiniteProductCech_degreeZero_not_isIso (h 0)

end AAT.AG.ReadingFunctorialityFinite
