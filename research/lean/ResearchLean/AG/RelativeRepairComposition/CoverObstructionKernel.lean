import ResearchLean.AG.RelativeRepairComposition.CoverCohomologyMaps
import ResearchLean.AG.RelativeRepairComposition.CoverObstruction

/-!
# Integration obstruction and the original relative H2 kernel

The connecting map is the native connecting map of the same original-K cover
short exact sequence. Its kernel is the sum of the full local H1 images, and
its range is exactly the kernel of the full original H2 restriction.
## Implementation notes

G-130 B starts the short exact sequence at the relative complex of K
itself. Native exactness determines both the connecting kernel and range.
The quotient retains the prescribed sum of local images; it is not defined
as a chosen image of the connecting morphism.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverObstructionKernel
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U V : ClosedRegion K)
/-- The first-minus-second range is exactly the sum of both full local images. -/
theorem difference_range : (CoverCohomologyMaps.differenceH1 M P U V).range =
    CoverObstruction.localImages M P U V := by
  ext x
  constructor
  · rintro ⟨⟨u,v⟩,rfl⟩
    exact (CoverObstruction.localImages M P U V).sub_mem
      (AddSubgroup.mem_sup_left ⟨u,rfl⟩) (AddSubgroup.mem_sup_right ⟨v,rfl⟩)
  · intro hx
    obtain ⟨a,⟨u,hu⟩,b,⟨v,hv⟩,hab⟩ := AddSubgroup.mem_sup.mp hx
    refine ⟨(u,-v),?_⟩
    change CoverCohomology.restrictH1 M P (ClosedRegion.inter_left U V) u -
      CoverCohomology.restrictH1 M P (ClosedRegion.inter_right U V) (-v) = x
    rw [map_neg,hu,hv,sub_neg_eq_add,hab]
/-- The native connecting map into H2 of the original presentation K. -/
noncomputable def connecting (hc : ClosedRegion.Cover U V) :
    CoverCohomology.H1 M P (ClosedRegion.inter U V) →+ RelativeComplex.H2 M P ∅ ∅ :=
  (OriginalCohomology.secondHomologyIso M P).hom.hom.comp
    (((RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)).hom.comp
      (CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv.hom)
/-- Both local H2 restrictions of the same original-K cohomology class. -/
noncomputable def restriction : RelativeComplex.H2 M P ∅ ∅ →+
    CoverCohomology.H2 M P U × CoverCohomology.H2 M P V :=
  (CoverPairCohomology.nativeSecondProductIso M P U V).hom.hom.comp
    ((HomologicalComplex.homologyMap
      (RelativeCover.originalCoverShortComplex M P U V).f 2).hom.comp
        (OriginalCohomology.secondHomologyIso M P).inv.hom)
/-- Both actual full local H1 images have zero native connecting class. -/
theorem connecting_difference (hc : ClosedRegion.Cover U V)
    (x : CoverCohomology.H1 M P U × CoverCohomology.H1 M P V) :
    connecting M P U V hc (CoverCohomologyMaps.differenceH1 M P U V x) = 0 := by
  let a := (CoverPairCohomology.nativeFirstProductIso M P U V).inv x
  have ha := CoverCohomologyMaps.native_difference_h1 M P U V a
  rw [(CoverPairCohomology.nativeFirstProductIso M P U V).inv_hom_id_apply] at ha
  rw [← ha]
  change (OriginalCohomology.secondHomologyIso M P).hom
    ((RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
      ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv
        ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).hom
          (HomologicalComplex.homologyMap (RelativeCover.differenceMap M P U V) 1 a)))) = 0
  rw [Iso.hom_inv_id_apply]
  have hz := congrArg (fun f => f a)
    ((RelativeCover.original_cover_short_exact M P U V hc).comp_δ 1 2 (by simp))
  change (RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
    (HomologicalComplex.homologyMap (RelativeCover.differenceMap M P U V) 1 a) = 0 at hz
  rw [hz,map_zero]
/-- The native connecting kernel is exactly the prescribed sum of full local H1 images. -/
theorem connecting_kernel (hc : ClosedRegion.Cover U V) :
    (connecting M P U V hc).ker = CoverObstruction.localImages M P U V := by
  rw [← difference_range M P U V]
  ext y
  constructor
  · intro hy
    have he := (RelativeCover.original_cover_short_exact M P U V hc).homology_exact₃ 1 2 (by simp)
    have hz : (RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
        ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv y) = 0 := by
      apply (AddCommGrpCat.mono_iff_injective
        (OriginalCohomology.secondHomologyIso M P).hom).mp inferInstance
      change connecting M P U V hc y = (OriginalCohomology.secondHomologyIso M P).hom 0
      rw [map_zero]
      exact hy
    obtain ⟨a,ha⟩ := (ShortComplex.ab_exact_iff _).mp he _ hz
    change HomologicalComplex.homologyMap (RelativeCover.differenceMap M P U V) 1 a =
      (CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv y at ha
    refine ⟨(CoverPairCohomology.nativeFirstProductIso M P U V).hom a,?_⟩
    rw [← CoverCohomologyMaps.native_difference_h1,ha,Iso.inv_hom_id_apply]
  · rintro ⟨x,rfl⟩
    exact connecting_difference M P U V hc x
/-- The native connecting range vanishes under both full original H2 restrictions. -/
theorem restriction_connecting (hc : ClosedRegion.Cover U V)
    (y : CoverCohomology.H1 M P (ClosedRegion.inter U V)) :
    restriction M P U V (connecting M P U V hc y) = 0 := by
  change (CoverPairCohomology.nativeSecondProductIso M P U V).hom
    (HomologicalComplex.homologyMap (RelativeCover.originalCoverShortComplex M P U V).f 2
      ((OriginalCohomology.secondHomologyIso M P).inv
        ((OriginalCohomology.secondHomologyIso M P).hom
          ((RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
            ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv y))))) = 0
  rw [Iso.hom_inv_id_apply]
  have hz := congrArg (fun f => f ((CoverCohomology.firstHomologyIso M P
    (ClosedRegion.inter U V)).inv y))
      ((RelativeCover.original_cover_short_exact M P U V hc).δ_comp 1 2 (by simp))
  change HomologicalComplex.homologyMap (RelativeCover.originalCoverShortComplex M P U V).f 2
    ((RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
      ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv y)) = 0 at hz
  rw [hz,map_zero]
/-- Every original H2 class vanishing on both regions is an integration class. -/
theorem connecting_range (hc : ClosedRegion.Cover U V) :
    (connecting M P U V hc).range = (restriction M P U V).ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact restriction_connecting M P U V hc y
  · intro hx
    have he := (RelativeCover.original_cover_short_exact M P U V hc).homology_exact₁ 1 2 (by simp)
    have hz : HomologicalComplex.homologyMap (RelativeCover.originalCoverShortComplex M P U V).f 2
        ((OriginalCohomology.secondHomologyIso M P).inv x) = 0 := by
      apply (AddCommGrpCat.mono_iff_injective
        (CoverPairCohomology.nativeSecondProductIso M P U V).hom).mp inferInstance
      change restriction M P U V x = (CoverPairCohomology.nativeSecondProductIso M P U V).hom 0
      rw [map_zero]
      exact hx
    obtain ⟨b,hb⟩ := (ShortComplex.ab_exact_iff _).mp he _ hz
    refine ⟨(CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).hom b,?_⟩
    change (OriginalCohomology.secondHomologyIso M P).hom
      ((RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
        ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv
          ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).hom b))) = x
    rw [Iso.hom_inv_id_apply,hb,Iso.inv_hom_id_apply]
/-- The prescribed integration quotient is the full original H2 restriction kernel. -/
noncomputable def omegaKernelEquiv (hc : ClosedRegion.Cover U V) :
    CoverObstruction.Omega M P U V ≃+ (restriction M P U V).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (connecting_kernel M P U V hc).symm).trans
    ((QuotientAddGroup.quotientKerEquivRange (connecting M P U V hc)).trans
      (AddEquiv.addSubgroupCongr (connecting_range M P U V hc)))
/-- The kernel comparison sends every integration class to its native connecting class. -/
theorem omega_kernel_value (hc : ClosedRegion.Cover U V)
    (z : CoverCohomology.H1 M P (ClosedRegion.inter U V)) :
    (omegaKernelEquiv M P U V hc (QuotientAddGroup.mk z)).1 = connecting M P U V hc z := rfl
/-- Both H2 restrictions retain exactly the original full quotient class values. -/
theorem restriction_original_class (x : CoverCohomology.H2 M P ClosedRegion.all) :
    restriction M P U V ((OriginalCohomology.familySecondIso M P).hom x) =
      CoverCohomologyMaps.diagonalH2 M P U V x := by
  change (CoverPairCohomology.nativeSecondProductIso M P U V).hom
    (HomologicalComplex.homologyMap (RelativeCover.originalCoverShortComplex M P U V).f 2
      ((OriginalCohomology.secondHomologyIso M P).inv
        ((OriginalCohomology.secondHomologyIso M P).hom
          (HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).hom 2
            ((CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv x))))) = _
  rw [Iso.hom_inv_id_apply]
  change (CoverPairCohomology.nativeSecondProductIso M P U V).hom
    (HomologicalComplex.homologyMap ((RelativeCover.originalComplexIso M P).inv ≫
      RelativeCover.diagonalMap M P U V) 2
      (HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).hom 2
        ((CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv x))) = _
  rw [HomologicalComplex.homologyMap_comp]
  change (CoverPairCohomology.nativeSecondProductIso M P U V).hom
    (HomologicalComplex.homologyMap (RelativeCover.diagonalMap M P U V) 2
      (HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).inv 2
        (HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).hom 2
          ((CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv x)))) = _
  have hh : HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).inv 2
      (HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).hom 2
        ((CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv x)) =
      (CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv x :=
    ((HomologicalComplex.homologyFunctor Ab (ComplexShape.up ℕ) 2).mapIso
      (RelativeCover.originalComplexIso M P)).hom_inv_id_apply _
  rw [hh,CoverCohomologyMaps.native_diagonal_h2,Iso.inv_hom_id_apply]
end CoverObstructionKernel
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
