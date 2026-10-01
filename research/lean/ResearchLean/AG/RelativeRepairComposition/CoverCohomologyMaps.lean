import ResearchLean.AG.RelativeRepairComposition.CoverNativeCohomology

/-!
# The native cover maps on full original cohomology classes

Restrictions, the first-minus-second difference and the diagonal are evaluated
on the entire original cycle representatives. Both local product factors remain.
## Implementation notes

G-130 B uses the same original restrictions in every native degree.
Evaluation on all original cycle classes identifies the native cover
difference and diagonal with the full explicit quotient maps. Equality
only after forgetting one product factor would not suffice.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverCohomology
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable {U V : ClosedRegion K}
/-- Every original degree is restricted by the same full cochain restriction. -/
noncomputable def restrictionComponent (inc : ClosedRegion.Inclusion V U) : ∀ n : ℕ,
    RelativeCover.cochainObject M P U n ⟶ RelativeCover.cochainObject M P V n
  | 0 => AddCommGrpCat.ofHom (RelativeCover.r0 M P inc)
  | 1 => AddCommGrpCat.ofHom (RelativeCover.r1 M P inc)
  | 2 => AddCommGrpCat.ofHom (RelativeCover.r2 M P inc)
  | 3 => AddCommGrpCat.ofHom (RelativeCover.r3 M P inc)
  | _ + 4 => 𝟙 _
/-- Full restriction commutes with all original differentials. -/
theorem restriction_component_comm (inc : ClosedRegion.Inclusion V U) (n : ℕ) :
    restrictionComponent M P inc n ≫ RelativeCover.cochainDifferential M P V n =
      RelativeCover.cochainDifferential M P U n ≫ restrictionComponent M P inc (n+1) := by
  rcases n with _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (RelativeCover.r_d0 M P inc b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (RelativeCover.r_d1 M P inc b).symm
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro b
    exact (RelativeCover.r_d2 M P inc b).symm
  · change _ ≫ (0 : _ ⟶ _) = (0 : _ ⟶ _) ≫ _
    rw [Limits.comp_zero,Limits.zero_comp]
/-- Full original restriction is a native map of complexes. -/
noncomputable def restrictionMap (inc : ClosedRegion.Inclusion V U) :
    RelativeCover.cochainComplex M P U ⟶ RelativeCover.cochainComplex M P V :=
  CochainComplex.ofHom _ _ _ _ _ _ (restrictionComponent M P inc)
    (restriction_component_comm M P inc)
/-- The inverse native H1 comparison restores the whole original cycle class. -/
theorem native_h1_inverse_class (z : Z1 M P U) :
    (firstHomologyIso M P U).inv (QuotientAddGroup.mk z) =
      CohomologyClass.classHom ((RelativeCover.cochainComplex M P U).sc 1)
        (nativeCycle1 M P U z) := by
  rw [← native_h1_class M P U z]
  exact (firstHomologyIso M P U).hom_inv_id_apply _
/-- The inverse native H2 comparison restores the whole original cycle class. -/
theorem native_h2_inverse_class (z : Z2 M P U) :
    (secondHomologyIso M P U).inv (QuotientAddGroup.mk z) =
      CohomologyClass.classHom ((RelativeCover.cochainComplex M P U).sc 2)
        (nativeCycle2 M P U z) := by
  rw [← native_h2_class M P U z]
  exact (secondHomologyIso M P U).hom_inv_id_apply _
/-- Native restriction acts on H1 by the same full original cycle restriction. -/
theorem restriction_h1_class (inc : ClosedRegion.Inclusion V U) (z : Z1 M P U) :
    (firstHomologyIso M P V).hom
      (HomologicalComplex.homologyMap (restrictionMap M P inc) 1
        ((firstHomologyIso M P U).inv (QuotientAddGroup.mk z))) =
      QuotientAddGroup.mk (restrictZ1 M P inc z) := by
  rw [native_h1_inverse_class]
  change (firstHomologyIso M P V).hom
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 1).map
        (restrictionMap M P inc)) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 1).map
        (restrictionMap M P inc)) (nativeCycle1 M P U z) =
      nativeCycle1 M P V (restrictZ1 M P inc z) := Subtype.ext rfl
  rw [hz]
  exact native_h1_class M P V _
/-- Native restriction acts on H2 by the same full original cycle restriction. -/
theorem restriction_h2_class (inc : ClosedRegion.Inclusion V U) (z : Z2 M P U) :
    (secondHomologyIso M P V).hom
      (HomologicalComplex.homologyMap (restrictionMap M P inc) 2
        ((secondHomologyIso M P U).inv (QuotientAddGroup.mk z))) =
      QuotientAddGroup.mk (restrictZ2 M P inc z) := by
  rw [native_h2_inverse_class]
  change (secondHomologyIso M P V).hom
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (restrictionMap M P inc)) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (restrictionMap M P inc)) (nativeCycle2 M P U z) =
      nativeCycle2 M P V (restrictZ2 M P inc z) := Subtype.ext rfl
  rw [hz]
  exact native_h2_class M P V _
/-- The native H1 restriction is the explicit restriction on every quotient class. -/
theorem restriction_h1 (inc : ClosedRegion.Inclusion V U) (x : H1 M P U) :
    (firstHomologyIso M P V).hom
      (HomologicalComplex.homologyMap (restrictionMap M P inc) 1
        ((firstHomologyIso M P U).inv x)) = restrictH1 M P inc x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (boundary1 M P U).range x
  exact restriction_h1_class M P inc z
/-- The native H2 restriction is the explicit restriction on every quotient class. -/
theorem restriction_h2 (inc : ClosedRegion.Inclusion V U) (x : H2 M P U) :
    (secondHomologyIso M P V).hom
      (HomologicalComplex.homologyMap (restrictionMap M P inc) 2
        ((secondHomologyIso M P U).inv x)) = restrictH2 M P inc x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (boundary2 M P U).range x
  exact restriction_h2_class M P inc z
end CoverCohomology
namespace CoverCohomologyMaps
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U V : ClosedRegion K)
/-- The full first-minus-second homomorphism on both local H1 groups. -/
noncomputable def differenceH1 :
    CoverCohomology.H1 M P U × CoverCohomology.H1 M P V →+
      CoverCohomology.H1 M P (ClosedRegion.inter U V) :=
  (CoverCohomology.restrictH1 M P (ClosedRegion.inter_left U V)).comp
    (AddMonoidHom.fst _ _) -
  (CoverCohomology.restrictH1 M P (ClosedRegion.inter_right U V)).comp
    (AddMonoidHom.snd _ _)
/-- The native cover difference has exactly its full original class values. -/
theorem native_difference_h1 (x : (RelativeCover.pairComplex M P U V).homology 1) :
    (CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).hom
      (HomologicalComplex.homologyMap (RelativeCover.differenceMap M P U V) 1 x) =
      differenceH1 M P U V ((CoverPairCohomology.nativeFirstProductIso M P U V).hom x) := by
  obtain ⟨z,rfl⟩ := CohomologyClass.class_surjective
    ((RelativeCover.pairComplex M P U V).sc 1) x
  let w : CoverPairCohomology.Z1 M P U V := ⟨z.1,by
    have hz := z.2
    change (RelativeCover.pairComplex M P U V).d 1 ((ComplexShape.up ℕ).next 1) z.1 = 0 at hz
    have hn : (ComplexShape.up ℕ).next 1 = 2 := by simp
    rw [hn] at hz
    change RelativeCover.pairD1 M P U V z.1 = 0
    simpa only [RelativeCover.pairComplex,CochainComplex.of_d,
      RelativeCover.pairDifferential] using hz⟩
  have hw : CoverPairCohomology.nativeCycle1 M P U V w = z := Subtype.ext rfl
  rw [← hw]
  change (CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).hom
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 1).map
        (RelativeCover.differenceMap M P U V)) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  let d : CoverCohomology.Z1 M P (ClosedRegion.inter U V) :=
    CoverCohomology.restrictZ1 M P (ClosedRegion.inter_left U V)
      (CoverPairCohomology.cycleLeft M P U V w) -
    CoverCohomology.restrictZ1 M P (ClosedRegion.inter_right U V)
      (CoverPairCohomology.cycleRight M P U V w)
  have hd : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 1).map
        (RelativeCover.differenceMap M P U V))
      (CoverPairCohomology.nativeCycle1 M P U V w) =
      CoverCohomology.nativeCycle1 M P (ClosedRegion.inter U V) d := Subtype.ext rfl
  rw [hd,CoverCohomology.native_h1_class]
  change QuotientAddGroup.mk d = differenceH1 M P U V
    (CoverPairCohomology.componentH1 M P U V
      ((CoverPairCohomology.firstHomologyIso M P U V).hom (CohomologyClass.classHom _ _)))
  rw [CoverPairCohomology.native_h1_class,CoverPairCohomology.component_h1_mk]
  exact map_sub (QuotientAddGroup.mk' (CoverCohomology.boundary1 M P
    (ClosedRegion.inter U V)).range) _ _
/-- The full global H2 diagonal is the pair of the same original restrictions. -/
noncomputable def diagonalH2 : CoverCohomology.H2 M P ClosedRegion.all →+
    CoverCohomology.H2 M P U × CoverCohomology.H2 M P V :=
  (CoverCohomology.restrictH2 M P (ClosedRegion.to_all U)).prod
    (CoverCohomology.restrictH2 M P (ClosedRegion.to_all V))
/-- The native H2 diagonal retains both full original local class values. -/
theorem native_diagonal_h2 (x : (RelativeCover.cochainComplex M P ClosedRegion.all).homology 2) :
    (CoverPairCohomology.nativeSecondProductIso M P U V).hom
      (HomologicalComplex.homologyMap (RelativeCover.diagonalMap M P U V) 2 x) =
      diagonalH2 M P U V ((CoverCohomology.secondHomologyIso M P ClosedRegion.all).hom x) := by
  obtain ⟨z,rfl⟩ := CohomologyClass.class_surjective
    ((RelativeCover.cochainComplex M P ClosedRegion.all).sc 2) x
  let w : CoverCohomology.Z2 M P ClosedRegion.all := ⟨z.1,by
    have hz := z.2
    change (RelativeCover.cochainComplex M P ClosedRegion.all).d 2 ((ComplexShape.up ℕ).next 2) z.1 = 0 at hz
    have hn : (ComplexShape.up ℕ).next 2 = 3 := by simp
    rw [hn] at hz
    change RelativeCover.d2 M ClosedRegion.all P z.1 = 0
    simpa only [RelativeCover.cochainComplex,CochainComplex.of_d,
      RelativeCover.cochainDifferential] using hz⟩
  have hw : CoverCohomology.nativeCycle2 M P ClosedRegion.all w = z := Subtype.ext rfl
  rw [← hw]
  change (CoverPairCohomology.nativeSecondProductIso M P U V).hom
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (RelativeCover.diagonalMap M P U V)) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  let d : CoverPairCohomology.Z2 M P U V :=
    ⟨(RelativeCover.r2 M P (ClosedRegion.to_all U) w.1,
      RelativeCover.r2 M P (ClosedRegion.to_all V) w.1),
      Prod.ext (CoverCohomology.restrictZ2 M P (ClosedRegion.to_all U) w).2
        (CoverCohomology.restrictZ2 M P (ClosedRegion.to_all V) w).2⟩
  have hd : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (RelativeCover.diagonalMap M P U V))
      (CoverCohomology.nativeCycle2 M P ClosedRegion.all w) =
      CoverPairCohomology.nativeCycle2 M P U V d := Subtype.ext rfl
  rw [hd,CoverCohomology.native_h2_class]
  change CoverPairCohomology.componentH2 M P U V
    ((CoverPairCohomology.secondHomologyIso M P U V).hom (CohomologyClass.classHom _ _)) = _
  rw [CoverPairCohomology.native_h2_class,CoverPairCohomology.component_h2_mk]
  rfl
end CoverCohomologyMaps
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
