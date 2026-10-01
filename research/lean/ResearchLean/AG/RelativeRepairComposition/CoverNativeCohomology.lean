import ResearchLean.AG.RelativeRepairComposition.CoverConnecting
import ResearchLean.AG.RelativeRepairComposition.CoverPairCohomology

/-!
# Full original representatives of native cover cohomology

The native cycle has precisely the same original cochain. Its homology class is
the explicit cycle quotient, with both inverse maps retained.
## Implementation notes

G-130 B compares full native and original-K cohomology through the accepted
complex isomorphisms. Explicit native segment isomorphisms keep every
middle cochain value, making the class comparison independent of opaque
proof casts. The all-region subtype is compared directly with K itself.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverCohomology
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U : ClosedRegion K)
/-- A full original one-cycle is the identical native cycle. -/
noncomputable def nativeCycle1 (z : Z1 M P U) :
    ((RelativeCover.cochainComplex M P U).sc 1).g.hom.ker :=
  ⟨z.1,by
    change (RelativeCover.cochainComplex M P U).d 1 ((ComplexShape.up ℕ).next 1) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 1 = 2 := by simp
    rw [hn]
    simpa only [RelativeCover.cochainComplex,CochainComplex.of_d,
      RelativeCover.cochainDifferential] using z.2⟩
/-- The native cycle keeps the whole original edge cochain. -/
theorem native_cycle1_value (z : Z1 M P U) : (nativeCycle1 M P U z).1 = z.1 := rfl
/-- Native H1 classes are exactly the full original quotient classes. -/
theorem native_h1_class (z : Z1 M P U) :
    (firstHomologyIso M P U).hom
      (CohomologyClass.classHom ((RelativeCover.cochainComplex M P U).sc 1)
        (nativeCycle1 M P U z)) = QuotientAddGroup.mk z := by
  change (firstShortComplex M P U).abHomologyIso.hom
    (ShortComplex.homologyMap (firstShortIso M P U).hom
      (CohomologyClass.classHom ((RelativeCover.cochainComplex M P U).sc 1)
        (nativeCycle1 M P U z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (firstShortIso M P U).hom (nativeCycle1 M P U z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (firstShortComplex M P U) z
/-- A full original two-cycle is the identical native cycle. -/
noncomputable def nativeCycle2 (z : Z2 M P U) :
    ((RelativeCover.cochainComplex M P U).sc 2).g.hom.ker :=
  ⟨z.1,by
    change (RelativeCover.cochainComplex M P U).d 2 ((ComplexShape.up ℕ).next 2) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 2 = 3 := by simp
    rw [hn]
    simpa only [RelativeCover.cochainComplex,CochainComplex.of_d,
      RelativeCover.cochainDifferential] using z.2⟩
/-- The native cycle keeps the whole original face cochain. -/
theorem native_cycle2_value (z : Z2 M P U) : (nativeCycle2 M P U z).1 = z.1 := rfl
/-- Native H2 classes are exactly the full original quotient classes. -/
theorem native_h2_class (z : Z2 M P U) :
    (secondHomologyIso M P U).hom
      (CohomologyClass.classHom ((RelativeCover.cochainComplex M P U).sc 2)
        (nativeCycle2 M P U z)) = QuotientAddGroup.mk z := by
  change (secondShortComplex M P U).abHomologyIso.hom
    (ShortComplex.homologyMap (secondShortIso M P U).hom
      (CohomologyClass.classHom ((RelativeCover.cochainComplex M P U).sc 2)
        (nativeCycle2 M P U z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (secondShortIso M P U).hom (nativeCycle2 M P U z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (secondShortComplex M P U) z
/-- The full local quotient is the native H1 of the independent restricted presentation. -/
noncomputable def nativeFirstIso : AddCommGrpCat.of (H1 M P U) ≅
    AddCommGrpCat.of (RelativeComplex.H1 (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅) :=
  (firstHomologyIso M P U).symm ≪≫
    (HomologicalComplex.homologyFunctor Ab (ComplexShape.up ℕ) 1).mapIso
      (RelativeCover.nativeComplexIso M P U) ≪≫
    RelativeComplex.firstCochainHomologyIso (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅
/-- The full local quotient is the native H2 of the independent restricted presentation. -/
noncomputable def nativeSecondIso : AddCommGrpCat.of (H2 M P U) ≅
    AddCommGrpCat.of (RelativeComplex.H2 (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅) :=
  (secondHomologyIso M P U).symm ≪≫
    (HomologicalComplex.homologyFunctor Ab (ComplexShape.up ℕ) 2).mapIso
      (RelativeCover.nativeComplexIso M P U) ≪≫
    RelativeComplex.secondCochainHomologyIso (ClosedRegion.restrictCoefficients U M)
      (ClosedRegion.nativeIntersection U P) ∅ ∅
/-- The complete original family quotient is cohomology of the original K itself. -/
noncomputable def originalFirstIso : AddCommGrpCat.of (H1 M P ClosedRegion.all) ≅
    AddCommGrpCat.of (RelativeComplex.H1 M P ∅ ∅) :=
  (firstHomologyIso M P ClosedRegion.all).symm ≪≫
    (HomologicalComplex.homologyFunctor Ab (ComplexShape.up ℕ) 1).mapIso
      (RelativeCover.originalComplexIso M P) ≪≫
    RelativeComplex.firstCochainHomologyIso M P ∅ ∅
/-- The complete original face quotient is H2 of the original K itself. -/
noncomputable def originalSecondIso : AddCommGrpCat.of (H2 M P ClosedRegion.all) ≅
    AddCommGrpCat.of (RelativeComplex.H2 M P ∅ ∅) :=
  (secondHomologyIso M P ClosedRegion.all).symm ≪≫
    (HomologicalComplex.homologyFunctor Ab (ComplexShape.up ℕ) 2).mapIso
      (RelativeCover.originalComplexIso M P) ≪≫
    RelativeComplex.secondCochainHomologyIso M P ∅ ∅
end CoverCohomology
namespace CoverPairCohomology
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U V : ClosedRegion K)
/-- The full original local-pair cycle is the same native cycle. -/
noncomputable def nativeCycle1 (z : Z1 M P U V) :
    ((RelativeCover.pairComplex M P U V).sc 1).g.hom.ker :=
  ⟨z.1,by
    change (RelativeCover.pairComplex M P U V).d 1 ((ComplexShape.up ℕ).next 1) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 1 = 2 := by simp
    rw [hn]
    simpa only [RelativeCover.pairComplex,CochainComplex.of_d,
      RelativeCover.pairDifferential] using z.2⟩
/-- The native class retains both entire original local-pair cycle values. -/
theorem native_h1_class (z : Z1 M P U V) :
    (firstHomologyIso M P U V).hom
      (CohomologyClass.classHom ((RelativeCover.pairComplex M P U V).sc 1)
        (nativeCycle1 M P U V z)) = QuotientAddGroup.mk z := by
  change (firstShortComplex M P U V).abHomologyIso.hom
    (ShortComplex.homologyMap (firstShortIso M P U V).hom
      (CohomologyClass.classHom ((RelativeCover.pairComplex M P U V).sc 1)
        (nativeCycle1 M P U V z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (firstShortIso M P U V).hom (nativeCycle1 M P U V z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (firstShortComplex M P U V) z
/-- The full original local-pair cycle is the same native cycle. -/
noncomputable def nativeCycle2 (z : Z2 M P U V) :
    ((RelativeCover.pairComplex M P U V).sc 2).g.hom.ker :=
  ⟨z.1,by
    change (RelativeCover.pairComplex M P U V).d 2 ((ComplexShape.up ℕ).next 2) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 2 = 3 := by simp
    rw [hn]
    simpa only [RelativeCover.pairComplex,CochainComplex.of_d,
      RelativeCover.pairDifferential] using z.2⟩
/-- The native class retains both entire original local-pair cycle values. -/
theorem native_h2_class (z : Z2 M P U V) :
    (secondHomologyIso M P U V).hom
      (CohomologyClass.classHom ((RelativeCover.pairComplex M P U V).sc 2)
        (nativeCycle2 M P U V z)) = QuotientAddGroup.mk z := by
  change (secondShortComplex M P U V).abHomologyIso.hom
    (ShortComplex.homologyMap (secondShortIso M P U V).hom
      (CohomologyClass.classHom ((RelativeCover.pairComplex M P U V).sc 2)
        (nativeCycle2 M P U V z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (secondShortIso M P U V).hom (nativeCycle2 M P U V z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (secondShortComplex M P U V) z
end CoverPairCohomology
namespace OriginalCohomology
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
/-- The original-K native second segment retains its complete face cochain. -/
noncomputable def secondNormalizedIso : (RelativeComplex.cochainComplex M P ∅ ∅).sc' 1 2 3 ≅
    RelativeComplex.secondShortComplex M P ∅ ∅ :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeComplex.cochainComplex M P ∅ ∅).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeComplex.cochainComplex,CochainComplex.of,
      RelativeComplex.cochainDifferential,RelativeComplex.secondShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeComplex.cochainComplex M P ∅ ∅).d 2 3 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeComplex.cochainComplex,CochainComplex.of,
      RelativeComplex.cochainDifferential,RelativeComplex.secondShortComplex])
/-- The original-K segment isomorphism keeps every actual face value. -/
noncomputable def secondShortIso : (RelativeComplex.cochainComplex M P ∅ ∅).sc 2 ≅
    RelativeComplex.secondShortComplex M P ∅ ∅ :=
  (RelativeComplex.cochainComplex M P ∅ ∅).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    secondNormalizedIso M P
/-- Native original-K H2 is the same explicit quotient of its full original cycles. -/
noncomputable def secondHomologyIso : (RelativeComplex.cochainComplex M P ∅ ∅).homology 2 ≅
    AddCommGrpCat.of (RelativeComplex.H2 M P ∅ ∅) :=
  ShortComplex.homologyMapIso (secondShortIso M P) ≪≫
    (RelativeComplex.secondShortComplex M P ∅ ∅).abHomologyIso
/-- An original-K face cycle is the identical native cycle. -/
noncomputable def nativeCycle2 (z : RelativeComplex.Z2 M P) :
    ((RelativeComplex.cochainComplex M P ∅ ∅).sc 2).g.hom.ker :=
  ⟨z.1,by
    change (RelativeComplex.cochainComplex M P ∅ ∅).d 2 ((ComplexShape.up ℕ).next 2) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 2 = 3 := by simp
    rw [hn]
    simpa only [RelativeComplex.cochainComplex,CochainComplex.of_d,
      RelativeComplex.cochainDifferential] using z.2⟩
/-- The native original-K H2 class is exactly the same full face quotient class. -/
theorem native_h2_class (z : RelativeComplex.Z2 M P) :
    (secondHomologyIso M P).hom
      (CohomologyClass.classHom ((RelativeComplex.cochainComplex M P ∅ ∅).sc 2)
        (nativeCycle2 M P z)) = QuotientAddGroup.mk z := by
  change (RelativeComplex.secondShortComplex M P ∅ ∅).abHomologyIso.hom
    (ShortComplex.homologyMap (secondShortIso M P).hom
      (CohomologyClass.classHom ((RelativeComplex.cochainComplex M P ∅ ∅).sc 2)
        (nativeCycle2 M P z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (secondShortIso M P).hom (nativeCycle2 M P z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (RelativeComplex.secondShortComplex M P ∅ ∅) z
/-- The full original-index face cycle is the same cycle on K itself. -/
noncomputable def familyCycle2 (z : CoverCohomology.Z2 M P ClosedRegion.all) : RelativeComplex.Z2 M P :=
  ⟨RelativeCover.original2 M P z.1,by
    change RelativeComplex.d2Relative M P (RelativeCover.original2 M P z.1) = 0
    rw [← RelativeCover.original_supported_d2,z.2,map_zero]⟩
/-- The family H2 quotient is directly original-K H2 through complete native complex maps. -/
noncomputable def familySecondIso : AddCommGrpCat.of (CoverCohomology.H2 M P ClosedRegion.all) ≅
    AddCommGrpCat.of (RelativeComplex.H2 M P ∅ ∅) :=
  (CoverCohomology.secondHomologyIso M P ClosedRegion.all).symm ≪≫
    (HomologicalComplex.homologyFunctor Ab (ComplexShape.up ℕ) 2).mapIso
      (RelativeCover.originalComplexIso M P) ≪≫ secondHomologyIso M P
/-- The original-K comparison preserves the entire original face quotient class. -/
theorem family_h2_class (z : CoverCohomology.Z2 M P ClosedRegion.all) :
    (familySecondIso M P).hom (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (familyCycle2 M P z) := by
  have hi : (CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv
      (QuotientAddGroup.mk z) =
      CohomologyClass.classHom ((RelativeCover.cochainComplex M P ClosedRegion.all).sc 2)
        (CoverCohomology.nativeCycle2 M P ClosedRegion.all z) := by
    rw [← CoverCohomology.native_h2_class M P ClosedRegion.all z]
    exact (CoverCohomology.secondHomologyIso M P ClosedRegion.all).hom_inv_id_apply _
  change (secondHomologyIso M P).hom
    (HomologicalComplex.homologyMap (RelativeCover.originalComplexIso M P).hom 2
      ((CoverCohomology.secondHomologyIso M P ClosedRegion.all).inv (QuotientAddGroup.mk z))) = _
  rw [hi]
  change (secondHomologyIso M P).hom
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (RelativeCover.originalComplexIso M P).hom) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (RelativeCover.originalComplexIso M P).hom)
      (CoverCohomology.nativeCycle2 M P ClosedRegion.all z) =
      nativeCycle2 M P (familyCycle2 M P z) := Subtype.ext rfl
  rw [hz]
  exact native_h2_class M P _
end OriginalCohomology
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
