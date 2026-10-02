import ResearchLean.AG.RelativeRepairComposition.RelativeComplex
import ResearchLean.AG.RelativeRepairComposition.CoverConnecting

/-!
# Native cohomology classes of the same supported relative complex

The comparisons keep the entire original middle cochain in both supported
segments. Every quotient class is evaluated on its full original cycle.

## Implementation notes

Explicit segment isomorphisms retain the actual middle value, avoiding an
opaque transport along equality of short complexes. These APIs are used for
the same subdivision chain maps in all permission ranges.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeCohomologyValues
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))
/-- The explicit segment isomorphism preserves every middle cochain value. -/
noncomputable def firstNormalizedIso : (RelativeComplex.cochainComplex M P candidates allowed).sc' 0 1 2 ≅
    RelativeComplex.firstShortComplex M P candidates allowed :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeComplex.cochainComplex M P candidates allowed).d 0 1 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeComplex.cochainComplex,CochainComplex.of,
      RelativeComplex.cochainDifferential,RelativeComplex.firstShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeComplex.cochainComplex M P candidates allowed).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeComplex.cochainComplex,CochainComplex.of,
      RelativeComplex.cochainDifferential,RelativeComplex.firstShortComplex])
/-- The native segment comparison keeps the complete original middle cochain. -/
noncomputable def firstShortIso : (RelativeComplex.cochainComplex M P candidates allowed).sc 1 ≅ RelativeComplex.firstShortComplex M P candidates allowed :=
  (RelativeComplex.cochainComplex M P candidates allowed).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    firstNormalizedIso M P candidates allowed
/-- Native homology is the same full original quotient, with an explicit cochain comparison. -/
noncomputable def firstHomologyIso :
    (RelativeComplex.cochainComplex M P candidates allowed).homology 1 ≅ AddCommGrpCat.of (RelativeComplex.H1 M P candidates allowed) :=
  ShortComplex.homologyMapIso (firstShortIso M P candidates allowed) ≪≫ (RelativeComplex.firstShortComplex M P candidates allowed).abHomologyIso
/-- The explicit segment isomorphism preserves every middle cochain value. -/
noncomputable def secondNormalizedIso : (RelativeComplex.cochainComplex M P candidates allowed).sc' 1 2 3 ≅
    RelativeComplex.secondShortComplex M P candidates allowed :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeComplex.cochainComplex M P candidates allowed).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeComplex.cochainComplex,CochainComplex.of,
      RelativeComplex.cochainDifferential,RelativeComplex.secondShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeComplex.cochainComplex M P candidates allowed).d 2 3 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeComplex.cochainComplex,CochainComplex.of,
      RelativeComplex.cochainDifferential,RelativeComplex.secondShortComplex])
/-- The native segment comparison keeps the complete original middle cochain. -/
noncomputable def secondShortIso : (RelativeComplex.cochainComplex M P candidates allowed).sc 2 ≅ RelativeComplex.secondShortComplex M P candidates allowed :=
  (RelativeComplex.cochainComplex M P candidates allowed).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    secondNormalizedIso M P candidates allowed
/-- Native homology is the same full original quotient, with an explicit cochain comparison. -/
noncomputable def secondHomologyIso :
    (RelativeComplex.cochainComplex M P candidates allowed).homology 2 ≅ AddCommGrpCat.of (RelativeComplex.H2 M P candidates allowed) :=
  ShortComplex.homologyMapIso (secondShortIso M P candidates allowed) ≪≫ (RelativeComplex.secondShortComplex M P candidates allowed).abHomologyIso
/-- A full original one-cycle is the identical native cycle. -/
noncomputable def nativeCycle1 (z : RelativeComplex.Z1 M P candidates allowed) :
    ((RelativeComplex.cochainComplex M P candidates allowed).sc 1).g.hom.ker :=
  ⟨z.1,by
    change (RelativeComplex.cochainComplex M P candidates allowed).d 1 ((ComplexShape.up ℕ).next 1) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 1 = 2 := by simp
    rw [hn]
    simpa only [RelativeComplex.cochainComplex,CochainComplex.of_d,
      RelativeComplex.cochainDifferential] using z.2⟩
/-- The native cycle keeps the whole original edge cochain. -/
theorem native_cycle1_value (z : RelativeComplex.Z1 M P candidates allowed) : (nativeCycle1 M P candidates allowed z).1 = z.1 := rfl
/-- Native H1 classes are exactly the full original quotient classes. -/
theorem native_h1_class (z : RelativeComplex.Z1 M P candidates allowed) :
    (firstHomologyIso M P candidates allowed).hom
      (CohomologyClass.classHom ((RelativeComplex.cochainComplex M P candidates allowed).sc 1)
        (nativeCycle1 M P candidates allowed z)) = QuotientAddGroup.mk z := by
  change (RelativeComplex.firstShortComplex M P candidates allowed).abHomologyIso.hom
    (ShortComplex.homologyMap (firstShortIso M P candidates allowed).hom
      (CohomologyClass.classHom ((RelativeComplex.cochainComplex M P candidates allowed).sc 1)
        (nativeCycle1 M P candidates allowed z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (firstShortIso M P candidates allowed).hom (nativeCycle1 M P candidates allowed z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (RelativeComplex.firstShortComplex M P candidates allowed) z
/-- A full original two-cycle is the identical native cycle. -/
noncomputable def nativeCycle2 (z : RelativeComplex.Z2 M P) :
    ((RelativeComplex.cochainComplex M P candidates allowed).sc 2).g.hom.ker :=
  ⟨z.1,by
    change (RelativeComplex.cochainComplex M P candidates allowed).d 2 ((ComplexShape.up ℕ).next 2) z.1 = 0
    have hn : (ComplexShape.up ℕ).next 2 = 3 := by simp
    rw [hn]
    simpa only [RelativeComplex.cochainComplex,CochainComplex.of_d,
      RelativeComplex.cochainDifferential] using z.2⟩
/-- The native cycle keeps the whole original face cochain. -/
theorem native_cycle2_value (z : RelativeComplex.Z2 M P) : (nativeCycle2 M P candidates allowed z).1 = z.1 := rfl
/-- Native H2 classes are exactly the full original quotient classes. -/
theorem native_h2_class (z : RelativeComplex.Z2 M P) :
    (secondHomologyIso M P candidates allowed).hom
      (CohomologyClass.classHom ((RelativeComplex.cochainComplex M P candidates allowed).sc 2)
        (nativeCycle2 M P candidates allowed z)) = QuotientAddGroup.mk z := by
  change (RelativeComplex.secondShortComplex M P candidates allowed).abHomologyIso.hom
    (ShortComplex.homologyMap (secondShortIso M P candidates allowed).hom
      (CohomologyClass.classHom ((RelativeComplex.cochainComplex M P candidates allowed).sc 2)
        (nativeCycle2 M P candidates allowed z))) = QuotientAddGroup.mk z
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap (secondShortIso M P candidates allowed).hom (nativeCycle2 M P candidates allowed z) = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact CohomologyClass.class_quotient (RelativeComplex.secondShortComplex M P candidates allowed) z

/-- The inverse native H1 comparison restores the entire original cycle class. -/
theorem native_h1_inverse_class (z : RelativeComplex.Z1 M P candidates allowed) :
    (firstHomologyIso M P candidates allowed).inv (QuotientAddGroup.mk z) =
      CohomologyClass.classHom ((RelativeComplex.cochainComplex M P candidates allowed).sc 1)
        (nativeCycle1 M P candidates allowed z) := by
  rw [← native_h1_class M P candidates allowed z]
  exact (firstHomologyIso M P candidates allowed).hom_inv_id_apply _

/-- The inverse native H2 comparison restores the entire original face cycle class. -/
theorem native_h2_inverse_class (z : RelativeComplex.Z2 M P) :
    (secondHomologyIso M P candidates allowed).inv (QuotientAddGroup.mk z) =
      CohomologyClass.classHom ((RelativeComplex.cochainComplex M P candidates allowed).sc 2)
        (nativeCycle2 M P candidates allowed z) := by
  rw [← native_h2_class M P candidates allowed z]
  exact (secondHomologyIso M P candidates allowed).hom_inv_id_apply _

end AAT.AG.RelativeRepairComposition.RelativeCohomologyValues
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeCohomologyValues
