import Mathlib.Algebra.Homology.HomologySequence
import ResearchLean.AG.RelativeRepairComposition.CoverEquation

/-!
# Cohomology on the same original relative cover complex

Cycles, boundaries and restrictions retain all original coefficient values.
The explicit quotients are native homology of the accepted relative complex.
## Implementation notes

G-130 B uses the accepted original-cell relative cochain groups. Explicit cycle
quotients are compared with mathlib native homology by segment isomorphisms
whose middle component is the identity. A quotient of repair objects alone
would discard the full coefficient classes and their restriction maps.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA u
namespace CohomologyClass
variable (S : ShortComplex Ab.{u})
/-- Every actual cycle defines its native class. -/
noncomputable def classHom : S.g.hom.ker →+ S.homology :=
  S.homologyπ.hom.comp S.abCyclesIso.inv.hom
/-- The native class is the same explicit cycle quotient. -/
theorem class_quotient (z : S.g.hom.ker) :
    S.abHomologyIso.hom (classHom S z) = QuotientAddGroup.mk z := by
  have h := S.abLeftHomologyData.π_comp_homologyIso_inv
  have hh := congrArg (fun f => f z) h
  change S.abHomologyIso.inv (QuotientAddGroup.mk z) = classHom S z at hh
  rw [← hh]
  exact S.abHomologyIso.inv_hom_id_apply _
/-- A class vanishes exactly when this cycle is an original boundary. -/
theorem class_eq_zero_iff (z : S.g.hom.ker) :
    classHom S z = 0 ↔ ∃ a : S.X₁, S.abToCycles a = z := by
  have hi : Function.Injective S.abHomologyIso.hom :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  rw [← hi.eq_iff, map_zero, class_quotient, QuotientAddGroup.eq_zero_iff]
  exact AddMonoidHom.mem_range
/-- All native classes have full original cycle representatives. -/
theorem class_surjective : Function.Surjective (classHom S) := by
  intro x
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk'_surjective (S.abToCycles.range)
    (S.abHomologyIso.hom x)
  refine ⟨z,?_⟩
  apply (AddCommGrpCat.mono_iff_injective S.abHomologyIso.hom).mp inferInstance
  rw [class_quotient]
  exact hz
end CohomologyClass
namespace CoverCohomology
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U : ClosedRegion K)
/-- Full relative original edge cycles. -/
noncomputable abbrev Z1 := (RelativeCover.d1 M U P).ker
/-- Full relative original face cycles. -/
noncomputable abbrev Z2 := (RelativeCover.d2 M U P).ker
/-- Original vertex boundaries with generated cycle membership. -/
noncomputable def boundary1 : RelativeCover.C0 M U P →+ Z1 M P U where
  toFun b := ⟨RelativeCover.d0 M U P b,RelativeCover.d1_d0 M U P b⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- Original edge boundaries with generated cycle membership. -/
noncomputable def boundary2 : RelativeCover.C1 M U P →+ Z2 M P U where
  toFun h := ⟨RelativeCover.d1 M U P h,RelativeCover.d2_d1 M U P h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- Relative first cohomology, without a support restriction. -/
abbrev H1 := Z1 M P U ⧸ (boundary1 M P U).range
/-- Relative second cohomology on the same original values. -/
abbrev H2 := Z2 M P U ⧸ (boundary2 M P U).range
/-- An original one-cycle vanishes exactly when it is a vertex boundary. -/
theorem h1_eq_zero_iff (z : Z1 M P U) :
    (QuotientAddGroup.mk z : H1 M P U) = 0 ↔ ∃ b, boundary1 M P U b = z := by
  rw [QuotientAddGroup.eq_zero_iff,AddMonoidHom.mem_range]
/-- An original two-cycle vanishes exactly when it is an edge boundary. -/
theorem h2_eq_zero_iff (z : Z2 M P U) :
    (QuotientAddGroup.mk z : H2 M P U) = 0 ↔ ∃ h, boundary2 M P U h = z := by
  rw [QuotientAddGroup.eq_zero_iff,AddMonoidHom.mem_range]
/-- The first segment retains the full original d0 and d1. -/
noncomputable def firstShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (RelativeCover.C0 M U P)
  X₂ := AddCommGrpCat.of (RelativeCover.C1 M U P)
  X₃ := AddCommGrpCat.of (RelativeCover.C2 M U P)
  f := AddCommGrpCat.ofHom (RelativeCover.d0 M U P)
  g := AddCommGrpCat.ofHom (RelativeCover.d1 M U P)
  zero := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact RelativeCover.d1_d0 M U P
/-- The second segment retains the full original d1 and d2. -/
noncomputable def secondShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (RelativeCover.C1 M U P)
  X₂ := AddCommGrpCat.of (RelativeCover.C2 M U P)
  X₃ := AddCommGrpCat.of (RelativeCover.C3 M U P)
  f := AddCommGrpCat.ofHom (RelativeCover.d1 M U P)
  g := AddCommGrpCat.ofHom (RelativeCover.d2 M U P)
  zero := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact RelativeCover.d2_d1 M U P
/-- The first segment is degree one of the accepted native complex. -/
theorem first_eq_sc : firstShortComplex M P U = (RelativeCover.cochainComplex M P U).sc 1 := by
  have hprev : (ComplexShape.up ℕ).prev 1 = 0 := by simp
  simp [HomologicalComplex.sc,HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor',RelativeCover.cochainComplex,
    RelativeCover.cochainObject,RelativeCover.cochainDifferential,CochainComplex.of,
    firstShortComplex,hprev]
  rw [hprev]
/-- The second segment is degree two of the accepted native complex. -/
theorem second_eq_sc : secondShortComplex M P U = (RelativeCover.cochainComplex M P U).sc 2 := by
  have hprev : (ComplexShape.up ℕ).prev 2 = 1 := by simp
  simp [HomologicalComplex.sc,HomologicalComplex.shortComplexFunctor,
    HomologicalComplex.shortComplexFunctor',RelativeCover.cochainComplex,
    RelativeCover.cochainObject,RelativeCover.cochainDifferential,CochainComplex.of,
    secondShortComplex,hprev]
  rw [hprev]
/-- The explicit segment isomorphism preserves every middle cochain value. -/
noncomputable def firstNormalizedIso : (RelativeCover.cochainComplex M P U).sc' 0 1 2 ≅
    firstShortComplex M P U :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeCover.cochainComplex M P U).d 0 1 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.cochainComplex,CochainComplex.of,
      RelativeCover.cochainDifferential,firstShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeCover.cochainComplex M P U).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.cochainComplex,CochainComplex.of,
      RelativeCover.cochainDifferential,firstShortComplex])
/-- The native segment comparison keeps the complete original middle cochain. -/
noncomputable def firstShortIso : (RelativeCover.cochainComplex M P U).sc 1 ≅ firstShortComplex M P U :=
  (RelativeCover.cochainComplex M P U).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    firstNormalizedIso M P U
/-- Native homology is the same full original quotient, with an explicit cochain comparison. -/
noncomputable def firstHomologyIso :
    (RelativeCover.cochainComplex M P U).homology 1 ≅ AddCommGrpCat.of (H1 M P U) :=
  ShortComplex.homologyMapIso (firstShortIso M P U) ≪≫ (firstShortComplex M P U).abHomologyIso
/-- The explicit segment isomorphism preserves every middle cochain value. -/
noncomputable def secondNormalizedIso : (RelativeCover.cochainComplex M P U).sc' 1 2 3 ≅
    secondShortComplex M P U :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 _ ≫ _ = (RelativeCover.cochainComplex M P U).d 1 2 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.cochainComplex,CochainComplex.of,
      RelativeCover.cochainDifferential,secondShortComplex]) (by
    change 𝟙 _ ≫ _ = (RelativeCover.cochainComplex M P U).d 2 3 ≫ 𝟙 _
    rw [Category.comp_id,Category.id_comp]
    simp [RelativeCover.cochainComplex,CochainComplex.of,
      RelativeCover.cochainDifferential,secondShortComplex])
/-- The native segment comparison keeps the complete original middle cochain. -/
noncomputable def secondShortIso : (RelativeCover.cochainComplex M P U).sc 2 ≅ secondShortComplex M P U :=
  (RelativeCover.cochainComplex M P U).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    secondNormalizedIso M P U
/-- Native homology is the same full original quotient, with an explicit cochain comparison. -/
noncomputable def secondHomologyIso :
    (RelativeCover.cochainComplex M P U).homology 2 ≅ AddCommGrpCat.of (H2 M P U) :=
  ShortComplex.homologyMapIso (secondShortIso M P U) ≪≫ (secondShortComplex M P U).abHomologyIso
variable {U V : ClosedRegion K}
/-- Restriction keeps full original one-cycles and fixed-P values. -/
noncomputable def restrictZ1 (inc : ClosedRegion.Inclusion V U) : Z1 M P U →+ Z1 M P V where
  toFun z := ⟨RelativeCover.r1 M P inc z.1,by
    change RelativeCover.d1 M V P (RelativeCover.r1 M P inc z.1) = 0
    rw [← RelativeCover.r_d1,z.2,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- Original vertex boundaries commute with the same restriction. -/
theorem restrict_boundary1 (inc : ClosedRegion.Inclusion V U) (b : RelativeCover.C0 M U P) :
    restrictZ1 M P inc (boundary1 M P U b) =
      boundary1 M P V (RelativeCover.r0 M P inc b) :=
  Subtype.ext (RelativeCover.r_d0 M P inc b)
/-- Full H1 restriction descends from the original cycle restriction. -/
noncomputable def restrictH1 (inc : ClosedRegion.Inclusion V U) : H1 M P U →+ H1 M P V :=
  QuotientAddGroup.map _ _ (restrictZ1 M P inc) (by
    rintro z ⟨b,rfl⟩
    exact ⟨RelativeCover.r0 M P inc b,(restrict_boundary1 M P inc b).symm⟩)
/-- H1 restriction keeps the entire original representative. -/
theorem restrict_h1_mk (inc : ClosedRegion.Inclusion V U) (z : Z1 M P U) :
    restrictH1 M P inc (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (restrictZ1 M P inc z) := rfl
/-- Restriction keeps full original two-cycles and fixed-P values. -/
noncomputable def restrictZ2 (inc : ClosedRegion.Inclusion V U) : Z2 M P U →+ Z2 M P V where
  toFun z := ⟨RelativeCover.r2 M P inc z.1,by
    change RelativeCover.d2 M V P (RelativeCover.r2 M P inc z.1) = 0
    rw [← RelativeCover.r_d2,z.2,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
/-- Original edge boundaries commute with the same restriction. -/
theorem restrict_boundary2 (inc : ClosedRegion.Inclusion V U) (h : RelativeCover.C1 M U P) :
    restrictZ2 M P inc (boundary2 M P U h) =
      boundary2 M P V (RelativeCover.r1 M P inc h) :=
  Subtype.ext (RelativeCover.r_d1 M P inc h)
/-- Full H2 restriction descends from the original cycle restriction. -/
noncomputable def restrictH2 (inc : ClosedRegion.Inclusion V U) : H2 M P U →+ H2 M P V :=
  QuotientAddGroup.map _ _ (restrictZ2 M P inc) (by
    rintro z ⟨h,rfl⟩
    exact ⟨RelativeCover.r1 M P inc h,(restrict_boundary2 M P inc h).symm⟩)
/-- H2 restriction keeps the entire original representative. -/
theorem restrict_h2_mk (inc : ClosedRegion.Inclusion V U) (z : Z2 M P U) :
    restrictH2 M P inc (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (restrictZ2 M P inc z) := rfl
end CoverCohomology
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
