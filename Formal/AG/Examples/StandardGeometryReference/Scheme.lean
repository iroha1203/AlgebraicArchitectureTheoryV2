import Formal.AG.Examples.StandardGeometryReference.LeftRestriction
import Formal.AG.Examples.StandardGeometryReference.RightRestriction
import Formal.AG.Examples.StandardGeometryReference.OverlapLeftRestriction
import Formal.AG.Examples.StandardGeometryReference.OverlapRightRestriction

/-!
# Standard geometry reference: two-principal-open scheme

This module owns SD1: the chart-domain isomorphisms, `leftChart`, `rightChart`,
`referenceAtlas`, `referenceOverlapPresentation`, `referenceScheme`, and
`actualOverlapIso`.

The scheme is the actual `Spec ℤ[x]`; its charts are the canonical
localization-away morphisms for `x` and `1 - x`. The overlap is obtained from
the localization pushout, and `referenceScheme` is assembled with
`StandardArchitectureScheme.ofPresentation`. Self-overlaps use identity
pullback squares and mixed overlaps use the proved localization pullback.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section

private theorem left_algebraMap_not_surjective :
    ¬ Function.Surjective
      (algebraMap AmbientRing (Localization.Away leftGenerator)) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (IsLocalization.Away.invSelf leftGenerator)
  have heq : algebraMap AmbientRing (Localization.Away leftGenerator)
      (leftGenerator * p) = algebraMap AmbientRing
        (Localization.Away leftGenerator) 1 := by
    rw [map_mul, hp, IsLocalization.Away.mul_invSelf, map_one]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq leftGenerator heq
  have hgen : leftGenerator ≠ 0 := by
    simpa [leftGenerator, coordinate] using
      (MvPolynomial.X_ne_zero (R := Int) ())
  have hmul : leftGenerator * p = 1 :=
    mul_left_cancel₀ (pow_ne_zero n hgen) (by simpa [mul_assoc] using hn)
  have hev := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) hmul
  norm_num [leftGenerator, coordinate] at hev

private theorem rightGenerator_ne_zero : rightGenerator ≠ 0 := by
  intro h
  have h' := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
  norm_num [rightGenerator, coordinate] at h'

private theorem right_algebraMap_not_surjective :
    ¬ Function.Surjective
      (algebraMap AmbientRing (Localization.Away rightGenerator)) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (IsLocalization.Away.invSelf rightGenerator)
  have heq : algebraMap AmbientRing (Localization.Away rightGenerator)
      (rightGenerator * p) = algebraMap AmbientRing
        (Localization.Away rightGenerator) 1 := by
    rw [map_mul, hp, IsLocalization.Away.mul_invSelf, map_one]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq rightGenerator heq
  have hmul : rightGenerator * p = 1 :=
    mul_left_cancel₀ (pow_ne_zero n rightGenerator_ne_zero)
      (by simpa [mul_assoc] using hn)
  have hev := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (1 : Int))) hmul
  norm_num [rightGenerator, coordinate] at hev

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_restriction_not_isIso :
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) := by
  intro h
  letI := h
  have hIso : IsIso
      (baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase ≫
        leftSectionRingIso.hom) := inferInstance
  have hAlg : IsIso (CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away leftGenerator))) := by
    rw [← left_restriction_is_localization]
    exact hIso
  exact left_algebraMap_not_surjective
    ((ConcreteCategory.isIso_iff_bijective _).mp hAlg).2

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_restriction_not_isIso :
    ¬ IsIso (sheafifiedRestriction referenceRaw rightToBase) := by
  intro h
  letI := h
  have hIso : IsIso
      (baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase ≫
        rightSectionRingIso.hom) := inferInstance
  have hAlg : IsIso (CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away rightGenerator))) := by
    rw [← right_restriction_is_localization]
    exact hIso
  exact right_algebraMap_not_surjective
    ((ConcreteCategory.isIso_iff_bijective _).mp hAlg).2

/-!
### SD1 actual principal-open atlas

The ambient scheme is `Spec ℤ[x]`.  Its two charts are the canonical
localization-away morphisms for `x` and `1 - x`; their joint coverage is
proved from the span computation already fixed by SD0.  The mixed overlap is
constructed from the localization pushout and transported to the
architecture chart restriction square.  Self-overlaps use the identity
pullback squares.  The overlap presentation, decoration compatibility, and
triple cocycle are then supplied by the generic `StandardArchitectureScheme`
API.
-/

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def ambientScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of AmbientRing)

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientScheme_eq :
    ambientScheme =
      AlgebraicGeometry.Spec (CommRingCat.of AmbientRing) :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def baseChartDomainIso :
    architectureChartSpec referenceRaw baseContext ≅
      ambientScheme :=
  AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem baseChartDomainIso_eq :
    baseChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftChartDomainIso :
    architectureChartSpec referenceRaw leftContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away leftGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftChartDomainIso_eq :
    leftChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightChartDomainIso :
    architectureChartSpec referenceRaw rightContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away rightGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightChartDomainIso_eq :
    rightChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def overlapChartDomainIso :
    architectureChartSpec referenceRaw overlapContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem overlapChartDomainIso_eq :
    overlapChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def ambientDecoration :
    AATReadingDecoration referenceRaw ambientScheme :=
  AATReadingDecoration.pullback
    referenceRaw baseChartDomainIso.inv
    (AATReadingDecoration.ofContext referenceRaw baseContext)

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientDecoration_eq :
    ambientDecoration =
      AATReadingDecoration.pullback
        referenceRaw baseChartDomainIso.inv
        (AATReadingDecoration.ofContext referenceRaw baseContext) :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftChart :
    ArchitectureAffineChart
      referenceRaw ambientScheme ambientDecoration where
  context := leftContext
  contextHom := leftToBase
  map :=
    leftChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom
          (algebraMap AmbientRing
            (Localization.Away leftGenerator))).op

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightChart :
    ArchitectureAffineChart
      referenceRaw ambientScheme ambientDecoration where
  context := rightContext
  contextHom := rightToBase
  map :=
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom
          (algebraMap AmbientRing
            (Localization.Away rightGenerator))).op

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceAtlas :
    ArchitectureAffineAtlas
      referenceRaw ambientScheme ambientDecoration where
  Index := Bool
  chart
    | false => leftChart
    | true => rightChart

private theorem leftChart_map_eq_restriction :
    leftChart.map =
      architectureChartRestriction referenceRaw leftToBase ≫
        baseChartDomainIso.hom := by
  simp only [leftChart, leftChartDomainIso, baseChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom]
  rw [← AlgebraicGeometry.Scheme.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  change
    CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away leftGenerator)) ≫
        leftSectionRingIso.inv =
      baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase
  rw [← cancel_mono leftSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact left_restriction_is_localization.symm

private theorem rightChart_map_eq_restriction :
    rightChart.map =
      architectureChartRestriction referenceRaw rightToBase ≫
        baseChartDomainIso.hom := by
  simp only [rightChart, rightChartDomainIso, baseChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom]
  rw [← AlgebraicGeometry.Scheme.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  change
    CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away rightGenerator)) ≫
        rightSectionRingIso.inv =
      baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase
  rw [← cancel_mono rightSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact right_restriction_is_localization.symm

private theorem leftChart_valid :
    IsArchitectureAffineChart referenceRaw leftChart := by
  constructor
  · simp only [leftChart]
    rw [AlgebraicGeometry.Scheme.Spec_map]
    simp only [Quiver.Hom.unop_op]
    letI : AlgebraicGeometry.IsOpenImmersion leftChartDomainIso.hom := by
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator)))) := by
      infer_instance
    exact AlgebraicGeometry.IsOpenImmersion.comp _ _
  · rw [leftChart_map_eq_restriction]
    simp only [leftChart]
    simp only [ambientDecoration, AATReadingDecoration.pullback_interpretation,
      AATReadingDecoration.ofContext_interpretation,
      AlgebraicGeometry.Scheme.Hom.comp_appTop, Category.assoc]
    rw [← Category.assoc baseChartDomainIso.inv.appTop,
      ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      baseChartDomainIso.hom_inv_id,
      AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp]
    rw [architectureChartRestriction_appTop]
    simp only [Iso.inv_hom_id_assoc]

private theorem rightChart_valid :
    IsArchitectureAffineChart referenceRaw rightChart := by
  constructor
  · simp only [rightChart]
    rw [AlgebraicGeometry.Scheme.Spec_map]
    simp only [Quiver.Hom.unop_op]
    letI : AlgebraicGeometry.IsOpenImmersion rightChartDomainIso.hom := by
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator)))) := by
      infer_instance
    exact AlgebraicGeometry.IsOpenImmersion.comp _ _
  · rw [rightChart_map_eq_restriction]
    simp only [rightChart]
    simp only [ambientDecoration, AATReadingDecoration.pullback_interpretation,
      AATReadingDecoration.ofContext_interpretation,
      AlgebraicGeometry.Scheme.Hom.comp_appTop, Category.assoc]
    rw [← Category.assoc baseChartDomainIso.inv.appTop,
      ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      baseChartDomainIso.hom_inv_id,
      AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp]
    rw [architectureChartRestriction_appTop]
    simp only [Iso.inv_hom_id_assoc]

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceAtlas_valid :
    IsArchitectureAffineAtlas referenceRaw referenceAtlas := by
  constructor
  · intro i
    cases i
    · exact leftChart_valid
    · exact rightChart_valid
  · intro x
    let C := AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of AmbientRing)
      coverGenerator coverGenerator_span_eq_top
    rcases C.covers x with ⟨y, hy⟩
    generalize hi : C.idx x = i at y hy
    cases i
    · refine ⟨false, leftChartDomainIso.inv y, ?_⟩
      simpa only [referenceAtlas, leftChart,
        AlgebraicGeometry.Scheme.inv_hom_apply,
        AlgebraicGeometry.Scheme.Hom.comp_apply,
        AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op,
        AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop_f,
        C, coverGenerator_false] using hy
    · refine ⟨true, rightChartDomainIso.inv y, ?_⟩
      simpa only [referenceAtlas, rightChart,
        AlgebraicGeometry.Scheme.inv_hom_apply,
        AlgebraicGeometry.Scheme.Hom.comp_apply,
        AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op,
        AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop_f,
        C, coverGenerator_true] using hy

private abbrev leftLocalizationMap :
    CommRingCat.of AmbientRing ⟶
      CommRingCat.of (Localization.Away leftGenerator) :=
  CommRingCat.ofHom
    (algebraMap AmbientRing (Localization.Away leftGenerator))

private abbrev rightLocalizationMap :
    CommRingCat.of AmbientRing ⟶
      CommRingCat.of (Localization.Away rightGenerator) :=
  CommRingCat.ofHom
    (algebraMap AmbientRing (Localization.Away rightGenerator))

private abbrev leftOverlapMap :
    CommRingCat.of (Localization.Away leftGenerator) ⟶
      CommRingCat.of (Localization.Away overlapGenerator) :=
  CommRingCat.ofHom leftToOverlapRingHom

private abbrev rightOverlapMap :
    CommRingCat.of (Localization.Away rightGenerator) ⟶
      CommRingCat.of (Localization.Away overlapGenerator) :=
  CommRingCat.ofHom rightToOverlapRingHom

private theorem overlapGenerator_isUnit_in_pushoutTarget
    (s : PushoutCocone leftLocalizationMap rightLocalizationMap) :
    IsUnit
      ((s.inl.hom.comp
          (algebraMap AmbientRing (Localization.Away leftGenerator)))
        overlapGenerator) := by
  rw [overlapGenerator_eq, map_mul]
  apply IsUnit.mul
  · exact (IsLocalization.Away.algebraMap_isUnit leftGenerator).map s.inl.hom
  · have hy :=
      (IsLocalization.Away.algebraMap_isUnit rightGenerator).map s.inr.hom
    have hc := congrArg (fun q => q.hom rightGenerator) s.condition
    have hc' :
        s.inl.hom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator) rightGenerator) =
          s.inr.hom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator) rightGenerator) := by
      simpa only [CommRingCat.comp_apply] using hc
    change IsUnit
      (s.inl.hom
        (algebraMap AmbientRing
          (Localization.Away leftGenerator) rightGenerator))
    rw [hc']
    exact hy

private noncomputable def overlapPushoutDesc
    (s : PushoutCocone leftLocalizationMap rightLocalizationMap) :
    CommRingCat.of (Localization.Away overlapGenerator) ⟶ s.pt :=
  CommRingCat.ofHom
    (IsLocalization.Away.lift overlapGenerator
      (overlapGenerator_isUnit_in_pushoutTarget s))

private theorem overlapPushoutDesc_comp_algebraMap
    (s : PushoutCocone leftLocalizationMap rightLocalizationMap) :
    (overlapPushoutDesc s).hom.comp
        (algebraMap AmbientRing (Localization.Away overlapGenerator)) =
      s.inl.hom.comp
        (algebraMap AmbientRing (Localization.Away leftGenerator)) :=
  IsLocalization.Away.lift_comp overlapGenerator
    (overlapGenerator_isUnit_in_pushoutTarget s)

private theorem localizationSquare_isPushout :
    IsPushout leftLocalizationMap rightLocalizationMap
      leftOverlapMap rightOverlapMap := by
  refine
    { w := ?_
      isColimit' := ⟨PushoutCocone.IsColimit.mk _ overlapPushoutDesc
        ?_ ?_ ?_⟩ }
  · apply ConcreteCategory.hom_ext
    intro a
    simpa only [CommRingCat.comp_apply] using
      congrArg (fun q => q a)
        (leftToOverlapRingHom_comp_algebraMap.trans
          rightToOverlapRingHom_comp_algebraMap.symm)
  · intro s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers leftGenerator)
    change
      ((overlapPushoutDesc s).hom.comp leftToOverlapRingHom).comp
          (algebraMap AmbientRing (Localization.Away leftGenerator)) =
        s.inl.hom.comp
          (algebraMap AmbientRing (Localization.Away leftGenerator))
    rw [RingHom.comp_assoc, leftToOverlapRingHom_comp_algebraMap]
    exact overlapPushoutDesc_comp_algebraMap s
  · intro s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers rightGenerator)
    change
      ((overlapPushoutDesc s).hom.comp rightToOverlapRingHom).comp
          (algebraMap AmbientRing (Localization.Away rightGenerator)) =
        s.inr.hom.comp
          (algebraMap AmbientRing (Localization.Away rightGenerator))
    rw [RingHom.comp_assoc, rightToOverlapRingHom_comp_algebraMap]
    rw [overlapPushoutDesc_comp_algebraMap]
    exact congrArg CommRingCat.Hom.hom s.condition
  · intro s m hmLeft _hmRight
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers overlapGenerator)
    change
      m.hom.comp
          (algebraMap AmbientRing (Localization.Away overlapGenerator)) =
        (overlapPushoutDesc s).hom.comp
          (algebraMap AmbientRing (Localization.Away overlapGenerator))
    rw [← leftToOverlapRingHom_comp_algebraMap]
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    have hm := congrArg CommRingCat.Hom.hom hmLeft
    change m.hom.comp leftToOverlapRingHom = s.inl.hom at hm
    rw [hm]
    rw [RingHom.comp_assoc, leftToOverlapRingHom_comp_algebraMap,
      overlapPushoutDesc_comp_algebraMap]

private theorem localizationSquare_isPullback :
    IsPullback
      (AlgebraicGeometry.Spec.map leftOverlapMap)
      (AlgebraicGeometry.Spec.map rightOverlapMap)
      (AlgebraicGeometry.Spec.map leftLocalizationMap)
      (AlgebraicGeometry.Spec.map rightLocalizationMap) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    leftLocalizationMap rightLocalizationMap
    leftOverlapMap rightOverlapMap localizationSquare_isPushout

private theorem overlapChart_toLeft :
    overlapChartDomainIso.hom ≫
        AlgebraicGeometry.Spec.map leftOverlapMap =
      architectureChartRestriction referenceRaw overlapToLeft ≫
        leftChartDomainIso.hom := by
  simp only [overlapChartDomainIso, leftChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  change
    leftOverlapMap ≫ overlapSectionRingIso.inv =
      leftSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToLeft
  rw [← cancel_mono overlapSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact overlap_left_restriction_is_localization.symm

private theorem overlapChart_toRight :
    overlapChartDomainIso.hom ≫
        AlgebraicGeometry.Spec.map rightOverlapMap =
      architectureChartRestriction referenceRaw overlapToRight ≫
        rightChartDomainIso.hom := by
  simp only [overlapChartDomainIso, rightChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  change
    rightOverlapMap ≫ overlapSectionRingIso.inv =
      rightSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToRight
  rw [← cancel_mono overlapSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact overlap_right_restriction_is_localization.symm

private theorem referenceAtlas_pairContext_false_true :
    referenceAtlas.pairContext referenceRaw false true = overlapContext := by
  change
    Site.ContextCategoryObject.of referenceContextPreorder
        (referenceOverlap.overlap
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.base)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.left)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.right)) =
      Site.ContextCategoryObject.of referenceContextPreorder
        (AAT.AG.FiniteModel.twoPatchContext
          AAT.AG.FiniteModel.TwoPatchContextIndex.overlap)
  congr 1
  exact referenceOverlap_selected _ _ _

private theorem referenceAtlas_pairContext_true_false :
    referenceAtlas.pairContext referenceRaw true false = overlapContext := by
  change
    Site.ContextCategoryObject.of referenceContextPreorder
        (referenceOverlap.overlap
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.base)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.right)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.left)) =
      Site.ContextCategoryObject.of referenceContextPreorder
        (AAT.AG.FiniteModel.twoPatchContext
          AAT.AG.FiniteModel.TwoPatchContextIndex.overlap)
  congr 1
  exact referenceOverlap_selected _ _ _

private theorem principalArchitectureSquare_isPullback :
    IsPullback
      (architectureChartRestriction referenceRaw overlapToLeft)
      (architectureChartRestriction referenceRaw overlapToRight)
      leftChart.map rightChart.map := by
  apply localizationSquare_isPullback.of_iso'
      overlapChartDomainIso leftChartDomainIso rightChartDomainIso
      (Iso.refl ambientScheme)
  · exact overlapChart_toLeft
  · exact overlapChart_toRight
  · rfl
  · rfl

private noncomputable def falseTruePairContextIso :
    referenceAtlas.pairContext referenceRaw false true ≅ overlapContext :=
  eqToIso referenceAtlas_pairContext_false_true

private noncomputable def falseTruePairDomainIso :
    architectureChartSpec referenceRaw
        (referenceAtlas.pairContext referenceRaw false true) ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  architectureChartIso referenceRaw falseTruePairContextIso ≪≫
    overlapChartDomainIso

private theorem falseTruePairDomain_toLeft :
    falseTruePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map leftOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw false true) ≫
        leftChartDomainIso.hom := by
  simp only [falseTruePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toLeft]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      leftChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem falseTruePairDomain_toRight :
    falseTruePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map rightOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToRight referenceRaw false true) ≫
        rightChartDomainIso.hom := by
  simp only [falseTruePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toRight]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      rightChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem falseTruePair_isPullback :
    IsPullback
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToLeft referenceRaw false true))
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToRight referenceRaw false true))
      leftChart.map rightChart.map := by
  apply localizationSquare_isPullback.of_iso'
      falseTruePairDomainIso leftChartDomainIso rightChartDomainIso
      (Iso.refl ambientScheme)
  · exact falseTruePairDomain_toLeft
  · exact falseTruePairDomain_toRight
  · rfl
  · rfl

private noncomputable def trueFalsePairContextIso :
    referenceAtlas.pairContext referenceRaw true false ≅ overlapContext :=
  eqToIso referenceAtlas_pairContext_true_false

private noncomputable def trueFalsePairDomainIso :
    architectureChartSpec referenceRaw
        (referenceAtlas.pairContext referenceRaw true false) ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  architectureChartIso referenceRaw trueFalsePairContextIso ≪≫
    overlapChartDomainIso

private theorem trueFalsePairDomain_toLeft :
    trueFalsePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map rightOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw true false) ≫
        rightChartDomainIso.hom := by
  simp only [trueFalsePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toRight]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      rightChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem trueFalsePairDomain_toRight :
    trueFalsePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map leftOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToRight referenceRaw true false) ≫
        leftChartDomainIso.hom := by
  simp only [trueFalsePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toLeft]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      leftChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem trueFalsePair_isPullback :
    IsPullback
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToLeft referenceRaw true false))
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToRight referenceRaw true false))
      rightChart.map leftChart.map := by
  apply localizationSquare_isPullback.flip.of_iso'
      trueFalsePairDomainIso rightChartDomainIso leftChartDomainIso
      (Iso.refl ambientScheme)
  · exact trueFalsePairDomain_toLeft
  · exact trueFalsePairDomain_toRight
  · rfl
  · rfl

private theorem referenceAtlas_pair_isPullback
    (i j : referenceAtlas.Index) :
    IsPullback
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToLeft referenceRaw i j))
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToRight referenceRaw i j))
      (referenceAtlas.chart i).map
      (referenceAtlas.chart j).map := by
  cases i <;> cases j
  · letI : IsIso
        (architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw false false)) := by
      change IsIso
        (architectureChartIso referenceRaw
          (referenceAtlas.selfPairContextIso referenceRaw false)).hom
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (referenceAtlas.chart false).map := leftChart_valid.isOpenImmersion
    apply IsPullback.of_horiz_isIso_mono
    constructor
    exact congrArg
      (fun q => architectureChartRestriction referenceRaw q ≫ leftChart.map)
      (Subsingleton.elim _ _)
  · exact falseTruePair_isPullback
  · exact trueFalsePair_isPullback
  · letI : IsIso
        (architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw true true)) := by
      change IsIso
        (architectureChartIso referenceRaw
          (referenceAtlas.selfPairContextIso referenceRaw true)).hom
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (referenceAtlas.chart true).map := rightChart_valid.isOpenImmersion
    apply IsPullback.of_horiz_isIso_mono
    constructor
    exact congrArg
      (fun q => architectureChartRestriction referenceRaw q ≫ rightChart.map)
      (Subsingleton.elim _ _)

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceOverlapPresentation :
    ArchitectureOverlapPresentation referenceRaw referenceAtlas where
  comparison i j := (referenceAtlas_pair_isPullback i j).isoPullback

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceOverlapPresentation_valid :
    IsArchitectureOverlapPresentation
      referenceRaw referenceOverlapPresentation := by
  constructor
  · intro i j
    exact IsPullback.isoPullback_hom_fst
      (referenceAtlas_pair_isPullback i j)
  · intro i j
    exact IsPullback.isoPullback_hom_snd
      (referenceAtlas_pair_isPullback i j)

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceScheme :
    StandardArchitectureScheme referenceRaw :=
  StandardArchitectureScheme.ofPresentation
    referenceRaw ambientScheme ambientDecoration
    referenceAtlas referenceAtlas_valid
    referenceOverlapPresentation
    referenceOverlapPresentation_valid

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceScheme_eq :
    referenceScheme =
      StandardArchitectureScheme.ofPresentation
        referenceRaw ambientScheme ambientDecoration
        referenceAtlas referenceAtlas_valid
        referenceOverlapPresentation
        referenceOverlapPresentation_valid :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftIndex : referenceScheme.atlas.Index :=
  false

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightIndex : referenceScheme.atlas.Index :=
  true

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem leftIndex_ne_rightIndex : leftIndex ≠ rightIndex := by
  change (false : Bool) ≠ true
  decide

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem index_cases (i : referenceScheme.atlas.Index) :
    i = leftIndex ∨ i = rightIndex := by
  cases i <;> simp [leftIndex, rightIndex]

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceScheme_underlying :
    referenceScheme.underlying = ambientScheme :=
  rfl

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem left_chart_context :
    (referenceScheme.atlas.chart leftIndex).context = leftContext :=
  rfl

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem right_chart_context :
    (referenceScheme.atlas.chart rightIndex).context = rightContext :=
  rfl

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem chart_contexts_ne :
    (referenceScheme.atlas.chart leftIndex).context ≠
      (referenceScheme.atlas.chart rightIndex).context := by
  rw [left_chart_context, right_chart_context]
  intro h
  have hctx := congrArg Site.ContextCategoryObject.ctx h
  have heq := congrArg
    (fun W : Site.ArchitectureContext AAT.AG.FiniteModel.corePackage.object =>
      (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) hctx
  injection heq with _ hindex
  exact AAT.AG.FiniteModel.TwoPatchContextIndex.noConfusion hindex

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem left_chart_map :
    (referenceScheme.atlas.chart leftIndex).map =
      leftChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator))).op :=
  rfl

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem right_chart_map :
    (referenceScheme.atlas.chart rightIndex).map =
      rightChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator))).op :=
  rfl

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map :=
  referenceScheme.atlasValid.chart_valid leftIndex |>.isOpenImmersion

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map :=
  referenceScheme.atlasValid.chart_valid rightIndex |>.isOpenImmersion

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem twoChart_jointlyCovers :
    ⨆ i,
        ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange =
      ⊤ :=
  referenceScheme.atlas.jointlyCovers referenceRaw referenceScheme.atlasValid

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_chart_not_isIso :
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map := by
  intro h
  have hChart : IsIso leftChart.map := h
  have hcomp : IsIso
      (architectureChartRestriction referenceRaw leftToBase ≫
        baseChartDomainIso.hom) := by
    rw [← leftChart_map_eq_restriction]
    exact hChart
  letI := hcomp
  haveI : IsIso
      (architectureChartRestriction referenceRaw leftToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_right _ baseChartDomainIso.hom
  haveI : IsIso
      ((architectureChartRestriction referenceRaw leftToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext)).hom) :=
    inferInstance
  haveI : IsIso
      ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom ≫
        sheafifiedRestriction referenceRaw leftToBase) := by
    rw [← architectureChartRestriction_appTop]
    infer_instance
  haveI : IsIso (sheafifiedRestriction referenceRaw leftToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_left
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).hom _
  exact left_restriction_not_isIso inferInstance

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_chart_not_isIso :
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map := by
  intro h
  have hChart : IsIso rightChart.map := h
  have hcomp : IsIso
      (architectureChartRestriction referenceRaw rightToBase ≫
        baseChartDomainIso.hom) := by
    rw [← rightChart_map_eq_restriction]
    exact hChart
  letI := hcomp
  haveI : IsIso
      (architectureChartRestriction referenceRaw rightToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_right _ baseChartDomainIso.hom
  haveI : IsIso
      ((architectureChartRestriction referenceRaw rightToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext)).hom) :=
    inferInstance
  haveI : IsIso
      ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom ≫
        sheafifiedRestriction referenceRaw rightToBase) := by
    rw [← architectureChartRestriction_appTop]
    infer_instance
  haveI : IsIso (sheafifiedRestriction referenceRaw rightToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_left
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).hom _
  exact right_restriction_not_isIso inferInstance

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem pair_context :
    referenceScheme.atlas.pairContext
        referenceRaw leftIndex rightIndex =
      overlapContext :=
  referenceAtlas_pairContext_false_true

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def actualOverlapIso :
    referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  (referenceScheme.overlap_is_actual_pullback
      referenceRaw leftIndex rightIndex).symm ≪≫
    eqToIso (by rw [pair_context]) ≪≫
    overlapChartDomainIso

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem actualOverlapIso_eq :
    actualOverlapIso =
      (referenceScheme.overlap_is_actual_pullback
          referenceRaw leftIndex rightIndex).symm ≪≫
        eqToIso (by rw [pair_context]) ≪≫
        overlapChartDomainIso :=
  rfl

private theorem overlapGenerator_ne_zero : overlapGenerator ≠ 0 := by
  rw [overlapGenerator_eq]
  apply mul_ne_zero
  · simpa [leftGenerator, coordinate] using
      (MvPolynomial.X_ne_zero (R := Int) ())
  · intro h
    have h' := congrArg
      (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
    norm_num [rightGenerator, coordinate] at h'

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem actualOverlap_nonempty :
    Nonempty
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) := by
  letI : Nontrivial (Localization.Away overlapGenerator) :=
    Function.Injective.nontrivial
      (IsLocalization.injective (Localization.Away overlapGenerator)
        (powers_le_nonZeroDivisors_of_noZeroDivisors overlapGenerator_ne_zero))
  let x := Classical.choice
    (inferInstance : Nonempty
      (AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator))))
  exact ⟨actualOverlapIso.inv x⟩

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem decoration_overlap :
    sheafifiedRestriction referenceRaw
        (referenceScheme.atlas.pairToLeft
            referenceRaw leftIndex rightIndex ≫
          (referenceScheme.atlas.chart leftIndex).contextHom) =
      sheafifiedRestriction referenceRaw
        (referenceScheme.atlas.pairToRight
            referenceRaw leftIndex rightIndex ≫
          (referenceScheme.atlas.chart rightIndex).contextHom) :=
  referenceScheme.atlas.decoration_overlap
    referenceRaw leftIndex rightIndex

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem actual_triple_cocycle :
    ∀ i j l : referenceScheme.atlas.Index,
      referenceScheme.atlas.actualTripleToLeft
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart i).map =
        referenceScheme.atlas.actualTripleToMiddle
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart j).map ∧
      referenceScheme.atlas.actualTripleToMiddle
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart j).map =
        referenceScheme.atlas.actualTripleToRight
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart l).map := by
  intro i j l
  exact referenceScheme.atlas.actualTriple_cocycle referenceRaw i j l


end
end AAT.AG.Examples.StandardGeometryReferenceModels
