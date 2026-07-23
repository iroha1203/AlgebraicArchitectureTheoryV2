import Formal.AG.Examples.StandardGeometryReference.EquationGeometry
import Mathlib.RingTheory.RingHom.Flat

/-!
# Standard geometry reference: negative fixtures

This module owns SD6: the duplicate atlas, collapsed and unit ideals,
non-flat coefficient map, and reflected chart fixtures.

Each negative fixture preserves the surrounding concrete model while changing
exactly the datum needed to expose one failure reason: duplicate coverage,
collapsed strictness, empty unit-ideal geometry, non-flat coefficients, or
reflected interpretation. Taking an arbitrary invalid atlas, chart, ideal, or
coefficient map was rejected because it would not identify the failed clause
inside the fixed model.
-/

set_option maxHeartbeats 4000000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section

/-!
## R7 negative fixtures

The duplicate atlas and reflected chart keep the underlying concrete maps visible while
isolating the failed coverage or interpretation clause.  Collapsed ideals, the unit ideal,
and `Int → ZMod 2` provide separate negative witnesses for strictness, nonempty closed
geometry, and flat coefficient change.
-/

/-- A negative atlas whose two entries both reuse the left chart. -/
noncomputable def duplicateLeftAtlas :
    ArchitectureAffineAtlas referenceRaw
      referenceScheme.underlying referenceScheme.decoration where
  Index := Bool
  chart _ := leftChart

/-- Both entries of the duplicate atlas are the fixed left chart. -/
@[simp] theorem duplicateLeftAtlas_chart (i : Bool) :
    duplicateLeftAtlas.chart i = leftChart :=
  rfl

private theorem leftChart_normalized_appTop :
    ambientGlobalSectionsIso.inv ≫
        leftChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext)).hom ≫
        leftSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away leftGenerator)) := by
  simp [leftChart, ambientGlobalSectionsIso, ambientScheme_eq,
    AlgebraicGeometry.Scheme.Spec_map]

private theorem zeroPoint_normalized_appTop :
    zeroPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom (evaluationRingHom 0) := by
  simpa only [zeroPoint, evaluationPoint, referenceScheme_underlying,
    ambientScheme_eq, ambientGlobalSectionsIso,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (evaluationRingHom 0))

/-- The zero evaluation point does not factor through the left principal open. -/
theorem zeroPoint_not_factors_through_leftChart :
    ¬ ∃ lift : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
        leftChart.domain,
      lift ≫ leftChart.map = zeroPoint := by
  rintro ⟨lift, hfactor⟩
  let φ : CommRingCat.of (Localization.Away leftGenerator) ⟶
      CommRingCat.of Int :=
    leftSectionRingIso.inv ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw leftContext)).inv ≫
      lift.appTop ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom
  have happ := congrArg AlgebraicGeometry.Scheme.Hom.appTop hfactor
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at happ
  have hcomp :
      CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away leftGenerator)) ≫ φ =
        CommRingCat.ofHom (evaluationRingHom 0) := by
    rw [← leftChart_normalized_appTop]
    simp only [φ, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc leftChart.map.appTop lift.appTop
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom]
    rw [happ, zeroPoint_normalized_appTop]
    simp
  have hcoord := ConcreteCategory.congr_hom hcomp coordinate
  change φ (algebraMap AmbientRing
      (Localization.Away leftGenerator) coordinate) =
    evaluationRingHom 0 coordinate at hcoord
  have hunit : IsUnit
      (φ (algebraMap AmbientRing
        (Localization.Away leftGenerator) coordinate)) := by
    apply IsUnit.map φ.hom
    rw [← leftGenerator_eq]
    exact IsLocalization.Away.algebraMap_isUnit leftGenerator
  have hzero : φ (algebraMap AmbientRing
      (Localization.Away leftGenerator) coordinate) = 0 := by
    exact hcoord.trans (by simp [evaluationRingHom, coordinate])
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

/-- The atlas duplicating the left chart fails pointwise coverage. -/
theorem duplicateLeftAtlas_not_valid :
    ¬ IsArchitectureAffineAtlas referenceRaw duplicateLeftAtlas := by
  intro hvalid
  have hsurjective : Function.Surjective leftChart.map := by
    intro x
    rcases hvalid.covers x with ⟨i, y, hy⟩
    exact ⟨y, by simpa only [duplicateLeftAtlas_chart] using hy⟩
  letI : AlgebraicGeometry.IsOpenImmersion leftChart.map := by
    simpa only [referenceScheme, referenceAtlas] using
      left_chart_isOpenImmersion
  have hrange : leftChart.map.opensRange = ⊤ := by
    apply top_unique
    intro x _
    exact AlgebraicGeometry.Scheme.Hom.mem_opensRange.mpr
      (hsurjective x)
  letI : IsIso leftChart.map :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top leftChart.map hrange
  apply zeroPoint_not_factors_through_leftChart
  exact ⟨zeroPoint ≫ inv leftChart.map, by simp⟩

/-- The strong reading collapsed to the weak reading. -/
noncomputable def collapsedStrongReading :
    ClosedEquationalLawReading referenceRaw referenceScheme
      weakLawEquationCore :=
  weakReading

/-- The collapsed strong reading is definitionally the weak reading. -/
@[simp] theorem collapsedStrongReading_eq :
    collapsedStrongReading = weakReading :=
  rfl

/-- Collapsing the readings destroys strict ideal inclusion. -/
theorem collapsedIdeal_not_strict :
    ¬ lawGeneratedIdealSheaf
        referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed <
      lawGeneratedIdealSheaf
        referenceRaw referenceScheme
        collapsedStrongReading weakReading_valid weakReading_requiredClosed := by
  simpa only [collapsedStrongReading] using
    (lt_irrefl (lawGeneratedIdealSheaf
      referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed))

/-- The unit ideal used as an empty closed-subscheme negative fixture. -/
noncomputable def unitIdealFixture :
    referenceScheme.underlying.IdealSheafData :=
  ⊤

/-- The unit-ideal fixture is the top ideal sheaf. -/
@[simp] theorem unitIdealFixture_eq :
    unitIdealFixture = ⊤ :=
  rfl

/-- The closed subscheme cut out by the unit ideal is empty. -/
theorem unitIdealFixture_subscheme_empty :
    IsEmpty unitIdealFixture.subscheme := by
  rw [unitIdealFixture_eq]
  infer_instance

/-- The quotient map to `ZMod 2`, used as a non-flat coefficient map. -/
noncomputable def nonFlatCoefficientMap :
    Int →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

/-- The negative coefficient map is the integer quotient to `ZMod 2`. -/
@[simp] theorem nonFlatCoefficientMap_eq :
    nonFlatCoefficientMap = Int.castRingHom (ZMod 2) :=
  rfl

/-- The quotient `Int → ZMod 2` is not flat, detected by two-torsion. -/
theorem nonFlatCoefficientMap_not_flat :
    ¬ nonFlatCoefficientMap.Flat := by
  intro hflat
  letI : Module Int (ZMod 2) := nonFlatCoefficientMap.toAlgebra.toModule
  haveI : Module.Flat Int (ZMod 2) := by
    exact hflat
  have hinjective : IsSMulRegular (ZMod 2) (2 : Int) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ZMod 2)
      (LinearMap.toSpanSingleton Int Int 2)
      (IsRegular.of_ne_zero' (by norm_num : (2 : Int) ≠ 0)).right
    have h2 : (fun (x : ZMod 2) => (2 : Int) • x) =
        ((TensorProduct.lid Int (ZMod 2)) ∘ₗ
          (LinearMap.rTensor (ZMod 2) (LinearMap.toSpanSingleton Int Int 2)) ∘ₗ
          (TensorProduct.lid Int (ZMod 2)).symm) := by
      ext
      simp
      change (2 : ZMod 2) * _ = (algebraMap Int (ZMod 2) 2) * _
      rfl
    rw [IsSMulRegular, h2]
    simp [h, LinearEquiv.injective]
  have hone : (1 : ZMod 2) = 0 := by
    apply hinjective
    change (2 : ZMod 2) = 0
    decide
  norm_num at hone

private noncomputable def coordinateReflectionAlgHom :
    AmbientRing →ₐ[Int] AmbientRing :=
  MvPolynomial.aeval (fun _ : Unit => rightGenerator)

private theorem coordinateReflectionAlgHom_involutive :
    coordinateReflectionAlgHom.comp coordinateReflectionAlgHom =
      AlgHom.id Int AmbientRing := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  simp [coordinateReflectionAlgHom, rightGenerator, coordinate]

/-- The involution of `Int[x]` sending `x` to `1 - x`. -/
noncomputable def coordinateReflection :
    AmbientRing ≃+* AmbientRing :=
  (AlgEquiv.ofAlgHom coordinateReflectionAlgHom coordinateReflectionAlgHom
    coordinateReflectionAlgHom_involutive
    coordinateReflectionAlgHom_involutive).toRingEquiv

/-- Coordinate reflection sends `x` to `1 - x`. -/
@[simp] theorem coordinateReflection_coordinate :
    coordinateReflection coordinate = rightGenerator := by
  simp [coordinateReflection, coordinateReflectionAlgHom, coordinate]

/-- Coordinate reflection sends `1 - x` back to `x`. -/
@[simp] theorem coordinateReflection_rightGenerator :
    coordinateReflection rightGenerator = coordinate := by
  simp [coordinateReflection, coordinateReflectionAlgHom,
    rightGenerator, coordinate]

/-- The right-localization map precomposed with coordinate reflection. -/
noncomputable def reflectedRightRingHom :
    AmbientRing →+* Localization.Away rightGenerator :=
  (algebraMap AmbientRing
    (Localization.Away rightGenerator)).comp
      coordinateReflection.toRingHom

/-- The reflected right-localization map sends `x` to the image of `1 - x`. -/
@[simp] theorem reflectedRightRingHom_coordinate :
    reflectedRightRingHom coordinate =
      algebraMap AmbientRing
        (Localization.Away rightGenerator) rightGenerator := by
  rw [reflectedRightRingHom, RingHom.comp_apply,
    show coordinateReflection.toRingHom coordinate =
      coordinateReflection coordinate from rfl,
    coordinateReflection_coordinate]

/-- A right-context chart whose open map uses reflected coordinates. -/
noncomputable def brokenRightChart :
    ArchitectureAffineChart referenceRaw
      referenceScheme.underlying referenceScheme.decoration where
  context := rightContext
  contextHom := rightToBase
  map :=
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom reflectedRightRingHom).op

/-- The broken chart retains the fixed right context. -/
@[simp] theorem brokenRightChart_context :
    brokenRightChart.context = rightContext :=
  rfl

/-- The broken chart map is the reflected right-localization map. -/
@[simp] theorem brokenRightChart_map :
    brokenRightChart.map =
      rightChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom reflectedRightRingHom).op :=
  rfl

private theorem brokenRightChart_normalized_appTop :
    baseSectionRingIso.inv ≫
        ambientDecoration.interpretation ≫
        brokenRightChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext)).hom ≫
        rightSectionRingIso.hom =
      CommRingCat.ofHom reflectedRightRingHom := by
  simp [brokenRightChart, AlgebraicGeometry.Scheme.Spec_map]

/-- Coordinate reflection preserves the open-immersion property of the right chart. -/
theorem brokenRightChart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion brokenRightChart.map := by
  simp only [brokenRightChart]
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp only [Quiver.Hom.unop_op]
  letI : AlgebraicGeometry.IsOpenImmersion rightChartDomainIso.hom := by
    infer_instance
  let reflectionMap : CommRingCat.of AmbientRing ⟶
      CommRingCat.of AmbientRing :=
    CommRingCat.ofHom coordinateReflection.toRingHom
  let localizationMap : CommRingCat.of AmbientRing ⟶
      CommRingCat.of (Localization.Away rightGenerator) :=
    CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away rightGenerator))
  have hreflected : CommRingCat.ofHom reflectedRightRingHom =
      reflectionMap ≫ localizationMap := by
    dsimp [reflectionMap, localizationMap, reflectedRightRingHom]
  rw [hreflected, AlgebraicGeometry.Spec.map_comp]
  letI : IsIso reflectionMap :=
    (ConcreteCategory.isIso_iff_bijective reflectionMap).2
      coordinateReflection.bijective
  letI : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map localizationMap) := by
    infer_instance
  letI : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map reflectionMap) := by
    infer_instance
  exact AlgebraicGeometry.IsOpenImmersion.comp _ _

private theorem reflectedRightGenerator_ne_zero : rightGenerator ≠ 0 := by
  intro h
  have h' := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
  norm_num [rightGenerator, coordinate] at h'

/-- The reflected chart map disagrees with the fixed right-context interpretation. -/
theorem brokenRightChart_interpretation_ne :
    sheafifiedRestriction referenceRaw brokenRightChart.contextHom ≠
      referenceScheme.decoration.interpretation ≫
        brokenRightChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing
            referenceRaw brokenRightChart.context)).hom := by
  intro hinterpretation
  have hinterpretation' :
      sheafifiedRestriction referenceRaw rightToBase =
        ambientDecoration.interpretation ≫
          brokenRightChart.map.appTop ≫
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw rightContext)).hom := by
    simpa only [brokenRightChart, referenceScheme] using hinterpretation
  have hmaps :
      CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away rightGenerator)) =
        CommRingCat.ofHom reflectedRightRingHom := by
    calc
      CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away rightGenerator)) =
          baseSectionRingIso.inv ≫
            sheafifiedRestriction referenceRaw rightToBase ≫
            rightSectionRingIso.hom :=
        right_restriction_is_localization.symm
      _ = baseSectionRingIso.inv ≫
            ambientDecoration.interpretation ≫
            brokenRightChart.map.appTop ≫
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing referenceRaw rightContext)).hom ≫
            rightSectionRingIso.hom := by
        rw [hinterpretation']
        rfl
      _ = CommRingCat.ofHom reflectedRightRingHom :=
        brokenRightChart_normalized_appTop
  have hcoord := ConcreteCategory.congr_hom hmaps coordinate
  change algebraMap AmbientRing
      (Localization.Away rightGenerator) coordinate =
    reflectedRightRingHom coordinate at hcoord
  rw [reflectedRightRingHom_coordinate] at hcoord
  have hinjective : Function.Injective
      (algebraMap AmbientRing (Localization.Away rightGenerator)) :=
    IsLocalization.injective (Localization.Away rightGenerator)
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        reflectedRightGenerator_ne_zero)
  have hsource : coordinate = rightGenerator := hinjective hcoord
  have heval := congrArg (evaluationRingHom 0) hsource
  simp [evaluationRingHom, coordinate, rightGenerator] at heval

/-- The reflected right chart fails the interpretation clause of chart validity. -/
theorem brokenRightChart_not_valid :
    ¬ IsArchitectureAffineChart referenceRaw brokenRightChart := by
  intro hvalid
  exact brokenRightChart_interpretation_ne hvalid.interpretation_compatible

end
end AAT.AG.Examples.StandardGeometryReferenceModels
