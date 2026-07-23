import Formal.AG.Examples.StandardGeometryReference.EquationGeometry
import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.ReadingFunctoriality.CoefficientGeometry
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Standard geometry reference: coefficient change

This module owns SD5: flat coefficient change, transported equation
geometries, and the coefficient-change comparison square.

The nontrivial coefficient-change definitions carry declaration-local
`Implementation notes` below. They adopt the free flat extension
`Int → Polynomial Int`, the generic scheme/reading base-change APIs, and the
induced mixed square; arbitrary flatness data, reconstructed atlases, and
external comparison morphisms are rejected there.
-/

set_option maxHeartbeats 4000000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section

/-! ## R6: coefficient change -/

/-!
### Implementation notes

The changed scheme, readings, generated ideals, chart squares, and lawful-locus maps are obtained
from the merged generic coefficient APIs. Strictness is detected by an actual point of the scheme
pullback above the source one-point, while non-isomorphism of the ambient projection is detected by
two coefficient-evaluation points that agree on all source sections and separate the new
polynomial coefficient. The mixed law square follows by composing with the monomorphic weak
ambient immersion and applying the two generic ambient-triangle theorems.
-/

/-- The canonical flat coefficient inclusion from integers to integer polynomials.

## Implementation notes

Flatness is constructed from the free `Int`-module structure of `Polynomial Int`; no
caller-supplied flatness certificate or alternate coefficient map is accepted.
-/
noncomputable def coefficientChange :
    FlatCoefficientChange Int (Polynomial Int) where
  hom := Polynomial.C
  flat := by
    change (algebraMap Int (Polynomial Int)).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_free

/-- The coefficient map is definitionally the constant-polynomial inclusion. -/
@[simp] theorem coefficientChange_hom :
    coefficientChange.hom = Polynomial.C :=
  rfl

/-- The polynomial variable witnesses failure of surjectivity. -/
theorem coefficientChange_not_surjective :
    ¬ Function.Surjective coefficientChange.hom := by
  intro hsurjective
  rcases hsurjective Polynomial.X with ⟨z, hz⟩
  have hcoeff := congrArg (fun p : Polynomial Int => p.coeff 1) hz
  simp only [coefficientChange, Polynomial.coeff_C,
    Polynomial.coeff_X] at hcoeff
  norm_num at hcoeff

/-- Scalar extension preserves the finite matching limits of the selected reference site.

## Implementation notes

The instance is discharged from the already constructed finite cover-arrow and relation
instances, followed by the generic finite-multicospan preservation theorem.
-/
noncomputable instance coefficientChange_hasSheafCompose :
    referenceSite.topology.HasSheafCompose
      (coefficientChange.coefficientExtension :
        AATCommAlgCat.{0, 0} Int ⥤
          AATCommAlgCat.{0, 0} (Polynomial Int)) := by
  letI : ∀ (X : referenceSite.category)
      (S : referenceSite.topology.Cover X)
      (P : referenceSite.categoryᵒᵖ ⥤ AATCommAlgCat.{0, 0} Int),
      PreservesLimit (S.index P).multicospan
        (coefficientChange.coefficientExtension :
          AATCommAlgCat.{0, 0} Int ⥤
            AATCommAlgCat.{0, 0} (Polynomial Int)) := by
    intro X S P
    classical
    letI : Fintype S.Arrow := Fintype.ofFinite S.Arrow
    letI : Fintype S.Relation := Fintype.ofFinite S.Relation
    letI : Fintype S.shape.L := Fintype.ofFinite S.Arrow
    letI : Fintype S.shape.R := Fintype.ofFinite S.Relation
    letI : DecidableEq S.shape.L := Classical.decEq _
    letI : DecidableEq S.shape.R := Classical.decEq _
    letI : FinCategory (WalkingMulticospan S.shape) := by
      infer_instance
    infer_instance
  exact CategoryTheory.hasSheafCompose_of_preservesMulticospan _ _

/-- The standard scheme obtained by the canonical generic coefficient base change.

## Implementation notes

This definition reuses `StandardArchitectureScheme.baseChange`; the changed atlas, overlaps,
decoration, and projection are not reconstructed inside the fixture.
-/
noncomputable def coefficientChangedScheme :
    StandardArchitectureScheme
      (referenceRaw.baseChange coefficientChange.hom) :=
  referenceScheme.baseChange referenceRaw coefficientChange

/-- The changed scheme is fixed to the generic base-change constructor. -/
@[simp] theorem coefficientChangedScheme_eq :
    coefficientChangedScheme =
      referenceScheme.baseChange referenceRaw coefficientChange :=
  rfl

/-- The weak reading transported by the generic semantic-core coefficient construction.

## Implementation notes

The target equations are the source equations sent through the actual base-change projection.
-/
noncomputable def coefficientChangedWeakReading :
    ClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme weakLawEquationCore :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

/-- The changed weak reading is fixed to `baseChangeOfSemanticCore`. -/
@[simp] theorem coefficientChangedWeakReading_eq :
    coefficientChangedWeakReading =
      ClosedEquationalLawReading.baseChangeOfSemanticCore
        referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge coefficientChange :=
  rfl

/-- The strong reading transported by the generic semantic-core coefficient construction.

## Implementation notes

The target equations are the source equations sent through the actual base-change projection.
-/
noncomputable def coefficientChangedStrongReading :
    ClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme strongLawEquationCore :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

/-- The changed strong reading is fixed to `baseChangeOfSemanticCore`. -/
@[simp] theorem coefficientChangedStrongReading_eq :
    coefficientChangedStrongReading =
      ClosedEquationalLawReading.baseChangeOfSemanticCore
        referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge coefficientChange :=
  rfl

/-- The transported weak reading satisfies the closed-equational reading laws. -/
theorem coefficientChangedWeakReading_valid :
    IsClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

/-- The transported strong reading satisfies the closed-equational reading laws. -/
theorem coefficientChangedStrongReading_valid :
    IsClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

/-- Every required weak law remains closed after coefficient change. -/
theorem coefficientChangedWeakReading_requiredClosed :
    RequiredClosed
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

/-- Every required strong law remains closed after coefficient change. -/
theorem coefficientChangedStrongReading_requiredClosed :
    RequiredClosed
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

/-- The changed weak generated ideal is the generic pullback of the source weak ideal. -/
theorem weakIdeal_baseChange :
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed :=
  lawGeneratedIdealSheaf_baseChange_ofSemanticCore
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
      coefficientChange

/-- The changed strong generated ideal is the generic pullback of the source strong ideal. -/
theorem strongIdeal_baseChange :
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed :=
  lawGeneratedIdealSheaf_baseChange_ofSemanticCore
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
      coefficientChange

/-- The coefficient-changed left chart forms the actual pullback square. -/
theorem leftChart_baseChange_isPullback :
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map :=
  referenceScheme.baseChangedChart_isPullback
    referenceRaw coefficientChange leftIndex

/-- The coefficient-changed right chart forms the actual pullback square. -/
theorem rightChart_baseChange_isPullback :
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map :=
  referenceScheme.baseChangedChart_isPullback
    referenceRaw coefficientChange rightIndex

/-- The changed weak-to-strong inclusion reuses the source law and atom maps.

## Implementation notes

Only the ambient raw system, scheme, and readings change; the generator indexing maps remain
definitionally those of `weakToStrong`.
-/
def coefficientChangedWeakToStrong :
    ClosedEquationalLawInclusion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme
      coefficientChangedWeakReading
      coefficientChangedStrongReading where
  lawMap := weakToStrong.lawMap
  atomMap := weakToStrong.atomMap

/-- The changed inclusion has the source law-index map. -/
@[simp] theorem coefficientChangedWeakToStrong_lawMap :
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap :=
  rfl

/-- The changed inclusion has the source atom map. -/
@[simp] theorem coefficientChangedWeakToStrong_atomMap :
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap :=
  rfl

private theorem sourceGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    semanticCoreGlobalEquation
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
          PUnit.unit a =
      semanticCoreGlobalEquation
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
          PUnit.unit (weakToStrongAtomMap a) := by
  apply (ConcreteCategory.bijective_of_isIso
    ambientGlobalSectionsIso.hom).1
  rw [weakGlobalEquation_eq, strongGlobalEquation_eq]
  cases a <;> simp [weakToStrongAtomMap]

private theorem coefficientChangedGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    baseChangedSemanticCoreGlobalEquation
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
          coefficientChange PUnit.unit a =
      baseChangedSemanticCoreGlobalEquation
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
          coefficientChange PUnit.unit (weakToStrongAtomMap a) := by
  exact congrArg
    (referenceScheme.baseChangeMap referenceRaw coefficientChange).appTop
    (sourceGlobalEquation_atomMap a)

/-- The changed inclusion preserves required laws, coordinates, and semantics. -/
theorem coefficientChangedWeakToStrong_valid :
    IsClosedEquationalLawInclusion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakToStrong where
  required_map := fun i hi => by
    simpa [coefficientChangedWeakToStrong] using hi
  closed_map := by
    intro i _
    change coefficientChangedWeakToStrong.lawMap i ∈
      (Set.univ : Set strongLawEquationCore.Index)
    exact Set.mem_univ _
  selected_map := by
    intro _V i _
    change coefficientChangedWeakToStrong.lawMap i ∈
      (Set.univ : Set strongLawEquationCore.Index)
    exact Set.mem_univ _
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [coefficientChangedWeakReading,
      coefficientChangedStrongReading,
      ClosedEquationalLawReading.baseChangeOfSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections_coordinate,
      coefficientChangedWeakToStrong, weakToStrong_atomMap]
    exact congrArg
      (coefficientChangedScheme.underlying.presheaf.map
        (homOfLE le_top).op)
      (coefficientChangedGlobalEquation_atomMap a)
  semantic_monotone := by
    intro T s i hs
    cases i
    change (ClosedEquationalLawReading.baseChangeOfSemanticCore
      referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
        coefficientChange).geometric.HoldsOn s PUnit.unit
    rw [ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff]
    change (ClosedEquationalLawReading.baseChangeOfSemanticCore
      referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
        coefficientChange).geometric.HoldsOn s PUnit.unit at hs
    rw [ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff]
      at hs
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge).HoldsOn
        (s ≫ referenceScheme.baseChangeMap
          referenceRaw coefficientChange) PUnit.unit
    rw [GeometricLawReading.ofSemanticCore_holdsOn]
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge).HoldsOn
        (s ≫ referenceScheme.baseChangeMap
          referenceRaw coefficientChange) PUnit.unit at hs
    rw [GeometricLawReading.ofSemanticCore_holdsOn] at hs
    intro a
    rw [sourceGlobalEquation_atomMap]
    exact hs (weakToStrongAtomMap a)

/-- The canonical changed strong-locus to weak-locus comparison.

## Implementation notes

The map is created directly by `lawfulClosedSubschemeMap`; no auxiliary comparison morphism is
accepted by the fixture.
-/
noncomputable def coefficientChangedLawComparison :
    lawfulClosedSubscheme
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ⟶
      lawfulClosedSubscheme
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed :=
  lawfulClosedSubschemeMap
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

/-- The changed comparison is fixed to the generic lawful-subscheme map. -/
@[simp] theorem coefficientChangedLawComparison_eq :
    coefficientChangedLawComparison =
      lawfulClosedSubschemeMap
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading_valid
        coefficientChangedStrongReading_valid
        coefficientChangedWeakReading_requiredClosed
        coefficientChangedStrongReading_requiredClosed
        coefficientChangedWeakToStrong
        coefficientChangedWeakToStrong_valid :=
  rfl

/-- The changed law comparison is a closed immersion. -/
theorem coefficientChangedLawComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      coefficientChangedLawComparison :=
  lawfulClosedSubschemeMap_isClosedImmersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

/-- The changed comparison commutes with the changed ambient immersions. -/
theorem coefficientChangedLawComparison_immersion :
    coefficientChangedLawComparison ≫
        lawfulClosedImmersion
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme
          coefficientChangedWeakReading
          coefficientChangedWeakReading_valid
          coefficientChangedWeakReading_requiredClosed =
      lawfulClosedImmersion
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed :=
  lawfulClosedSubschemeMap_immersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

private def liftedPolynomialEval (n : Int) :
    ULift.{0, 0} (Polynomial Int) →+* Int :=
  (Polynomial.evalRingHom n).comp ULift.ringEquiv.toRingHom

private theorem ambientGlobalSectionsIso_unit_r6
    (x : referenceRaw.rawAlgebra baseContext) :
    ambientGlobalSectionsIso.hom
        (ambientDecoration.interpretation
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x := by
  letI := canonical_component_isIso baseContext
  simp only [ambientGlobalSectionsIso, ambientDecoration,
    AATReadingDecoration.pullback_interpretation,
    AATReadingDecoration.ofContext_interpretation,
    baseChartDomainIso, AlgebraicGeometry.Scheme.Spec.mapIso_inv]
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing)).hom
        (((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv ≫
          (AlgebraicGeometry.Scheme.Spec.map
            baseSectionRingIso.hom.op).appTop)
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp only [CommRingCat.comp_apply]
  have hΓ := congrArg
    (fun q => q.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).inv
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)))
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      baseSectionRingIso.hom)
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of AmbientRing)).hom
        ((AlgebraicGeometry.Spec.map baseSectionRingIso.hom).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) =
      baseSectionRingIso.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) at hΓ
  calc
    _ = baseSectionRingIso.hom
        ((sheafificationUnitAlgHom referenceRaw baseContext) x) := by
      simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply,
        Quiver.Hom.unop_op] using hΓ
    _ = baseRawAlgebraIso.hom x := by
      change baseRawAlgebraIso.hom
          ((inv (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
            ((referenceRaw.toRingedSite.canonical.app
              (op baseContext)).right x)) = _
      have hcancel := congrArg
        (fun q => q x)
        (IsIso.hom_inv_id
          (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
      rw [show (inv (referenceRaw.toRingedSite.canonical.app
          (op baseContext)).right)
          ((referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right x) = x by
        simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel]

private theorem evaluationPoint_normalized_appTop_r6 (n : Int) :
    (evaluationPoint n).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom (evaluationRingHom n) := by
  simpa only [evaluationPoint, referenceScheme_underlying, ambientScheme_eq,
    ambientGlobalSectionsIso, AlgebraicGeometry.Scheme.Spec_map,
    Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (evaluationRingHom n))

private noncomputable def coefficientEvaluationPoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      AlgebraicGeometry.Spec
        (CommRingCat.of (ULift.{0, 0} (Polynomial Int))) :=
  AlgebraicGeometry.Scheme.Spec.map
    (CommRingCat.ofHom (liftedPolynomialEval n)).op

private theorem coefficientOnePoint_square (n : Int) :
    onePoint ≫ referenceScheme.coefficientStructureMap referenceRaw =
      coefficientEvaluationPoint n ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom coefficientChange.liftedHom).op := by
  apply (AlgebraicGeometry.ΓSpec.adjunction.homEquiv
    (AlgebraicGeometry.Spec (CommRingCat.of Int))
    (op (CommRingCat.of (ULift Int)))).symm.injective
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
  simp [onePoint, evaluationPoint,
    StandardArchitectureScheme.coefficientStructureMap,
    coefficientEvaluationPoint]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  let oldObject :=
    referenceRaw.toRingedSite.structureSheaf.val.obj
      (op referenceScheme.decoration.context)
  have hcoefficient :
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift Int))).inv ≫
          (referenceScheme.coefficientStructureMap referenceRaw).appTop =
        oldObject.hom ≫ referenceScheme.decoration.interpretation := by
    simpa only [StandardArchitectureScheme.coefficientStructureMap] using
      (AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        (oldObject.hom ≫ referenceScheme.decoration.interpretation))
  change (((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift Int))).inv ≫
        (referenceScheme.coefficientStructureMap referenceRaw).appTop) ≫ _) = _
  rw [hcoefficient]
  rw [← cancel_mono
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom]
  simp only [Category.assoc]
  change oldObject.hom ≫ referenceScheme.decoration.interpretation ≫
      ((evaluationPoint 1).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of Int)).hom) = _
  rw [evaluationPoint_normalized_appTop_r6]
  have hzero :
      (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom (liftedPolynomialEval n)).op).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of Int)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom ≫
        CommRingCat.ofHom (liftedPolynomialEval n) := by
    simpa only [AlgebraicGeometry.Scheme.Spec_map,
      Quiver.Hom.unop_op] using
        (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (liftedPolynomialEval n)))
  have hchange :
      (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom coefficientChange.liftedHom).op).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} Int))).hom ≫
        CommRingCat.ofHom coefficientChange.liftedHom := by
    simpa only [AlgebraicGeometry.Scheme.Spec_map,
      Quiver.Hom.unop_op] using
        (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom coefficientChange.liftedHom))
  change _ = (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} Int))).inv ≫
    (AlgebraicGeometry.Scheme.Spec.map
      (CommRingCat.ofHom coefficientChange.liftedHom).op).appTop ≫
    (AlgebraicGeometry.Scheme.Spec.map
      (CommRingCat.ofHom (liftedPolynomialEval n)).op).appTop ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom
  rw [hzero]
  rw [← Category.assoc
    (AlgebraicGeometry.Scheme.Spec.map
      (CommRingCat.ofHom coefficientChange.liftedHom).op).appTop
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom
    (CommRingCat.ofHom (liftedPolynomialEval n))]
  rw [hchange]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply CommRingCat.hom_ext
  ext z
  rcases z with ⟨z⟩
  change evaluationRingHom 1
      (ambientGlobalSectionsIso.hom
        (referenceScheme.decoration.interpretation
          (oldObject.hom ⟨z⟩))) =
    liftedPolynomialEval n (coefficientChange.liftedHom ⟨z⟩)
  have hold : oldObject.hom ⟨z⟩ =
      (sheafificationUnitAlgHom referenceRaw baseContext)
        (algebraMap Int (referenceRaw.rawAlgebra baseContext) z) := by
    exact (sheafificationUnitAlgHom referenceRaw baseContext).commutes z |>.symm
  rw [hold]
  change evaluationRingHom 1
      (ambientGlobalSectionsIso.hom
        (ambientDecoration.interpretation
          ((sheafificationUnitAlgHom referenceRaw baseContext)
            (algebraMap Int (referenceRaw.rawAlgebra baseContext) z)))) = _
  rw [ambientGlobalSectionsIso_unit_r6]
  simp [evaluationRingHom, baseRawAlgebraIso]
  change z = Polynomial.eval n (Polynomial.C z)
  simp

private noncomputable def coefficientOnePoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      coefficientChangedScheme.underlying := by
  change AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
    pullback (referenceScheme.coefficientStructureMap referenceRaw)
      (AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom coefficientChange.liftedHom).op)
  exact pullback.lift onePoint (coefficientEvaluationPoint n)
    (coefficientOnePoint_square n)

private theorem coefficientOnePoint_fst (n : Int) :
    coefficientOnePoint n ≫
        referenceScheme.baseChangeMap referenceRaw coefficientChange =
      onePoint := by
  exact pullback.lift_fst _ _ _

private theorem coefficientOnePoint_weak_ideal :
    IdealLawfulAlong
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading
      coefficientChangedWeakReading_valid
      coefficientChangedWeakReading_requiredClosed
      (coefficientOnePoint 0) := by
  change Scheme.IdealSheafData.comap
      (lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed)
      (coefficientOnePoint 0) = ⊥
  rw [← weakIdeal_baseChange]
  rw [← Scheme.IdealSheafData.comap_comp]
  rw [coefficientOnePoint_fst]
  exact onePoint_fires.2.2.1

private theorem coefficientOnePoint_not_strong_ideal :
    ¬ IdealLawfulAlong
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading
      coefficientChangedStrongReading_valid
      coefficientChangedStrongReading_requiredClosed
      (coefficientOnePoint 0) := by
  intro h
  apply onePoint_fires.2.2.2.2.2.2.1
  change Scheme.IdealSheafData.comap strongIdealSheaf onePoint = ⊥
  change Scheme.IdealSheafData.comap
      (lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed)
      (coefficientOnePoint 0) = ⊥ at h
  rw [← strongIdeal_baseChange] at h
  rw [← Scheme.IdealSheafData.comap_comp] at h
  rw [coefficientOnePoint_fst] at h
  exact h

/-- The transported weak ideal remains strictly below the transported strong ideal. -/
theorem coefficientChanged_ideal_strict :
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [← weakIdeal_baseChange, ← strongIdeal_baseChange]
    exact (Scheme.IdealSheafData.comap_mono
      (referenceScheme.baseChangeMap referenceRaw coefficientChange))
        weakIdeal_lt_strongIdeal.le
  · intro heq
    apply coefficientOnePoint_not_strong_ideal
    change Scheme.IdealSheafData.comap
        (lawGeneratedIdealSheaf
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed)
        (coefficientOnePoint 0) = ⊥
    rw [← heq]
    exact coefficientOnePoint_weak_ideal

/-- Strictness of the changed ideals makes the changed comparison non-isomorphic. -/
theorem coefficientChangedLawComparison_not_isIso :
    ¬ IsIso coefficientChangedLawComparison := by
  intro hIso
  letI : IsIso coefficientChangedLawComparison := hIso
  let weakChangedIdeal := lawGeneratedIdealSheaf
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakReading
    coefficientChangedWeakReading_valid
    coefficientChangedWeakReading_requiredClosed
  let strongChangedIdeal := lawGeneratedIdealSheaf
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedStrongReading
    coefficientChangedStrongReading_valid
    coefficientChangedStrongReading_requiredClosed
  let weakChangedImmersion := lawfulClosedImmersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakReading
    coefficientChangedWeakReading_valid
    coefficientChangedWeakReading_requiredClosed
  let strongChangedImmersion := lawfulClosedImmersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedStrongReading
    coefficientChangedStrongReading_valid
    coefficientChangedStrongReading_requiredClosed
  have hker := Scheme.Hom.ker_comp_of_isIso
    coefficientChangedLawComparison weakChangedImmersion
  have hsheaf : strongChangedIdeal = weakChangedIdeal := by
    calc
      strongChangedIdeal = strongChangedImmersion.ker :=
        (lawfulClosedImmersion_ker
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme coefficientChangedStrongReading
          coefficientChangedStrongReading_valid
          coefficientChangedStrongReading_requiredClosed).symm
      _ = (coefficientChangedLawComparison ≫ weakChangedImmersion).ker := by
        rw [coefficientChangedLawComparison_immersion]
      _ = weakChangedImmersion.ker := hker
      _ = weakChangedIdeal :=
        lawfulClosedImmersion_ker
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme coefficientChangedWeakReading
          coefficientChangedWeakReading_valid
          coefficientChangedWeakReading_requiredClosed
  exact (ne_of_lt coefficientChanged_ideal_strict) hsheaf.symm

/-- Coefficient change and the concrete weak-to-strong law comparison form the mixed square. -/
theorem coefficient_law_comparison_square :
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison := by
  letI : AlgebraicGeometry.IsClosedImmersion weakImmersion := by
    dsimp only [weakImmersion, lawfulClosedImmersion]
    infer_instance
  have hweak :
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
            coefficientChange ≫ weakImmersion =
        lawfulClosedImmersion
            (referenceRaw.baseChange coefficientChange.hom)
            coefficientChangedScheme coefficientChangedWeakReading
            coefficientChangedWeakReading_valid
            coefficientChangedWeakReading_requiredClosed ≫
          referenceScheme.baseChangeMap referenceRaw coefficientChange := by
    exact lawfulClosedSubschemeBaseChangeMap_immersion
      referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
        coefficientChange
  have hstrong :
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
            coefficientChange ≫ strongImmersion =
        lawfulClosedImmersion
            (referenceRaw.baseChange coefficientChange.hom)
            coefficientChangedScheme coefficientChangedStrongReading
            coefficientChangedStrongReading_valid
            coefficientChangedStrongReading_requiredClosed ≫
          referenceScheme.baseChangeMap referenceRaw coefficientChange := by
    exact lawfulClosedSubschemeBaseChangeMap_immersion
      referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
        coefficientChange
  rw [← cancel_mono weakImmersion]
  simp only [Category.assoc]
  rw [hweak]
  rw [← Category.assoc, coefficientChangedLawComparison_immersion]
  rw [lawComparison_immersion]
  rw [hstrong]

private noncomputable def coefficientProjection :
    coefficientChangedScheme.underlying ⟶
      AlgebraicGeometry.Spec
        (CommRingCat.of (ULift.{0, 0} (Polynomial Int))) := by
  change pullback (referenceScheme.coefficientStructureMap referenceRaw)
      (AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom coefficientChange.liftedHom).op) ⟶ _
  exact pullback.snd _ _

private def coefficientPointEval (n : Int) :
    Γ(coefficientChangedScheme.underlying, ⊤) →+* Int :=
  ((coefficientOnePoint n).appTop ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).hom

private noncomputable def targetCoefficientX :
    Γ(coefficientChangedScheme.underlying, ⊤) :=
  coefficientProjection.appTop
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
        (ULift.up Polynomial.X))

private theorem coefficientEvaluationPoint_normalized (n : Int) :
    (coefficientEvaluationPoint n).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom ≫
        CommRingCat.ofHom (liftedPolynomialEval n) := by
  simpa only [coefficientEvaluationPoint,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
      (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (liftedPolynomialEval n)))

private theorem coefficientPointEval_targetCoefficientX (n : Int) :
    coefficientPointEval n targetCoefficientX = n := by
  have hsnd : coefficientOnePoint n ≫ coefficientProjection =
      coefficientEvaluationPoint n := by
    exact pullback.lift_snd _ _ _
  have happ := congrArg AlgebraicGeometry.Scheme.Hom.appTop hsnd
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at happ
  change (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
    ((coefficientOnePoint n).appTop
      (coefficientProjection.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
            (ULift.up Polynomial.X)))) = n
  have hpx := ConcreteCategory.congr_hom happ
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
        (ULift.up Polynomial.X))
  rw [CommRingCat.comp_apply] at hpx
  rw [hpx]
  have hnormalized := ConcreteCategory.congr_hom
    (coefficientEvaluationPoint_normalized n)
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
        (ULift.up Polynomial.X))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnormalized
  rw [hnormalized]
  rw [Iso.inv_hom_id_apply]
  change Polynomial.eval n Polynomial.X = n
  simp

private theorem coefficientPointEval_agree_on_baseMap
    (x : Γ(referenceScheme.underlying, ⊤)) :
    coefficientPointEval 0
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x) =
      coefficientPointEval 1
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x) := by
  have hzero := congrArg AlgebraicGeometry.Scheme.Hom.appTop
    (coefficientOnePoint_fst 0)
  have hone := congrArg AlgebraicGeometry.Scheme.Hom.appTop
    (coefficientOnePoint_fst 1)
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at hzero hone
  change (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
      ((coefficientOnePoint 0).appTop
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x)) =
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
      ((coefficientOnePoint 1).appTop
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x))
  have hz := ConcreteCategory.congr_hom hzero x
  have ho := ConcreteCategory.congr_hom hone x
  rw [CommRingCat.comp_apply] at hz ho
  exact congrArg
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
    (hz.trans ho.symm)

/-- The ambient coefficient-change projection is not an isomorphism. -/
theorem coefficientChange_schemeMap_not_isIso :
    ¬ IsIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange) := by
  intro hIso
  letI : IsIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange) := hIso
  have hsurjective : Function.Surjective
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange).appTop :=
    (ConcreteCategory.bijective_of_isIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange).appTop).2
  have heval : coefficientPointEval 0 = coefficientPointEval 1 := by
    apply RingHom.ext
    intro y
    rcases hsurjective y with ⟨x, rfl⟩
    exact coefficientPointEval_agree_on_baseMap x
  have hx := DFunLike.congr_fun heval targetCoefficientX
  rw [coefficientPointEval_targetCoefficientX,
    coefficientPointEval_targetCoefficientX] at hx
  norm_num at hx


end
end AAT.AG.Examples.StandardGeometryReferenceModels
