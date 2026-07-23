import Formal.AG.Examples.StandardGeometryReference.Geometry
import Formal.AG.Examples.StandardGeometryReference.EquationGeometry
import Formal.AG.Examples.StandardGeometryReference.CoefficientChange
import Formal.AG.Examples.StandardGeometryReference.NegativeFixtures

/-!
# Standard geometry reference models

This small aggregate module preserves the historical import path and owns the
SD7 integrated firing theorem.  The stable geometry, equation geometry,
coefficient change, and negative fixtures live in responsibility-specific
modules under `StandardGeometryReference/`.

The integrated theorem is a direct conjunction of the earlier component
theorems rather than a new certificate structure.
-/

set_option maxHeartbeats 4000000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section

/--
All positive component theorems fire simultaneously in the fixed standard-geometry model.

This theorem is assembled only from the component theorems; it does not replace their
individual executable contracts or the negative fixtures above.
-/
theorem standardGeometryReference_fires :
    Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf ∧
    (∀ W : referenceSite.category,
      IsIso (referenceRaw.toRingedSite.canonical.app (op W))) ∧
    (⨆ i, ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange = ⊤) ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map ∧
    Nonempty (referenceScheme.atlas.actualOverlap
      referenceRaw leftIndex rightIndex) ∧
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) = weakAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) = strongAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) = rigidAmbientIdeal ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
      weakLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
      weakRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      weakOverlapIdeal ∧
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
      strongLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
      strongRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      strongOverlapIdeal ∧
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    weakAmbientIdeal ≠ ⊥ ∧ weakAmbientIdeal ≠ ⊤ ∧
    strongAmbientIdeal ≠ ⊥ ∧ strongAmbientIdeal ≠ ⊤ ∧
    weakIdealSheaf < strongIdealSheaf ∧
    rigidAmbientIdeal ≠ ⊥ ∧ rigidAmbientIdeal ≠ ⊤ ∧
    strongIdealSheaf < rigidIdealSheaf ∧
    weakImmersion.ker = weakIdealSheaf ∧
    strongImmersion.ker = strongIdealSheaf ∧
    Set.range weakImmersion = weakIdealSheaf.support ∧
    Set.range strongImmersion = strongIdealSheaf.support ∧
    IsIso weakAffineQuotientChart ∧ IsIso strongAffineQuotientChart ∧
    Nonempty weakLocus ∧ Nonempty strongLocus ∧ Nonempty rigidLocus ∧
    ¬ IsIso weakImmersion ∧ ¬ IsIso strongImmersion ∧ ¬ IsIso rigidImmersion ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint) ∧
    AlgebraicGeometry.IsClosedImmersion lawComparison ∧
    lawComparison ≫ weakImmersion = strongImmersion ∧
    ¬ IsIso lawComparison ∧
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison ∧
    strongToRigidComparison ≫ strongImmersion = rigidImmersion ∧
    ¬ IsIso strongToRigidComparison ∧
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison ∧
    ¬ Function.Surjective coefficientChange.hom ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas referenceRaw coefficientChange).chart
        (cast (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas referenceRaw coefficientChange).chart
        (cast (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map ∧
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedWeakReading coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed ∧
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedStrongReading coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedWeakReading coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedStrongReading coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    AlgebraicGeometry.IsClosedImmersion coefficientChangedLawComparison ∧
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap ∧
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap ∧
    ¬ IsIso coefficientChangedLawComparison ∧
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison ∧
    ¬ IsIso (referenceScheme.baseChangeMap referenceRaw coefficientChange) := by
  rcases zeroPoint_fires with ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩
  rcases onePoint_fires with ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩
  rcases twoPoint_fires with ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩
  exact ⟨
    referenceRaw_isSheaf, fun W => canonical_component_isIso W,
    twoChart_jointlyCovers, left_chart_isOpenImmersion,
    right_chart_isOpenImmersion, left_chart_not_isIso, right_chart_not_isIso,
    actualOverlap_nonempty, left_restriction_not_isIso,
    weakIdeal_top_eq, strongIdeal_top_eq, rigidIdeal_top_eq,
    weakIdeal_left_eq, weakIdeal_right_eq, weakIdeal_overlap_eq,
    weakIdeal_overlap_agrees, strongIdeal_left_eq, strongIdeal_right_eq,
    strongIdeal_overlap_eq, strongIdeal_overlap_agrees,
    weakAmbientIdeal_ne_bot, weakAmbientIdeal_ne_top,
    strongAmbientIdeal_ne_bot, strongAmbientIdeal_ne_top,
    weakIdeal_lt_strongIdeal, rigidAmbientIdeal_ne_bot, rigidAmbientIdeal_ne_top,
    strongIdeal_lt_rigidIdeal, weakImmersion_ker, strongImmersion_ker,
    weakImmersion_zeroLocus, strongImmersion_zeroLocus,
    weakAffineQuotientChart_isIso, strongAffineQuotientChart_isIso,
    weakLocus_nonempty, strongLocus_nonempty, rigidLocus_nonempty,
    weakImmersion_not_isIso, strongImmersion_not_isIso, rigidImmersion_not_isIso,
    z1, z2, z3, z4, z5, z6, z7, z8,
    o1, o2, o3, o4, o5, o6, o7, o8,
    t1, t2, t3, t4, t5, t6, t7, t8,
    lawComparison_isClosedImmersion, lawComparison_immersion,
    lawComparison_not_isIso, strongToRigidComparison_isClosedImmersion,
    strongToRigidComparison_immersion, strongToRigidComparison_not_isIso,
    lawComparison_comp_fires, coefficientChange_not_surjective,
    leftChart_baseChange_isPullback, rightChart_baseChange_isPullback,
    weakIdeal_baseChange, strongIdeal_baseChange, coefficientChanged_ideal_strict,
    coefficientChangedLawComparison_isClosedImmersion,
    coefficientChangedWeakToStrong_lawMap,
    coefficientChangedWeakToStrong_atomMap,
    coefficientChangedLawComparison_not_isIso,
    coefficient_law_comparison_square, coefficientChange_schemeMap_not_isIso⟩


end
end AAT.AG.Examples.StandardGeometryReferenceModels
