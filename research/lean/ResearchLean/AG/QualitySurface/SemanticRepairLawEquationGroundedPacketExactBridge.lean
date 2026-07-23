import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketBridge
import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketBridgePart1
import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketBridgePart2

/-!
Exact conclusion bridge from the native finite-free body packet back to the
accepted Research law-equation packet statement.
-/

noncomputable section

universe u v w x y z r a b

set_option maxHeartbeats 1000000

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open Opposite
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1
open SemanticRepairObstructionTower

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis

open CoverRelativeCechGeneratedSemanticCoefficient
open GroundedPacketBridge

variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {semanticSite : SemanticRepairSite.{r, v} U.Atom}
variable {S : AAT.AG.Site.AATSite A}
variable {coverGeometry : FinitePosetAtomLawCoverGeometry S}
variable {G : SemanticLawEquationWitnessIdealGeometry semanticSite S}
variable {skeleton :
  SourceSectionFreeSkeleton
    (semanticSite := semanticSite) (S := S)
    (regime := lawEquationRegime coverGeometry G)
    (C := lawEquationStandardComplex coverGeometry G)
    (Ob := G.lawEquationObstructionSheaf)
    (K := lawEquationCechComplex coverGeometry G)}

/--
The accepted Research packet, reconstructed field-for-field from the native
finite-free body theorem.  The Research source theorem is not used.
-/
theorem lawEquation_constructs_groundedComparisonPacket_viaBody
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    (chartSimplex :
      semanticCover.CoverChart ->
        (AAT.AG.Cohomology.finitePosetCoverRelativeCover
          (lawEquationStandardComplex coverGeometry G)).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 1)
    (tripleSimplex :
      (Sigma fun triple :
        semanticCover.CoverChart × semanticCover.CoverChart ×
          semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 2)
    (hholds : D.DisplayedRequiredEquationsHoldOn) :
    let surface :=
      lawEquationCurrentG06InputSurface coverGeometry G semanticCover
        chartSimplex overlapSimplex tripleSimplex
    let source := D.toCoverRelativeBaseRestrictionSource
    let restrictionSource :=
      source.toRestrictionRealizedBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let boundarySource :=
      restrictionSource.toBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let freeSource := boundarySource.toFreeSemanticAtomLawInputBoundarySource
    let geometry :=
      CoverRelativeCechSemanticAtomLawInputBoundaryGeometry.ofFreeSemanticAtomLawInputBoundarySource
        freeSource
    let boundary :=
      geometry.toBoundaryGeneratedCoefficient
        (K := surface.K) source.c0Order source.c1Order
    let generated := boundary.toGeneratedCoefficient
    let canonical :=
      CoverRelativeCechGeneratedCanonicalH1Envelope.defaultObservationEnvelope
        (site := semanticSite) generated
    let envelope := canonical.toGeneratedEnvelope
    let realization := envelope.toCochainRealization
    (forall sigma :
      (AAT.AG.Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex coverGeometry G)).simplex 0,
      source.toPrimitive sigma =
        G.lawEquationObstructionSheaf.carrier.toPresheaf.map
          (homOfLE
            ((lawEquationRegime coverGeometry G).simplexOverlap_le_patch 0
              sigma 0)).op
          (D.toSupportOnlySemanticAtomLawInputBoundarySource.interpret
            ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)
            (D.toSupportOnlySemanticAtomLawInputBoundarySource.input
              ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)))) /\
      D.toSupportOnlySemanticAtomLawInputBoundarySource.displayedRequiredLawRestrictionEvaluator
        D.objectOfLocalInput /\
      atomLawOverlap_sourceSectionFreeSkeleton_sourceC0CechZero coverGeometry
        G.toSemanticAtomLawAdditiveCoefficientGeometry skeleton
        D.toSupportOnlySemanticAtomLawInputBoundarySource /\
      Nonempty
        (SelectedSemanticCoefficientDirectRealizationLayer
          (E := envelope.toEnvelope)
          (additive := envelope.toAdditiveCechH1Data) surface) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (E := envelope.toEnvelope)
        (additive := envelope.toAdditiveCechH1Data)
        (coverBridge := surface.coverBridge)
        (K := surface.K) /\
      Nonempty
        (SemanticRepairCoverRelativeCochainRealization
          envelope.toAdditiveCechH1Data surface.K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) /\
      canonical.residualBoundary /\
      SemanticRepairH1Zero envelope.toEnvelope /\
      SemanticRepairAdditiveH1Zero envelope.toAdditiveCechH1Data := by
  dsimp
  let bodyGeometry := toBodyFinitePosetCoverGeometry coverGeometry
  let bodyG := toBodyWitnessIdealGeometry G skeleton
  let bodyK :=
    AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquationCechComplex
      bodyG.quotientIsSheaf
      bodyGeometry.canonicalTupleCoverGeometryFromOverlap
  let bodyD := toBodyDefectSource D
  let bodySource := bodyD.toLawEquationBodyCechSource
  let bodyRealization :=
    AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryCochainRealization
      bodyK bodySource.toPrimitive
  have hbody :
      let K := bodyK
      let source := bodyD.toLawEquationBodyCechSource
      let surface :=
        AAT.AG.SemanticRepair.lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
          (toBodySemanticCover semanticCover skeleton) bodyGeometry K
          (toBodyDegreeZeroSimplexMap semanticCover chartSimplex)
          (toBodyDegreeOneSimplexMap semanticCover overlapSimplex)
          (toBodyDegreeTwoSimplexMap semanticCover tripleSimplex)
          bodyG.quotientIsSheaf
      Nonempty
        (AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.LawEquationGroundedComparisonFiniteFreeConjunctsBody.{r, max v w, r, r, r, r}
          bodyD surface source) :=
    AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquation_constructs_groundedComparisonPacket_finiteFree
        (toBodySemanticInput semanticSite skeleton)
        (toBodySemanticCover semanticCover skeleton)
        bodyG bodyGeometry bodyD
        (toBodyDegreeZeroSimplexMap semanticCover chartSimplex)
        (toBodyDegreeOneSimplexMap semanticCover overlapSimplex)
        (toBodyDegreeTwoSimplexMap semanticCover tripleSimplex)
        (toBodyDisplayedRequiredLawsHoldOn D hholds)
  dsimp only at hbody
  rcases hbody with ⟨packet⟩
  rcases packet.selectedRealizationLayer with ⟨bodyLayer⟩
  rcases packet.cochainRealization with ⟨bodyCochainRealization⟩
  rcases packet.h1ComparisonPackage with ⟨bodyComparisonPackage⟩
  let surface :=
    lawEquationCurrentG06InputSurface coverGeometry G semanticCover
      chartSimplex overlapSimplex tripleSimplex
  let source := D.toCoverRelativeBaseRestrictionSource
  let restrictionSource :=
    source.toRestrictionRealizedBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
  let boundarySource :=
    restrictionSource.toBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
  let freeSource := boundarySource.toFreeSemanticAtomLawInputBoundarySource
  let geometry :=
    CoverRelativeCechSemanticAtomLawInputBoundaryGeometry.ofFreeSemanticAtomLawInputBoundarySource
      freeSource
  let boundary :=
    geometry.toBoundaryGeneratedCoefficient
      (K := surface.K) source.c0Order source.c1Order
  let canonical :=
    CoverRelativeCechGeneratedCanonicalH1Envelope.defaultObservationEnvelope
      (site := semanticSite) boundary.toGeneratedCoefficient
  have bodyCochainRealization' :
      AAT.AG.SemanticRepair.SemanticRepairCoverRelativeCochainRealization
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          surface.K boundary.primitive)
        surface.K := by
    refine
      { c0Equiv := ?_, c1Equiv := ?_, c2Equiv := ?_,
        c2Equiv_zero := ?_, c2Equiv_symm_zero := ?_,
        d0_to := ?_, d0_from := ?_, d1_to := ?_, d1_from := ?_ }
    all_goals first
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.c0Equiv
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.c1Equiv
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.c2Equiv
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.c2Equiv_zero
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.c2Equiv_symm_zero
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.d0_to
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.d0_from
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.d1_to
    | simpa [surface, boundary, geometry, freeSource, boundarySource,
        restrictionSource, source, bodyK, bodySource, bodyD, bodyGeometry,
        bodyG, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
        toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface, lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyCochainRealization.d1_from
  let bodyRealization' :
      AAT.AG.SemanticRepair.SemanticRepairCoverRelativeCochainRealization
        (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          surface.K boundary.primitive)
        surface.K :=
    AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryCochainRealization
      surface.K boundary.primitive
  have bodyComparisonPackage' :
      AAT.AG.SemanticRepair.SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage.{r, r, r, r, r, r, r}
        bodyRealization'.toH1Comparison := by
    let comparison := bodyRealization'.toH1Comparison
    refine
      { toCoverRelativeH1 := ?_
        fromCoverRelativeH1 := ?_
        h1Equiv := ?_
        h1AddEquiv := ?_
        sameClass_iff_coverRelative := ?_
        zero_iff_coverRelativeZero := ?_ }
    · simpa [comparison, bodyRealization', bodyRealization, surface, boundary,
        geometry, freeSource, boundarySource, restrictionSource, source, bodyK,
        bodySource, bodyD, bodyGeometry, bodyG, toBodyDefectSource,
        toBodyFinitePosetCoverGeometry, toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface,
        lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyComparisonPackage.toCoverRelativeH1
    · simpa [comparison, bodyRealization', bodyRealization, surface, boundary,
        geometry, freeSource, boundarySource, restrictionSource, source, bodyK,
        bodySource, bodyD, bodyGeometry, bodyG, toBodyDefectSource,
        toBodyFinitePosetCoverGeometry, toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface,
        lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyComparisonPackage.fromCoverRelativeH1
    · simpa [comparison, bodyRealization', bodyRealization, surface, boundary,
        geometry, freeSource, boundarySource, restrictionSource, source, bodyK,
        bodySource, bodyD, bodyGeometry, bodyG, toBodyDefectSource,
        toBodyFinitePosetCoverGeometry, toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface,
        lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyComparisonPackage.h1Equiv
    · simpa [comparison, bodyRealization', bodyRealization, surface, boundary,
        geometry, freeSource, boundarySource, restrictionSource, source, bodyK,
        bodySource, bodyD, bodyGeometry, bodyG, toBodyDefectSource,
        toBodyFinitePosetCoverGeometry, toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface,
        lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyComparisonPackage.h1AddEquiv
    intro left right
    simpa [comparison, bodyRealization', bodyRealization, surface, boundary,
      geometry, freeSource, boundarySource, restrictionSource, source, bodyK,
      bodySource, bodyD, bodyGeometry, bodyG, toBodyDefectSource,
      toBodyFinitePosetCoverGeometry, toBodyWitnessIdealGeometry,
      lawEquationCurrentG06InputSurface,
      lawEquationCoverBridge,
      LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
      using bodyComparisonPackage.sameClass_iff_coverRelative left right
    · simpa [comparison, bodyRealization', bodyRealization, surface, boundary,
        geometry, freeSource, boundarySource, restrictionSource, source, bodyK,
        bodySource, bodyD, bodyGeometry, bodyG, toBodyDefectSource,
        toBodyFinitePosetCoverGeometry, toBodyWitnessIdealGeometry,
        lawEquationCurrentG06InputSurface,
        lawEquationCoverBridge,
        LawEquationDefectSemanticAtomLawInputBoundarySource.toCoverRelativeBaseRestrictionSource,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface]
        using bodyComparisonPackage.zero_iff_coverRelativeZero
  exact
    ⟨toResearchDisplayedInterpretationRealization D
        packet.displayedInterpretationRealization,
      toResearchDisplayedRequiredLawRestrictionEvaluator D hholds
        packet.displayedRequiredLawRestrictionEvaluator,
      toResearchSourceC0CechZero D packet.sourceC0CechZero,
      toResearchSelectedRealizationLayer D semanticCover chartSimplex overlapSimplex
        tripleSimplex ⟨bodyLayer⟩,
      toResearchDegreewiseCarrierFaceEquations surface boundary canonical
        packet.degreewiseCarrierFaceEquations,
      ⟨toResearchCochainRealization boundary canonical bodyCochainRealization'⟩,
      ⟨toResearchH1ComparisonPackage boundary canonical bodyRealization'
        bodyComparisonPackage'⟩,
      toResearchResidualBoundary boundary canonical packet.residualBoundary,
      toResearchSemanticH1Zero boundary canonical packet.semanticH1Zero,
      toResearchAdditiveH1Zero boundary canonical packet.additiveH1Zero⟩

end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
