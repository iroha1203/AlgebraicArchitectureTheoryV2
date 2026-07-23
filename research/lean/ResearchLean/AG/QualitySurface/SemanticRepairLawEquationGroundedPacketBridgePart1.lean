import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketBridge

/-!
Converters for body conjuncts 2--5 of the grounded law-equation packet.
-/

noncomputable section

universe v w r

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
namespace GroundedPacketBridge

open CoverRelativeCechGeneratedSemanticCoefficient

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

/-- Body conjunct 2, applied to every displayed common refinement. -/
theorem toResearchDisplayedRequiredLawRestrictionEvaluator
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (hholds : D.DisplayedRequiredEquationsHoldOn)
    (hbody :
      (toBodyDefectSource D).toLawEquationBodyCechSource
        |>.DisplayedRequiredLawRestrictionEvaluator) :
    D.toSupportOnlySemanticAtomLawInputBoundarySource
      |>.displayedRequiredLawRestrictionEvaluator D.objectOfLocalInput := by
  intro i j Z gi gj hcomm lawIndexI lawIndexJ hmemI hmemJ
    hrequiredI hrequiredJ hholdsI hholdsJ
  let sigma :
      AAT.AG.Site.FinitePosetCechCanonicalTupleSimplex
        coverGeometry.cover.Index 0 := fun _ => i
  let tau :
      AAT.AG.Site.FinitePosetCechCanonicalTupleSimplex
        coverGeometry.cover.Index 0 := fun _ => j
  have hbodyComm :
      gi ≫
          (toBodyDefectSource D).toLawEquationBodyCechSource.chartToBase sigma =
        gj ≫
          (toBodyDefectSource D).toLawEquationBodyCechSource.chartToBase tau := by
    simpa [sigma, tau, toBodyDefectSource, toBodyFinitePosetCoverGeometry,
      AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationBodyCechSource,
      AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationDefectSource,
      lawEquationRegime,
      FinitePosetAtomLawCanonicalTupleOverlapGeometry.toCanonicalTupleCoverGeometry]
      using hcomm
  obtain ⟨equationIndexI, hequationMemI⟩ :=
    D.lawSupport_nonempty i (D.input i)
  obtain ⟨equationIndexJ, hequationMemJ⟩ :=
    D.lawSupport_nonempty j (D.input j)
  have hequationRequiredI :=
    D.lawSupport_required i (D.input i) equationIndexI hequationMemI
  have hequationRequiredJ :=
    D.lawSupport_required j (D.input j) equationIndexJ hequationMemJ
  exact
    hbody sigma tau gi gj hbodyComm equationIndexI equationIndexJ
      hequationMemI hequationMemJ hequationRequiredI hequationRequiredJ
      (hholds i equationIndexI hequationMemI hequationRequiredI)
      (hholds j equationIndexJ hequationMemJ hequationRequiredJ)

/-- Body conjunct 3, unfolded to the original generated-Cech zero predicate. -/
theorem toResearchSourceC0CechZero
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (hbody :
      (toBodyDefectSource D).toLawEquationBodyCechSource.SourceC0CechZero) :
    atomLawOverlap_sourceSectionFreeSkeleton_sourceC0CechZero coverGeometry
      G.toSemanticAtomLawAdditiveCoefficientGeometry skeleton
      D.toSupportOnlySemanticAtomLawInputBoundarySource := by
  simpa [
    AAT.AG.SemanticRepair.LawEquationBodyCechSource.SourceC0CechZero,
    AAT.AG.SemanticRepair.LawEquationBodyCechSource.displayedSourceC0,
    AAT.AG.SemanticRepair.LawEquationBodyCechSource.restrictedDisplayedInterpretation,
    atomLawOverlap_sourceSectionFreeSkeleton_sourceC0CechZero,
    atomLawOverlap_sourceSectionFreeSkeleton_sourceC0,
    toBodyDefectSource, toBodyWitnessIdealGeometry,
    toBodyFinitePosetCoverGeometry]
    using hbody

variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}

/--
Convert body conjunct 5 to the original face-restriction statement.  Every
carrier equivalence, zero law, and direct differential equation from the body
field is copied into the Research presentation.
-/
theorem toResearchDegreewiseCarrierFaceEquations
    {semanticCover : SemanticRepairCover.{r, v, w} semanticSite}
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover surface.coverBridge) Ob}
    (boundary :
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient semanticSite K)
    (canonical :
      CoverRelativeCechGeneratedCanonicalH1Envelope
        boundary.toGeneratedCoefficient)
    (hbody :
      AAT.AG.SemanticRepair.DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
          (AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface K
              boundary.primitive)
          K) :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
      (E := canonical.toEnvelope)
      (additive := canonical.toAdditiveCechH1Data)
      (coverBridge := surface.coverBridge) (K := K) := by
  rcases hbody with
    ⟨c0Equiv, c1Equiv, c2Equiv, hc2zero, hc2symmZero,
      hd0to, hd0from, hd1to, hd1from⟩
  letI := canonical.toAdditiveCechH1Data.c0AddCommGroup
  letI := canonical.toAdditiveCechH1Data.c1AddCommGroup
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  refine
    ⟨CarrierSpecificAdditiveComparisonData.ofAddEquiv c0Equiv,
      CarrierSpecificAdditiveComparisonData.ofAddEquiv c1Equiv,
      c2Equiv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using hc2zero
  · simpa [CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using hc2symmZero
  · intro primitive
    rw [← K.d_eq_alternatingFaceCombination 0]
    simpa [CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv,
      CarrierSpecificAdditiveComparisonData.ofAddEquiv] using hd0to primitive
  · intro primitive
    rw [← K.d_eq_alternatingFaceCombination 0]
    simpa [CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv,
      CarrierSpecificAdditiveComparisonData.ofAddEquiv] using hd0from primitive
  · intro cochain
    rw [← K.d_eq_alternatingFaceCombination 1]
    simpa [CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv,
      CarrierSpecificAdditiveComparisonData.ofAddEquiv] using hd1to cochain
  · intro cochain
    rw [← K.d_eq_alternatingFaceCombination 1]
    simpa [CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
      CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
      CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
      CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
      CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
      CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
      AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv,
      CarrierSpecificAdditiveComparisonData.ofAddEquiv] using hd1from cochain

/--
Convert body conjunct 4 to the original selected semantic coefficient layer.
The body layer's generated cover, cover equality, and all nine realization
fields are used directly.
-/
theorem toResearchSelectedRealizationLayer
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
    (hbody :
      let bodyGeometry := toBodyFinitePosetCoverGeometry coverGeometry
      let bodyG := toBodyWitnessIdealGeometry G skeleton
      let bodyK :=
        AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquationCechComplex bodyG.quotientIsSheaf
            bodyGeometry.canonicalTupleCoverGeometryFromOverlap
      let bodyD := toBodyDefectSource D
      let bodySource := bodyD.toLawEquationBodyCechSource
      let bodySurface :=
        AAT.AG.SemanticRepair.lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
          (toBodySemanticCover semanticCover skeleton) bodyGeometry bodyK
          (toBodyDegreeZeroSimplexMap semanticCover chartSimplex)
          (toBodyDegreeOneSimplexMap semanticCover overlapSimplex)
          (toBodyDegreeTwoSimplexMap semanticCover tripleSimplex)
          bodyG.quotientIsSheaf
      let bodyAdditive :=
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface
          bodyK bodySource.toPrimitive
      Nonempty
        (AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
            bodyD bodySource bodySurface bodyAdditive)) :
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
    Nonempty
      (SelectedSemanticCoefficientDirectRealizationLayer
        (E := envelope.toEnvelope)
        (additive := envelope.toAdditiveCechH1Data) surface) := by
  dsimp only at hbody ⊢
  rcases hbody with ⟨layer⟩
  let realization := layer.atomSupportedSource.realization
  let source := D.toCoverRelativeBaseRestrictionSource
  let restrictionSource :=
    source.toRestrictionRealizedBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
  let boundarySource :=
    restrictionSource.toBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
  let freeSource := boundarySource.toFreeSemanticAtomLawInputBoundarySource
  let geometry :=
    CoverRelativeCechSemanticAtomLawInputBoundaryGeometry.ofFreeSemanticAtomLawInputBoundarySource
      freeSource
  let surface :=
    lawEquationCurrentG06InputSurface coverGeometry G semanticCover
      chartSimplex overlapSimplex tripleSimplex
  let boundary :=
    geometry.toBoundaryGeneratedCoefficient
      (K := surface.K) source.c0Order source.c1Order
  let canonical :=
    CoverRelativeCechGeneratedCanonicalH1Envelope.defaultObservationEnvelope
      (site := semanticSite) boundary.toGeneratedCoefficient
  let additive := canonical.toGeneratedEnvelope.toAdditiveCechH1Data
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  letI := surface.K.cochainAddCommGroup 0
  letI := surface.K.cochainAddCommGroup 1
  change Nonempty
    (SelectedSemanticCoefficientDirectRealizationLayer
      (E := canonical.toGeneratedEnvelope.toEnvelope)
      (additive := additive) surface)
  refine ⟨{ family := ?_, cover_eq := ?_, directLower := ?_ }⟩
  · simpa [AAT.AG.SemanticRepair.lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry,
      lawEquationCurrentG06InputSurface, toBodyFinitePosetCoverGeometry] using
      layer.family
  · simpa [AAT.AG.SemanticRepair.lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry,
      lawEquationCurrentG06InputSurface, toBodyFinitePosetCoverGeometry] using
      layer.cover_eq
  · refine
      ⟨CarrierSpecificAdditiveComparisonData.ofAddEquiv realization.c0Equiv,
        CarrierSpecificAdditiveComparisonData.ofAddEquiv realization.c1Equiv,
        realization.c2Equiv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [realization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using
        realization.c2Equiv_zero
    · simpa [realization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface] using
        realization.c2Equiv_symm_zero
    · intro primitive
      simpa [realization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c0SectionEquiv,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        CarrierSpecificAdditiveComparisonData.ofAddEquiv] using
        realization.d0_to primitive
    · intro primitive
      simpa [realization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c0SectionEquiv,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        CarrierSpecificAdditiveComparisonData.ofAddEquiv] using
        realization.d0_from primitive
    · intro cochain
      simpa [realization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        CarrierSpecificAdditiveComparisonData.ofAddEquiv] using
        realization.d1_to cochain
    · intro cochain
      simpa [realization,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toEnvelope,
        CoverRelativeCechGeneratedCanonicalH1Envelope.toGeneratedEnvelope,
        CoverRelativeCechGeneratedSemanticEnvelope.toAdditiveCechH1Data,
        CoverRelativeCechGeneratedSemanticEnvelope.toEnvelope,
        CoverRelativeCechGeneratedSemanticCoefficient.toCoefficient,
        CoverRelativeCechBoundaryGeneratedSemanticCoefficient.toGeneratedCoefficient,
        AAT.AG.SemanticRepair.coverRelativeGeneratedBoundaryAdditiveH1Surface,
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        CarrierSpecificAdditiveComparisonData.ofAddEquiv] using
        realization.d1_from cochain

end GroundedPacketBridge
end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
