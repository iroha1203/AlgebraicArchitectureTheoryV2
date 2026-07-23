import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacketExactBridge

/-!
Type and projection contracts for the exact body-to-Research grounded packet
bridge.
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

variable (coverGeometry : FinitePosetAtomLawCoverGeometry S)

example : (toBodyFinitePosetCoverGeometry coverGeometry).ContextIndex =
    coverGeometry.ContextIndex := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).finiteContextIndex =
    coverGeometry.finiteContextIndex := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).context =
    coverGeometry.context := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).contextLe =
    coverGeometry.contextLe := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).contextMeet =
    coverGeometry.contextMeet := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).base =
    coverGeometry.base := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).cover =
    coverGeometry.cover := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).nerveSimplex =
    coverGeometry.nerveSimplex := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).simplexIndices =
    coverGeometry.simplexIndices := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).simplexOverlap =
    coverGeometry.simplexOverlap := rfl
example : (toBodyFinitePosetCoverGeometry coverGeometry).adequacyRequirements =
    coverGeometry.adequacyRequirements := rfl

variable (G : SemanticLawEquationWitnessIdealGeometry semanticSite S)

variable {coverGeometry G}
variable {skeleton :
  SourceSectionFreeSkeleton
    (semanticSite := semanticSite) (S := S)
    (regime := lawEquationRegime coverGeometry G)
    (C := lawEquationStandardComplex coverGeometry G)
    (Ob := G.lawEquationObstructionSheaf)
    (K := lawEquationCechComplex coverGeometry G)}

example :
    (toBodyWitnessIdealGeometry G skeleton).equationSystem =
      G.equationSystem := rfl
example {source target : S.category} (f : source ⟶ target) :
    (toBodyWitnessIdealGeometry G skeleton).equationSystem.restrict f =
      G.equationSystem.restrict f := rfl
example (W : S.category) (equationIndex : G.equationSystem.Index)
    (atom : U.Atom) :
    (toBodyWitnessIdealGeometry G skeleton).equationSystem.violationCoordinate
        W equationIndex atom =
      G.equationSystem.violationCoordinate W equationIndex atom := rfl
example (W : S.category) (object : AAT.AG.ArchitectureObject U)
    (equationIndex : G.equationSystem.Index) (atom : U.Atom) :
    (toBodyWitnessIdealGeometry G skeleton).equationSystem.equationResidual
        W object equationIndex atom =
      G.equationSystem.equationResidual W object equationIndex atom := rfl
example :
    (toBodyWitnessIdealGeometry G skeleton).supportAtom = G.supportAtom := rfl

example : (toBodySemanticInput semanticSite skeleton).Component =
    (U.Atom × SourceSectionFreeSkeleton
      (semanticSite := semanticSite) (S := S)
      (regime := lawEquationRegime coverGeometry G)
      (C := lawEquationStandardComplex coverGeometry G)
      (Ob := G.lawEquationObstructionSheaf)
      (K := lawEquationCechComplex coverGeometry G)) := rfl
example (atom : U.Atom) :
    (toBodySemanticInput semanticSite skeleton).project atom =
      (atom, skeleton) := rfl
example (atom : U.Atom) :
    (toBodySemanticInput semanticSite skeleton).sourceTraceToken atom =
      semanticSite.sourceTraceToken atom := rfl

variable (D :
  LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G skeleton)

example : (toBodyDefectSource D).LocalInput = D.LocalInput := rfl
example : (toBodyDefectSource D).input = D.input := rfl
example : (toBodyDefectSource D).atomSupport = D.atomSupport := rfl
example : (toBodyDefectSource D).lawSupport = D.lawSupport := rfl
example : (toBodyDefectSource D).objectOfLocalInput = D.objectOfLocalInput := rfl
example : (toBodyDefectSource D).defect = D.defect := rfl

variable (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)

example : (toBodySemanticCover semanticCover skeleton).baseCover.Transition =
    ULift.{r, 0} (Fin semanticCover.overlapOrder.length) := rfl
example (chart : semanticCover.CoverChart) :
    (toBodySemanticCover semanticCover skeleton).chart (ULift.up chart) =
      ⟨(chart, semanticCover.chart chart), rfl⟩ := rfl
example (atom : U.Atom) :
    (toBodySemanticCover semanticCover skeleton).baseCover.holonomySupport
        (atom, skeleton) =
      (semanticSite.sourceTraceToken atom = true) := rfl
example (left right : semanticCover.CoverChart) :
    (toBodySemanticCover semanticCover skeleton).Overlap
        (ULift.up left) (ULift.up right) =
      ULift.{max v w, w} (semanticCover.Overlap left right) := rfl
example (left middle right : semanticCover.CoverChart) :
    (toBodySemanticCover semanticCover skeleton).TripleOverlap
        (ULift.up left) (ULift.up middle) (ULift.up right) =
      ULift.{max v w, w} (semanticCover.TripleOverlap left middle right) := rfl
example (left right : semanticCover.CoverChart) :
    (toBodySemanticCover semanticCover skeleton).selectedOverlap
        (ULift.up left) (ULift.up right) =
      ULift.up (semanticCover.selectedOverlap left right) := rfl
example (left middle right : semanticCover.CoverChart) :
    (toBodySemanticCover semanticCover skeleton).selectedTriple
        (ULift.up left) (ULift.up middle) (ULift.up right) =
      ULift.up (semanticCover.selectedTriple left middle right) := rfl

variable (chartSimplex :
  semanticCover.CoverChart ->
    (AAT.AG.Cohomology.finitePosetCoverRelativeCover
      (lawEquationStandardComplex coverGeometry G)).simplex 0)
variable (overlapSimplex :
  (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
    semanticCover.Overlap pair.1 pair.2) ->
      (AAT.AG.Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex coverGeometry G)).simplex 1)
variable (tripleSimplex :
  (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
    semanticCover.CoverChart =>
    semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
      (AAT.AG.Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex coverGeometry G)).simplex 2)

example (chart : semanticCover.CoverChart) :
    toBodyDegreeZeroSimplexMap (skeleton := skeleton) semanticCover chartSimplex
        (ULift.up chart) =
      chartSimplex chart := rfl
example (overlap :
    Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
      semanticCover.Overlap pair.1 pair.2) :
    toBodyDegreeOneSimplexMap (skeleton := skeleton) semanticCover overlapSimplex
        ⟨(ULift.up overlap.1.1, ULift.up overlap.1.2), ULift.up overlap.2⟩ =
      overlapSimplex overlap := rfl
example (triple :
    Sigma fun indices : semanticCover.CoverChart × semanticCover.CoverChart ×
      semanticCover.CoverChart =>
      semanticCover.TripleOverlap indices.1 indices.2.1 indices.2.2) :
    toBodyDegreeTwoSimplexMap (skeleton := skeleton) semanticCover tripleSimplex
        ⟨(ULift.up triple.1.1, ULift.up triple.1.2.1,
          ULift.up triple.1.2.2), ULift.up triple.2⟩ =
      tripleSimplex triple := rfl

example
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
      SemanticRepairAdditiveH1Zero envelope.toAdditiveCechH1Data :=
  lawEquation_constructs_groundedComparisonPacket_viaBody D semanticCover
    chartSimplex overlapSimplex tripleSimplex hholds

end GroundedPacketBridge
end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
