import ResearchLean.AG.DoctrineFiberProduct.DoctrinePullbackWitnesses
import ResearchLean.AG.DoctrineFiberProduct.PointedDoctrinePullback
import ResearchLean.AG.DoctrineFiberProduct.CartesianBranch
import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducerWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticCovarianceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCPastingClosure
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastedCrossRouteCompatibility

/-!
# Doctrine Fiber Product and Base Change Theorem

This module states the fixed G-110 target as one carrier-polymorphic theorem.
Its five fields retain the accepted `(A)`--`(E)` producers, exactness and
noncanonicity witnesses, actual-route diagnostic covariance, and horizontal
and vertical pasting laws.  The constructor consumes the reviewed declarations
directly; it does not accept a pullback, lift, mate, target diagnostic, or
pasting certificate from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open CategoryTheory.Limits
open AtomFoundation CrossStageCoherence TransportCoherence

local instance targetFiniteModelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- `(A)`: generated doctrine pullbacks, together with the finite-code proper
fiber firing that rules out empty or product-like degeneration. -/
structure DoctrineFiberProductLayer
    (U : AtomCarrier.{u}) : Prop where
  universal : ∀ {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base),
    IsPullback
      (doctrinePullbackFst sigmaOne sigmaTwo)
      (doctrinePullbackSnd sigmaOne sigmaTwo)
      sigmaOne sigmaTwo
  finiteProper :
    ProperDoctrineFiber
      (doctrinePullbackFst finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom)
      (doctrinePullbackSnd finiteThreeToTwoDoctrineHom
        finiteThreeToTwoDoctrineHom)

/-- `(B)`: the one carrier-global branch, its finite-code soundness surface,
and the selected-regime lift producer used downstream. -/
structure CartesianLiftLayer
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] : Prop where
  schemaSound : ∀ presentation : CartPresentation U,
    (∀ source,
      (toSemanticCart presentation).target.doctrine.normalize
          ((toSemanticCart presentation).hom.doctrineHom.sourceMap source) =
        (toSemanticCart presentation).hom.doctrineHom.sourceMap
          ((toSemanticCart presentation).source.doctrine.normalize source)) ∧
    (∀ source atom,
      (toSemanticCart presentation).source.doctrine.extracts source atom ↔
        (toSemanticCart presentation).target.doctrine.extracts
          ((toSemanticCart presentation).hom.doctrineHom.sourceMap source)
          ((toSemanticCart presentation).hom.doctrineHom.atomEquiv atom)) ∧
    (toSemanticCart presentation).hom.doctrineHom.sourceMap
        (toSemanticCart presentation).source.source =
      (toSemanticCart presentation).target.source
  globalBranch : GlobalCartesianLift.{u}
  artifactBranch :
    globalDisjunctionArtifact = .global globalCartesianLift
  rightBranchExcluded : IsEmpty RightBranch.{u}
  producerMembership : ∀ (input : RealizableHom U),
    (cartesianRegimeOfDisjunction globalDisjunctionArtifact U).HCart input
  producerLift : ∀ (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target),
    (cartesianRegimeOfDisjunction globalDisjunctionArtifact U).HCart input →
    HasStrongCartesianLift input.semantic targetPackage

/-- `(C)`: pointed pullback generation, exact canonical mates for all
cleavages, and the authored-support positive/negative canonicity pair. -/
structure BeckChevalleyLayer
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] : Prop where
  pointedPullback : ∀ {DOne DTwo Base : ExtractionInstance U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base),
    IsPullback
      (pointedPullbackFst sigmaOne sigmaTwo)
      (pointedPullbackSnd sigmaOne sigmaTwo)
      sigmaOne sigmaTwo
  canonicalMateExact : ∀ presentation : BCPresentation U,
    IsIso (coreBeckChevalleyMate presentation)
  arbitraryCleavageMateExact : ∀ (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic),
    IsIso (coreBeckChevalleyCleavageMate presentation
      leftCleavage rightCleavage)
  canonicityPositive :
    MateCoherentRel FiniteModel.carrier finiteAuthoredBCDatumSquare
  canonicityNegative :
    ¬ MateCoherentRel FiniteModel.carrier finiteAxisFoldBCDatumSquare
  canonicityOrbitFailure : ∀
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData),
    InReselectionOrbit finiteAxisFoldBCDatumSquare.toTransportData cochain →
      ∃ reselection : EdgeReselection finiteAxisFoldBCDatumSquare.context.lift,
        initialRawDefectCochain
            (finiteAxisFoldBCDatumSquare.reselectEdges reselection).toTransportData =
          cochain ∧
        ¬ MateCoherentRel FiniteModel.carrier
          (finiteAxisFoldBCDatumSquare.reselectEdges reselection)
  canonicityOrbitNontrivial :
    ∃ cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData,
      InReselectionOrbit finiteAxisFoldBCDatumSquare.toTransportData cochain ∧
        cochain ≠
          initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
  comparisonReplacement : ∀
    (input : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance input.context.square.semantic),
    (authoredSupportDirectRouteReplacementComparison
        input.context replacement).hom ≫
      generatedAuthoredDiagnosticObjectCollapseComparison
        (input.replacePresentation replacement) =
    generatedAuthoredDiagnosticObjectCollapseComparison input ≫
      (authoredSupportViaBaseRouteReplacementComparison
        input.context replacement).hom
  relationReplacement : ∀
    (input : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance input.context.square.semantic),
    MateCoherentRel U (input.replacePresentation replacement) ↔
      MateCoherentRel U input

/-- The named finite `(D)` firing, kept as one proposition so the target
theorem cannot forget either nonidentity input or either actual-route output. -/
def FiniteDiagnosticCovarianceNonvacuity : Prop :=
  initialRawDefectCochain
      finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
      SingleDiskTwoCell.face ≠ 1 ∧
    finiteCovarianceSourceReselection ≠ 1 ∧
    CoherentAt
      finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
      finiteCovarianceSourceReselection ∧
    CoherentAt
      (bcDiagnosticDirectTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence)
      (bcDiagnosticDirectMapEdgeReselection finiteCovarianceBCPresentation
        finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
        finiteCovarianceSourceReselection) ∧
    CoherentAt
      (bcDiagnosticViaBaseTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence)
      (bcDiagnosticViaBaseMapEdgeReselection finiteCovarianceBCPresentation
        finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
        finiteCovarianceSourceReselection) ∧
    TransportObstructionVanishes
      (bcDiagnosticDirectTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence) ∧
    TransportObstructionVanishes
      (bcDiagnosticViaBaseTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence)

/-- `(D)`: unconditional source-fiber-qualified covariance on both actual
Beck--Chevalley routes, with the fixed finite nonvacuity witness. -/
structure DiagnosticBaseChangeLayer
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] : Prop where
  generatedD1D3 : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation
      interpretation),
    QualifiedDiagnosticBaseChangeD1D3 presentation interpretation incidence
  directReselectedPath : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (reselection : EdgeReselection incidence.toFiberwise.toLiftData)
    {i j : (toSemanticBC presentation).diagnostic.Vertex}
    (path : (toSemanticBC presentation).diagnostic.Path i j),
    fiberReselectedPath
        (incidence.toFiberwise.map (bcDiagnosticDirectFunctor presentation))
        (bcDiagnosticDirectMapEdgeReselection presentation interpretation
          incidence reselection) path =
      (bcDiagnosticDirectFunctor presentation).map
        (fiberReselectedPath incidence.toFiberwise reselection path)
  viaBaseReselectedPath : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (reselection : EdgeReselection incidence.toFiberwise.toLiftData)
    {i j : (toSemanticBC presentation).diagnostic.Vertex}
    (path : (toSemanticBC presentation).diagnostic.Path i j),
    fiberReselectedPath
        (incidence.toFiberwise.map (bcDiagnosticViaBaseFunctor presentation))
        (bcDiagnosticViaBaseMapEdgeReselection presentation interpretation
          incidence reselection) path =
      (bcDiagnosticViaBaseFunctor presentation).map
        (fiberReselectedPath incidence.toFiberwise reselection path)
  directCoherence : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (reselection : EdgeReselection incidence.toFiberwise.toLiftData),
    CoherentAt incidence.toFiberwise.toTransportData reselection →
      CoherentAt
        (bcDiagnosticDirectTransportedInterpretationData presentation
          interpretation incidence)
        (bcDiagnosticDirectMapEdgeReselection presentation interpretation
          incidence reselection)
  viaBaseCoherence : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (reselection : EdgeReselection incidence.toFiberwise.toLiftData),
    CoherentAt incidence.toFiberwise.toTransportData reselection →
      CoherentAt
        (bcDiagnosticViaBaseTransportedInterpretationData presentation
          interpretation incidence)
        (bcDiagnosticViaBaseMapEdgeReselection presentation interpretation
          incidence reselection)
  directVanishing : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation),
    TransportObstructionVanishes incidence.toFiberwise.toTransportData →
      TransportObstructionVanishes
        (bcDiagnosticDirectTransportedInterpretationData presentation
          interpretation incidence)
  viaBaseVanishing : ∀
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation),
    TransportObstructionVanishes incidence.toFiberwise.toTransportData →
      TransportObstructionVanishes
        (bcDiagnosticViaBaseTransportedInterpretationData presentation
          interpretation incidence)
  finiteNonvacuity : FiniteDiagnosticCovarianceNonvacuity

/-- `(E)`: finite-code pullback closure and diagnostic comparison compatibility
for both generated pasting directions. -/
structure PastingClosureLayer
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] : Prop where
  pullbackClosure : ∀ input : BCPastingInput U, BCPastingClosure input
  horizontalDiagnostic : ∀
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation),
    HorizontalPastedBCDiagnosticCrossRouteCompatibility
      pasting interpretation incidence
  verticalDiagnostic : ∀
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation),
    VerticalPastedBCDiagnosticCrossRouteCompatibility
      pasting interpretation incidence

/-- Fixed G-110 target statement: the five accepted layers hold together for
every carrier in the finite-presentation realization calculus. -/
structure DoctrineFiberProductAndBaseChangeTheorem
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] : Prop where
  fiberProduct : DoctrineFiberProductLayer U
  cartesianLift : CartesianLiftLayer U
  beckChevalley : BeckChevalleyLayer U
  diagnosticBaseChange : DiagnosticBaseChangeLayer U
  pastingClosure : PastingClosureLayer U

/-- The Doctrine Fiber Product and Base Change Theorem. -/
theorem doctrineFiberProductAndBaseChangeTheorem
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    DoctrineFiberProductAndBaseChangeTheorem U where
  fiberProduct :=
    { universal := doctrinePullback_isPullback
      finiteProper := finiteProperDoctrineFiber }
  cartesianLift :=
    { schemaSound := toSemanticCart_sound
      globalBranch := globalCartesianLift
      artifactBranch := rfl
      rightBranchExcluded := rightBranch_isEmpty
      producerMembership := selectedCartesianRegime_HCart U
      producerLift := fun input targetPackage membership =>
        CartesianRegime.hasStrongCartesianLift
          (cartesianRegimeOfDisjunction globalDisjunctionArtifact U)
          input membership targetPackage }
  beckChevalley :=
    { pointedPullback := pointedPullback_isPullback
      canonicalMateExact := coreBeckChevalleyMate_isIso
      arbitraryCleavageMateExact := coreBeckChevalleyCleavageMate_isIso
      canonicityPositive :=
        finiteAuthoredBCDatumSquare_mateCoherentRel
      canonicityNegative := finiteAxisFoldBCDatumSquare_not_mateCoherentRel
      canonicityOrbitFailure :=
        finiteAxisFold_public_not_mateCoherentRel_on_orbit
      canonicityOrbitNontrivial :=
        finiteAxisFold_authoredComparison_orbit_nontrivial
      comparisonReplacement :=
        generatedAuthoredDiagnosticObjectCollapseComparison_replacement
      relationReplacement := mateCoherentRel_replacePresentation_iff }
  diagnosticBaseChange :=
    { generatedD1D3 := qualifiedDiagnosticBaseChangeD1D3
      directReselectedPath := bcDiagnosticDirectReselectedPath_map
      viaBaseReselectedPath := bcDiagnosticViaBaseReselectedPath_map
      directCoherence := bcDiagnosticDirectCoherentAt_map
      viaBaseCoherence := bcDiagnosticViaBaseCoherentAt_map
      directVanishing := bcDiagnosticDirectTransportObstructionVanishes
      viaBaseVanishing := bcDiagnosticViaBaseTransportObstructionVanishes
      finiteNonvacuity := finiteDiagnosticCovariance_nonvacuous }
  pastingClosure :=
    { pullbackClosure := bcPastingClosure
      horizontalDiagnostic :=
        horizontalPastedBCDiagnosticCrossRouteCompatibility
      verticalDiagnostic :=
        verticalPastedBCDiagnosticCrossRouteCompatibility }

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
