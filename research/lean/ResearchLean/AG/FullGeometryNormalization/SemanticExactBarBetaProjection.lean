import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedViaCoreNaturality
import ResearchLean.AG.FullGeometryNormalization.SemanticExactCoreBarSelector
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedBarAlphaProjection
import ResearchLean.AG.FullGeometryNormalization.SemanticCoreBeckChevalleyMateIdentification

/-! # Projection of the semantic cochain-selected beta -/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct TransportCoherence

set_option maxHeartbeats 3000000

/-- The complete target projector is the image of the selected source
geometry normalization under the literal via-base functor. -/
theorem semanticExactBarDAt_eq_sourceSelector_map
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      (geomFiberTransportFunctor input.square.bottom ⋙
        semanticGeometryPullFunctor input.square.right).map
          (semanticExactBarSourceGeometrySelectorAt
            input interpretation z omega k g endpoint_eq) := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · simp [semanticExactBarDAt,
      semanticExactBarSourceGeometrySelectorAt, selected]
  · simp [semanticExactBarDAt,
      semanticExactBarSourceGeometrySelectorAt, selected]
    rfl

/-- The target geometry projector projects to the independent selected
global core projector through the generated via-base comparison. -/
theorem semanticExactBarDAt_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    (geometryFiberProjection input.square.northeast).map
        (semanticExactBarDAt input interpretation z omega k g endpoint_eq) ≫
      (semanticDerivedViaBaseCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom =
    (semanticDerivedViaBaseCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq := by
  let sourceSelector := semanticExactBarSourceGeometrySelectorAt
    input interpretation z omega k g endpoint_eq
  have hNat := semanticDerivedViaCoreComparison_naturality
    input sourceSelector
  have hSource := semanticExactBarSourceSelector_projection
    input interpretation z omega k g endpoint_eq
  rw [semanticDerivedViaCoreComparisonApp_fixed] at hNat
  rw [hSource] at hNat
  rw [semanticExactBarDAt_eq_sourceSelector_map]
  exact hNat

/-- The cochain-selected complete beta projects to the generated core mate
followed by the selected core target projector. -/
theorem semanticExactBarBetaAt_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (geometryFiberProjection input.square.northeast).map
        (semanticExactBarBetaAt input interpretation z omega k g
          endpoint_eq square_isPullback) ≫
      (semanticDerivedViaBaseCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom =
    (semanticDerivedDirectCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom ≫
      semanticExactBarCoreBetaAt
        input interpretation z omega endpoint_eq := by
  change
    (geometryFiberProjection input.square.northeast).map
      ((semanticDerivedBarAlphaIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq square_isPullback).hom ≫
        semanticExactBarDAt input interpretation z omega k g endpoint_eq) ≫
      (semanticDerivedViaBaseCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom = _
  rw [Functor.map_comp, Category.assoc,
    semanticExactBarDAt_projection]
  rw [← Category.assoc,
    semanticDerivedBarAlphaIsoAt_projection]
  rfl

/-- The selected core beta uses the canonical semantic mate of Theorem 5.11
followed by the cochain-selected target projector. -/
theorem semanticExactBarCoreBetaAt_eq_doctrineMate
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarCoreBetaAt input interpretation z omega endpoint_eq =
      (DoctrineFiberProduct.semanticCoreBeckChevalleyMate input.square).app
        (semanticExactBarSourceCoreFiberAt
          input interpretation z endpoint_eq) ≫
      semanticExactBarTargetGlobalCoreProjectorAt
        input interpretation z omega endpoint_eq := by
  simp only [semanticExactBarCoreBetaAt,
    semanticCoreBeckChevalleyMate_app_eq_doctrine]

/-- The complete beta projection with the original canonical core mate
exposed as its first factor. -/
theorem semanticExactBarBetaAt_projection_doctrineMate
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (geometryFiberProjection input.square.northeast).map
        (semanticExactBarBetaAt input interpretation z omega k g
          endpoint_eq square_isPullback) ≫
      (semanticDerivedViaBaseCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom =
    (semanticDerivedDirectCoreIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).hom ≫
      ((DoctrineFiberProduct.semanticCoreBeckChevalleyMate input.square).app
        (semanticExactBarSourceCoreFiberAt
          input interpretation z endpoint_eq) ≫
        semanticExactBarTargetGlobalCoreProjectorAt
          input interpretation z omega endpoint_eq) := by
  rw [← semanticExactBarCoreBetaAt_eq_doctrineMate]
  exact semanticExactBarBetaAt_projection input interpretation z omega
    k g endpoint_eq square_isPullback

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
