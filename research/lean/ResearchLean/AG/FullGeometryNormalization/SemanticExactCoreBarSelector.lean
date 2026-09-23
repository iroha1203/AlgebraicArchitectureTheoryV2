import ResearchLean.AG.FullGeometryNormalization.SemanticExactBarBetaClassification
import ResearchLean.AG.FullGeometryNormalization.SemanticExactCoreNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.SemanticCoreBeckChevalleyMate

/-!
# The semantic cochain selector on the core route

The same diagnostic face and cochain used by the complete-geometry comparison
select a source core normalization. The core target projector is its image along
the actual bottom transport and right Cartesian pullback.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence DoctrineFiberProduct
open TransportCoherence

set_option maxHeartbeats 3000000

/-- The core of the chosen diagnostic face in the semantic southwest fiber. -/
def semanticExactBarSourceCoreFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) : CoreFiber input.square.southwest :=
  ⟨semanticExactBarSourceCoreAt input interpretation z, endpoint_eq⟩

/-- Core via-base route selected by the same semantic square. -/
noncomputable def semanticExactBarViaCoreAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) : CoreFiber input.square.northeast :=
  (semanticCoreInverseReindexFunctor input.square.right).obj
    ((coreFiberTransportFunctor input.square.bottom).obj
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq))

/-- The cochain selects the canonical source core normalization, or the
identity when its specified condition does not hold. -/
noncomputable def semanticExactBarSourceCoreSelectorAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq ⟶
      semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · exact canonicalCoreFiberNormalization
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)
      selected.2
  · exact 𝟙 _

/-- Source geometry selector associated with the same diagnostic cochain. -/
noncomputable def semanticExactBarSourceGeometrySelectorAt
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
    semanticDerivedSouthwestGeometryFiber input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq ⟶
    semanticDerivedSouthwestGeometryFiber input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · exact canonicalGeometryFiberNormalization _ selected.2
  · exact 𝟙 _

/-- The selected source geometry normalization has exactly the selected
core normalization as its projection. -/
theorem semanticExactBarSourceSelector_projection
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
    (geometryFiberProjection input.square.southwest).map
      (semanticExactBarSourceGeometrySelectorAt
        input interpretation z omega k g endpoint_eq) =
      semanticExactBarSourceCoreSelectorAt
        input interpretation z omega endpoint_eq := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · simp [semanticExactBarSourceGeometrySelectorAt,
      semanticExactBarSourceCoreSelectorAt, selected,
      canonicalGeometryFiberNormalization,
      canonicalCoreFiberNormalization]
    apply CategoryTheory.Functor.Fiber.hom_ext
    rfl
  · simp [semanticExactBarSourceGeometrySelectorAt,
      semanticExactBarSourceCoreSelectorAt, selected]
    rfl

/-- The selected core target projector is transported through the actual
bottom-push/right-pull route. -/
noncomputable def semanticExactBarTargetCoreProjectorAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarViaCoreAt input interpretation z endpoint_eq ⟶
      semanticExactBarViaCoreAt input interpretation z endpoint_eq :=
  (semanticCoreInverseReindexFunctor input.square.right).map
    ((coreFiberTransportFunctor input.square.bottom).map
      (semanticExactBarSourceCoreSelectorAt
        input interpretation z omega endpoint_eq))

/-- The target core route in the global cleavage used by the independent
semantic Beck--Chevalley mate. -/
noncomputable def semanticExactBarViaGlobalCoreAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) : CoreFiber input.square.northeast :=
  (coreFiberTransportFunctor input.square.bottom ⋙
    exact_bottom_semantic_global_reindex_functor input.square.right).obj
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq)

/-- The selected target core projector in the global right cleavage. -/
noncomputable def semanticExactBarTargetGlobalCoreProjectorAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarViaGlobalCoreAt input interpretation z endpoint_eq ⟶
      semanticExactBarViaGlobalCoreAt input interpretation z endpoint_eq :=
  (coreFiberTransportFunctor input.square.bottom ⋙
    exact_bottom_semantic_global_reindex_functor input.square.right).map
      (semanticExactBarSourceCoreSelectorAt
        input interpretation z omega endpoint_eq)

/-- The core cochain-selected beta is the generated semantic core mate
followed by the selected via-base projector. -/
noncomputable def semanticExactBarCoreBetaAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    (exact_bottom_semantic_global_reindex_functor input.square.left ⋙
      coreFiberTransportFunctor input.square.top).obj
        (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq) ⟶
      semanticExactBarViaGlobalCoreAt input interpretation z endpoint_eq :=
  (semanticCoreBeckChevalleyMate input).app
      (semanticExactBarSourceCoreFiberAt input interpretation z endpoint_eq) ≫
    semanticExactBarTargetGlobalCoreProjectorAt
      input interpretation z omega endpoint_eq

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
