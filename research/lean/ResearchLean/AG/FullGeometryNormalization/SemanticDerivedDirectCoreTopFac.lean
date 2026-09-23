import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedCoreEndpointProjection

/-! # The top-edge factorization of the semantic direct core endpoint -/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

private theorem semanticDerivedDirectCoreIsoAt_hom_parts
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    let G := semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq
    let S := (geometryFiberProjection input.square.southwest).obj
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
    let compare := (semanticCoreInverseReindexToGlobalIso input.square.left).app S
    (semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom.1 =
      (towerTransportComparisonApp input.square.top G).hom.1 ≫
        ((coreFiberTransportFunctor input.square.top).map compare.hom).1 := by
  dsimp only
  simp only [semanticDerivedDirectCoreIsoAt, Iso.trans_hom,
    Functor.mapIso_hom, semanticDerivedPullCoreIsoApp, Iso.refl_hom]
  change ((towerTransportComparisonApp input.square.top
        (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)).hom ≫
      (coreFiberTransportFunctor input.square.top).map (𝟙 _) ≫
      (coreFiberTransportFunctor input.square.top).map
        ((semanticCoreInverseReindexToGlobalIso input.square.left).app
          ((geometryFiberProjection input.square.southwest).obj
            (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))).hom).1 =
    ((towerTransportComparisonApp input.square.top
        (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)).hom ≫
      (coreFiberTransportFunctor input.square.top).map
        ((semanticCoreInverseReindexToGlobalIso input.square.left).app
          ((geometryFiberProjection input.square.southwest).obj
            (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))).hom).1
  exact congrArg Subtype.val (by simp)

/-- The projected top lift followed by the direct endpoint comparison is
the global selected pull comparison followed by core transport. -/
theorem semanticDerivedDirectCoreIsoAt_top_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    let S := (geometryFiberProjection input.square.southwest).obj
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
    (geometryProjection U).map
        (geomFiberLift input.square.top
          (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)) ≫
      (semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom.1 =
    ((semanticCoreInverseReindexToGlobalIso input.square.left).app S).hom.1 ≫
      coreFiberLift input.square.top
        ((exact_bottom_semantic_global_reindex_functor input.square.left).obj S) := by
  dsimp only
  let G := semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq
  let S := (geometryFiberProjection input.square.southwest).obj
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  let compare := (semanticCoreInverseReindexToGlobalIso input.square.left).app S
  let topLift := (geometryProjection U).map (geomFiberLift input.square.top G)
  let tower := towerTransportComparisonApp input.square.top G
  have htower : topLift ≫ tower.hom.1 =
      coreFiberLift input.square.top
        ((geometryFiberProjection input.square.northwest).obj G) := by
    simpa only [topLift, tower] using
      towerTransportComparisonApp_hom_fac input.square.top G
  have hmap : coreFiberLift input.square.top
        ((geometryFiberProjection input.square.northwest).obj G) ≫
      ((coreFiberTransportFunctor input.square.top).map compare.hom).1 =
    compare.hom.1 ≫ coreFiberLift input.square.top
      ((exact_bottom_semantic_global_reindex_functor input.square.left).obj S) := by
    exact coreFiberTransportMap_fac input.square.top compare.hom
  rw [semanticDerivedDirectCoreIsoAt_hom_parts]
  rw [← Category.assoc, htower]
  exact hmap

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
