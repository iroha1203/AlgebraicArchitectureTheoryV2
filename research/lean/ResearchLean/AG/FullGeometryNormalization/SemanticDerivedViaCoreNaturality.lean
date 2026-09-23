import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedPullCoreMapNaturality

/-! # Naturality of the via-base geometry/core comparison -/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The via-base comparison at an arbitrary southwest geometry. -/
noncomputable def semanticDerivedViaCoreComparisonApp
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (G : GeomFiber.{u, v} input.square.southwest) :
    (geometryFiberProjection input.square.northeast).obj
      ((geomFiberTransportFunctor input.square.bottom ⋙
        semanticGeometryPullFunctor input.square.right).obj G) ≅
    (coreFiberTransportFunctor input.square.bottom ⋙
      exact_bottom_semantic_global_reindex_functor input.square.right).obj
        ((geometryFiberProjection input.square.southwest).obj G) :=
  semanticDerivedPullCoreIsoApp input.square.right
      ((geomFiberTransportFunctor input.square.bottom).obj G) ≪≫
    (semanticCoreInverseReindexFunctor input.square.right).mapIso
      (towerTransportComparisonApp input.square.bottom G) ≪≫
    (semanticCoreInverseReindexToGlobalIso input.square.right).app
      ((coreFiberTransportFunctor input.square.bottom).obj
        ((geometryFiberProjection input.square.southwest).obj G))

/-- The generic comparison specializes to the fixed-coefficient endpoint. -/
theorem semanticDerivedViaCoreComparisonApp_fixed
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (Q : AATCorePackage U) (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedViaCoreComparisonApp input
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq) =
    semanticDerivedViaBaseCoreIsoAt input Q k g endpoint_eq := rfl

/-- Naturality of the via-base comparison on every southwest vertical
geometry morphism. -/
theorem semanticDerivedViaCoreComparison_naturality
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    {G H : GeomFiber.{u, v} input.square.southwest} (f : G ⟶ H) :
    (geometryFiberProjection input.square.northeast).map
        ((geomFiberTransportFunctor input.square.bottom ⋙
          semanticGeometryPullFunctor input.square.right).map f) ≫
      (semanticDerivedViaCoreComparisonApp input H).hom =
    (semanticDerivedViaCoreComparisonApp input G).hom ≫
      (coreFiberTransportFunctor input.square.bottom ⋙
        exact_bottom_semantic_global_reindex_functor input.square.right).map
          ((geometryFiberProjection input.square.southwest).map f) := by
  let fPush := (geomFiberTransportFunctor input.square.bottom).map f
  let coreF := (geometryFiberProjection input.square.southwest).map f
  have hPull := semanticDerivedPullCoreMap_eq input.square.right fPush
  have hTower := towerTransportComparison_naturality input.square.bottom f
  have hGlobalPush := (semanticCoreInverseReindexToGlobalIso
    input.square.right).hom.naturality
      ((geometryFiberProjection input.square.southeast).map fPush)
  have hTowerGlobal := congrArg
    (exact_bottom_semantic_global_reindex_functor input.square.right).map
      hTower
  simp only [Functor.map_comp, Functor.comp_map] at hTowerGlobal
  unfold semanticDerivedViaCoreComparisonApp
  simp [semanticDerivedPullCoreIsoApp, Functor.comp_map,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hPull]
  dsimp only [fPush] at hGlobalPush hTowerGlobal ⊢
  simp only [← Category.assoc]
  rw [hGlobalPush]
  simp only [Category.assoc]
  rw [hTowerGlobal]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
