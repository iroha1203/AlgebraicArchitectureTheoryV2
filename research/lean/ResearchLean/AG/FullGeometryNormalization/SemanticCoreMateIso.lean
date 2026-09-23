import ResearchLean.AG.FullGeometryNormalization.SemanticCoreBeckChevalleyMate

/-! # Invertibility of the semantic core Beck--Chevalley mate -/

namespace AAT.AG.FullGeometryNormalization

universe u

open CategoryTheory AtomFoundation CrossStageCoherence
open DoctrineFiberProduct

/-- The generated semantic core mate component is invertible since the
semantic transport/reindex units and counits are invertible. -/
theorem semanticCoreBeckChevalleyMate_app_isIso
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (source : CoreFiber input.square.southwest) :
    IsIso ((semanticCoreBeckChevalleyMate input).app source) := by
  let topSource := (coreFiberTransportFunctor input.square.top).obj
    ((exact_bottom_semantic_global_reindex_functor input.square.left).obj source)
  let unitApp := (semanticGlobalTransportReindexAdjunction
    input.square.right).unit.app topSource
  let squareApp := (bcSemanticCoreTransportSquareIso input).hom.app
    ((exact_bottom_semantic_global_reindex_functor input.square.left).obj source)
  let counitApp := (semanticGlobalTransportReindexAdjunction
    input.square.left).counit.app source
  let mappedSquare :=
    (exact_bottom_semantic_global_reindex_functor input.square.right).map
      squareApp
  let mappedCounit :=
    (exact_bottom_semantic_global_reindex_functor input.square.right).map
      ((coreFiberTransportFunctor input.square.bottom).map counitApp)
  letI : IsIso unitApp := by
    change IsIso ((semanticGlobalTransportReindexUnit
      input.square.right).app topSource)
    exact semanticGlobalTransportReindexUnit_app_isIso
      input.square.right topSource
  letI : IsIso squareApp := by
    dsimp [squareApp]
    infer_instance
  letI : IsIso counitApp := by
    change IsIso ((semanticGlobalTransportReindexCounit
      input.square.left).app source)
    exact semanticGlobalTransportReindexCounit_app_isIso
      input.square.left source
  letI : IsIso mappedSquare := by
    dsimp [mappedSquare]
    infer_instance
  letI : IsIso mappedCounit := by
    dsimp [mappedCounit]
    infer_instance
  rw [semanticCoreBeckChevalleyMate_app]
  change IsIso (unitApp ≫ mappedSquare ≫ mappedCounit)
  infer_instance

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
