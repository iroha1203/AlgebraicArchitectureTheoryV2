import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Classification
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Mate
import ResearchLean.AG.DoctrineFiberProduct.ExactBottomGlobalLiftCoherence

/-!
# Active G-114 supply for Gr4 consumers

The context contains an actual target package and the local regime generated
from the fixed condition.  Exact pullback transport and both refinement lifts
remain derived definitions.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Active refinement base-change data exported to G-115 and G-116. -/
structure ActiveRefinementBCContext (U : AtomCarrier.{u}) where
  /-- Raw unpointed configuration. -/
  configuration : RefinementBCConfiguration U
  /-- Compatible selected sources. -/
  source : configuration.CompatibleSource
  /-- Actual package realizing the selected target point. -/
  targetPackage : CoreFiber (configuration.targetPointAt source)
  /-- The fixed realized-support condition at this selected refinement. -/
  condition : RealizedLocusExtractionReflecting
    (configuration.baseRefinementAt source)
  /-- Local base/pulled regime generated from the fixed condition. -/
  regime : RefinementBCRegimeAt configuration source

/-- Construct the active context; the caller supplies no cleavage or regime. -/
noncomputable def activeRefinementBCContextOfCondition
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (p : C.CompatibleSource) (target : CoreFiber (C.targetPointAt p))
    (condition : RealizedLocusExtractionReflecting (C.baseRefinementAt p)) :
    ActiveRefinementBCContext U where
  configuration := C
  source := p
  targetPackage := target
  condition := condition
  regime := {
    baseCleavage := refinementCleavageOfRealizedReflection
      (C.baseRefinementAt p) condition
    pulledCleavage := refinementCleavageOfRealizedReflection
      (C.pulledRefinementAt p) (pulledRealizedReflection C p condition)
  }

namespace ActiveRefinementBCContext

/-- The regime-generated base refinement lift at the actual target package. -/
noncomputable def baseLift (ctx : ActiveRefinementBCContext U) :
    RefinementCartesianLift
      (ctx.configuration.baseRefinementAt ctx.source) ctx.targetPackage :=
  ctx.regime.baseCleavage.lift ctx.targetPackage

/-- Exact G-112 reindexing of the target package to the pullback target. -/
noncomputable def pullbackTargetPackage (ctx : ActiveRefinementBCContext U) :
    CoreFiber (ctx.configuration.pullbackTargetAt ctx.source) :=
  (exact_bottom_semantic_global_reindex_functor
    (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst).obj
      ctx.targetPackage

/-- The regime-generated pulled refinement lift at the exact-reindexed package. -/
noncomputable def pulledLift (ctx : ActiveRefinementBCContext U) :
    RefinementCartesianLift
      (ctx.configuration.pulledRefinementAt ctx.source)
      ctx.pullbackTargetPackage :=
  ctx.regime.pulledCleavage.lift ctx.pullbackTargetPackage

/-- Relative universal-property regime derived from the context condition. -/
noncomputable def legacyRegime (ctx : ActiveRefinementBCContext U) :
    LegacyRefinementBCRegime
      (ctx.configuration.pointedConfigurationAt ctx.source) :=
  legacyRefinementBCRegimeOfConditionAt
    ctx.configuration ctx.source ctx.condition

/-- Canonical G-112/refinement base-change mate derived from the context. -/
noncomputable def mate (ctx : ActiveRefinementBCContext U) :
    ((ctx.legacyRegime).reverseBase ⋙
        exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst) ⟶
      (exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ⋙
        (ctx.legacyRegime).reversePullback) :=
  refinementBCMateAt ctx.configuration ctx.source ctx.condition

/-- Actual package reached by the base-reverse, then exact-pulled route. -/
noncomputable def baseMatePackage (ctx : ActiveRefinementBCContext U) :
    CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) :=
  (exact_bottom_semantic_global_reindex_functor
    (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).obj
      ((ctx.legacyRegime).reverseBase.obj ctx.targetPackage)

/-- Actual package reached by exact pullback reindexing, then pulled reverse transport. -/
noncomputable def pulledMatePackage (ctx : ActiveRefinementBCContext U) :
    CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) :=
  (ctx.legacyRegime).reversePullback.obj ctx.pullbackTargetPackage

/-- The canonical mate evaluated between the two actual route packages. -/
noncomputable def mateAtTarget (ctx : ActiveRefinementBCContext U) :
    ctx.baseMatePackage ⟶ ctx.pulledMatePackage :=
  ctx.mate.app ctx.targetPackage

end ActiveRefinementBCContext

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
