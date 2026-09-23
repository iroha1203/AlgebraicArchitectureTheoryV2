import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedBarAlphaLeftPostFactor
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedDirectCoreTopFac

/-!
# Core projection of the semantic complete-geometry mate

The projected complete geometry comparison is the independently generated
semantic core Beck--Chevalley mate, conjugated by the generated endpoint
comparisons. The proof compares both arrows after the top cocartesian lift
and the right Cartesian lift, then cancels those lifts.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Core projection of the complete semantic comparison, the generic form
of the 5.38 projection triangle. -/
theorem semanticDerivedBarAlphaIsoAt_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (geometryFiberProjection input.square.northeast).map
          (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq
            square_isPullback).hom ≫
        (semanticDerivedViaBaseCoreIsoAt input Q k g endpoint_eq).hom =
      (semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom ≫
        (semanticCoreBeckChevalleyMate input).app
          ((geometryFiberProjection input.square.southwest).obj
            (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)) := by
  apply semanticDerivedBarAlpha_projection_of_post_fac
    input Q k g endpoint_eq square_isPullback
  let S := (geometryFiberProjection input.square.southwest).obj
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  let topLift := (geometryProjection U).map
    (geomFiberLift input.square.top
      (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq))
  let rightLift := (exact_bottom_semantic_global_selected_lift
    input.square.right ((coreFiberTransportFunctor input.square.bottom).obj S)).hom
  let leftPull := (geometryProjection U).map
    (semanticGeometryPullLift input.square.left
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
  let bottomLift := coreFiberLift input.square.bottom S
  let compareLeft := ((semanticCoreInverseReindexToGlobalIso
    input.square.left).app S).hom.1
  let topCoreLift := coreFiberLift input.square.top
    ((exact_bottom_semantic_global_reindex_functor input.square.left).obj S)
  have hleft := semanticDerivedBarAlpha_left_post_fac
    input Q k g endpoint_eq square_isPullback
  have htop := semanticDerivedDirectCoreIsoAt_top_fac
    input Q k g endpoint_eq
  have hmate := semanticCoreBeckChevalleyMate_app_iterated_fac
    input S
  have hcompare := semanticCoreInverseReindexToGlobalIso_hom_fac
    input.square.left S
  have hpull := semanticDerivedPullCoreLift_eq input.square.left
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  change topLift ≫
      (semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom.1 =
    compareLeft ≫ topCoreLift at htop
  change topCoreLift ≫ ((semanticCoreBeckChevalleyMate input).app S).1 ≫
      rightLift =
    (exact_bottom_semantic_global_selected_lift input.square.left S).hom ≫
      bottomLift at hmate
  change compareLeft ≫
      (exact_bottom_semantic_global_selected_lift input.square.left S).hom =
    (semanticCoreInverseLift input.square.left S).hom at hcompare
  change leftPull = (semanticCoreInverseLift input.square.left S).hom at hpull
  change topLift ≫
      (((geometryFiberProjection input.square.northeast).map
        (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq
          square_isPullback).hom ≫
        (semanticDerivedViaBaseCoreIsoAt input Q k g endpoint_eq).hom).1 ≫
        rightLift) =
    topLift ≫
      (((semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom ≫
        (semanticCoreBeckChevalleyMate input).app S).1 ≫ rightLift)
  have hright :
      topLift ≫
        (((semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom ≫
          (semanticCoreBeckChevalleyMate input).app S).1 ≫ rightLift) =
      leftPull ≫ bottomLift := by
    change topLift ≫
      (((semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom.1 ≫
        ((semanticCoreBeckChevalleyMate input).app S).1) ≫ rightLift) = _
    calc
      _ = (topLift ≫
            (semanticDerivedDirectCoreIsoAt input Q k g endpoint_eq).hom.1) ≫
          (((semanticCoreBeckChevalleyMate input).app S).1 ≫ rightLift) := by
            simp only [Category.assoc]
      _ = (compareLeft ≫ topCoreLift) ≫
          (((semanticCoreBeckChevalleyMate input).app S).1 ≫ rightLift) :=
            congrArg (fun h => h ≫
              (((semanticCoreBeckChevalleyMate input).app S).1 ≫ rightLift)) htop
      _ = compareLeft ≫
          (topCoreLift ≫ ((semanticCoreBeckChevalleyMate input).app S).1 ≫
            rightLift) := by simp only [Category.assoc]
      _ = compareLeft ≫
          ((exact_bottom_semantic_global_selected_lift
            input.square.left S).hom ≫ bottomLift) :=
            congrArg (fun h => compareLeft ≫ h) hmate
      _ = (compareLeft ≫
          (exact_bottom_semantic_global_selected_lift
            input.square.left S).hom) ≫ bottomLift := by
              simp only [Category.assoc]
      _ = leftPull ≫ bottomLift := by rw [hcompare, ← hpull]
  exact hleft.trans hright.symm

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
