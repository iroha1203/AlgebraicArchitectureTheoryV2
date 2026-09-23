import ResearchLean.AG.FullGeometryNormalization.SemanticCoreBeckChevalleyMate
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedBarAlphaProjection
import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyFactorization

/-!
# Identification of the semantic core mate with Theorem 5.11

The semantic complete-geometry construction uses the canonical core mate of
the fixed semantic square. Proposition 5.12 identifies its components by the
two selected lift triangles, independently of any finite presentation.
-/

namespace AAT.AG.FullGeometryNormalization

universe u
universe v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport
open DoctrineFiberProduct

/-- The core mate used by complete-geometry normalization is the component
of the canonical semantic mate of Theorem 5.11 at every southwest package. -/
theorem semanticCoreBeckChevalleyMate_app_eq_doctrine
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (source : CoreFiber input.square.southwest) :
    (semanticCoreBeckChevalleyMate input).app source =
      (DoctrineFiberProduct.semanticCoreBeckChevalleyMate input.square).app source := by
  exact (DoctrineFiberProduct.semanticCoreBeckChevalleyMate_lift_fac_iff
    input.square source ((semanticCoreBeckChevalleyMate input).app source)).mp
      (semanticCoreBeckChevalleyMate_app_iterated_fac input source)

/-- Identification of the full natural transformations, without a finite
code, decidable equality, or an additional comparison hypothesis. -/
theorem semanticCoreBeckChevalleyMate_eq_doctrine
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    semanticCoreBeckChevalleyMate input =
      DoctrineFiberProduct.semanticCoreBeckChevalleyMate input.square := by
  apply NatTrans.ext
  funext source
  exact semanticCoreBeckChevalleyMate_app_eq_doctrine input source

/-- The fixed Proposition 5.38 projection triangle with the canonical mate
of Theorem 5.11 as its core edge. -/
theorem semanticDerivedBarAlphaIsoAt_projection_doctrineMate
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
        (DoctrineFiberProduct.semanticCoreBeckChevalleyMate input.square).app
          ((geometryFiberProjection input.square.southwest).obj
            (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)) := by
  rw [← semanticCoreBeckChevalleyMate_app_eq_doctrine input]
  exact semanticDerivedBarAlphaIsoAt_projection input Q k g endpoint_eq square_isPullback

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
