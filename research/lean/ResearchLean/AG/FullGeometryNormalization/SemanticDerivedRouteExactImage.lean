import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedGeneratedMate

/-!
# Exact images and lower routes for a semantic derived square

The bottom refinement and the generated horizontal refinement come from exact
arrows.  For a fixed southwest geometry, the two lower routes through the
generated mixed pullback agree with the original two-edge routes after the
source comparison supplied by the pullback property of the semantic square.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable local instance semanticDerivedRouteAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _

/-- The actual bottom exact arrow at the endpoints selected by the derived
refinement configuration. -/
def semanticDerivedBaseRefinementExactArrow
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    (semanticDerivedRefinementBCConfiguration input).sourcePointAt
        (semanticDerivedRefinementBCCompatibleSource input) ⟶
      (semanticDerivedRefinementBCConfiguration input).targetPointAt
        (semanticDerivedRefinementBCCompatibleSource input) where
  doctrineHom := input.square.bottom.doctrineHom
  source_eq := rfl

/-- The derived base refinement is the full pointed refinement image of the
semantic bottom exact arrow. -/
theorem semanticDerivedBaseRefinement_exactImage
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    (semanticDerivedRefinementBCConfiguration input).baseRefinementAt
        (semanticDerivedRefinementBCCompatibleSource input) =
      (exactPointedToRefinement U).map
        (semanticDerivedBaseRefinementExactArrow input) := by
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · funext source
    rfl
  · funext atom
    rfl

/-- The generated mixed horizontal refinement is the image of the generated
exact comparison.  Its exactness follows from the semantic bottom arrow. -/
theorem semanticDerivedPulledRefinement_exactImage
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    (semanticDerivedRefinementBCConfiguration input).pulledRefinementAt
        (semanticDerivedRefinementBCCompatibleSource input) =
      (exactPointedToRefinement U).map
        (semanticDerivedPulledComparison input) := by
  exact (pulledRefinementAt_mem_exactComparisonImage
    (semanticDerivedRefinementBCConfiguration input)
    (semanticDerivedRefinementBCCompatibleSource input)
    (semanticDerivedRefinementBC_exactImage input)).symm

/-- The mixed-source first projection becomes the original left edge after
inverting the pullback comparison. -/
theorem semanticDerivedMixedFst_sourceIso_inv
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedPullbackSourceIso input square_isPullback).inv ≫
      semanticDerivedMixedFst input = input.square.left := by
  rw [← semanticDerivedPullbackSourceIso_hom_left input square_isPullback]
  simp

/-- The generated exact comparison, followed by the target comparison,
becomes the original top edge after inverting the source comparison. -/
theorem semanticDerivedPulledComparison_sourceIso_inv
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedPullbackSourceIso input square_isPullback).inv ≫
        semanticDerivedPulledComparison input ≫
        (semanticDerivedPullbackTargetIso input).hom =
      input.square.top := by
  rw [← semanticDerivedPulledComparison_comparisonSquare input square_isPullback]
  simp

/-- At the fixed source geometry, the mixed base-first lower route factors as
the literal left-then-bottom route of the semantic square. -/
theorem semanticDerivedGeneratedBaseRoute_lower_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U) (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    eqToHom (semanticDerivedGeneratedBaseRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback).2 ≫
        (semanticDerivedPullbackSourceIso input square_isPullback).inv ≫
        semanticDerivedMixedFst input ≫ input.square.bottom =
      eqToHom (semanticDerivedGeneratedBaseRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback).2 ≫
        input.square.left ≫ input.square.bottom := by
  calc
    _ = eqToHom (semanticDerivedGeneratedBaseRouteNorthwestAt
          input Q k g endpoint_eq square_isPullback).2 ≫
          ((semanticDerivedPullbackSourceIso input square_isPullback).inv ≫
            semanticDerivedMixedFst input) ≫ input.square.bottom := by
        simp only [Category.assoc]
    _ = _ := by
      rw [semanticDerivedMixedFst_sourceIso_inv input square_isPullback]

/-- At the fixed source geometry, the mixed pulled-first lower route factors
as the literal top-then-right route of the semantic square. -/
theorem semanticDerivedGeneratedPulledRoute_lower_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U) (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    eqToHom (semanticDerivedGeneratedPulledRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback).2 ≫
        (semanticDerivedPullbackSourceIso input square_isPullback).inv ≫
        semanticDerivedPulledComparison input ≫
        (semanticDerivedPullbackTargetIso input).hom ≫
        input.square.right =
      eqToHom (semanticDerivedGeneratedPulledRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback).2 ≫
        input.square.top ≫ input.square.right := by
  calc
    _ = eqToHom (semanticDerivedGeneratedPulledRouteNorthwestAt
          input Q k g endpoint_eq square_isPullback).2 ≫
          ((semanticDerivedPullbackSourceIso input square_isPullback).inv ≫
            semanticDerivedPulledComparison input ≫
            (semanticDerivedPullbackTargetIso input).hom) ≫
          input.square.right := by
        simp only [Category.assoc]
    _ = _ := by
      rw [semanticDerivedPulledComparison_sourceIso_inv input square_isPullback]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
