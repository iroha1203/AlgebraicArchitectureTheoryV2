import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedGeneratedEndpointBridge
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedBarAlphaTriangle
import ResearchLean.AG.DoctrineFiberProduct.BCSchema

/-!
# Semantic derived comparison at a G-106 diagnostic face

The source package here is the package selected by the same semantic
diagnostic interpretation and face `z`.  The southwest endpoint equation and
Cartesian square are explicit geometric hypotheses.  The comparison and its
G-118 factorization are inherited from the constructed semantic routes.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

/-- The actual G-106 source package selected at diagnostic face `z`. -/
abbrev semanticDerivedDiagnosticSourcePackageAt
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell) : AATCorePackage U :=
  interpretation.data.lift.package (input.diagnostic.twoTarget z)

/-- The literal direct complete geometry generated from the selected package. -/
noncomputable abbrev semanticDerivedDiagnosticDirectGeometryAt
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) =
        input.square.southwest) : GeomFiber input.square.northeast :=
  semanticDerivedDirectGeometryAt input
    (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
    k g endpoint_eq

/-- The literal via-base complete geometry generated from the selected package. -/
noncomputable abbrev semanticDerivedDiagnosticViaBaseGeometryAt
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) =
        input.square.southwest) : GeomFiber input.square.northeast :=
  semanticDerivedViaBaseGeometryAt input
    (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
    k g endpoint_eq

/-- The complete two-route comparison at the actual diagnostic source `P_z`. -/
noncomputable def semanticDerivedDiagnosticBarAlphaIsoAt
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) =
        input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedDiagnosticDirectGeometryAt input interpretation z k g endpoint_eq ≅
      semanticDerivedDiagnosticViaBaseGeometryAt input interpretation z k g endpoint_eq :=
  semanticDerivedBarAlphaIsoAt input
    (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
    k g endpoint_eq square_isPullback

/-- The diagnostic comparison makes the original square's complete geometry
routes commute. -/
theorem semanticDerivedDiagnosticBarAlphaIsoAt_triangle
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) =
        input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    geomFiberLift input.square.top
        (semanticDerivedLeftPulledGeometryAt input
          (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
          k g endpoint_eq) ≫
      (semanticDerivedDiagnosticBarAlphaIsoAt input interpretation z
        k g endpoint_eq square_isPullback).hom.1 ≫
      semanticGeometryPullLift input.square.right
        (semanticDerivedTargetGeometryAt input
          (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
          k g endpoint_eq) =
    semanticGeometryPullLift input.square.left
        (semanticDerivedSouthwestGeometryFiber input
          (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
          k g endpoint_eq) ≫
      geomFiberLift input.square.bottom
        (semanticDerivedSouthwestGeometryFiber input
          (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
          k g endpoint_eq) := by
  exact semanticDerivedBarAlphaIsoAt_triangle input
    (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
    k g endpoint_eq square_isPullback

/-- The diagnostic comparison is the bottom unit, generated source endpoint
comparison, actual G-118 mate, generated target endpoint comparison, and top
counit. -/
theorem semanticDerivedDiagnosticBarAlphaIsoAt_generatedFiveFactor_hom
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticDerivedDiagnosticSourcePackageAt input interpretation z) =
        input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedDiagnosticBarAlphaIsoAt input interpretation z
      k g endpoint_eq square_isPullback).hom =
      (semanticDerivedUnitTopPushIsoAt input
        (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
        k g endpoint_eq).hom ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedBToGeneratedBaseNorthwestIsoAt input
          (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
          k g endpoint_eq square_isPullback).hom ≫
      semanticDerivedGeneratedMateTopPushAt input
        (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
        k g endpoint_eq square_isPullback ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedGeneratedPulledToTNorthwestIsoAt input
          (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
          k g endpoint_eq square_isPullback).hom ≫
      (semanticDerivedTopCounitIsoAt input
        (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
        k g endpoint_eq).hom := by
  exact semanticDerivedBarAlphaIsoAt_generatedFiveFactor_hom input
    (semanticDerivedDiagnosticSourcePackageAt input interpretation z)
    k g endpoint_eq square_isPullback

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
