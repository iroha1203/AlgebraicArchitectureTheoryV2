import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedRouteExactImage
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleMateNaturality

/-!
# Generated semantic route triangle and core projection

The G-118 mate generated from the semantic square satisfies its route triangle.
Its exact core projection is the conjugated G-114 mate generated from the same
fixed southwest geometry. These equalities precede the unit and counit factors
of the complete Beck--Chevalley comparison.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The generated semantic mixed-fiber mate satisfies the full refinement
geometry route triangle. -/
theorem semanticDerivedGeneratedMateInMixedFiberAt_triangle
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U) (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (exactGeometryToRefinementGeometry U).map
        (semanticDerivedGeneratedMateInMixedFiberAt
          input Q k g endpoint_eq).1 ≫
      (semanticDerivedCompatibleProblemData input Q k g endpoint_eq
        ).generatedPulledRouteLegAt PUnit.unit =
      (semanticDerivedCompatibleProblemData input Q k g endpoint_eq
        ).generatedBaseRouteLegAt PUnit.unit := by
  classical
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  change (exactGeometryToRefinementGeometry U).map
      (problem.generatedCompatibleUpperGeometryMateAt PUnit.unit) ≫
      problem.generatedPulledRouteLegAt PUnit.unit =
    problem.generatedBaseRouteLegAt PUnit.unit
  exact problem.generatedCompatibleUpperGeometryMateAt_triangle PUnit.unit

/-- The generated semantic mixed-fiber mate projects to the conjugated G-114
core mate on the two generated routes. -/
theorem semanticDerivedGeneratedMateInMixedFiberAt_core_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U) (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (semanticDerivedGeneratedMateInMixedFiberAt
      input Q k g endpoint_eq).1.base =
      ((semanticDerivedCompatibleProblemData input Q k g endpoint_eq
        ).generatedCompatibleConjugateCoreMateAt PUnit.unit).1 := by
  classical
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  change (problem.generatedCompatibleUpperGeometryMateAt PUnit.unit).base =
    (problem.generatedCompatibleConjugateCoreMateAt PUnit.unit).1
  rw [problem.generatedCompatibleUpperGeometryMateAt_base,
    problem.generatedCompatibleConjugateCoreMateAt_eq_generated]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
