import Formal.AG.SemanticRepair.LawEquationGeneratedPair

/-!
Executable elaboration contracts for the Part X theorem-7.5 finite-free route.
The examples below fix the signatures against the declarations imported from
`Formal.AG.SemanticRepair.LawEquationGeneratedPair`.
The examples below fix the complete input-structure and ten-field contract.
-/

namespace AAT.AG
namespace SemanticRepair
namespace StandardFinitePosetGeneratedBoundary

open CategoryTheory

universe v w x

variable {Ulaw : AtomCarrier.{x}}
variable {Alaw : ArchitectureObject Ulaw}
variable {Slaw : Site.AATSite.{x} Alaw}

/-- Contract for the law-independent conclusions 4--10. -/
example
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2) :
    let K := lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    let additive := coverRelativeGeneratedBoundaryAdditiveH1Surface K source.toPrimitive
    let realization := coverRelativeGeneratedBoundaryCochainRealization K source.toPrimitive
    Nonempty (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
      D source surface additive) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K /\
      Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) /\
      GeneratedResidualBoundarySurfaceBody additive /\
      GeneratedSemanticH1ZeroBody additive /\
      additive.H1Zero :=
  lawEquation_constructs_finiteFreeLawIndependentConjuncts
    semanticInput semanticCover G geometry D chartSimplex overlapSimplex tripleSimplex

/-- Contract for the complete finite-free ten-conclusion theorem. -/
example
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    let K := lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    Nonempty
      (LawEquationGroundedComparisonFiniteFreeConjunctsBody
        D surface source) :=
  lawEquation_constructs_groundedComparisonPacket_finiteFree
    semanticInput semanticCover G geometry D chartSimplex overlapSimplex
      tripleSimplex hholds

end StandardFinitePosetGeneratedBoundary
end SemanticRepair
end AAT.AG
