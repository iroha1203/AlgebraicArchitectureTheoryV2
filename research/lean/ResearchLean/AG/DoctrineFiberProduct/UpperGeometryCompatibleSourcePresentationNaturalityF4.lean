import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF3

/-!
# Generated-range correspondence under source-presentation change

Central `T` naturality and surjectivity of the source-pair conjugation identify
the two independently generated ranges.  The statement is kept as the literal
ambient-set image equality required by G-118 C3 and is separate from the full
qualified-comparison subgroup equality proved in F3.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C3 generated-image correspondence:
`Theta_BP,i (Set.range T'_i) = Set.range T_i`.  Forward inclusion uses central
naturality, while reverse inclusion uses the actual inverse of the source-pair
conjugation rather than any surjectivity premise on `T`. -/
theorem generatedEndpointPairMulEquivAt_image_range_generatedComparisonPairHomAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.generatedEndpointPairMulEquivAt i ''
        Set.range (change.changedInput.generatedComparisonPairHomAt i) =
      Set.range (input.generatedComparisonPairHomAt i) := by
  ext oldOutput
  constructor
  · rintro ⟨changedOutput, ⟨changedInputPair, rfl⟩, rfl⟩
    refine ⟨change.generatedSourcePairMulEquivAt i changedInputPair, ?_⟩
    exact (change.generatedEndpointPairMulEquivAt_generatedComparisonPairHomAt
      i changedInputPair).symm
  · rintro ⟨oldInputPair, rfl⟩
    let changedInputPair :=
      (change.generatedSourcePairMulEquivAt i).symm oldInputPair
    refine ⟨change.changedInput.generatedComparisonPairHomAt i changedInputPair,
      ⟨changedInputPair, rfl⟩, ?_⟩
    rw [change.generatedEndpointPairMulEquivAt_generatedComparisonPairHomAt]
    exact congrArg (input.generatedComparisonPairHomAt i)
      ((change.generatedSourcePairMulEquivAt i).apply_symm_apply oldInputPair)

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
