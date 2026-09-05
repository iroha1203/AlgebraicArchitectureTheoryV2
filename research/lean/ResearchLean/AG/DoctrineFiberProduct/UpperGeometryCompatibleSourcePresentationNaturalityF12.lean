import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF11

/-!
# Finite-chain residual subgroup and coefficient naturality

This module transports the residual source subgroup `J` and both pair
coefficient observations along the actual source and endpoint actions pasted
from a dependent C1s chain.  The residual subgroup remains the preimage of the
target stabilizer under the generated pulled comparison; it is not identified
with either projection kernel of the full qualified-comparison subgroup.

The bridge theorems expose the recursively composed action of every chain
link before deriving the literal subgroup image and coefficient-observation
equalities.  No normality, endpoint surjectivity, or faithfulness of
coefficient observation is assumed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleSourcePresentationChange.Chain

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C1s/C3 component bridge: on `(a, 1)`, the first component of the
recursive every-link source action is conjugation by the pasted source
comparison. -/
theorem recursiveSourcePairMulEquivAt_fst_left_one_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (chain.composite.changedInput.sourceGeometry i).package) :
    (chain.recursiveSourcePairMulEquivAt i
      (automorphism, (1 : CompositeFiberAut
        (chain.composite.changedInput.sourceGeometry i).package))).1 =
      CompositeFiberAut.conjugationMulEquiv
        (chain.pastedSourceGeometryIsoAt i) automorphism := by
  rw [← chain.pastedSourcePairMulEquivAt_eq_recursive]
  rfl

/-- G-118 C1s/C3 residual-subgroup membership expressed through the
recursively composed source-pair action of every chain link. -/
theorem generatedPulledComparisonKernel_mem_recursiveSourcePair_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (chain.composite.changedInput.sourceGeometry i).package) :
    automorphism ∈
        chain.composite.changedInput.generatedPulledComparisonKernel i ↔
      (chain.recursiveSourcePairMulEquivAt i
        (automorphism, (1 : CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package))).1 ∈
        input.generatedPulledComparisonKernel i := by
  have h :=
    chain.composite.generatedPulledComparisonKernel_mem_sourcePresentation_iff
      i automorphism
  change automorphism ∈
        chain.composite.changedInput.generatedPulledComparisonKernel i ↔
      (chain.composite.generatedSourcePairMulEquivAt i
        (automorphism, (1 : CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package))).1 ∈
        input.generatedPulledComparisonKernel i at h
  rw [← chain.recursiveSourcePairMulEquivAt_eq_composite_generated] at h
  exact h

/-- G-118 C1s/C3 residual-subgroup membership under conjugation by the
actual source comparison pasted along the dependent chain. -/
theorem pastedSourceConjugation_mem_generatedPulledComparisonKernel_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (chain.composite.changedInput.sourceGeometry i).package) :
    automorphism ∈
        chain.composite.changedInput.generatedPulledComparisonKernel i ↔
      CompositeFiberAut.conjugationMulEquiv
          (chain.pastedSourceGeometryIsoAt i) automorphism ∈
        input.generatedPulledComparisonKernel i := by
  rw [← chain.recursiveSourcePairMulEquivAt_fst_left_one_eq_pasted]
  exact chain.generatedPulledComparisonKernel_mem_recursiveSourcePair_iff
    i automorphism

/-- G-118 C1s/C3 literal finite-chain residual-subgroup correspondence
`Ad(w_chain)(J_terminal) = J_initial`. -/
theorem pastedSourceConjugation_map_generatedPulledComparisonKernel
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    Subgroup.map
        (CompositeFiberAut.conjugationMulEquiv
          (chain.pastedSourceGeometryIsoAt i)).toMonoidHom
        (chain.composite.changedInput.generatedPulledComparisonKernel i) =
      input.generatedPulledComparisonKernel i := by
  apply SetLike.ext
  intro oldAutomorphism
  constructor
  · rintro ⟨newAutomorphism, membership, rfl⟩
    exact (chain.pastedSourceConjugation_mem_generatedPulledComparisonKernel_iff
      i newAutomorphism).mp membership
  · intro membership
    let newAutomorphism :=
      (CompositeFiberAut.conjugationMulEquiv
        (chain.pastedSourceGeometryIsoAt i)).symm oldAutomorphism
    refine ⟨newAutomorphism, ?_, ?_⟩
    · apply (chain.pastedSourceConjugation_mem_generatedPulledComparisonKernel_iff
        i newAutomorphism).mpr
      simpa only [newAutomorphism, MulEquiv.apply_symm_apply] using membership
    · exact (CompositeFiberAut.conjugationMulEquiv
        (chain.pastedSourceGeometryIsoAt i)).apply_symm_apply oldAutomorphism

/-- G-118 C1s/C3 preservation and reflection of the exact residual
criterion `J = {1}` along a dependent finite source-change chain. -/
theorem generatedPulledComparisonKernel_eq_bot_pasted_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.changedInput.generatedPulledComparisonKernel i = ⊥ ↔
      input.generatedPulledComparisonKernel i = ⊥ := by
  let sourceEquiv :=
    CompositeFiberAut.conjugationMulEquiv
      (chain.pastedSourceGeometryIsoAt i)
  constructor
  · intro changedIdentity
    calc
      input.generatedPulledComparisonKernel i =
          Subgroup.map sourceEquiv.toMonoidHom
            (chain.composite.changedInput.generatedPulledComparisonKernel i) :=
        (chain.pastedSourceConjugation_map_generatedPulledComparisonKernel i).symm
      _ = Subgroup.map sourceEquiv.toMonoidHom ⊥ := by rw [changedIdentity]
      _ = ⊥ := Subgroup.map_bot sourceEquiv.toMonoidHom
  · intro oldIdentity
    have mapped :
        Subgroup.map sourceEquiv.toMonoidHom
            (chain.composite.changedInput.generatedPulledComparisonKernel i) = ⊥ := by
      rw [chain.pastedSourceConjugation_map_generatedPulledComparisonKernel i]
      exact oldIdentity
    exact (Subgroup.map_eq_bot_iff_of_injective
      (chain.composite.changedInput.generatedPulledComparisonKernel i)
      sourceEquiv.injective).mp mapped

/-- G-118 C1s/C3 source-pair coefficient observation commutes with the
actual pasted and recursively composed finite-chain action. -/
theorem pastedSourcePairMulEquivAt_coefficientObservation
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package ×
        CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package) :
    input.sourcePairCoefficientObservationAt i
        (chain.pastedSourcePairMulEquivAt i pair) =
      chain.composite.changedInput.sourcePairCoefficientObservationAt i pair := by
  have h :=
    chain.composite.generatedSourcePairMulEquivAt_coefficientObservation i pair
  rw [← chain.recursiveSourcePairMulEquivAt_eq_composite_generated,
    ← chain.pastedSourcePairMulEquivAt_eq_recursive] at h
  exact h

/-- G-118 C1s/C3 generated endpoint-pair coefficient observation commutes
with the actual pasted and recursively composed finite-chain action. -/
theorem pastedEndpointPairMulEquivAt_coefficientObservation
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut
          (chain.composite.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) :
    input.generatedPairCoefficientObservationAt i
        (chain.pastedEndpointPairMulEquivAt i pair) =
      chain.composite.changedInput.generatedPairCoefficientObservationAt i pair := by
  have h :=
    chain.composite.generatedEndpointPairMulEquivAt_coefficientObservation i pair
  rw [← chain.recursiveEndpointPairMulEquivAt_eq_composite_generated,
    ← chain.pastedEndpointPairMulEquivAt_eq_recursive] at h
  exact h

end UpperGeometryCompatibleSourcePresentationChange.Chain
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
