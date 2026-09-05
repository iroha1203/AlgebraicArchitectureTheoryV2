import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF8

/-!
# Pasted source and endpoint actions along dependent source-change chains

The selected complete-source comparison and the two independently generated
endpoint comparisons can be pasted link by link along a dependent C1s chain.
This module proves that these recursive pastings equal the comparisons freshly
generated from the chain composite.  Consequently, the source-pair and
endpoint-pair conjugation equivalences have genuine finite-chain coherence.
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

/-- Linkwise paste of the selected complete-source comparisons. -/
noncomputable def pastedSourceGeometryIsoAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    (chain.composite.changedInput.sourceGeometry i).package ≅
      (input.sourceGeometry i).package
  | .nil initial, i => Iso.refl (initial.sourceGeometry i).package
  | .cons head tail, i =>
      tail.pastedSourceGeometryIsoAt i ≪≫ head.geometryIso i

/-- Linkwise paste of independently generated base-route endpoint
comparisons. -/
noncomputable def pastedBaseRouteExactGeometryIsoAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    chain.composite.changedInput.generatedBaseRouteGeometryAt i ≅
      input.generatedBaseRouteGeometryAt i
  | .nil initial, i => Iso.refl (initial.generatedBaseRouteGeometryAt i)
  | .cons head tail, i =>
      tail.pastedBaseRouteExactGeometryIsoAt i ≪≫
        head.generatedBaseRouteExactGeometryIsoAt i

/-- Linkwise paste of independently generated pulled-route endpoint
comparisons. -/
noncomputable def pastedPulledRouteExactGeometryIsoAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    chain.composite.changedInput.generatedPulledRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i
  | .nil initial, i => Iso.refl (initial.generatedPulledRouteGeometryAt i)
  | .cons head tail, i =>
      tail.pastedPulledRouteExactGeometryIsoAt i ≪≫
        head.generatedPulledRouteExactGeometryIsoAt i

/-- The selected source comparison freshly generated from the chain composite
equals the linkwise pasted source comparison. -/
theorem composite_geometryIso_eq_pastedSourceGeometryIsoAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.geometryIso i = chain.pastedSourceGeometryIsoAt i := by
  induction chain with
  | nil initial => simp [pastedSourceGeometryIsoAt, composite, identity]
  | cons head tail inductionHypothesis =>
      simp only [composite, pastedSourceGeometryIsoAt, comp]
      rw [inductionHypothesis]

/-- The independently generated base comparison of the chain composite equals
the linkwise pasted base comparison. -/
theorem composite_generatedBaseRouteExactGeometryIsoAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedBaseRouteExactGeometryIsoAt i =
      chain.pastedBaseRouteExactGeometryIsoAt i := by
  induction chain with
  | nil initial =>
      simpa [composite, pastedBaseRouteExactGeometryIsoAt] using
        generatedBaseRouteExactGeometryIsoAt_identity initial i
  | cons head tail inductionHypothesis =>
      simp only [composite, pastedBaseRouteExactGeometryIsoAt]
      rw [generatedBaseRouteExactGeometryIsoAt_comp, inductionHypothesis]

/-- The independently generated pulled comparison of the chain composite
equals the linkwise pasted pulled comparison. -/
theorem composite_generatedPulledRouteExactGeometryIsoAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedPulledRouteExactGeometryIsoAt i =
      chain.pastedPulledRouteExactGeometryIsoAt i := by
  induction chain with
  | nil initial =>
      simpa [composite, pastedPulledRouteExactGeometryIsoAt] using
        generatedPulledRouteExactGeometryIsoAt_identity initial i
  | cons head tail inductionHypothesis =>
      simp only [composite, pastedPulledRouteExactGeometryIsoAt]
      rw [generatedPulledRouteExactGeometryIsoAt_comp, inductionHypothesis]

/-- Source-pair conjugation induced directly by the pasted source comparison
of a dependent chain. -/
noncomputable def pastedSourcePairMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    (CompositeFiberAut (chain.composite.changedInput.sourceGeometry i).package ×
        CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package) ≃*
      (CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package) :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedSourceGeometryIsoAt i))
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedSourceGeometryIsoAt i))

/-- Endpoint-pair conjugation induced directly by the two pasted generated
endpoint comparisons of a dependent chain. -/
noncomputable def pastedEndpointPairMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    (CompositeFiberAut
          (chain.composite.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) ≃*
      (CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut (input.generatedPulledRouteGeometryAt i)) :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i))
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i))

/-- The source-pair action generated by the composite change is exactly the
action induced by the pasted source comparison. -/
theorem composite_generatedSourcePairMulEquivAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedSourcePairMulEquivAt i =
      chain.pastedSourcePairMulEquivAt i := by
  rw [generatedSourcePairMulEquivAt, pastedSourcePairMulEquivAt,
    chain.composite_geometryIso_eq_pastedSourceGeometryIsoAt]

/-- The endpoint-pair action generated by the composite change is exactly the
action induced by the pasted generated endpoint comparisons. -/
theorem composite_generatedEndpointPairMulEquivAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedEndpointPairMulEquivAt i =
      chain.pastedEndpointPairMulEquivAt i := by
  rw [generatedEndpointPairMulEquivAt, pastedEndpointPairMulEquivAt,
    chain.composite_generatedBaseRouteExactGeometryIsoAt_eq_pasted,
    chain.composite_generatedPulledRouteExactGeometryIsoAt_eq_pasted]

end UpperGeometryCompatibleSourcePresentationChange.Chain
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
