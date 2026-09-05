import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF9

/-!
# Finite-chain qualified comparison and generated-range transport

This module lifts the one-step C3 classification theorems to the actual pasted
actions of a dependent C1s chain.  It keeps three constructions visible and
separate: the action recursively composed from every link, the action induced
by the pasted endpoint comparisons, and the action freshly generated from the
structural chain composite.  Their F9 comparison equalities are used inside
the theorem bodies rather than hiding the finite chain behind the composite.

Full qualified-comparison transport and generated-range transport remain
distinct.  The former uses endpoint conjugation as an equivalence on the full
subgroup; the latter identifies the images of the two independently generated
comparison maps and does not assert that either map is onto that subgroup.
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

/-- G-118 C1s/C3 bridge API: the recursively composed selected-source action
of every chain link is the action freshly generated from the structural chain
composite. -/
theorem recursiveSourcePairMulEquivAt_eq_composite_generated
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.recursiveSourcePairMulEquivAt i =
      chain.composite.generatedSourcePairMulEquivAt i :=
  (chain.pastedSourcePairMulEquivAt_eq_recursive i).symm.trans
    (chain.composite_generatedSourcePairMulEquivAt_eq_pasted i).symm

/-- G-118 C1s/C3 bridge API: the recursively composed independently generated
endpoint action of every chain link is the action freshly generated from the
structural chain composite. -/
theorem recursiveEndpointPairMulEquivAt_eq_composite_generated
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.recursiveEndpointPairMulEquivAt i =
      chain.composite.generatedEndpointPairMulEquivAt i :=
  (chain.pastedEndpointPairMulEquivAt_eq_recursive i).symm.trans
    (chain.composite_generatedEndpointPairMulEquivAt_eq_pasted i).symm

/-- G-118 C1s/C3 comparison equation in the actual pasted endpoint
presentations.  The source comparison is selected along the chain, whereas
the base and pulled comparisons are independently generated at every link. -/
theorem generatedCompatibleUpperGeometryMateAt_eq_pasted_conjugation
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    input.generatedCompatibleUpperGeometryMateAt i =
      ((chain.pastedBaseRouteExactGeometryIsoAt i).inv.comp
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)).comp
          (chain.pastedPulledRouteExactGeometryIsoAt i).hom := by
  have h :=
    chain.composite.generatedCompatibleUpperGeometryMateAt_eq_sourcePresentation_conjugation i
  rw [chain.composite_generatedBaseRouteExactGeometryIsoAt_eq_pasted,
    chain.composite_generatedPulledRouteExactGeometryIsoAt_eq_pasted] at h
  exact h

/-- G-118 C1s/C3 full `Gamma` preservation and reflection by the endpoint
action pasted from every actual chain link.  This theorem uses the recursive
action bridge and is not derived from the range of the generated comparison
map. -/
theorem pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut
          (chain.composite.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) :
    pair ∈ qualifiedComparisonSubgroup
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) ↔
      chain.pastedEndpointPairMulEquivAt i pair ∈
        qualifiedComparisonSubgroup
          (input.generatedCompatibleUpperGeometryMateAt i) := by
  have h :=
    chain.composite.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      i pair
  rw [← chain.recursiveEndpointPairMulEquivAt_eq_composite_generated,
    ← chain.pastedEndpointPairMulEquivAt_eq_recursive] at h
  exact h

/-- G-118 C1s/C3 full qualified-comparison equivalence whose underlying raw
map is definitionally the endpoint action pasted from the dependent chain. -/
noncomputable def pastedQualifiedComparisonMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    qualifiedComparisonSubgroup
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) ≃*
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) where
  toFun pair :=
    ⟨chain.pastedEndpointPairMulEquivAt i pair.1,
      (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i pair.1).mp pair.2⟩
  invFun pair :=
    ⟨(chain.pastedEndpointPairMulEquivAt i).symm pair.1, by
      apply (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i ((chain.pastedEndpointPairMulEquivAt i).symm pair.1)).mpr
      simpa only [MulEquiv.apply_symm_apply] using pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    exact (chain.pastedEndpointPairMulEquivAt i).symm_apply_apply pair.1
  right_inv pair := by
    apply Subtype.ext
    exact (chain.pastedEndpointPairMulEquivAt i).apply_symm_apply pair.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (chain.pastedEndpointPairMulEquivAt i) left.1 right.1

/-- The underlying raw pair of the pasted full-`Gamma` equivalence is the
pasted endpoint action itself. -/
@[simp] theorem pastedQualifiedComparisonMulEquivAt_val
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair : qualifiedComparisonSubgroup
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)) :
    (chain.pastedQualifiedComparisonMulEquivAt i pair).1 =
      chain.pastedEndpointPairMulEquivAt i pair.1 := by
  rfl

/-- Proof-use API: the raw pair transported by the full-`Gamma` equivalence is
also the typed recursive composition of every actual link endpoint action. -/
theorem pastedQualifiedComparisonMulEquivAt_val_eq_recursive
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair : qualifiedComparisonSubgroup
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)) :
    (chain.pastedQualifiedComparisonMulEquivAt i pair).1 =
      chain.recursiveEndpointPairMulEquivAt i pair.1 := by
  rw [pastedQualifiedComparisonMulEquivAt_val,
    chain.pastedEndpointPairMulEquivAt_eq_recursive]

/-- G-118 C1s/C3 literal full-subgroup image equality under the pasted
endpoint action.  Reverse inclusion uses its actual inverse, not a surjectivity
claim about the generated comparison map. -/
theorem pastedEndpointPairMulEquivAt_map_qualifiedComparisonSubgroup
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    Subgroup.map
        (chain.pastedEndpointPairMulEquivAt i).toMonoidHom
        (qualifiedComparisonSubgroup
          (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)) =
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  have h :=
    chain.composite.generatedEndpointPairMulEquivAt_map_qualifiedComparisonSubgroup i
  rw [← chain.recursiveEndpointPairMulEquivAt_eq_composite_generated,
    ← chain.pastedEndpointPairMulEquivAt_eq_recursive] at h
  exact h

/-- G-118 C1s/C3 central generated-map square expressed by the actual pasted
source and endpoint actions.  Both generated maps are constructed independently
before this equality is proved. -/
theorem pastedEndpointPairMulEquivAt_generatedComparisonPairHomAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package ×
        CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package) :
    chain.pastedEndpointPairMulEquivAt i
        (chain.composite.changedInput.generatedComparisonPairHomAt i pair) =
      input.generatedComparisonPairHomAt i
        (chain.pastedSourcePairMulEquivAt i pair) := by
  have h :=
    chain.composite.generatedEndpointPairMulEquivAt_generatedComparisonPairHomAt
      i pair
  rw [← chain.recursiveEndpointPairMulEquivAt_eq_composite_generated,
    ← chain.pastedEndpointPairMulEquivAt_eq_recursive,
    ← chain.recursiveSourcePairMulEquivAt_eq_composite_generated,
    ← chain.pastedSourcePairMulEquivAt_eq_recursive] at h
  exact h

/-- G-118 C1s/C3 generated-range correspondence under the pasted endpoint
action.  This is an equality of the two independently generated ranges and
does not identify either range with the full qualified-comparison subgroup. -/
theorem pastedEndpointPairMulEquivAt_image_range_generatedComparisonPairHomAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.pastedEndpointPairMulEquivAt i ''
        Set.range
          (chain.composite.changedInput.generatedComparisonPairHomAt i) =
      Set.range (input.generatedComparisonPairHomAt i) := by
  have h :=
    chain.composite.generatedEndpointPairMulEquivAt_image_range_generatedComparisonPairHomAt i
  rw [← chain.recursiveEndpointPairMulEquivAt_eq_composite_generated,
    ← chain.pastedEndpointPairMulEquivAt_eq_recursive] at h
  exact h

end UpperGeometryCompatibleSourcePresentationChange.Chain
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
