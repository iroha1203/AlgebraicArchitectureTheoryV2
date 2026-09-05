import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF2
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonEndpointTransport

/-!
# Qualified-comparison correspondence under source-presentation change

The generated comparison-component square identifies the old mate with the
endpoint conjugate of the independently generated changed mate.  The general
endpoint-conjugation API therefore restricts the generated endpoint-pair
equivalence to the full qualified-comparison subgroups and proves the literal
subgroup-image equality required by G-118 C3.  A final pointwise law records
that this same endpoint transport is the one occurring in central `T`
naturality; full subgroup surjectivity does not come from the range of `T`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C3 comparison normalization.  The old generated mate is exactly the
changed generated mate written in the old independently generated endpoint
presentations. -/
theorem generatedCompatibleUpperGeometryMateAt_eq_sourcePresentation_conjugation
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    input.generatedCompatibleUpperGeometryMateAt i =
      ((change.generatedBaseRouteExactGeometryIsoAt i).inv.comp
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i)).comp
          (change.generatedPulledRouteExactGeometryIsoAt i).hom := by
  let etaBase := change.generatedBaseRouteExactGeometryIsoAt i
  let etaPulled := change.generatedPulledRouteExactGeometryIsoAt i
  let oldMate := input.generatedCompatibleUpperGeometryMateAt i
  let newMate := change.changedInput.generatedCompatibleUpperGeometryMateAt i
  have hnat : etaBase.hom.comp oldMate = newMate.comp etaPulled.hom :=
    change.generatedCompatibleUpperGeometryMateAt_naturality i
  change oldMate = (etaBase.inv.comp newMate).comp etaPulled.hom
  calc
    oldMate = etaBase.inv.comp (etaBase.hom.comp oldMate) :=
      (etaBase.inv_hom_id_assoc oldMate).symm
    _ = etaBase.inv.comp (newMate.comp etaPulled.hom) :=
      congrArg (fun hom => etaBase.inv.comp hom) hnat
    _ = (etaBase.inv.comp newMate).comp etaPulled.hom := by
      change etaBase.inv ≫ (newMate ≫ etaPulled.hom) =
        (etaBase.inv ≫ newMate) ≫ etaPulled.hom
      exact (Category.assoc _ _ _).symm

/-- G-118 C3 raw-pair form of full qualified-comparison preservation and
reflection by the generated endpoint-pair conjugation. -/
theorem generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut
          (change.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (change.changedInput.generatedPulledRouteGeometryAt i)) :
    pair ∈ qualifiedComparisonSubgroup
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) ↔
      change.generatedEndpointPairMulEquivAt i pair ∈
        qualifiedComparisonSubgroup
          (input.generatedCompatibleUpperGeometryMateAt i) := by
  let etaBase := change.generatedBaseRouteExactGeometryIsoAt i
  let etaPulled := change.generatedPulledRouteExactGeometryIsoAt i
  let newMate := change.changedInput.generatedCompatibleUpperGeometryMateAt i
  have h := inverseConjugatedPair_mem_qualifiedComparison_iff
    etaBase etaPulled newMate
    (change.generatedEndpointPairMulEquivAt i pair)
  rw [← change.generatedCompatibleUpperGeometryMateAt_eq_sourcePresentation_conjugation i]
    at h
  change
    (((CompositeFiberAut.conjugationMulEquiv etaBase).symm
          ((CompositeFiberAut.conjugationMulEquiv etaBase) pair.1),
        (CompositeFiberAut.conjugationMulEquiv etaPulled).symm
          ((CompositeFiberAut.conjugationMulEquiv etaPulled) pair.2)) ∈
        qualifiedComparisonSubgroup newMate ↔
      change.generatedEndpointPairMulEquivAt i pair ∈
        qualifiedComparisonSubgroup
          (input.generatedCompatibleUpperGeometryMateAt i)) at h
  simpa only [MulEquiv.symm_apply_apply] using h

/-- G-118 C3 full qualified-comparison equivalence.  It is the restriction of
literal endpoint conjugation by the independently generated `eta_B, eta_P`;
its explicit construction exposes the endpoint-pair map definitionally and is
not a restriction to the generated range of `T`. -/
noncomputable def generatedQualifiedComparisonSourcePresentationMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    qualifiedComparisonSubgroup
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) ≃*
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) where
  toFun pair :=
    ⟨change.generatedEndpointPairMulEquivAt i pair.1,
      (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i pair.1).mp pair.2⟩
  invFun pair :=
    ⟨(change.generatedEndpointPairMulEquivAt i).symm pair.1, by
      apply (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i ((change.generatedEndpointPairMulEquivAt i).symm pair.1)).mpr
      simpa only [MulEquiv.apply_symm_apply] using pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    exact (change.generatedEndpointPairMulEquivAt i).symm_apply_apply pair.1
  right_inv pair := by
    apply Subtype.ext
    exact (change.generatedEndpointPairMulEquivAt i).apply_symm_apply pair.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (change.generatedEndpointPairMulEquivAt i) left.1 right.1

/-- G-118 C3 literal subgroup-image form of
`Theta_BP,i (Gamma_(c'_i)) = Gamma_(c_i)`.  Reverse inclusion uses the actual
inverse endpoint conjugation, not surjectivity of the generated map `T`. -/
theorem generatedEndpointPairMulEquivAt_map_qualifiedComparisonSubgroup
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    Subgroup.map
        (change.generatedEndpointPairMulEquivAt i).toMonoidHom
        (qualifiedComparisonSubgroup
          (change.changedInput.generatedCompatibleUpperGeometryMateAt i)) =
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  apply SetLike.ext
  intro oldPair
  constructor
  · rintro ⟨newPair, newMembership, rfl⟩
    exact (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
      i newPair).mp newMembership
  · intro oldMembership
    let newPair := (change.generatedEndpointPairMulEquivAt i).symm oldPair
    refine ⟨newPair, ?_, ?_⟩
    · apply (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i newPair).mpr
      simpa only [newPair, MulEquiv.apply_symm_apply] using oldMembership
    · exact (change.generatedEndpointPairMulEquivAt i).apply_symm_apply oldPair

/-- G-118 C3 compatibility of the full endpoint transport with the central
generated comparison-map square.  This is the pointwise form of Cycle 15 and
keeps full `Gamma` transport distinct from generated-range transport. -/
theorem generatedEndpointPairMulEquivAt_generatedComparisonPairHomAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut (change.changedInput.sourceGeometry i).package ×
        CompositeFiberAut (change.changedInput.sourceGeometry i).package) :
    change.generatedEndpointPairMulEquivAt i
        (change.changedInput.generatedComparisonPairHomAt i pair) =
      input.generatedComparisonPairHomAt i
        (change.generatedSourcePairMulEquivAt i pair) := by
  exact (DFunLike.congr_fun
    (change.generatedComparisonPairHomAt_sourcePresentation_naturality i)
    pair).symm

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
