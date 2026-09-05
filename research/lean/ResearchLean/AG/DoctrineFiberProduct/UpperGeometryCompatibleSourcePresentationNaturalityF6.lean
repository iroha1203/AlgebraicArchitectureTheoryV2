import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF5
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientTransport

/-!
# Residual-subgroup and coefficient naturality under source-presentation change

This module completes the next G-118 C3 transport layer.  The actual pulled
generated map and the transported target stabilizer identify the residual
subgroups `J'` and `J` under source conjugation.  Independently derived
coefficient identities for the source, base, and pulled exact isomorphisms
give the two product coefficient-observation squares.  No normality,
surjectivity of an endpoint map, or faithfulness of coefficient observation is
assumed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C3 pointwise transport of the residual subgroup `J`: membership in
the changed preimage of the target stabilizer is equivalent to membership of
the source conjugate in the old preimage. -/
theorem generatedPulledComparisonKernel_mem_sourcePresentation_iff
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (automorphism :
      CompositeFiberAut (change.changedInput.sourceGeometry i).package) :
    automorphism ∈
        change.changedInput.generatedPulledComparisonKernel i ↔
      CompositeFiberAut.conjugationMulEquiv
          (change.geometryIso i) automorphism ∈
        input.generatedPulledComparisonKernel i := by
  change
    change.changedInput.generatedPulledCompositeFiberAutAt i automorphism ∈
        qualifiedComparisonTargetStabilizer
          (change.changedInput.generatedCompatibleUpperGeometryMateAt i) ↔
      input.generatedPulledCompositeFiberAutAt i
          (CompositeFiberAut.conjugationMulEquiv
            (change.geometryIso i) automorphism) ∈
        qualifiedComparisonTargetStabilizer
          (input.generatedCompatibleUpperGeometryMateAt i)
  rw [← change.generatedPulledCompositeFiberAutAt_naturality i automorphism]
  constructor
  · intro membership
    exact (change.generatedTargetStabilizerSourcePresentationMulEquivAt i
      ⟨_, membership⟩).2
  · intro membership
    have transported :
        CompositeFiberAut.conjugationMulEquiv
              (change.generatedPulledRouteExactGeometryIsoAt i)
              (change.changedInput.generatedPulledCompositeFiberAutAt
                i automorphism) ∈
          qualifiedComparisonTargetStabilizer
            (input.generatedCompatibleUpperGeometryMateAt i) :=
      membership
    have preimageMembership :=
      ((change.generatedTargetStabilizerSourcePresentationMulEquivAt i).symm
        ⟨_, transported⟩).2
    change
      (CompositeFiberAut.conjugationMulEquiv
          (change.generatedPulledRouteExactGeometryIsoAt i)).symm
          (CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i)
            (change.changedInput.generatedPulledCompositeFiberAutAt
              i automorphism)) ∈
        qualifiedComparisonTargetStabilizer
          (change.changedInput.generatedCompatibleUpperGeometryMateAt i)
      at preimageMembership
    simpa only [MulEquiv.symm_apply_apply] using preimageMembership

/-- G-118 C3 literal residual-subgroup correspondence
`Ad(w_i)(J'_i) = J_i`. -/
theorem generatedSourceConjugation_map_generatedPulledComparisonKernel
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    Subgroup.map
        (CompositeFiberAut.conjugationMulEquiv
          (change.geometryIso i)).toMonoidHom
        (change.changedInput.generatedPulledComparisonKernel i) =
      input.generatedPulledComparisonKernel i := by
  apply SetLike.ext
  intro oldAutomorphism
  constructor
  · rintro ⟨newAutomorphism, membership, rfl⟩
    exact (change.generatedPulledComparisonKernel_mem_sourcePresentation_iff
      i newAutomorphism).mp membership
  · intro membership
    let newAutomorphism :=
      (CompositeFiberAut.conjugationMulEquiv
        (change.geometryIso i)).symm oldAutomorphism
    refine ⟨newAutomorphism, ?_, ?_⟩
    · apply (change.generatedPulledComparisonKernel_mem_sourcePresentation_iff
        i newAutomorphism).mpr
      simpa only [newAutomorphism, MulEquiv.apply_symm_apply] using membership
    · exact (CompositeFiberAut.conjugationMulEquiv
        (change.geometryIso i)).apply_symm_apply oldAutomorphism

/-- G-118 C3 preservation and reflection of the exact residual criterion
`J = {1}` under source-presentation change. -/
theorem generatedPulledComparisonKernel_eq_bot_sourcePresentation_iff
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.changedInput.generatedPulledComparisonKernel i = ⊥ ↔
      input.generatedPulledComparisonKernel i = ⊥ := by
  let sourceEquiv :=
    CompositeFiberAut.conjugationMulEquiv (change.geometryIso i)
  constructor
  · intro changedIdentity
    calc
      input.generatedPulledComparisonKernel i =
          Subgroup.map sourceEquiv.toMonoidHom
            (change.changedInput.generatedPulledComparisonKernel i) :=
        (change.generatedSourceConjugation_map_generatedPulledComparisonKernel i).symm
      _ = Subgroup.map sourceEquiv.toMonoidHom ⊥ := by rw [changedIdentity]
      _ = ⊥ := Subgroup.map_bot sourceEquiv.toMonoidHom
  · intro oldIdentity
    have mapped :
        Subgroup.map sourceEquiv.toMonoidHom
            (change.changedInput.generatedPulledComparisonKernel i) = ⊥ := by
      rw [change.generatedSourceConjugation_map_generatedPulledComparisonKernel i]
      exact oldIdentity
    exact (Subgroup.map_eq_bot_iff_of_injective
      (change.changedInput.generatedPulledComparisonKernel i)
      sourceEquiv.injective).mp mapped

/-- G-118 C3 source conjugation commutes with the complete coefficient
observation.  Both coefficient identities of the selected source isomorphism
are used. -/
theorem generatedSourceConjugation_coefficientHom
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (automorphism :
      CompositeFiberAut (change.changedInput.sourceGeometry i).package) :
    (CompositeFiberAut.hom
      (CompositeFiberAut.conjugationMulEquiv
        (change.geometryIso i) automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (change.geometryIso i).hom.geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (change.geometryIso i).inv.geometry.coefficientHom) = _
  rw [change.geometryIso_hom_coefficient_id,
    change.geometryIso_inv_coefficient_id]
  rfl

/-- G-118 C3 base endpoint conjugation commutes with the complete coefficient
observation, using the coefficient identities derived for `eta_B`. -/
theorem generatedBaseEndpointConjugation_coefficientHom
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (change.changedInput.generatedBaseRouteGeometryAt i)) :
    (CompositeFiberAut.hom
      (CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i)
        automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (change.generatedBaseRouteExactGeometryIsoAt i).hom.geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (change.generatedBaseRouteExactGeometryIsoAt i).inv.geometry.coefficientHom) = _
  rw [change.generatedBaseRouteExactGeometryIsoAt_hom_coefficient_id,
    change.generatedBaseRouteExactGeometryIsoAt_inv_coefficient_id]
  rfl

/-- G-118 C3 pulled endpoint conjugation commutes with the complete
coefficient observation, using the coefficient identities derived for
`eta_P`. -/
theorem generatedPulledEndpointConjugation_coefficientHom
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (change.changedInput.generatedPulledRouteGeometryAt i)) :
    (CompositeFiberAut.hom
      (CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i)
        automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (change.generatedPulledRouteExactGeometryIsoAt i).hom.geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (change.generatedPulledRouteExactGeometryIsoAt i).inv.geometry.coefficientHom) = _
  rw [change.generatedPulledRouteExactGeometryIsoAt_hom_coefficient_id,
    change.generatedPulledRouteExactGeometryIsoAt_inv_coefficient_id]
  rfl

/-- G-118 C3 coefficient observation commutes in both source components. -/
theorem generatedSourcePairMulEquivAt_coefficientObservation
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut (change.changedInput.sourceGeometry i).package ×
        CompositeFiberAut (change.changedInput.sourceGeometry i).package) :
    input.sourcePairCoefficientObservationAt i
        (change.generatedSourcePairMulEquivAt i pair) =
      change.changedInput.sourcePairCoefficientObservationAt i pair := by
  apply Prod.ext
  · change
      CompositeFiberAut.coefficientObservation
          (input.sourceGeometry i).package
          (CompositeFiberAut.conjugationMulEquiv
            (change.geometryIso i) pair.1) =
        CompositeFiberAut.coefficientObservation
          (change.changedInput.sourceGeometry i).package pair.1
    apply CategoryTheory.Iso.ext
    ext value
    rw [CompositeFiberAut.coefficientObservation_hom,
      CompositeFiberAut.coefficientObservation_hom,
      change.generatedSourceConjugation_coefficientHom]
  · change
      CompositeFiberAut.coefficientObservation
          (input.sourceGeometry i).package
          (CompositeFiberAut.conjugationMulEquiv
            (change.geometryIso i) pair.2) =
        CompositeFiberAut.coefficientObservation
          (change.changedInput.sourceGeometry i).package pair.2
    apply CategoryTheory.Iso.ext
    ext value
    rw [CompositeFiberAut.coefficientObservation_hom,
      CompositeFiberAut.coefficientObservation_hom,
      change.generatedSourceConjugation_coefficientHom]

/-- G-118 C3 coefficient observation commutes in the generated base and
pulled endpoint components. -/
theorem generatedEndpointPairMulEquivAt_coefficientObservation
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pair :
      CompositeFiberAut
          (change.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (change.changedInput.generatedPulledRouteGeometryAt i)) :
    input.generatedPairCoefficientObservationAt i
        (change.generatedEndpointPairMulEquivAt i pair) =
      change.changedInput.generatedPairCoefficientObservationAt i pair := by
  apply Prod.ext
  · change
      CompositeFiberAut.coefficientObservation
          (input.generatedBaseRouteGeometryAt i)
          (CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i) pair.1) =
        CompositeFiberAut.coefficientObservation
          (change.changedInput.generatedBaseRouteGeometryAt i) pair.1
    apply CategoryTheory.Iso.ext
    ext value
    rw [CompositeFiberAut.coefficientObservation_hom,
      CompositeFiberAut.coefficientObservation_hom,
      change.generatedBaseEndpointConjugation_coefficientHom]
  · change
      CompositeFiberAut.coefficientObservation
          (input.generatedPulledRouteGeometryAt i)
          (CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i) pair.2) =
        CompositeFiberAut.coefficientObservation
          (change.changedInput.generatedPulledRouteGeometryAt i) pair.2
    apply CategoryTheory.Iso.ext
    ext value
    rw [CompositeFiberAut.coefficientObservation_hom,
      CompositeFiberAut.coefficientObservation_hom,
      change.generatedPulledEndpointConjugation_coefficientHom]

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
