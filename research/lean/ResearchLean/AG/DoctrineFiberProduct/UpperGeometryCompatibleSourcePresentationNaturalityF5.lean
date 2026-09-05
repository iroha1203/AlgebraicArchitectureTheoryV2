import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF4

/-!
# Projection, kernel, fiber, and action transport under source change

The full qualified-comparison equivalence of G-118 C3 respects both endpoint
projections.  Consequently it restricts to both projection kernels, transports
both kinds of lift fiber, preserves and reflects their nonemptiness, and is
equivariant for the corresponding stabilizer actions.  Every construction is
the generated source-presentation specialization of the general endpoint
conjugation API.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C3 source-projection naturality for the full generated
qualified-comparison equivalence. -/
@[simp] theorem generatedQualifiedComparisonSourcePresentationMulEquivAt_sourceProjection
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pair : qualifiedComparisonSubgroup
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i)) :
    qualifiedComparisonSourceProjection
        (input.generatedCompatibleUpperGeometryMateAt i)
        (change.generatedQualifiedComparisonSourcePresentationMulEquivAt i pair) =
      CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i)
        (qualifiedComparisonSourceProjection
          (change.changedInput.generatedCompatibleUpperGeometryMateAt i) pair) := by
  rfl

/-- G-118 C3 target-projection naturality for the full generated
qualified-comparison equivalence. -/
@[simp] theorem generatedQualifiedComparisonSourcePresentationMulEquivAt_targetProjection
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pair : qualifiedComparisonSubgroup
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i)) :
    qualifiedComparisonTargetProjection
        (input.generatedCompatibleUpperGeometryMateAt i)
        (change.generatedQualifiedComparisonSourcePresentationMulEquivAt i pair) =
      CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i)
        (qualifiedComparisonTargetProjection
          (change.changedInput.generatedCompatibleUpperGeometryMateAt i) pair) := by
  rfl

/-- G-118 C3 transport of the target stabilizer acting on target-partner
fibers. -/
noncomputable def generatedTargetStabilizerSourcePresentationMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    qualifiedComparisonTargetStabilizer
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) ≃*
      qualifiedComparisonTargetStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) where
  toFun stabilizer :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i) stabilizer.1, by
      have newMembership :
          (1, stabilizer.1) ∈ qualifiedComparisonSubgroup
            (change.changedInput.generatedCompatibleUpperGeometryMateAt i) := by
        change change.changedInput.generatedCompatibleUpperGeometryMateAt i =
          (change.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
            (CompositeFiberAut.hom stabilizer.1)
        exact stabilizer.2.symm
      have oldMembership :=
        (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i (1, stabilizer.1)).mp newMembership
      change
        (CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i) 1,
          CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i) stabilizer.1) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) at oldMembership
      rw [map_one] at oldMembership
      change input.generatedCompatibleUpperGeometryMateAt i =
        (input.generatedCompatibleUpperGeometryMateAt i).comp
          (CompositeFiberAut.hom (CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i) stabilizer.1))
        at oldMembership
      exact oldMembership.symm⟩
  invFun stabilizer :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i)).symm stabilizer.1, by
      have oldMembership :
          (1, stabilizer.1) ∈ qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) := by
        change input.generatedCompatibleUpperGeometryMateAt i =
          (input.generatedCompatibleUpperGeometryMateAt i).comp
            (CompositeFiberAut.hom stabilizer.1)
        exact stabilizer.2.symm
      have newMembership :=
        (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i (1, (CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i)).symm
              stabilizer.1)).mpr (by
            change
              (CompositeFiberAut.conjugationMulEquiv
                  (change.generatedBaseRouteExactGeometryIsoAt i) 1,
                CompositeFiberAut.conjugationMulEquiv
                  (change.generatedPulledRouteExactGeometryIsoAt i)
                  ((CompositeFiberAut.conjugationMulEquiv
                    (change.generatedPulledRouteExactGeometryIsoAt i)).symm
                      stabilizer.1)) ∈
                qualifiedComparisonSubgroup
                  (input.generatedCompatibleUpperGeometryMateAt i)
            simpa only [map_one, MulEquiv.apply_symm_apply] using oldMembership)
      change change.changedInput.generatedCompatibleUpperGeometryMateAt i =
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
          (CompositeFiberAut.hom
            ((CompositeFiberAut.conjugationMulEquiv
              (change.generatedPulledRouteExactGeometryIsoAt i)).symm
                stabilizer.1)) at newMembership
      exact newMembership.symm⟩
  left_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i)).apply_symm_apply _
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i)) _ _

/-- G-118 C3 transport of the source stabilizer acting on source-partner
fibers. -/
noncomputable def generatedSourceStabilizerSourcePresentationMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    qualifiedComparisonSourceStabilizer
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) ≃*
      qualifiedComparisonSourceStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) where
  toFun stabilizer :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i) stabilizer.1, by
      have newMembership :
          (stabilizer.1, 1) ∈ qualifiedComparisonSubgroup
            (change.changedInput.generatedCompatibleUpperGeometryMateAt i) := by
        change (CompositeFiberAut.hom stabilizer.1).comp
            (change.changedInput.generatedCompatibleUpperGeometryMateAt i) =
          change.changedInput.generatedCompatibleUpperGeometryMateAt i
        exact stabilizer.2
      have oldMembership :=
        (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i (stabilizer.1, 1)).mp newMembership
      change
        (CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i) stabilizer.1,
          CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i) 1) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) at oldMembership
      rw [map_one] at oldMembership
      change (CompositeFiberAut.hom (CompositeFiberAut.conjugationMulEquiv
          (change.generatedBaseRouteExactGeometryIsoAt i) stabilizer.1)).comp
            (input.generatedCompatibleUpperGeometryMateAt i) =
        input.generatedCompatibleUpperGeometryMateAt i at oldMembership
      exact oldMembership⟩
  invFun stabilizer :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i)).symm stabilizer.1, by
      have oldMembership :
          (stabilizer.1, 1) ∈ qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) := by
        change (CompositeFiberAut.hom stabilizer.1).comp
            (input.generatedCompatibleUpperGeometryMateAt i) =
          input.generatedCompatibleUpperGeometryMateAt i
        exact stabilizer.2
      have newMembership :=
        (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i ((CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i)).symm
              stabilizer.1, 1)).mpr (by
            change
              (CompositeFiberAut.conjugationMulEquiv
                  (change.generatedBaseRouteExactGeometryIsoAt i)
                  ((CompositeFiberAut.conjugationMulEquiv
                    (change.generatedBaseRouteExactGeometryIsoAt i)).symm
                      stabilizer.1),
                CompositeFiberAut.conjugationMulEquiv
                  (change.generatedPulledRouteExactGeometryIsoAt i) 1) ∈
                qualifiedComparisonSubgroup
                  (input.generatedCompatibleUpperGeometryMateAt i)
            simpa only [map_one, MulEquiv.apply_symm_apply] using oldMembership)
      change (CompositeFiberAut.hom
          ((CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i)).symm
              stabilizer.1)).comp
            (change.changedInput.generatedCompatibleUpperGeometryMateAt i) =
        change.changedInput.generatedCompatibleUpperGeometryMateAt i at newMembership
      exact newMembership⟩
  left_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i)).apply_symm_apply _
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i)) _ _

/-- G-118 C3 transport of the source-projection kernel. -/
noncomputable def generatedSourceProjectionKernelSourcePresentationMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (qualifiedComparisonSourceProjection
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i)).ker ≃*
    (qualifiedComparisonSourceProjection
      (input.generatedCompatibleUpperGeometryMateAt i)).ker := by
  rw [change.generatedCompatibleUpperGeometryMateAt_eq_sourcePresentation_conjugation i]
  exact qualifiedComparisonEndpointConjugationSourceKernelMulEquiv
    (change.generatedBaseRouteExactGeometryIsoAt i)
    (change.generatedPulledRouteExactGeometryIsoAt i)
    (change.changedInput.generatedCompatibleUpperGeometryMateAt i)

/-- G-118 C3 transport of the target-projection kernel. -/
noncomputable def generatedTargetProjectionKernelSourcePresentationMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (qualifiedComparisonTargetProjection
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i)).ker ≃*
    (qualifiedComparisonTargetProjection
      (input.generatedCompatibleUpperGeometryMateAt i)).ker := by
  rw [change.generatedCompatibleUpperGeometryMateAt_eq_sourcePresentation_conjugation i]
  exact qualifiedComparisonEndpointConjugationTargetKernelMulEquiv
    (change.generatedBaseRouteExactGeometryIsoAt i)
    (change.generatedPulledRouteExactGeometryIsoAt i)
    (change.changedInput.generatedCompatibleUpperGeometryMateAt i)

/-- G-118 C3 equivalence of target-partner fibers under generated endpoint
transport. -/
noncomputable def generatedQualifiedComparisonTargetLiftSourcePresentationEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (base : CompositeFiberAut
      (change.changedInput.generatedBaseRouteGeometryAt i)) :
    QualifiedComparisonTargetLift
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) base ≃
      QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (change.generatedBaseRouteExactGeometryIsoAt i) base) where
  toFun lift :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i) lift.1,
      (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i (base, lift.1)).mp lift.2⟩
  invFun lift :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i)).symm lift.1, by
      apply (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i (base, (CompositeFiberAut.conjugationMulEquiv
          (change.generatedPulledRouteExactGeometryIsoAt i)).symm lift.1)).mpr
      change
        (CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i) base,
          CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i)
            ((CompositeFiberAut.conjugationMulEquiv
              (change.generatedPulledRouteExactGeometryIsoAt i)).symm lift.1)) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i)
      simpa only [MulEquiv.apply_symm_apply] using lift.2⟩
  left_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i)).apply_symm_apply _

/-- G-118 C3 equivalence of source-partner fibers under generated endpoint
transport. -/
noncomputable def generatedQualifiedComparisonSourceLiftSourcePresentationEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pulled : CompositeFiberAut
      (change.changedInput.generatedPulledRouteGeometryAt i)) :
    QualifiedComparisonSourceLift
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) pulled ≃
      QualifiedComparisonSourceLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (change.generatedPulledRouteExactGeometryIsoAt i) pulled) where
  toFun lift :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i) lift.1,
      (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i (lift.1, pulled)).mp lift.2⟩
  invFun lift :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i)).symm lift.1, by
      apply (change.generatedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i ((CompositeFiberAut.conjugationMulEquiv
          (change.generatedBaseRouteExactGeometryIsoAt i)).symm lift.1,
            pulled)).mpr
      change
        (CompositeFiberAut.conjugationMulEquiv
            (change.generatedBaseRouteExactGeometryIsoAt i)
            ((CompositeFiberAut.conjugationMulEquiv
              (change.generatedBaseRouteExactGeometryIsoAt i)).symm lift.1),
          CompositeFiberAut.conjugationMulEquiv
            (change.generatedPulledRouteExactGeometryIsoAt i) pulled) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i)
      simpa only [MulEquiv.apply_symm_apply] using lift.2⟩
  left_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i)).apply_symm_apply _

/-- G-118 C3 preservation and reflection of nonempty target-partner
fibers. -/
theorem generatedQualifiedComparisonTargetLiftSourcePresentation_nonempty_iff
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (base : CompositeFiberAut
      (change.changedInput.generatedBaseRouteGeometryAt i)) :
    Nonempty (QualifiedComparisonTargetLift
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) base) ↔
      Nonempty (QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (change.generatedBaseRouteExactGeometryIsoAt i) base)) := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨change.generatedQualifiedComparisonTargetLiftSourcePresentationEquivAt
      i base lift⟩
  · rintro ⟨lift⟩
    exact ⟨(change.generatedQualifiedComparisonTargetLiftSourcePresentationEquivAt
      i base).symm lift⟩

/-- G-118 C3 preservation and reflection of nonempty source-partner
fibers. -/
theorem generatedQualifiedComparisonSourceLiftSourcePresentation_nonempty_iff
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pulled : CompositeFiberAut
      (change.changedInput.generatedPulledRouteGeometryAt i)) :
    Nonempty (QualifiedComparisonSourceLift
        (change.changedInput.generatedCompatibleUpperGeometryMateAt i) pulled) ↔
      Nonempty (QualifiedComparisonSourceLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (change.generatedPulledRouteExactGeometryIsoAt i) pulled)) := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨change.generatedQualifiedComparisonSourceLiftSourcePresentationEquivAt
      i pulled lift⟩
  · rintro ⟨lift⟩
    exact ⟨(change.generatedQualifiedComparisonSourceLiftSourcePresentationEquivAt
      i pulled).symm lift⟩

/-- G-118 C3 equivariance of the target-stabilizer action on target-partner
fibers. -/
theorem generatedQualifiedComparisonTargetLiftSourcePresentation_smul
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (base : CompositeFiberAut
      (change.changedInput.generatedBaseRouteGeometryAt i))
    (stabilizer : qualifiedComparisonTargetStabilizer
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i))
    (lift : QualifiedComparisonTargetLift
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i) base) :
    change.generatedQualifiedComparisonTargetLiftSourcePresentationEquivAt
        i base (stabilizer • lift) =
      change.generatedTargetStabilizerSourcePresentationMulEquivAt i stabilizer •
        change.generatedQualifiedComparisonTargetLiftSourcePresentationEquivAt
          i base lift := by
  apply Subtype.ext
  exact map_mul
    (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i))
    stabilizer.1 lift.1

/-- G-118 C3 equivariance of the source-stabilizer action on source-partner
fibers. -/
theorem generatedQualifiedComparisonSourceLiftSourcePresentation_smul
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (pulled : CompositeFiberAut
      (change.changedInput.generatedPulledRouteGeometryAt i))
    (stabilizer : qualifiedComparisonSourceStabilizer
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i))
    (lift : QualifiedComparisonSourceLift
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i) pulled) :
    change.generatedQualifiedComparisonSourceLiftSourcePresentationEquivAt
        i pulled (stabilizer • lift) =
      change.generatedSourceStabilizerSourcePresentationMulEquivAt i stabilizer •
        change.generatedQualifiedComparisonSourceLiftSourcePresentationEquivAt
          i pulled lift := by
  apply Subtype.ext
  exact map_mul
    (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i))
    stabilizer.1 lift.1

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
