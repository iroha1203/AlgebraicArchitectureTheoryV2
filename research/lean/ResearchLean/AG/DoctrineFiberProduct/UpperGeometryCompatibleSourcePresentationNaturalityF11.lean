import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF10

/-!
# Finite-chain projection, kernel, and lift-fiber transport

This module specializes the generic endpoint-conjugation classification API
to the actual base and pulled comparisons pasted along a dependent C1s chain.
The constructions use the F10 pasted `Gamma` membership theorem and explicit
full-`Gamma` equivalence directly; they are not aliases for the corresponding
structures attached to `Chain.composite`.

The coordinate convention is explicit.  The source projection is the base
coordinate, so its kernel corresponds to the target stabilizer.  The target
projection is the pulled coordinate, so its kernel corresponds to the source
stabilizer.  Target-partner fibers fix the base coordinate and transport their
varying pulled coordinate; source-partner fibers do the converse.
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

/-- G-118 C1s/C3 source-projection square for the explicit pasted full-`Gamma`
equivalence.  The source coordinate is transported by the pasted base
comparison. -/
@[simp] theorem pastedQualifiedComparisonMulEquivAt_sourceProjection
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair : qualifiedComparisonSubgroup
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)) :
    qualifiedComparisonSourceProjection
        (input.generatedCompatibleUpperGeometryMateAt i)
        (chain.pastedQualifiedComparisonMulEquivAt i pair) =
      CompositeFiberAut.conjugationMulEquiv
        (chain.pastedBaseRouteExactGeometryIsoAt i)
        (qualifiedComparisonSourceProjection
          (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
          pair) := by
  rfl

/-- G-118 C1s/C3 target-projection square for the explicit pasted full-`Gamma`
equivalence.  The target coordinate is transported by the pasted pulled
comparison. -/
@[simp] theorem pastedQualifiedComparisonMulEquivAt_targetProjection
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pair : qualifiedComparisonSubgroup
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)) :
    qualifiedComparisonTargetProjection
        (input.generatedCompatibleUpperGeometryMateAt i)
        (chain.pastedQualifiedComparisonMulEquivAt i pair) =
      CompositeFiberAut.conjugationMulEquiv
        (chain.pastedPulledRouteExactGeometryIsoAt i)
        (qualifiedComparisonTargetProjection
          (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
          pair) := by
  rfl

/-- G-118 C1s/C3 target-stabilizer transport constructed directly from the
pasted pulled endpoint comparison. -/
noncomputable def pastedTargetStabilizerMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    qualifiedComparisonTargetStabilizer
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) ≃*
      qualifiedComparisonTargetStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) where
  toFun stabilizer :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (chain.pastedPulledRouteExactGeometryIsoAt i) stabilizer.1, by
      have newMembership :
          (1, stabilizer.1) ∈ qualifiedComparisonSubgroup
            (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) := by
        change chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i =
          (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
            (CompositeFiberAut.hom stabilizer.1)
        exact stabilizer.2.symm
      have oldMembership :=
        (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i (1, stabilizer.1)).mp newMembership
      change
        (CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i) 1,
          CompositeFiberAut.conjugationMulEquiv
            (chain.pastedPulledRouteExactGeometryIsoAt i) stabilizer.1) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) at oldMembership
      rw [map_one] at oldMembership
      change input.generatedCompatibleUpperGeometryMateAt i =
        (input.generatedCompatibleUpperGeometryMateAt i).comp
          (CompositeFiberAut.hom
            (CompositeFiberAut.conjugationMulEquiv
              (chain.pastedPulledRouteExactGeometryIsoAt i) stabilizer.1))
        at oldMembership
      exact oldMembership.symm⟩
  invFun stabilizer :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (chain.pastedPulledRouteExactGeometryIsoAt i)).symm stabilizer.1, by
      have oldMembership :
          (1, stabilizer.1) ∈ qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) := by
        change input.generatedCompatibleUpperGeometryMateAt i =
          (input.generatedCompatibleUpperGeometryMateAt i).comp
            (CompositeFiberAut.hom stabilizer.1)
        exact stabilizer.2.symm
      have newMembership :=
        (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i (1, (CompositeFiberAut.conjugationMulEquiv
            (chain.pastedPulledRouteExactGeometryIsoAt i)).symm
              stabilizer.1)).mpr (by
            change
              (CompositeFiberAut.conjugationMulEquiv
                  (chain.pastedBaseRouteExactGeometryIsoAt i) 1,
                CompositeFiberAut.conjugationMulEquiv
                  (chain.pastedPulledRouteExactGeometryIsoAt i)
                  ((CompositeFiberAut.conjugationMulEquiv
                    (chain.pastedPulledRouteExactGeometryIsoAt i)).symm
                      stabilizer.1)) ∈
                qualifiedComparisonSubgroup
                  (input.generatedCompatibleUpperGeometryMateAt i)
            simpa only [map_one, MulEquiv.apply_symm_apply] using oldMembership)
      change chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i =
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
          (CompositeFiberAut.hom
            ((CompositeFiberAut.conjugationMulEquiv
              (chain.pastedPulledRouteExactGeometryIsoAt i)).symm
                stabilizer.1)) at newMembership
      exact newMembership.symm⟩
  left_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i)).apply_symm_apply _
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i)) _ _

/-- G-118 C1s/C3 source-stabilizer transport constructed directly from the
pasted base endpoint comparison. -/
noncomputable def pastedSourceStabilizerMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    qualifiedComparisonSourceStabilizer
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) ≃*
      qualifiedComparisonSourceStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) where
  toFun stabilizer :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (chain.pastedBaseRouteExactGeometryIsoAt i) stabilizer.1, by
      have newMembership :
          (stabilizer.1, 1) ∈ qualifiedComparisonSubgroup
            (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) := by
        change (CompositeFiberAut.hom stabilizer.1).comp
            (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) =
          chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i
        exact stabilizer.2
      have oldMembership :=
        (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i (stabilizer.1, 1)).mp newMembership
      change
        (CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i) stabilizer.1,
          CompositeFiberAut.conjugationMulEquiv
            (chain.pastedPulledRouteExactGeometryIsoAt i) 1) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) at oldMembership
      rw [map_one] at oldMembership
      change (CompositeFiberAut.hom
          (CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i) stabilizer.1)).comp
            (input.generatedCompatibleUpperGeometryMateAt i) =
        input.generatedCompatibleUpperGeometryMateAt i at oldMembership
      exact oldMembership⟩
  invFun stabilizer :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (chain.pastedBaseRouteExactGeometryIsoAt i)).symm stabilizer.1, by
      have oldMembership :
          (stabilizer.1, 1) ∈ qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) := by
        change (CompositeFiberAut.hom stabilizer.1).comp
            (input.generatedCompatibleUpperGeometryMateAt i) =
          input.generatedCompatibleUpperGeometryMateAt i
        exact stabilizer.2
      have newMembership :=
        (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
          i ((CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i)).symm
              stabilizer.1, 1)).mpr (by
            change
              (CompositeFiberAut.conjugationMulEquiv
                  (chain.pastedBaseRouteExactGeometryIsoAt i)
                  ((CompositeFiberAut.conjugationMulEquiv
                    (chain.pastedBaseRouteExactGeometryIsoAt i)).symm
                      stabilizer.1),
                CompositeFiberAut.conjugationMulEquiv
                  (chain.pastedPulledRouteExactGeometryIsoAt i) 1) ∈
                qualifiedComparisonSubgroup
                  (input.generatedCompatibleUpperGeometryMateAt i)
            simpa only [map_one, MulEquiv.apply_symm_apply] using oldMembership)
      change (CompositeFiberAut.hom
          ((CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i)).symm
              stabilizer.1)).comp
            (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i) =
        chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i
        at newMembership
      exact newMembership⟩
  left_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i)).apply_symm_apply _
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i)) _ _

/-- G-118 C1s/C3 transport of the source-projection kernel.  This is the
kernel with trivial base coordinate and hence corresponds to the target
stabilizer side. -/
noncomputable def pastedSourceProjectionKernelMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    (qualifiedComparisonSourceProjection
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)).ker ≃*
    (qualifiedComparisonSourceProjection
      (input.generatedCompatibleUpperGeometryMateAt i)).ker where
  toFun pair :=
    ⟨chain.pastedQualifiedComparisonMulEquivAt i pair.1, by
      change qualifiedComparisonSourceProjection
          (input.generatedCompatibleUpperGeometryMateAt i)
          (chain.pastedQualifiedComparisonMulEquivAt i pair.1) = 1
      rw [pastedQualifiedComparisonMulEquivAt_sourceProjection, pair.2,
        map_one]⟩
  invFun pair :=
    ⟨(chain.pastedQualifiedComparisonMulEquivAt i).symm pair.1, by
      apply (CompositeFiberAut.conjugationMulEquiv
        (chain.pastedBaseRouteExactGeometryIsoAt i)).injective
      rw [map_one, ← pastedQualifiedComparisonMulEquivAt_sourceProjection,
        (chain.pastedQualifiedComparisonMulEquivAt i).apply_symm_apply]
      exact pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    exact (chain.pastedQualifiedComparisonMulEquivAt i).symm_apply_apply pair.1
  right_inv pair := by
    apply Subtype.ext
    exact (chain.pastedQualifiedComparisonMulEquivAt i).apply_symm_apply pair.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (chain.pastedQualifiedComparisonMulEquivAt i) left.1 right.1

/-- G-118 C1s/C3 transport of the target-projection kernel.  This is the
kernel with trivial pulled coordinate and hence corresponds to the source
stabilizer side. -/
noncomputable def pastedTargetProjectionKernelMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    (qualifiedComparisonTargetProjection
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)).ker ≃*
    (qualifiedComparisonTargetProjection
      (input.generatedCompatibleUpperGeometryMateAt i)).ker where
  toFun pair :=
    ⟨chain.pastedQualifiedComparisonMulEquivAt i pair.1, by
      change qualifiedComparisonTargetProjection
          (input.generatedCompatibleUpperGeometryMateAt i)
          (chain.pastedQualifiedComparisonMulEquivAt i pair.1) = 1
      rw [pastedQualifiedComparisonMulEquivAt_targetProjection, pair.2,
        map_one]⟩
  invFun pair :=
    ⟨(chain.pastedQualifiedComparisonMulEquivAt i).symm pair.1, by
      apply (CompositeFiberAut.conjugationMulEquiv
        (chain.pastedPulledRouteExactGeometryIsoAt i)).injective
      rw [map_one, ← pastedQualifiedComparisonMulEquivAt_targetProjection,
        (chain.pastedQualifiedComparisonMulEquivAt i).apply_symm_apply]
      exact pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    exact (chain.pastedQualifiedComparisonMulEquivAt i).symm_apply_apply pair.1
  right_inv pair := by
    apply Subtype.ext
    exact (chain.pastedQualifiedComparisonMulEquivAt i).apply_symm_apply pair.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (chain.pastedQualifiedComparisonMulEquivAt i) left.1 right.1

/-- G-118 C1s/C3 equivalence of target-partner fibers.  The fixed base
coordinate is transported by the pasted base comparison and the varying
pulled coordinate by the pasted pulled comparison. -/
noncomputable def pastedQualifiedComparisonTargetLiftEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (base : CompositeFiberAut
      (chain.composite.changedInput.generatedBaseRouteGeometryAt i)) :
    QualifiedComparisonTargetLift
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
        base ≃
      QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (chain.pastedBaseRouteExactGeometryIsoAt i) base) where
  toFun lift :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (chain.pastedPulledRouteExactGeometryIsoAt i) lift.1,
      (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i (base, lift.1)).mp lift.2⟩
  invFun lift :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (chain.pastedPulledRouteExactGeometryIsoAt i)).symm lift.1, by
      apply (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i (base, (CompositeFiberAut.conjugationMulEquiv
          (chain.pastedPulledRouteExactGeometryIsoAt i)).symm lift.1)).mpr
      change
        (CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i) base,
          CompositeFiberAut.conjugationMulEquiv
            (chain.pastedPulledRouteExactGeometryIsoAt i)
            ((CompositeFiberAut.conjugationMulEquiv
              (chain.pastedPulledRouteExactGeometryIsoAt i)).symm lift.1)) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i)
      simpa only [MulEquiv.apply_symm_apply] using lift.2⟩
  left_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i)).apply_symm_apply _

/-- G-118 C1s/C3 equivalence of source-partner fibers.  The fixed pulled
coordinate is transported by the pasted pulled comparison and the varying
base coordinate by the pasted base comparison. -/
noncomputable def pastedQualifiedComparisonSourceLiftEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pulled : CompositeFiberAut
      (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) :
    QualifiedComparisonSourceLift
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
        pulled ≃
      QualifiedComparisonSourceLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (chain.pastedPulledRouteExactGeometryIsoAt i) pulled) where
  toFun lift :=
    ⟨CompositeFiberAut.conjugationMulEquiv
        (chain.pastedBaseRouteExactGeometryIsoAt i) lift.1,
      (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i (lift.1, pulled)).mp lift.2⟩
  invFun lift :=
    ⟨(CompositeFiberAut.conjugationMulEquiv
        (chain.pastedBaseRouteExactGeometryIsoAt i)).symm lift.1, by
      apply (chain.pastedEndpointPairMulEquivAt_mem_qualifiedComparison_iff
        i ((CompositeFiberAut.conjugationMulEquiv
          (chain.pastedBaseRouteExactGeometryIsoAt i)).symm lift.1,
            pulled)).mpr
      change
        (CompositeFiberAut.conjugationMulEquiv
            (chain.pastedBaseRouteExactGeometryIsoAt i)
            ((CompositeFiberAut.conjugationMulEquiv
              (chain.pastedBaseRouteExactGeometryIsoAt i)).symm lift.1),
          CompositeFiberAut.conjugationMulEquiv
            (chain.pastedPulledRouteExactGeometryIsoAt i) pulled) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i)
      simpa only [MulEquiv.apply_symm_apply] using lift.2⟩
  left_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i)).symm_apply_apply _
  right_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i)).apply_symm_apply _

/-- G-118 C1s/C3 preservation and reflection of nonempty target-partner
fibers under the pasted endpoint comparisons. -/
theorem pastedQualifiedComparisonTargetLift_nonempty_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (base : CompositeFiberAut
      (chain.composite.changedInput.generatedBaseRouteGeometryAt i)) :
    Nonempty (QualifiedComparisonTargetLift
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
        base) ↔
      Nonempty (QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (chain.pastedBaseRouteExactGeometryIsoAt i) base)) := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨chain.pastedQualifiedComparisonTargetLiftEquivAt i base lift⟩
  · rintro ⟨lift⟩
    exact ⟨(chain.pastedQualifiedComparisonTargetLiftEquivAt i base).symm lift⟩

/-- G-118 C1s/C3 preservation and reflection of nonempty source-partner
fibers under the pasted endpoint comparisons. -/
theorem pastedQualifiedComparisonSourceLift_nonempty_iff
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pulled : CompositeFiberAut
      (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) :
    Nonempty (QualifiedComparisonSourceLift
        (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
        pulled) ↔
      Nonempty (QualifiedComparisonSourceLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (chain.pastedPulledRouteExactGeometryIsoAt i) pulled)) := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨chain.pastedQualifiedComparisonSourceLiftEquivAt i pulled lift⟩
  · rintro ⟨lift⟩
    exact ⟨(chain.pastedQualifiedComparisonSourceLiftEquivAt i pulled).symm lift⟩

/-- G-118 C1s/C3 equivariance of the target-stabilizer action on a
target-partner fiber under the pasted endpoint comparisons. -/
theorem pastedQualifiedComparisonTargetLift_smul
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (base : CompositeFiberAut
      (chain.composite.changedInput.generatedBaseRouteGeometryAt i))
    (stabilizer : qualifiedComparisonTargetStabilizer
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i))
    (lift : QualifiedComparisonTargetLift
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
      base) :
    chain.pastedQualifiedComparisonTargetLiftEquivAt i base
        (stabilizer • lift) =
      chain.pastedTargetStabilizerMulEquivAt i stabilizer •
        chain.pastedQualifiedComparisonTargetLiftEquivAt i base lift := by
  apply Subtype.ext
  exact map_mul (CompositeFiberAut.conjugationMulEquiv
    (chain.pastedPulledRouteExactGeometryIsoAt i)) stabilizer.1 lift.1

/-- G-118 C1s/C3 equivariance of the source-stabilizer action on a
source-partner fiber under the pasted endpoint comparisons. -/
theorem pastedQualifiedComparisonSourceLift_smul
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex)
    (pulled : CompositeFiberAut
      (chain.composite.changedInput.generatedPulledRouteGeometryAt i))
    (stabilizer : qualifiedComparisonSourceStabilizer
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i))
    (lift : QualifiedComparisonSourceLift
      (chain.composite.changedInput.generatedCompatibleUpperGeometryMateAt i)
      pulled) :
    chain.pastedQualifiedComparisonSourceLiftEquivAt i pulled
        (stabilizer • lift) =
      chain.pastedSourceStabilizerMulEquivAt i stabilizer •
        chain.pastedQualifiedComparisonSourceLiftEquivAt i pulled lift := by
  apply Subtype.ext
  exact map_mul (CompositeFiberAut.conjugationMulEquiv
    (chain.pastedBaseRouteExactGeometryIsoAt i)) stabilizer.1 lift.1

end UpperGeometryCompatibleSourcePresentationChange.Chain
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
