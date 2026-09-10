import ResearchLean.AG.ComparisonInformationLoss.EndpointKernelClassification
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientNonfactorization

/-!
# Fixed coefficient-invisible observation-loss witness

This module applies the G-120 observation-loss classification to the fixed
positive and negative generated-comparison pairs already chosen by G-118.
Their quotient is an actual observation-kernel element outside the compatible
subgroup, hence gives both a nonbasepoint loss class and a nonidentity value
under the endpoint-kernel classification.

Implementation notes: no new example is selected.  The coefficient collision
and qualified/nonqualified separation are the existing fixed witness facts;
the new proofs expose their exact kernel, coset, and `Psi` consequences.
-/

namespace AAT.AG.ComparisonInformationLoss.GeneratedComparison

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open AAT.AG.DoctrineFiberProduct
open AAT.AG.DoctrineFiberProduct.UpperDecisionWitness

set_option synthInstance.maxHeartbeats 100000

noncomputable section

/-- G-120(B3) fixed data `q₊`: the existing positive generated-comparison
pair, viewed in the actual change group of `problem.data`. -/
abbrev fixedPositiveChange : ChangeGroupAt problem.data PUnit.unit :=
  fixedPositiveQualifiedPair

/-- G-120(B3) fixed data `q₋`: the existing negative generated-comparison
pair, with the same coefficient observation as `q₊`. -/
abbrev fixedNegativeChange : ChangeGroupAt problem.data PUnit.unit :=
  fixedNegativeQualifiedPair

/-- G-120(B3) fixed observation map `O_*`; this is the actual generated-pair
coefficient observation, definitionally the existing fixed observation. -/
abbrev fixedObservation := observationAt problem.data PUnit.unit

/-- G-120(B3) premise discharge: the existing positive pair belongs to the
actual generated-comparison compatible subgroup `Γ_*`. -/
theorem fixedPositiveChange_mem_compatible :
    fixedPositiveChange ∈ compatibleSubgroupAt problem.data PUnit.unit :=
  fixedPositiveQualifiedDecision

/-- G-120(B3) premise discharge: the existing negative pair does not belong
to the actual generated-comparison compatible subgroup `Γ_*`. -/
theorem fixedNegativeChange_not_mem_compatible :
    fixedNegativeChange ∉ compatibleSubgroupAt problem.data PUnit.unit :=
  fixedNegativeNotQualifiedDecision

/-- G-120(B3) premise discharge: the two fixed changes have the same value
under the actual product coefficient observation `O_*`. -/
theorem fixedObservation_positive_eq_negative :
    fixedObservation fixedPositiveChange =
      fixedObservation fixedNegativeChange :=
  fixedCoefficientObservation_positive_eq_negative

/-- G-120(B3) fixed kernel witness
`k_* := q₊⁻¹ q₋ ∈ K_*`, with kernel membership derived from the existing
coefficient-observation collision. -/
def fixedKernelChange : observationKernelAt problem.data PUnit.unit :=
  ⟨fixedPositiveChange⁻¹ * fixedNegativeChange, by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, fixedObservation_positive_eq_negative]
    simp⟩

/-- G-120(B3) API: the underlying change of `k_*` is literally
`q₊⁻¹ q₋`. -/
@[simp] theorem fixedKernelChange_value :
    (fixedKernelChange : ChangeGroupAt problem.data PUnit.unit) =
      fixedPositiveChange⁻¹ * fixedNegativeChange :=
  rfl

/-- G-120(B3) main separation: the fixed kernel witness does not belong to
the compatible subgroup `Γ_*`. -/
theorem fixedKernelChange_not_mem_compatible :
    (fixedKernelChange : ChangeGroupAt problem.data PUnit.unit) ∉
      compatibleSubgroupAt problem.data PUnit.unit := by
  intro hk
  apply fixedNegativeChange_not_mem_compatible
  have hmul := (compatibleSubgroupAt problem.data PUnit.unit).mul_mem
    fixedPositiveChange_mem_compatible hk
  simpa [fixedKernelChange, mul_assoc] using hmul

/-- G-120(B3) equivalent intersection form: `k_*` lies outside
`L_* = K_* ∩ Γ_*`. -/
theorem fixedKernelChange_not_mem_compatibleKernel :
    fixedKernelChange ∉ compatibleKernelAt problem.data PUnit.unit := by
  rw [mem_compatibleKernel_iff]
  exact fixedKernelChange_not_mem_compatible

/-- G-120(B3) main pointed obstruction: the left coset `k_*L_*` differs
from the distinguished coset `L_*`. -/
theorem fixedKernelChange_coset_ne_basepoint :
    QuotientGroup.mk fixedKernelChange ≠
      (QuotientGroup.mk 1 : observationLossAt problem.data PUnit.unit) := by
  intro hcoset
  have hpositiveMul :
      fixedPositiveChange *
          (fixedKernelChange : ChangeGroupAt problem.data PUnit.unit) ∈
        compatibleSubgroupAt problem.data PUnit.unit :=
    (mul_mem_iff_kernel_coset_basepoint
      (observationAt problem.data PUnit.unit)
      (compatibleSubgroupAt problem.data PUnit.unit)
      fixedPositiveChange_mem_compatible fixedKernelChange).2 hcoset
  apply fixedNegativeChange_not_mem_compatible
  simpa [fixedKernelChange, mul_assoc] using hpositiveMul

/-- G-120(B3) nonfactorization derived through the clause-A kernel
criterion from the explicit witness `k_* ∈ K_* \ Γ_*`.  Its statement is the
same fixed qualified-decision nonfactorization already proved in G-118. -/
theorem fixedQualifiedDecision_not_factor_via_observationKernel :
    ¬ ∃ diagnostic : FixedCoefficientObservationSpace → Prop,
      ∀ pair : FixedQualifiedPair,
        FixedQualifiedDecision pair ↔
          diagnostic (fixedCoefficientObservation pair) := by
  change ¬ ∃ diagnostic : ObservationGroupAt problem.data PUnit.unit → Prop,
    ∀ change : ChangeGroupAt problem.data PUnit.unit,
      change ∈ compatibleSubgroupAt problem.data PUnit.unit ↔
        diagnostic (observationAt problem.data PUnit.unit change)
  rw [exists_observation_predicate_iff_kernel_leAt problem.data PUnit.unit]
  intro hle
  exact fixedKernelChange_not_mem_compatible (hle fixedKernelChange.2)

/-- G-120(B3) evaluation of the fixed loss class under `Psi`, specialized
from the general representative formula of B2. -/
theorem fixedKernelChange_Psi_value :
    observationLossEquivTargetKernelAt problem.data PUnit.unit
        (QuotientGroup.mk fixedKernelChange) =
      ((endpointKernelProductEquivAt problem.data PUnit.unit).symm
          fixedKernelChange).2 *
        (endpointObservationKernelEquivAt problem.data PUnit.unit
          ((endpointKernelProductEquivAt problem.data PUnit.unit).symm
            fixedKernelChange).1)⁻¹ :=
  observationLossEquivTargetKernelAt_mk problem.data PUnit.unit fixedKernelChange

/-- G-120(B3) main classified obstruction: the explicit value of `Psi` on
the fixed nonbasepoint loss class is not the identity of the target endpoint
observation kernel. -/
theorem fixedKernelChange_Psi_ne_one :
    observationLossEquivTargetKernelAt problem.data PUnit.unit
        (QuotientGroup.mk fixedKernelChange) ≠ 1 := by
  intro hvalue
  rw [fixedKernelChange_Psi_value] at hvalue
  apply fixedKernelChange_coset_ne_basepoint
  apply (observationLossEquivTargetKernelAt problem.data PUnit.unit).injective
  rw [observationLossEquivTargetKernelAt_basepoint]
  rw [fixedKernelChange_Psi_value]
  exact hvalue

end

end AAT.AG.ComparisonInformationLoss.GeneratedComparison

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss.GeneratedComparison
