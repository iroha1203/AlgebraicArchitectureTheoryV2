import ResearchLean.AG.ComparisonInformationLoss.ObservationTransport
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientTransport
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonFixedDecision

/-!
# Observation loss for a generated comparison

This module instantiates the general observation-kernel construction at every
G-118 generated compatible comparison.  It also constructs the coefficient
isomorphism carried by the actual generated comparison and proves that
conjugation of endpoint changes commutes with coefficient observation.

Implementation notes: the coefficient equivalence is built from the forward
and inverse coefficient maps of the complete-geometry isomorphism.  The
endpoint kernel equivalence is then derived from the commuting observation
square; it is not stored as an additional hypothesis.
-/

namespace AAT.AG.ComparisonInformationLoss.GeneratedComparison

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open AAT.AG.DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable section

/-- The raw endpoint-change group of a generated compatible comparison. -/
abbrev ChangeGroupAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  UpperGeometryCompatibleProblemInputData.GeneratedQualifiedPairAt input i

/-- The product coefficient-observation group of a generated comparison. -/
abbrev ObservationGroupAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (_input : UpperGeometryCompatibleProblemInputData ctx P k) (_i : P.Vertex) :=
  Aut (CommRingCat.of k) × Aut (CommRingCat.of k)

/-- Product coefficient observation on both generated endpoints. -/
noncomputable def observationAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    ChangeGroupAt input i →* ObservationGroupAt input i :=
  input.generatedPairCoefficientObservationAt i

/-- Comparison-preserving endpoint changes for the generated comparison. -/
def compatibleSubgroupAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Subgroup (ChangeGroupAt input i) :=
  qualifiedComparisonSubgroup (input.generatedCompatibleUpperGeometryMateAt i)

/-- Coefficient-invisible endpoint changes for the generated comparison. -/
abbrev observationKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  (observationAt input i).ker

/-- Coefficient-invisible changes that also preserve the generated comparison. -/
abbrev compatibleKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  compatibleKernel (observationAt input i) (compatibleSubgroupAt input i)

/-- The pointed left-coset obstruction attached to the generated comparison. -/
abbrev observationLossAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  observationKernelAt input i ⧸ compatibleKernelAt input i

/-- The general observation criterion specialized to the generated comparison
diagram: qualified membership is determined by the product coefficient
observation exactly when every invisible change is qualified. -/
theorem exists_observation_predicate_iff_kernel_leAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (∃ predicate : ObservationGroupAt input i → Prop,
        ∀ change : ChangeGroupAt input i,
          change ∈ compatibleSubgroupAt input i ↔
            predicate (observationAt input i change)) ↔
      observationKernelAt input i ≤ compatibleSubgroupAt input i :=
  exists_observation_predicate_iff_ker_le
    (observationAt input i) (compatibleSubgroupAt input i)

/-- The actual generated comparison, packaged as a complete-geometry
isomorphism using its already proved invertibility. -/
noncomputable def comparisonIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedBaseRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i := by
  letI := input.generatedCompatibleUpperGeometryMateAt_isIso i
  exact asIso (input.generatedCompatibleUpperGeometryMateAt i)

/-- A complete-geometry isomorphism induces the coefficient-ring equivalence
given by its actual forward and inverse coefficient maps. -/
noncomputable def coefficientRingEquivOfGeometryIso
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) : G.Coefficient ≃+* H.Coefficient where
  toFun := iso.hom.geometry.coefficientHom
  invFun := iso.inv.geometry.coefficientHom
  left_inv value := by
    exact congrArg
      (fun hom : GeometryTotalHom G G => hom.geometry.coefficientHom value)
      iso.hom_inv_id
  right_inv value := by
    exact congrArg
      (fun hom : GeometryTotalHom H H => hom.geometry.coefficientHom value)
      iso.inv_hom_id
  map_mul' := iso.hom.geometry.coefficientHom.map_mul
  map_add' := iso.hom.geometry.coefficientHom.map_add

/-- The coefficient-ring isomorphism carried by the generated comparison. -/
noncomputable def comparisonCoefficientIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CommRingCat.of (input.generatedBaseRouteGeometryAt i).Coefficient ≅
      CommRingCat.of (input.generatedPulledRouteGeometryAt i).Coefficient :=
  (coefficientRingEquivOfGeometryIso (comparisonIsoAt input i)).toCommRingCatIso

/-- The forward map of the generated coefficient isomorphism is the actual
coefficient map of the generated comparison. -/
@[simp] theorem comparisonCoefficientIsoAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (comparisonCoefficientIsoAt input i).hom.hom =
      (input.generatedCompatibleUpperGeometryMateAt i).geometry.coefficientHom :=
  rfl

/-- Conjugation by the coefficient component of a complete-geometry
isomorphism transports coefficient automorphisms between the endpoints. -/
noncomputable def coefficientConjugationMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    Aut (CommRingCat.of G.Coefficient) ≃*
      Aut (CommRingCat.of H.Coefficient) :=
  Aut.autMulEquivOfIso
    (coefficientRingEquivOfGeometryIso iso).toCommRingCatIso

/-- Endpoint conjugation commutes with coefficient observation. -/
theorem coefficientObservation_conjugation
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut G) :
    CompositeFiberAut.coefficientObservation H
        (CompositeFiberAut.conjugationMulEquiv iso automorphism) =
      coefficientConjugationMulEquiv iso
        (CompositeFiberAut.coefficientObservation G automorphism) := by
  apply CategoryTheory.Iso.ext
  ext value
  rfl

/-- The generated comparison transports source endpoint changes by the
existing complete-fiber conjugation. -/
noncomputable def endpointChangeEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ≃*
      CompositeFiberAut (input.generatedPulledRouteGeometryAt i) :=
  CompositeFiberAut.conjugationMulEquiv (comparisonIsoAt input i)

/-- In ordinary composition notation, endpoint transport has underlying map
`b ↦ c b c⁻¹`; the displayed Lean composite reads from left to right. -/
@[simp] theorem endpointChangeEquivAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedBaseRouteGeometryAt i)) :
    CompositeFiberAut.hom (endpointChangeEquivAt input i automorphism) =
      ((comparisonIsoAt input i).inv.comp
        (CompositeFiberAut.hom automorphism)).comp
          (comparisonIsoAt input i).hom :=
  CompositeFiberAut.conjugationMulEquiv_hom
    (comparisonIsoAt input i) automorphism

/-- The actual coefficient component of the generated comparison transports
coefficient automorphisms by conjugation. -/
noncomputable def endpointObservationEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Aut (CommRingCat.of (input.generatedBaseRouteGeometryAt i).Coefficient) ≃*
      Aut (CommRingCat.of (input.generatedPulledRouteGeometryAt i).Coefficient) :=
  coefficientConjugationMulEquiv (comparisonIsoAt input i)

/-- The two endpoint coefficient observations form the commuting square
required by the general observation transport theorem. -/
theorem endpointObservation_commutesAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedBaseRouteGeometryAt i)) :
    CompositeFiberAut.coefficientObservation
        (input.generatedPulledRouteGeometryAt i)
        (endpointChangeEquivAt input i automorphism) =
      endpointObservationEquivAt input i
        (CompositeFiberAut.coefficientObservation
          (input.generatedBaseRouteGeometryAt i) automorphism) :=
  coefficientObservation_conjugation (comparisonIsoAt input i) automorphism

/-- Restrict comparison conjugation to the coefficient-observation kernels
at the two generated endpoints. -/
noncomputable def endpointObservationKernelEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (CompositeFiberAut.coefficientObservation
        (input.generatedBaseRouteGeometryAt i)).ker ≃*
      (CompositeFiberAut.coefficientObservation
        (input.generatedPulledRouteGeometryAt i)).ker := by
  let diagram : ObservationEquiv
      (CompositeFiberAut.coefficientObservation
        (input.generatedBaseRouteGeometryAt i)) ⊤
      (CompositeFiberAut.coefficientObservation
        (input.generatedPulledRouteGeometryAt i)) ⊤ :=
    { changeEquiv := endpointChangeEquivAt input i
      observationEquiv := endpointObservationEquivAt input i
      observation_comm := endpointObservation_commutesAt input i
      compatible_map := by simp }
  exact diagram.kernelEquiv

/-- The kernel equivalence has the comparison-conjugation map on underlying
endpoint automorphisms. -/
@[simp] theorem endpointObservationKernelEquivAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : (CompositeFiberAut.coefficientObservation
      (input.generatedBaseRouteGeometryAt i)).ker) :
    (endpointObservationKernelEquivAt input i automorphism :
      CompositeFiberAut (input.generatedPulledRouteGeometryAt i)) =
        endpointChangeEquivAt input i automorphism :=
  rfl

end

end AAT.AG.ComparisonInformationLoss.GeneratedComparison

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss.GeneratedComparison
