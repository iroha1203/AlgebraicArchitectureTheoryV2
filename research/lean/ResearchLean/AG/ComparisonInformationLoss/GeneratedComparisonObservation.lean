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

/-- G-120(B1) data: the raw endpoint-change group.  It reuses the two actual
generated endpoint `CompositeFiberAut` groups supplied by the G-118 input. -/
abbrev ChangeGroupAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  UpperGeometryCompatibleProblemInputData.GeneratedQualifiedPairAt input i

/-- G-120(B1) data: the observation codomain.  Its two factors are the
coefficient automorphism groups fixed by the generated input coefficient `k`. -/
abbrev ObservationGroupAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (_input : UpperGeometryCompatibleProblemInputData ctx P k) (_i : P.Vertex) :=
  Aut (CommRingCat.of k) × Aut (CommRingCat.of k)

/-- G-120(B1) main construction `O_c`: product coefficient observation on both
generated endpoints, inherited from G-118's existing endpoint observations. -/
noncomputable def observationAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    ChangeGroupAt input i →* ObservationGroupAt input i :=
  input.generatedPairCoefficientObservationAt i

/-- G-120(B1) main construction `Gamma_c`: comparison-preserving endpoint
changes, using the actual generated comparison and the existing G-118 subgroup. -/
def compatibleSubgroupAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Subgroup (ChangeGroupAt input i) :=
  qualifiedComparisonSubgroup (input.generatedCompatibleUpperGeometryMateAt i)

/-- G-120(B1) data `K_c`: the kernel of the constructed product observation;
no extra invisibility certificate is supplied. -/
abbrev observationKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  (observationAt input i).ker

/-- G-120(B1) data `L_c`: invisible changes that also preserve the generated
comparison, obtained by the clause-A `compatibleKernel` construction. -/
abbrev compatibleKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  compatibleKernel (observationAt input i) (compatibleSubgroupAt input i)

/-- G-120(B1) data: the pointed left-coset obstruction `K_c/L_c`.  This is the
general clause-A coset type and does not require normality of `L_c`. -/
abbrev observationLossAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  observationKernelAt input i ⧸ compatibleKernelAt input i

/-- G-120(B1) API theorem applying clause A to the generated comparison diagram:
qualified membership is determined by the product coefficient observation
exactly when every invisible change is qualified.  It has no new premise. -/
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

/-- G-120(B1) construction of `c : X ≅ Y`: the actual generated comparison,
packaged using G-118's already proved `generatedCompatibleUpperGeometryMateAt_isIso`. -/
noncomputable def comparisonIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedBaseRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i := by
  letI := input.generatedCompatibleUpperGeometryMateAt_isIso i
  exact asIso (input.generatedCompatibleUpperGeometryMateAt i)

/-- G-120(B1) helper construction: a complete-geometry isomorphism induces the
coefficient-ring equivalence given by its actual forward and inverse coefficient
maps.  The only premise is the supplied geometry isomorphism. -/
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

/-- G-120(B1) main coefficient isomorphism `S_c`, specialized from the actual
generated comparison isomorphism rather than a chosen coefficient identity. -/
noncomputable def comparisonCoefficientIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CommRingCat.of (input.generatedBaseRouteGeometryAt i).Coefficient ≅
      CommRingCat.of (input.generatedPulledRouteGeometryAt i).Coefficient :=
  (coefficientRingEquivOfGeometryIso (comparisonIsoAt input i)).toCommRingCatIso

/-- G-120(B1) API evaluation: the forward map of `S_c` is the actual coefficient
map of the generated comparison.  It unfolds the preceding construction. -/
@[simp] theorem comparisonCoefficientIsoAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (comparisonCoefficientIsoAt input i).hom.hom =
      (input.generatedCompatibleUpperGeometryMateAt i).geometry.coefficientHom :=
  rfl

/-- G-120(B1) helper construction: conjugation by the actual coefficient
component of a geometry isomorphism transports coefficient automorphisms. -/
noncomputable def coefficientConjugationMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    Aut (CommRingCat.of G.Coefficient) ≃*
      Aut (CommRingCat.of H.Coefficient) :=
  Aut.autMulEquivOfIso
    (coefficientRingEquivOfGeometryIso iso).toCommRingCatIso

/-- G-120(B1) helper theorem: endpoint conjugation commutes with coefficient
observation.  The equality is derived from the actual coefficient components
of the supplied geometry isomorphism and endpoint automorphism. -/
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

/-- G-120(B1) main construction `T_c`: the generated comparison transports
source endpoint changes by the existing G-118 complete-fiber conjugation. -/
noncomputable def endpointChangeEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ≃*
      CompositeFiberAut (input.generatedPulledRouteGeometryAt i) :=
  CompositeFiberAut.conjugationMulEquiv (comparisonIsoAt input i)

/-- G-120(B1) API evaluation for `T_c`: in ordinary composition notation its
underlying map is `b ↦ c b c⁻¹`; the displayed Lean composite reads from left
to right and follows from the existing conjugation theorem. -/
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

/-- G-120(B1) main construction `S_c`: the actual coefficient component of the
generated comparison transports coefficient automorphisms by conjugation. -/
noncomputable def endpointObservationEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Aut (CommRingCat.of (input.generatedBaseRouteGeometryAt i).Coefficient) ≃*
      Aut (CommRingCat.of (input.generatedPulledRouteGeometryAt i).Coefficient) :=
  coefficientConjugationMulEquiv (comparisonIsoAt input i)

/-- G-120(B1) main theorem `O_Y T_c = S_c O_X`: the endpoint observations form
the commuting square required by clause A.  It specializes the coefficient
conjugation equality to the actual generated comparison. -/
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

/-- G-120(B1) main kernel theorem: restrict `T_c` to the two endpoint
coefficient-observation kernels.  Kernel membership is derived from the
commuting square through clause A, not supplied as a premise. -/
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

/-- G-120(B1) API evaluation: the induced kernel equivalence has `T_c` as its
underlying endpoint map.  It unfolds the clause-A kernel restriction. -/
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
