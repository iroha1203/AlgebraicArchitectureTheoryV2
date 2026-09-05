import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientNonfactorization
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonEndpointTransport

/-!
# Transport of coefficient-invisible qualified comparison information

This module implements the C1 and C3 transport clauses of G-118(D).  The C1
selected endpoint conjugations preserve the complete product coefficient
observation and reflect literal qualified membership.  The generated C3 pair
map preserves coefficient observations for every source pair; it preserves
and reflects the qualified decision when the residual subgroup `J_i` is
trivial.  The C2 connection is the fixed edge pair used by the predecessor
nonfactorization theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- Pair space in the selected canonical-authored endpoint presentation. -/
abbrev CanonicalQualifiedPairAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  CompositeFiberAut (input.canonicalAuthoredBaseRouteGeometryAt i) ×
    CompositeFiberAut (input.canonicalAuthoredPulledRouteGeometryAt i)

/-- Pair space in the generated endpoint presentation. -/
abbrev GeneratedQualifiedPairAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ×
    CompositeFiberAut (input.generatedPulledRouteGeometryAt i)

/-- Product coefficient observation on the canonical-authored endpoints. -/
noncomputable def canonicalPairCoefficientObservationAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CanonicalQualifiedPairAt input i →*
      (Aut (CommRingCat.of k) × Aut (CommRingCat.of k)) :=
  MonoidHom.prodMap
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (input.canonicalAuthoredBaseRouteGeometryAt i))
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (input.canonicalAuthoredPulledRouteGeometryAt i))

/-- Product coefficient observation on the generated endpoints. -/
noncomputable def generatedPairCoefficientObservationAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeneratedQualifiedPairAt input i →*
      (Aut (CommRingCat.of k) × Aut (CommRingCat.of k)) :=
  MonoidHom.prodMap
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (input.generatedBaseRouteGeometryAt i))
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (input.generatedPulledRouteGeometryAt i))

/-- Move an arbitrary generated pair backward through the two selected C1
endpoint changes. -/
noncomputable def canonicalPairBackwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : GeneratedQualifiedPairAt input i) :
    CanonicalQualifiedPairAt input i :=
  ((CompositeFiberAut.conjugationMulEquiv
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)).symm
      pair.1,
    (CompositeFiberAut.conjugationMulEquiv
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)).symm
      pair.2)

/-- C1 backward conjugation preserves and reflects literal qualified
membership for every generated raw pair. -/
theorem canonicalPairBackwardAt_mem_qualifiedComparison_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : GeneratedQualifiedPairAt input i) :
    input.canonicalPairBackwardAt i pair ∈
        qualifiedComparisonSubgroup
          (input.canonicalCompanionUpperRefinementBCSolution.component i) ↔
      pair ∈ qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact inverseConjugatedPair_mem_qualifiedComparison_iff
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i) pair

/-- C1 backward transport commutes with the complete product coefficient
observation for every pair. -/
theorem canonicalPairBackwardAt_coefficientObservation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : GeneratedQualifiedPairAt input i) :
    input.canonicalPairCoefficientObservationAt i
        (input.canonicalPairBackwardAt i pair) =
      input.generatedPairCoefficientObservationAt i pair := by
  apply Prod.ext
  · change
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.canonicalAuthoredBaseRouteGeometryAt i)
          ((CompositeFiberAut.conjugationMulEquiv
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)).symm
            pair.1) =
        AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.generatedBaseRouteGeometryAt i) pair.1
    apply CategoryTheory.Iso.ext
    ext value
    rw [AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      input.canonicalAuthoredBaseConjugation_symm_coefficientHom]
  · change
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.canonicalAuthoredPulledRouteGeometryAt i)
          ((CompositeFiberAut.conjugationMulEquiv
            (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)).symm
            pair.2) =
        AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.generatedPulledRouteGeometryAt i) pair.2
    apply CategoryTheory.Iso.ext
    ext value
    rw [AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      input.canonicalAuthoredPulledConjugation_symm_coefficientHom]

/-- The actual generated base endpoint map preserves every coefficient map,
not only coefficient-trivial inputs. -/
theorem generatedBaseCompositeFiberAutAt_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (CompositeFiberAut.hom
      (input.generatedBaseCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
        (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  have factorization := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedBaseCompositeFiberAutAt_fac i automorphism)
  change
    (input.generatedBaseRouteLegAt i).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (input.generatedBaseCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.generatedBaseRouteLegAt i).geometry.coefficientHom
    at factorization
  rw [input.generatedBaseRouteLegAt_coefficient_id] at factorization
  simpa only [RingHom.id_comp, RingHom.comp_id] using factorization

/-- The actual generated pulled endpoint map preserves every coefficient
map. -/
theorem generatedPulledCompositeFiberAutAt_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (CompositeFiberAut.hom
      (input.generatedPulledCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
        (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  have factorization := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedPulledCompositeFiberAutAt_fac i automorphism)
  change
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (input.generatedPulledCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.generatedPulledRouteLegAt i).geometry.coefficientHom
    at factorization
  rw [input.generatedPulledRouteLegAt_coefficient_id] at factorization
  simpa only [RingHom.id_comp, RingHom.comp_id] using factorization

/-- Product coefficient observation on a source pair. -/
noncomputable def sourcePairCoefficientObservationAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package) →*
      (Aut (CommRingCat.of k) × Aut (CommRingCat.of k)) :=
  MonoidHom.prodMap
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (input.sourceGeometry i).package)
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (input.sourceGeometry i).package)

/-- C3 preserves the complete product coefficient observation for every
source pair. -/
theorem generatedComparisonPairHomAt_coefficientObservation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPairCoefficientObservationAt i
        (input.generatedComparisonPairHomAt i pair) =
      input.sourcePairCoefficientObservationAt i pair := by
  apply Prod.ext
  · change
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.generatedBaseRouteGeometryAt i)
          (input.generatedBaseCompositeFiberAutHomAt i pair.1) =
        AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.sourceGeometry i).package pair.1
    apply CategoryTheory.Iso.ext
    ext value
    rw [AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      input.generatedBaseCompositeFiberAutAt_coefficientHom]
  · change
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.generatedPulledRouteGeometryAt i)
          (input.generatedPulledCompositeFiberAutHomAt i pair.2) =
        AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
          (input.sourceGeometry i).package pair.2
    apply CategoryTheory.Iso.ext
    ext value
    rw [AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation_hom,
      input.generatedPulledCompositeFiberAutAt_coefficientHom]

/-- Under the exact C3 reflection condition, the generated pair map preserves
and reflects the literal qualified decision. -/
theorem generatedComparisonPairHomAt_mem_qualifiedComparison_iff_of_kernel_eq_bot
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (kernelIdentity : input.generatedPulledComparisonKernel i = ⊥)
    (pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedComparisonPairHomAt i pair ∈
        qualifiedComparisonSubgroup
          (input.generatedCompatibleUpperGeometryMateAt i) ↔
      pair ∈ qualifiedComparisonSubgroup
        (𝟙 (input.sourceGeometry i).package) := by
  constructor
  · exact ((input.generatedComparisonPairHomAt_reflects_qualifiedComparison_iff
      i).2 kernelIdentity) pair
  · exact input.generatedComparisonPairHomAt_preserves_qualifiedComparison i

/-- A source observation collision separated by the source identity
comparison transports to a coefficient-invisible target separation whenever
the exact C3 reflection condition holds. -/
theorem generatedQualifiedDecision_not_factor_of_source_collision
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (kernelIdentity : input.generatedPulledComparisonKernel i = ⊥)
    (positive negative : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package)
    (observationCollision :
      input.sourcePairCoefficientObservationAt i positive =
        input.sourcePairCoefficientObservationAt i negative)
    (positiveDecision : positive ∈ qualifiedComparisonSubgroup
      (𝟙 (input.sourceGeometry i).package))
    (negativeDecision : ¬ negative ∈ qualifiedComparisonSubgroup
      (𝟙 (input.sourceGeometry i).package)) :
    ¬ ∃ diagnostic : (Aut (CommRingCat.of k) × Aut (CommRingCat.of k)) → Prop,
      ∀ pair : GeneratedQualifiedPairAt input i,
        pair ∈ qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) ↔
          diagnostic (input.generatedPairCoefficientObservationAt i pair) := by
  rintro ⟨diagnostic, factors⟩
  have positiveTarget :=
    (input.generatedComparisonPairHomAt_mem_qualifiedComparison_iff_of_kernel_eq_bot
      i kernelIdentity positive).2 positiveDecision
  have negativeTarget :=
    (input.generatedComparisonPairHomAt_mem_qualifiedComparison_iff_of_kernel_eq_bot
      i kernelIdentity negative).not.mpr negativeDecision
  have targetObservationCollision :
      input.generatedPairCoefficientObservationAt i
          (input.generatedComparisonPairHomAt i positive) =
        input.generatedPairCoefficientObservationAt i
          (input.generatedComparisonPairHomAt i negative) := by
    rw [input.generatedComparisonPairHomAt_coefficientObservation,
      input.generatedComparisonPairHomAt_coefficientObservation]
    exact observationCollision
  have positiveObserved :=
    (factors (input.generatedComparisonPairHomAt i positive)).mp positiveTarget
  have negativeObserved : diagnostic
      (input.generatedPairCoefficientObservationAt i
        (input.generatedComparisonPairHomAt i negative)) := by
    rw [← targetObservationCollision]
    exact positiveObserved
  exact negativeTarget
    ((factors (input.generatedComparisonPairHomAt i negative)).mpr
      negativeObserved)

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The fixed canonical-authored pair space used by C1 transport. -/
abbrev CanonicalFixedQualifiedPair :=
  problem.data.CanonicalQualifiedPairAt PUnit.unit

/-- Fixed C1 product coefficient observation. -/
noncomputable def canonicalFixedCoefficientObservation :
    CanonicalFixedQualifiedPair →*
      (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) :=
  problem.data.canonicalPairCoefficientObservationAt PUnit.unit

/-- Literal fixed qualified decision in the canonical-authored presentation. -/
def CanonicalFixedQualifiedDecision
    (pair : CanonicalFixedQualifiedPair) : Prop :=
  pair ∈ qualifiedComparisonSubgroup
    (problem.data.canonicalCompanionUpperRefinementBCSolution.component
      PUnit.unit)

/-- The fixed positive canonical-authored edge pair. -/
noncomputable def canonicalFixedPositiveQualifiedPair :
    CanonicalFixedQualifiedPair :=
  (canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist,
    canonicalCompanionPulledComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist)

/-- The fixed negative canonical-authored pair keeps the same base edge and
replaces the pulled edge by identity. -/
noncomputable def canonicalFixedNegativeQualifiedPair :
    CanonicalFixedQualifiedPair :=
  (canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist,
    (CoefficientTrivialUpperEdgeReselection.one
      problem.data.canonicalAuthoredPulledRouteTransport).toUpperEdgeReselection
        PUnit.unit PUnit.unit DecisionEdge.twist)

/-- The fixed canonical positive pair is exactly the C1 backward image of the
Cycle 9 generated positive pair. -/
theorem canonicalFixedPositiveQualifiedPair_eq_backward :
    canonicalFixedPositiveQualifiedPair =
      problem.data.canonicalPairBackwardAt PUnit.unit
        fixedPositiveQualifiedPair := by
  rfl

/-- The fixed canonical negative pair is exactly the C1 backward image of the
Cycle 9 generated pulled-identity pair. -/
theorem canonicalFixedNegativeQualifiedPair_eq_backward :
    canonicalFixedNegativeQualifiedPair =
      problem.data.canonicalPairBackwardAt PUnit.unit
        fixedNegativeQualifiedPair := by
  apply Prod.ext
  · rfl
  · simp only [canonicalFixedNegativeQualifiedPair,
      fixedNegativeQualifiedPair,
      problem.data.generatedPulledIdentityComparatorTransport_comparator,
      CoefficientTrivialUpperEdgeReselection.one_toUpperEdgeReselection,
      UpperGeometryCompatibleProblemInputData.canonicalPairBackwardAt,
      map_one]
    rfl

/-- The transported fixed pairs retain their coefficient-observation
collision. -/
theorem canonicalFixedCoefficientObservation_positive_eq_negative :
    canonicalFixedCoefficientObservation canonicalFixedPositiveQualifiedPair =
      canonicalFixedCoefficientObservation canonicalFixedNegativeQualifiedPair := by
  rw [canonicalFixedPositiveQualifiedPair_eq_backward,
    canonicalFixedNegativeQualifiedPair_eq_backward]
  calc
    _ = problem.data.generatedPairCoefficientObservationAt PUnit.unit
        fixedPositiveQualifiedPair :=
      problem.data.canonicalPairBackwardAt_coefficientObservation _ _
    _ = problem.data.generatedPairCoefficientObservationAt PUnit.unit
        fixedNegativeQualifiedPair := fixedCoefficientObservation_positive_eq_negative
    _ = _ :=
      (problem.data.canonicalPairBackwardAt_coefficientObservation _ _).symm

/-- The C1-transported positive pair remains qualified. -/
theorem canonicalFixedPositiveQualifiedDecision :
    CanonicalFixedQualifiedDecision canonicalFixedPositiveQualifiedPair := by
  rw [canonicalFixedPositiveQualifiedPair_eq_backward]
  exact (problem.data.canonicalPairBackwardAt_mem_qualifiedComparison_iff
    PUnit.unit fixedPositiveQualifiedPair).2 fixedPositiveQualifiedDecision

/-- The C1-transported negative pair remains outside the qualified group. -/
theorem canonicalFixedNegativeNotQualifiedDecision :
    ¬ CanonicalFixedQualifiedDecision canonicalFixedNegativeQualifiedPair := by
  rw [canonicalFixedNegativeQualifiedPair_eq_backward]
  exact (problem.data.canonicalPairBackwardAt_mem_qualifiedComparison_iff
    PUnit.unit fixedNegativeQualifiedPair).not.mpr
      fixedNegativeNotQualifiedDecision

/-- The fixed qualified decision remains nonfactorable after the complete C1
presentation change. -/
theorem canonicalFixedQualifiedDecision_not_factor_through_coefficientObservation :
    ¬ ∃ diagnostic :
        (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) → Prop,
      ∀ pair : CanonicalFixedQualifiedPair,
        CanonicalFixedQualifiedDecision pair ↔
          diagnostic (canonicalFixedCoefficientObservation pair) := by
  rintro ⟨diagnostic, factors⟩
  have positiveObserved :=
    (factors canonicalFixedPositiveQualifiedPair).mp
      canonicalFixedPositiveQualifiedDecision
  have negativeObserved :
      diagnostic (canonicalFixedCoefficientObservation
        canonicalFixedNegativeQualifiedPair) := by
    rw [← canonicalFixedCoefficientObservation_positive_eq_negative]
    exact positiveObserved
  exact canonicalFixedNegativeNotQualifiedDecision
    ((factors canonicalFixedNegativeQualifiedPair).mpr negativeObserved)

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
