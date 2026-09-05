import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonBaseTransport
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonEdgeReselectionConsequences

/-!
# Coefficient-invisible qualified comparison information

This module implements the fixed-datum nonfactorization clause of G-118(D).
The literal positive and negative pairs from C2 have the same coefficient
observation, while qualified-comparison membership separates them.  Hence the
qualified decision cannot factor through the product coefficient observation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperDecisionWitness

/-- The fixed space `Q_*` of complete base/pulled automorphism pairs. -/
abbrev FixedQualifiedPair :=
  CompositeFiberAut
      (problem.data.generatedBaseRouteGeometryAt PUnit.unit) ×
    CompositeFiberAut
      (problem.data.generatedPulledRouteGeometryAt PUnit.unit)

/-- The product coefficient-observation space at the fixed datum. -/
abbrev FixedCoefficientObservationSpace :=
  Aut (CommRingCat.of
      (problem.data.generatedBaseRouteGeometryAt PUnit.unit).Coefficient) ×
    Aut (CommRingCat.of
      (problem.data.generatedPulledRouteGeometryAt PUnit.unit).Coefficient)

/-- The fixed product observation `O_*(b,p) = (κ_X(b), κ_Y(p))`. -/
noncomputable def fixedCoefficientObservation :
    FixedQualifiedPair →* FixedCoefficientObservationSpace :=
  MonoidHom.prodMap
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (problem.data.generatedBaseRouteGeometryAt PUnit.unit))
    (AAT.AG.DoctrineFiberProduct.CompositeFiberAut.coefficientObservation
      (problem.data.generatedPulledRouteGeometryAt PUnit.unit))

/-- The fixed decision predicate `D_*` is literal membership in the qualified
comparison subgroup of the generated comparison. -/
def FixedQualifiedDecision (pair : FixedQualifiedPair) : Prop :=
  pair ∈ qualifiedComparisonSubgroup (solution.component PUnit.unit)

/-- The named C2 generated comparator pair at the twist edge. -/
noncomputable def fixedPositiveQualifiedPair : FixedQualifiedPair :=
  (generatedBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist,
    generatedPulledComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist)

/-- The C2 negative pair keeps the generated base comparator and replaces the
pulled comparator by the identity. -/
noncomputable def fixedNegativeQualifiedPair : FixedQualifiedPair :=
  (generatedBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist,
    1)

/-- The fixed positive and negative pairs are indistinguishable by the full
product coefficient observation. -/
theorem fixedCoefficientObservation_positive_eq_negative :
    fixedCoefficientObservation fixedPositiveQualifiedPair =
      fixedCoefficientObservation fixedNegativeQualifiedPair := by
  apply Prod.ext
  · rfl
  · apply CategoryTheory.Iso.ext
    ext value
    change
      (CompositeFiberAut.hom
        (generatedPulledComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
          PUnit.unit PUnit.unit DecisionEdge.twist)).geometry.coefficientHom value =
        (CompositeFiberAut.hom (1 : CompositeFiberAut
          (problem.data.generatedPulledRouteGeometryAt PUnit.unit))).geometry.coefficientHom
            value
    rw [generatedPulledComparatorCoefficientTrivialUpperReselection.coefficient_id]
    rfl

/-- The named generated comparator pair is accepted by `D_*`. -/
theorem fixedPositiveQualifiedDecision :
    FixedQualifiedDecision fixedPositiveQualifiedPair :=
  generatedComparatorUpperReselections_twist_mem_qualifiedComparison

/-- The pulled-identity companion is rejected by `D_*`. -/
theorem fixedNegativeNotQualifiedDecision :
    ¬ FixedQualifiedDecision fixedNegativeQualifiedPair :=
  generatedBaseComparatorPulledIdentity_twist_not_mem_qualifiedComparison

/-- Qualified-comparison membership at the fixed datum does not factor
through the product coefficient observation. -/
theorem fixedQualifiedDecision_not_factor_through_coefficientObservation :
    ¬ ∃ diagnostic : FixedCoefficientObservationSpace → Prop,
      ∀ pair : FixedQualifiedPair,
        FixedQualifiedDecision pair ↔
          diagnostic (fixedCoefficientObservation pair) := by
  rintro ⟨diagnostic, factors⟩
  have positiveObserved :
      diagnostic (fixedCoefficientObservation fixedPositiveQualifiedPair) :=
    (factors fixedPositiveQualifiedPair).mp fixedPositiveQualifiedDecision
  have negativeObserved :
      diagnostic (fixedCoefficientObservation fixedNegativeQualifiedPair) := by
    rw [← fixedCoefficientObservation_positive_eq_negative]
    exact positiveObserved
  exact fixedNegativeNotQualifiedDecision
    ((factors fixedNegativeQualifiedPair).mpr negativeObserved)

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
