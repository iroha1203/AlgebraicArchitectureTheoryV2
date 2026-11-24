import Formal.SHIGURE.AssertStandardAxioms
import Formal.SHIGURE.Part1.PreservationExamples
import Formal.SHIGURE.Part1.ReadingExamples

/-! # SHIGURE kernel audit entry point -/

namespace SHIGURE.AxiomAudit

/-- Exercise the audit entry point with a kernel-checked use of propositional extensionality. -/
theorem and_true_eq (p : Prop) : (p ∧ True) = p :=
  propext ⟨And.left, fun h => ⟨h, True.intro⟩⟩

-- The main proofs from Chapter 1, the counterexample, and the reading square.
#shigure_assert_standard_axioms_of [
  Term.eval_substitute,
  Term.mem_domain_substitute,
  Formula.holds_substitute,
  StructureMap.mem_domain_map,
  StructureMap.eval_get_map,
  StructureMap.holds_map,
  StructureMap.inputSet_image_subset,
  OrderedEquation.jointInputs_image_subset,
  OrderedEquation.residual_map,
  OrderedEquation.jointInputs_substitute,
  OrderedEquation.residual_substitute,
  OrderedEquation.Written.holds_iff_residual,
  OrderedEquation.Written.toLaw_substitute,
  Law.mem_inputSet_substitute,
  SHIGURE.Chapter1.DomainTransport.atConstant_holds_A,
  SHIGURE.Chapter1.DomainTransport.atConstant_fails_B,
  SHIGURE.Chapter1.DomainTransport.identity_cannot_preserve_domain,
  SHIGURE.Chapter1.DomainTransport.guarded_holds_B,
  SHIGURE.Chapter1.DomainTransport.unrestricted_fails_B,
  SHIGURE.Chapter1.DomainTransport.identity_translation_not_interpretation,
  ReadingComparison.commutes_eq,
  ReadingComparison.pullback_isModel,
  ReadingComparison.restricted_evaluation_commutes,
  ReadingComparison.transport_restricted_formula,
  Reading.sharedInput_unique,
  Interpretation.Equivalent.refl,
  Interpretation.Equivalent.symm,
  Interpretation.Equivalent.trans,
  Reading.sharedInput_injective,
  SHIGURE.Chapter1.RestrictedCoefficients.compares_after_restricting_ambient_readings,
  SHIGURE.Chapter1.RestrictedCoefficients.cannot_change_retained_law,
  SHIGURE.Chapter1.RestrictedCoefficients.cannot_erase_retained_ordered_terms,
  SHIGURE.Chapter1.RestrictedCoefficients.cannot_replace_retained_derivation,
  SHIGURE.Chapter1.RestrictedCoefficients.cannot_discard_declared_observation_sort,
  SHIGURE.Chapter1.CoefficientTransport.cannot_repeat_common_named_position,
  SHIGURE.Chapter1.CoefficientTransport.independently_reindexed_comparison,
  SHIGURE.Chapter1.CoefficientTransport.cannot_discard_coefficient_sort,
  SHIGURE.Chapter1.CoefficientTransport.cannot_relabel_coefficient_position,
  SHIGURE.Chapter1.CoefficientTransport.named_subset_keeps_original_position,
  SHIGURE.Chapter1.CoefficientTransport.padded_ordinary_product_keeps_first_name,
  SHIGURE.Chapter1.CoefficientTransport.offset_not_determined_by_retained_structure,
  SHIGURE.Chapter1.CoefficientTransport.point_evaluation_respects_restriction,
  SHIGURE.Chapter1.RetainedCoefficientInputs.compatible_explicit_sharing_survives_name_collision,
  SHIGURE.Chapter1.RetainedCoefficientInputs.declared_observation_covers_both_sorts,
  SHIGURE.Chapter1.RetainedCoefficientInputs.declared_observation_cannot_use_sort_only_assignment,
  ReadingComparison.target_input_is_covered,
  ReadingContextChange.target_evaluation_input_is_covered,
  ReadingComparison.covered_commutes,
  ReadingComparison.target_observation_is_assigned,
  ReadingComparison.observation_square_on_retained,
  Interpretation.Equivalent.formula_holds_iff,
  SHIGURE.Chapter1.CoverTransport.equivalent_representative_transports_in_assigned_piece,
  SHIGURE.Chapter1.AdditionalCoefficientInputs.extra_cannot_change_original_sort,
  SHIGURE.Chapter1.AdditionalCoefficientInputs.extra_can_restore_unused_name,
  SHIGURE.Chapter1.AdditionalCoefficientInputs.extra_keeps_original_sharing,
  SHIGURE.Chapter1.AdditionalCoefficientInputs.extra_cannot_reassign_original_sharing,
  SHIGURE.Chapter1.Observation.cannot_compare_external_after_forgetting_input,
  SHIGURE.Chapter1.Observation.constant_observations_compare_through_empty_cover,
  SHIGURE.Chapter1.CoefficientTransport.identity_coefficients_across_cover_change,
  SHIGURE.Chapter1.RetainedCoefficientInputs.fixed_parameters_cannot_invent_ordinary_share,
  SHIGURE.Chapter1.IndexedObservation.nonidentity_at_fixed_context,
  SHIGURE.Chapter1.IndexedObservation.external_stays_available_when_declarations_are_added,
  ReadingInputMap.mapRestrictedValues_restrict,
  ReadingComparison.observation_and_coefficients_on_retained,
  SHIGURE.Chapter1.CoefficientTransport.cannot_use_empty_ambient_to_skip_coefficient_square,
  SHIGURE.Chapter1.CoefficientTransport.introduces_scalar_at_retained_tuple,
  SHIGURE.Chapter1.CoefficientTransport.joint_input_ignores_unused_empty_position,
  CoefficientComparison.restricted_evaluation_commutes,
  CoefficientComparison.evaluation_from_support,
  ReadingComparison.coefficient_support_on_retained,
  CoefficientReading.evaluateRetained_mk
]

end SHIGURE.AxiomAudit

#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
