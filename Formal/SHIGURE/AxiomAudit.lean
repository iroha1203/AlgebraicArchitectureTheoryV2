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
  SHIGURE.Chapter1.CoefficientTransport.cannot_repeat_common_named_position
]

end SHIGURE.AxiomAudit

#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
