import Formal.SHIGURE.AssertStandardAxioms
import Formal.SHIGURE.Part1.PreservationExamples
import Formal.SHIGURE.Part1.ReadingExamples

/-! # SHIGURE kernel audit entry point -/

namespace SHIGURE.AxiomAudit

/-- Exercise the audit entry point with a kernel-checked use of propositional extensionality. -/
theorem and_true_eq (p : Prop) : (p ∧ True) = p :=
  propext ⟨And.left, fun h => ⟨h, True.intro⟩⟩

namespace Chapter1

-- These aliases register the imported proofs as roots of the transitive kernel audit.
def termSubstitution := @Term.eval_substitute
def substitutionDomain := @Term.mem_domain_substitute
def formulaSubstitution := @Formula.holds_substitute
def termDomainMap := @StructureMap.mem_domain_map
def termValueMap := @StructureMap.eval_get_map
def formulaMap := @StructureMap.holds_map
def lawInputMap := @StructureMap.inputSet_image_subset
def jointInputMap := @OrderedEquation.jointInputs_image_subset
def residualMap := @OrderedEquation.residual_map
def jointInputSubstitution := @OrderedEquation.jointInputs_substitute
def residualSubstitution := @OrderedEquation.residual_substitute
def writtenEquationSatisfaction := @OrderedEquation.Written.holds_iff_residual

def constantGraphSource := SHIGURE.Chapter1.DomainTransport.atConstant_holds_A
def constantGraphTarget := SHIGURE.Chapter1.DomainTransport.atConstant_fails_B
def constantDomainCounterexample := SHIGURE.Chapter1.DomainTransport.identity_cannot_preserve_domain
def guardedModel := SHIGURE.Chapter1.DomainTransport.guarded_holds_B
def unguardedCounterexample := SHIGURE.Chapter1.DomainTransport.unrestricted_fails_B
def interpretationCounterexample := SHIGURE.Chapter1.DomainTransport.identity_translation_not_interpretation

def readingSquare := @ReadingComparison.commutes_eq
def readingPullbackModel := @ReadingComparison.pullback_isModel
def readingLocalEvaluation := @ReadingComparison.restricted_evaluation_commutes
def readingLocalTransport := @ReadingComparison.transport_restricted_formula
def sharedInputUniqueness := @Reading.sharedInput_unique

end Chapter1

end SHIGURE.AxiomAudit

#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
