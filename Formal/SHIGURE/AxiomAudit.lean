import Formal.SHIGURE.AssertStandardAxioms

/-! # SHIGURE kernel audit entry point -/

namespace SHIGURE.AxiomAudit

/-- Exercise the audit entry point with a kernel-checked use of propositional extensionality. -/
theorem and_true_eq (p : Prop) : (p ∧ True) = p :=
  propext ⟨And.left, fun h => ⟨h, True.intro⟩⟩

end SHIGURE.AxiomAudit

#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
