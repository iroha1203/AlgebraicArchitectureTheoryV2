import Formal.SHIGURE.AssertStandardAxioms

namespace SHIGURE.AxiomAudit

/-- Exercise the audit entry point with a kernel-checked use of propositional extensionality. -/
theorem andTrue (p : Prop) : (p ∧ True) = p :=
  propext ⟨And.left, fun h => ⟨h, True.intro⟩⟩

end SHIGURE.AxiomAudit

#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit
