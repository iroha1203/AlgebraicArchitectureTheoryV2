import Formal.SHIGURE.AssertStandardAxioms

/-- error: No declarations in namespace 'SHIGURE' in the current module -/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE

namespace SHIGURE.KernelAuditTest.Allowed.Nested

theorem reflexivity : True := True.intro

theorem propositionalEquality (p q : Prop) (h : p ↔ q) : p = q := propext h

noncomputable def takeChoice {α : Type} (h : Nonempty α) : α := Classical.choice h

theorem quotientEquality {α : Type} {r : α → α → Prop} {x y : α} (h : r x y) :
    Quot.mk r x = Quot.mk r y := Quot.sound h

end SHIGURE.KernelAuditTest.Allowed.Nested

#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Allowed

-- This declaration is the deliberate negative-test assumption.
axiom SHIGURE.KernelAuditTest.nonstandard : False

namespace SHIGURE.KernelAuditTest.Rejected

theorem derived : False := nonstandard

end SHIGURE.KernelAuditTest.Rejected

/--
error: Declaration 'SHIGURE.KernelAuditTest.Rejected.derived' depends on nonstandard kernel assumptions: [SHIGURE.KernelAuditTest.nonstandard]
-/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Rejected

namespace SHIGURE.KernelAuditTest.Private

private theorem derived : False := nonstandard

end SHIGURE.KernelAuditTest.Private

/--
error: Declaration 'SHIGURE.KernelAuditTest.Private.derived' depends on nonstandard kernel assumptions: [SHIGURE.KernelAuditTest.nonstandard]
-/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Private

/-- error: No declarations in namespace 'SHIGURE.KernelAuditTest.Empty' in the current module -/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Empty
