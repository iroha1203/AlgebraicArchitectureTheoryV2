import Formal.SHIGURE.AssertStandardAxioms

/-! # Positive and negative cases for the kernel audit command -/

/-- error: No declarations in namespace 'SHIGURE' in the current module -/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE

namespace SHIGURE.KernelAuditTest.Allowed.Nested

/-- A declaration with no assumptions. -/
theorem trivially_true : True := True.intro

/-- A direct use of propositional extensionality. -/
theorem prop_eq_of_iff (p q : Prop) (h : p ↔ q) : p = q := propext h

/-- A direct use of classical choice. -/
noncomputable def takeChoice {α : Type} (h : Nonempty α) : α := Classical.choice h

/-- A direct use of quotient soundness. -/
theorem quot_eq_of_rel {α : Type} {r : α → α → Prop} {x y : α} (h : r x y) :
    Quot.mk r x = Quot.mk r y := Quot.sound h

end SHIGURE.KernelAuditTest.Allowed.Nested

#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Allowed
#shigure_assert_standard_axioms_of [
  SHIGURE.KernelAuditTest.Allowed.Nested.prop_eq_of_iff,
  SHIGURE.KernelAuditTest.Allowed.Nested.takeChoice,
  SHIGURE.KernelAuditTest.Allowed.Nested.quot_eq_of_rel
]

/-- The deliberately nonstandard assumption used by the rejection fixtures. -/
private axiom SHIGURE.KernelAuditTest.nonstandard : False

namespace SHIGURE.KernelAuditTest.Rejected

/-- The audited declaration inherits the forbidden assumption. -/
private theorem derived : False := nonstandard

end SHIGURE.KernelAuditTest.Rejected

/--
error: Declaration 'SHIGURE.KernelAuditTest.Rejected.derived' depends on nonstandard kernel assumptions: [SHIGURE.KernelAuditTest.nonstandard]
-/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Rejected

/--
error: Declaration 'SHIGURE.KernelAuditTest.Rejected.derived' depends on nonstandard kernel assumptions: [SHIGURE.KernelAuditTest.nonstandard]
-/
#guard_msgs in
#shigure_assert_standard_axioms_of [SHIGURE.KernelAuditTest.Rejected.derived]

/-- A declaration whose name coincides with the requested empty namespace. -/
theorem SHIGURE.KernelAuditTest.Empty : True := True.intro

/-- error: No declarations in namespace 'SHIGURE.KernelAuditTest.Empty' in the current module -/
#guard_msgs in
#shigure_assert_standard_axioms_only SHIGURE.KernelAuditTest.Empty
