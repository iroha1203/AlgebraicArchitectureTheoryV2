import Formal.Util.AssertStandardAxioms

/-!
Tests for `#assert_standard_axioms_only`.

This file is NOT imported by the `Formal` library: it declares a probe
`axiom` on purpose (to test the detection path) and must stay out of the
library environment. CI runs it directly:

```bash
lake env lean Formal/Util/AssertStandardAxiomsTest.lean
```
-/

namespace AAT.Util.Test.Clean

theorem oneAddOne : 1 + 1 = 2 := rfl

end AAT.Util.Test.Clean

/-- info: axiom audit: 1 declarations under AAT.Util.Test.Clean, standard axioms only -/
#guard_msgs in
#assert_standard_axioms_only AAT.Util.Test.Clean

namespace AAT.Util.Test.Offending

axiom auditProbeAxiom : True

theorem usesAuditProbeAxiom : True := auditProbeAxiom

end AAT.Util.Test.Offending

/--
error: AAT.Util.Test.Offending.auditProbeAxiom depends on non-standard axioms: [AAT.Util.Test.Offending.auditProbeAxiom]
---
error: AAT.Util.Test.Offending.usesAuditProbeAxiom depends on non-standard axioms: [AAT.Util.Test.Offending.auditProbeAxiom]
---
error: #assert_standard_axioms_only: 2 offending declaration(s)
-/
#guard_msgs in
#assert_standard_axioms_only AAT.Util.Test.Offending

/-- error: #assert_standard_axioms_only: no declarations found under AAT.Util.Test.Nothing -/
#guard_msgs in
#assert_standard_axioms_only AAT.Util.Test.Nothing
