import Formal.Util.AssertStandardAxioms
import Mathlib.CategoryTheory.Idempotents.Karoubi

namespace CompletionExternalFixture

theorem repoRuntimeCanary : AAT.Util.standardAxioms.length = 3 := rfl

theorem externalRuntimeCanary {C : Type} [CategoryTheory.Category C]
    (X : CategoryTheory.Idempotents.Karoubi C) : X.p ≫ X.p = X.p := X.idem

end CompletionExternalFixture
