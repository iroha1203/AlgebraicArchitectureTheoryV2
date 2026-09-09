import Formal.Util.AssertStandardAxioms
import Mathlib.CategoryTheory.Idempotents.Karoubi

namespace CompletionExternalFixture

open CategoryTheory

theorem repoRuntimeCanary : AAT.Util.standardAxioms.length = 3 := rfl

theorem externalRuntimeCanary {C : Type} [Category C]
    (X : Idempotents.Karoubi C) : X.p ≫ X.p = X.p := X.idem

end CompletionExternalFixture
