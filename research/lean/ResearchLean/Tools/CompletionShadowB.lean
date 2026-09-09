import ResearchLean.Tools.CompletionFixture

/-! Second same-namespace artifact for completion extraction isolation tests. -/

namespace CompletionShadow
/-- Second shadow value, routed through a separate repository module. -/
def b : Nat := CompletionFixture.universeIdentity 2
end CompletionShadow
