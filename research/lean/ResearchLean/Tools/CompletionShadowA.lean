import ResearchLean.Tools.CompletionShadowB

/-! First same-namespace artifact for completion extraction isolation tests. -/

namespace CompletionShadow
/-- First shadow value, with a transitive repository-local predecessor. -/
def a : Nat := b + 1
end CompletionShadow
