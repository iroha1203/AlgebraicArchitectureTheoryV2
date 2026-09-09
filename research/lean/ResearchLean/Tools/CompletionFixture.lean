import Lean

/-! Small declarations used only by the target-completion packet integration test. -/

namespace CompletionFixture

/-- Recognize zero in the integration fixture. -/
def positive (n : Nat) : Prop := n = 0
/-- Zero satisfies the fixture predicate. -/
theorem identityMember : positive 0 := rfl
/-- One does not satisfy the fixture predicate. -/
theorem negativeMember : ¬ positive 1 := by
  intro h
  cases h
/-- Extract equality from the fixture predicate. -/
theorem differenceCriterion (n : Nat) (h : positive n) : n = 0 := h
/-- Reconstruct the fixture predicate from equality. -/
theorem kernelInputCriterion (n : Nat) (h : n = 0) : positive n := h
/-- Characterize the fixture predicate in both directions. -/
theorem inputCharacterization (n : Nat) : positive n ↔ n = 0 :=
  ⟨differenceCriterion n, kernelInputCriterion n⟩
/-- Private intermediate used to test indirect dependency extraction. -/
private theorem helper (n : Nat) (h : positive n) : n = 0 := differenceCriterion n h
/-- Exercise a proof dependency through a private helper. -/
theorem throughHelper (n : Nat) (h : positive n) : n = 0 := helper n h
/-- Exercise a dependency retained through simplification. -/
theorem bySimp (n : Nat) (h : positive n) : n + 0 = 0 := by
  simpa using differenceCriterion n h
/-- Exercise a type-only dependency. -/
def typedOnly (_h : positive 0) : Nat := 0
/-- Exercise projection metadata. -/
def projected (p : Nat × Nat) : Nat := p.1
/-- Exercise universe-parameter extraction. -/
def universeIdentity.{u} {α : Sort u} (a : α) : α := a

end CompletionFixture
