import Lean

namespace CompletionFixture

def positive (n : Nat) : Prop := n = 0
theorem identityMember : positive 0 := rfl
theorem negativeMember : ¬ positive 1 := by
  intro h
  cases h
theorem differenceCriterion (n : Nat) (h : positive n) : n = 0 := h
theorem kernelInputCriterion (n : Nat) (h : n = 0) : positive n := h
theorem inputCharacterization (n : Nat) : positive n ↔ n = 0 :=
  ⟨differenceCriterion n, kernelInputCriterion n⟩
private theorem helper (n : Nat) (h : positive n) : n = 0 := differenceCriterion n h
theorem throughHelper (n : Nat) (h : positive n) : n = 0 := helper n h
theorem bySimp (n : Nat) (h : positive n) : n + 0 = 0 := by
  simpa using differenceCriterion n h
def typedOnly (_h : positive 0) : Nat := 0
def projected (p : Nat × Nat) : Nat := p.1

end CompletionFixture
