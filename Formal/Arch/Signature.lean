namespace Formal.Arch

/--
Initial architecture signature.

Every field is normalized as a risk axis: larger values mean greater structural
risk on that axis. `hasCycle` is a 0/1 risk indicator.

Future refinements may replace `sccMaxSize` with `sccExcessSize = sccMaxSize - 1`
and `averageFanout` with `fanoutRisk` or `maxFanout`.
-/
structure ArchitectureSignature where
  hasCycle : Nat
  sccMaxSize : Nat
  maxDepth : Nat
  averageFanout : Nat
  boundaryViolationCount : Nat
  abstractionViolationCount : Nat
  deriving DecidableEq, Repr

namespace ArchitectureSignature

/-- Componentwise risk order for architecture signatures. -/
def RiskLE (a b : ArchitectureSignature) : Prop :=
  a.hasCycle ≤ b.hasCycle ∧
  a.sccMaxSize ≤ b.sccMaxSize ∧
  a.maxDepth ≤ b.maxDepth ∧
  a.averageFanout ≤ b.averageFanout ∧
  a.boundaryViolationCount ≤ b.boundaryViolationCount ∧
  a.abstractionViolationCount ≤ b.abstractionViolationCount

instance : LE ArchitectureSignature where
  le := RiskLE

/-- Risk order is reflexive. -/
theorem riskLE_refl (a : ArchitectureSignature) : a ≤ a := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _⟩

/-- Risk order is transitive. -/
theorem riskLE_trans {a b c : ArchitectureSignature}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with ⟨h1, h2, h3, h4, h5, h6⟩
  rcases hbc with ⟨k1, k2, k3, k4, k5, k6⟩
  exact ⟨Nat.le_trans h1 k1, Nat.le_trans h2 k2, Nat.le_trans h3 k3,
    Nat.le_trans h4 k4, Nat.le_trans h5 k5, Nat.le_trans h6 k6⟩

end ArchitectureSignature

end Formal.Arch
