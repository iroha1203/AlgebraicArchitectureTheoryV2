import Formal.Arch.Graph

namespace Formal.Arch

universe u

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

/-- Risk order is antisymmetric. -/
theorem riskLE_antisymm {a b : ArchitectureSignature}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases a with ⟨a1, a2, a3, a4, a5, a6⟩
  rcases b with ⟨b1, b2, b3, b4, b5, b6⟩
  rcases hab with ⟨h1, h2, h3, h4, h5, h6⟩
  rcases hba with ⟨k1, k2, k3, k4, k5, k6⟩
  have e1 : a1 = b1 := Nat.le_antisymm h1 k1
  have e2 : a2 = b2 := Nat.le_antisymm h2 k2
  have e3 : a3 = b3 := Nat.le_antisymm h3 k3
  have e4 : a4 = b4 := Nat.le_antisymm h4 k4
  have e5 : a5 = b5 := Nat.le_antisymm h5 k5
  have e6 : a6 = b6 := Nat.le_antisymm h6 k6
  cases e1
  cases e2
  cases e3
  cases e4
  cases e5
  cases e6
  rfl

/-- Convert a Boolean predicate into the 0/1 risk convention. -/
def boolRisk (b : Bool) : Nat :=
  if b then 1 else 0

/-- Maximum of a finite list of natural-number measurements. -/
def maxNatList (xs : List Nat) : Nat :=
  xs.foldl Nat.max 0

/-- Count entries satisfying a Boolean predicate. -/
def countWhere {α : Type u} (xs : List α) (p : α → Bool) : Nat :=
  (xs.filter p).length

/--
All ordered component pairs from a finite component universe.

The list is intentionally allowed to contain duplicates when `components`
contains duplicates; v0 metrics treat the supplied list as the measurement
universe.
-/
def componentPairs {C : Type u} (components : List C) : List (C × C) :=
  components.flatMap (fun c => components.map (fun d => (c, d)))

/-- Bounded reachability search over a supplied finite component universe. -/
def reachesWithin {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) : Nat → C → C → Bool
  | 0, c, d => decide (c = d)
  | fuel + 1, c, d =>
      decide (c = d) ||
        components.any (fun next =>
          decide (G.edge c next) && reachesWithin G components fuel next d)

/--
Cycle indicator over a finite component universe.

A cycle is detected as an edge followed by bounded reachability back to the
source.
-/
def hasCycleBool {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) : Bool :=
  components.any (fun c =>
    components.any (fun d =>
      decide (G.edge c d) && reachesWithin G components components.length d c))

/-- Number of supplied components mutually reachable with `c`, using bounded search. -/
def sccSizeAt {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) (c : C) : Nat :=
  countWhere components (fun d =>
    reachesWithin G components components.length c d &&
      reachesWithin G components components.length d c)

/-- Maximum bounded SCC size over the supplied component universe. -/
def sccMaxSizeOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) : Nat :=
  maxNatList (components.map (fun c => sccSizeAt G components c))

/-- Outgoing dependency count for one component within the supplied universe. -/
def fanout {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) (c : C) : Nat :=
  countWhere components (fun d => decide (G.edge c d))

/-- Total outgoing dependency count over the supplied finite universe. -/
def totalFanout {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat :=
  (components.map (fun c => fanout G components c)).sum

/--
Coarse Nat-valued average fanout used by the initial signature.

For an empty component universe, Lean's natural-number division gives `0`.
-/
def averageFanoutOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat :=
  totalFanout G components / components.length

/-- Bounded longest dependency-chain depth from one component. -/
def boundedDepthFrom {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat → C → Nat
  | 0, _ => 0
  | fuel + 1, c =>
      maxNatList (components.map (fun d =>
        if decide (G.edge c d) then boundedDepthFrom G components fuel d + 1 else 0))

/-- Maximum bounded dependency-chain depth over the supplied finite universe. -/
def maxDepthOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat :=
  maxNatList (components.map (fun c => boundedDepthFrom G components components.length c))

/-- Count dependency edges that violate a supplied boundary policy. -/
def boundaryViolationCountOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge]
    (components : List C) (boundaryAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] : Nat :=
  countWhere (componentPairs components) (fun pair =>
    decide (G.edge pair.1 pair.2) && ! decide (boundaryAllowed pair.1 pair.2))

/-- Count dependency edges that violate a supplied abstraction policy. -/
def abstractionViolationCountOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge]
    (components : List C) (abstractionAllowed : C → C → Prop)
    [DecidableRel abstractionAllowed] : Nat :=
  countWhere (componentPairs components) (fun pair =>
    decide (G.edge pair.1 pair.2) && ! decide (abstractionAllowed pair.1 pair.2))

/--
Build the initial v0 signature from a finite component universe and two local
edge policies.

This is an executable metric definition, not yet a proof that the supplied list
is duplicate-free or contains every semantic component of a larger codebase.
-/
def v0OfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignature where
  hasCycle := boolRisk (hasCycleBool G components)
  sccMaxSize := sccMaxSizeOfFinite G components
  maxDepth := maxDepthOfFinite G components
  averageFanout := averageFanoutOfFinite G components
  boundaryViolationCount := boundaryViolationCountOfFinite G components boundaryAllowed
  abstractionViolationCount := abstractionViolationCountOfFinite G components abstractionAllowed

namespace Examples

/-- One-component graph with no dependency edges. -/
def unitNoEdgeGraph : ArchGraph Unit where
  edge _ _ := False

/-- One-component graph with a self dependency. -/
def unitSelfLoopGraph : ArchGraph Unit where
  edge _ _ := True

instance : DecidableRel unitNoEdgeGraph.edge := by
  intro c d
  exact isFalse (by intro h; exact h)

instance : DecidableRel unitSelfLoopGraph.edge := by
  intro c d
  exact isTrue trivial

/-- The no-edge graph has no cycle and zero fanout/depth risk. -/
theorem v0_unitNoEdge :
    v0OfFinite unitNoEdgeGraph [()] (fun _ _ => True) (fun _ _ => True) =
      { hasCycle := 0
        sccMaxSize := 1
        maxDepth := 0
        averageFanout := 0
        boundaryViolationCount := 0
        abstractionViolationCount := 0 } := by
  rfl

/-- A self dependency is detected as a 0/1 cycle risk. -/
theorem v0_unitSelfLoop :
    v0OfFinite unitSelfLoopGraph [()] (fun _ _ => True) (fun _ _ => True) =
      { hasCycle := 1
        sccMaxSize := 1
        maxDepth := 1
        averageFanout := 1
        boundaryViolationCount := 0
        abstractionViolationCount := 0 } := by
  rfl

end Examples

end ArchitectureSignature

end Formal.Arch
