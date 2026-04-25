import Formal.Arch.Graph

namespace Formal.Arch

universe u

/--
Initial architecture signature.

Every field is normalized as a risk axis: larger values mean greater structural
risk on that axis. `hasCycle` is a 0/1 risk indicator.

Future refinements may replace `sccMaxSize` with `sccExcessSize = sccMaxSize - 1`
and may split `fanoutRisk` into more refined propagation metrics.
-/
structure ArchitectureSignature where
  hasCycle : Nat
  sccMaxSize : Nat
  maxDepth : Nat
  fanoutRisk : Nat
  boundaryViolationCount : Nat
  abstractionViolationCount : Nat
  deriving DecidableEq, Repr

namespace ArchitectureSignature

/-- Componentwise risk order for architecture signatures. -/
def RiskLE (a b : ArchitectureSignature) : Prop :=
  a.hasCycle ≤ b.hasCycle ∧
  a.sccMaxSize ≤ b.sccMaxSize ∧
  a.maxDepth ≤ b.maxDepth ∧
  a.fanoutRisk ≤ b.fanoutRisk ∧
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

/--
Measured dependency edges with a fixed source component.

The target side is measured over the supplied finite component list, matching
`fanout G components c`.
-/
def measuredDependencyEdgesFromSource {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) (c : C) : List (C × C) :=
  (components.filter (fun d => decide (G.edge c d))).map (fun d => (c, d))

/--
Membership in `measuredDependencyEdgesFromSource` is exactly being a measured
edge with the selected source.
-/
theorem mem_measuredDependencyEdgesFromSource_iff {C : Type u}
    {G : ArchGraph C} [DecidableRel G.edge] {components : List C}
    {source : C} {edge : C × C} :
    edge ∈ measuredDependencyEdgesFromSource G components source ↔
      edge.1 = source ∧ edge.2 ∈ components ∧ G.edge source edge.2 := by
  rcases edge with ⟨c, d⟩
  constructor
  · intro h
    simp [measuredDependencyEdgesFromSource] at h
    rcases h with ⟨⟨hMem, hEdge⟩, hEq⟩
    exact ⟨hEq.symm, hMem, hEdge⟩
  · intro h
    rcases h with ⟨hEq, hMem, hEdge⟩
    simp [measuredDependencyEdgesFromSource]
    exact ⟨⟨hMem, hEdge⟩, hEq.symm⟩

/--
The per-source fanout count is exactly the number of measured dependency edges
with that source.
-/
theorem fanout_eq_measuredDependencyEdgesFromSource_length {C : Type u}
    (G : ArchGraph C) [DecidableRel G.edge] (components : List C) (c : C) :
    fanout G components c =
      (measuredDependencyEdgesFromSource G components c).length := by
  simp [fanout, measuredDependencyEdgesFromSource, countWhere]

/-- Total outgoing dependency count over the supplied finite universe. -/
def totalFanout {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat :=
  (components.map (fun c => fanout G components c)).sum

/--
Measured dependency edges over the supplied finite component list.

The list is measurement-universe based: duplicates in `components` intentionally
produce duplicate measured pairs, matching the executable v0 metrics.
-/
def measuredDependencyEdges {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : List (C × C) :=
  components.flatMap (fun c => measuredDependencyEdgesFromSource G components c)

/--
Membership in `measuredDependencyEdges` is exactly being an edge whose source
and target are both in the supplied measurement list.
-/
theorem mem_measuredDependencyEdges_iff {C : Type u} {G : ArchGraph C}
    [DecidableRel G.edge] {components : List C} {edge : C × C} :
    edge ∈ measuredDependencyEdges G components ↔
      edge.1 ∈ components ∧ edge.2 ∈ components ∧ G.edge edge.1 edge.2 := by
  rcases edge with ⟨c, d⟩
  constructor
  · intro h
    simp [measuredDependencyEdges,
      mem_measuredDependencyEdgesFromSource_iff] at h
    rcases h with ⟨source, hSourceMem, hEq, hTargetMem, hEdge⟩
    subst c
    exact ⟨hSourceMem, hTargetMem, hEdge⟩
  · intro h
    rcases h with ⟨hSourceMem, hTargetMem, hEdge⟩
    simp [measuredDependencyEdges, mem_measuredDependencyEdgesFromSource_iff]
    exact ⟨c, hSourceMem, rfl, hTargetMem, hEdge⟩

/--
The total fanout metric is exactly the number of measured dependency edges.
-/
theorem totalFanout_eq_measuredDependencyEdges_length {C : Type u}
    (G : ArchGraph C) [DecidableRel G.edge] (components : List C) :
    totalFanout G components = (measuredDependencyEdges G components).length := by
  simp [totalFanout, measuredDependencyEdges,
    fanout_eq_measuredDependencyEdgesFromSource_length]

/--
Fanout risk for Signature v0.

The v0 signature uses total outgoing dependency count rather than Nat-valued
average fanout, so sparse graphs with at least one measured dependency do not
round down to zero risk. A future signature can add `maxFanout` as a separate
shape axis without changing this total propagation-load axis.
-/
def fanoutRiskOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat :=
  totalFanout G components

/--
Signature v1 core SCC excess metric.

This normalizes the v0 maximum SCC size so singleton SCCs contribute zero risk.
It remains a derived finite-universe metric; graph-level SCC facts are proved as
separate bridge theorems.
-/
def sccExcessSizeOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) : Nat :=
  sccMaxSizeOfFinite G components - 1

/--
SCC excess around one component.

Singleton SCCs contribute zero risk by Nat subtraction. This is the local
building block for weighted SCC risk.
-/
def sccExcessAt {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) (c : C) : Nat :=
  sccSizeAt G components c - 1

/--
Weighted SCC risk contribution of one component.

The weight is supplied by the caller. Lean only treats it as a natural-number
importance factor; evidence used to extract that weight belongs to empirical
tooling rather than this graph-level metric.
-/
def weightedSccContributionAt {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) (weight : C → Nat) (c : C) : Nat :=
  weight c * sccExcessAt G components c

/--
Signature v1 weighted SCC risk over a finite measurement universe.

The counting rule sums each measured component's weight multiplied by its local
SCC excess. Non-cyclic singleton SCCs therefore contribute zero risk, while
larger mutually reachable classes can be emphasized by caller-supplied weights.
Duplicates in `components` are counted as repeated measurements, matching the
rest of the finite executable metrics.
-/
def weightedSccRiskOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) (weight : C → Nat) : Nat :=
  (components.map (fun c => weightedSccContributionAt G components weight c)).sum

/-- Zero weights make weighted SCC risk zero for any measured graph. -/
theorem weightedSccRiskOfFinite_zero_weight {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge] (components : List C) :
    weightedSccRiskOfFinite G components (fun _ => 0) = 0 := by
  have h : ∀ xs : List C, (xs.map (fun _ => 0)).sum = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ xs ih => simp [ih]
  simpa [weightedSccRiskOfFinite, weightedSccContributionAt] using h components

/--
With unit weights, weighted SCC risk is the sum of local SCC excess values.
-/
theorem weightedSccRiskOfFinite_unit_weight {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge] (components : List C) :
    weightedSccRiskOfFinite G components (fun _ => 1) =
      (components.map (fun c => sccExcessAt G components c)).sum := by
  simp [weightedSccRiskOfFinite, weightedSccContributionAt]

/--
Signature v1 core local fanout concentration metric.

Unlike v0 `fanoutRiskOfFinite`, this records the largest per-component outgoing
dependency count rather than the total dependency load.
-/
def maxFanoutOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableRel G.edge] (components : List C) : Nat :=
  maxNatList (components.map (fun c => fanout G components c))

/--
The v1 core max-fanout metric is the maximum number of measured dependency
edges with a common source component.
-/
theorem maxFanoutOfFinite_eq_max_measuredDependencyEdgesFromSource_length
    {C : Type u} (G : ArchGraph C) [DecidableRel G.edge] (components : List C) :
    maxFanoutOfFinite G components =
      maxNatList
        (components.map (fun c =>
          (measuredDependencyEdgesFromSource G components c).length)) := by
  simp [maxFanoutOfFinite, fanout_eq_measuredDependencyEdgesFromSource_length]

/--
Strict bounded reachable cone size from one component.

The source component itself is excluded so an isolated component has propagation
cone size zero. The direction follows the graph convention used by the existing
bounded depth metric: `edge c d` means `c` depends on `d`.
-/
def reachableConeSizeAt {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) (c : C) : Nat :=
  countWhere components (fun d =>
    decide (c ≠ d) && reachesWithin G components components.length c d)

/--
Signature v1 core reachable-cone metric.

This is the maximum strict bounded reachable cone size over the supplied finite
measurement universe.
-/
def reachableConeSizeOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) : Nat :=
  maxNatList (components.map (fun c => reachableConeSizeAt G components c))

/--
The v0 fanout risk is exactly the number of measured dependency edges.
-/
theorem fanoutRiskOfFinite_eq_measuredDependencyEdges_length {C : Type u}
    (G : ArchGraph C) [DecidableRel G.edge] (components : List C) :
    fanoutRiskOfFinite G components =
      (measuredDependencyEdges G components).length := by
  simp [fanoutRiskOfFinite, totalFanout_eq_measuredDependencyEdges_length]

/--
Legacy coarse Nat-valued average fanout.

For an empty component universe, Lean's natural-number division gives `0`.
Because this is integer division, sparse graphs can also round down to `0`.
It is kept as a derived executable metric, but Signature v0 uses
`fanoutRiskOfFinite`.
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

/--
Maximum bounded dependency-chain depth over the supplied finite universe.

On cyclic graphs this is a fuel-bounded measurement, not a true global depth.
Cycle risk is represented separately by `hasCycle`.
-/
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
  fanoutRisk := fanoutRiskOfFinite G components
  boundaryViolationCount := boundaryViolationCountOfFinite G components boundaryAllowed
  abstractionViolationCount := abstractionViolationCountOfFinite G components abstractionAllowed

/--
Lean-side Signature v1 core schema.

The v0 signature remains embedded as the stable compatibility layer. The extra
fields are finite-universe derived metrics whose graph-level bridge theorems
are developed separately.
-/
structure ArchitectureSignatureV1Core where
  v0 : ArchitectureSignature
  sccExcessSize : Nat
  maxFanout : Nat
  reachableConeSize : Nat
  deriving DecidableEq, Repr

/--
Full Signature v1 output schema.

The optional fields represent axes that may be unavailable for a given
extractor output or are still future bridge work. `none` means not measured; it
must not be read as risk zero.
-/
structure ArchitectureSignatureV1 where
  core : ArchitectureSignatureV1Core
  weightedSccRisk : Option Nat
  projectionSoundnessViolation : Option Nat
  lspViolationCount : Option Nat
  nilpotencyIndex : Option Nat
  runtimePropagation : Option Nat
  relationComplexity : Option Nat
  empiricalChangeCost : Option Nat
  deriving DecidableEq, Repr

/--
Build the Lean-measured Signature v1 core from a finite component universe.

This keeps `ArchitectureSignature` v0 intact and adds the currently executable
v1 core axes as derived metrics.
-/
def v1CoreOfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1Core where
  v0 := v0OfFinite G components boundaryAllowed abstractionAllowed
  sccExcessSize := sccExcessSizeOfFinite G components
  maxFanout := maxFanoutOfFinite G components
  reachableConeSize := reachableConeSizeOfFinite G components

/--
Build a Signature v1 value with only the Lean-measured core axes populated.

Future, policy-dependent, and empirical axes are left as `none` so that missing
measurements stay distinct from zero risk.
-/
def v1OfFinite {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1 where
  core := v1CoreOfFinite G components boundaryAllowed abstractionAllowed
  weightedSccRisk := none
  projectionSoundnessViolation := none
  lspViolationCount := none
  nilpotencyIndex := none
  runtimePropagation := none
  relationComplexity := none
  empiricalChangeCost := none

/--
Build a Signature v1 value with the Lean executable weighted SCC axis populated.

The caller supplies component weights explicitly. This keeps weight extraction
or calibration outside the Lean graph core while still making the counting rule
executable.
-/
def v1OfFiniteWithWeightedSccRisk {C : Type u} (G : ArchGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed]
    (weight : C → Nat) :
    ArchitectureSignatureV1 where
  core := v1CoreOfFinite G components boundaryAllowed abstractionAllowed
  weightedSccRisk := some (weightedSccRiskOfFinite G components weight)
  projectionSoundnessViolation := none
  lspViolationCount := none
  nilpotencyIndex := none
  runtimePropagation := none
  relationComplexity := none
  empiricalChangeCost := none

/--
Runtime propagation radius over a finite runtime dependency graph.

This reuses the existing strict reachable-cone metric on the runtime graph role.
Runtime edge metadata and circuit-breaker policy remain outside this Lean
counting rule.
-/
def runtimePropagationOfFinite {C : Type u} (G : RuntimeDependencyGraph C)
    [DecidableEq C] [DecidableRel G.edge]
    (components : List C) : Nat :=
  reachableConeSizeOfFinite G components

/--
Build a Signature v1 value and populate the runtime propagation extension axis.

The core axes are still computed from the static dependency graph. The runtime
axis is computed from a separate 0/1 runtime dependency graph, keeping runtime
coupling distinct from static structural constraints.
-/
def v1OfFiniteWithRuntimePropagation {C : Type u}
    (static : StaticDependencyGraph C)
    (runtime : RuntimeDependencyGraph C)
    [DecidableEq C]
    [DecidableRel static.edge] [DecidableRel runtime.edge]
    (components : List C)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1 where
  core := v1CoreOfFinite static components boundaryAllowed abstractionAllowed
  weightedSccRisk := none
  projectionSoundnessViolation := none
  lspViolationCount := none
  nilpotencyIndex := none
  runtimePropagation := some (runtimePropagationOfFinite runtime components)
  relationComplexity := none
  empiricalChangeCost := none

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
        fanoutRisk := 0
        boundaryViolationCount := 0
        abstractionViolationCount := 0 } := by
  rfl

/-- A self dependency is detected as a 0/1 cycle risk. -/
theorem v0_unitSelfLoop :
    v0OfFinite unitSelfLoopGraph [()] (fun _ _ => True) (fun _ _ => True) =
      { hasCycle := 1
        sccMaxSize := 1
        maxDepth := 1
        fanoutRisk := 1
        boundaryViolationCount := 0
        abstractionViolationCount := 0 } := by
  rfl

/-- Two-component graph with one dependency edge. -/
def boolForwardGraph : ArchGraph Bool where
  edge c d := c = false ∧ d = true

instance : DecidableRel boolForwardGraph.edge := by
  intro c d
  change Decidable (c = false ∧ d = true)
  infer_instance

/-- Two-component graph whose components are mutually reachable. -/
def boolCycleGraph : ArchGraph Bool where
  edge c d := c ≠ d

instance : DecidableRel boolCycleGraph.edge := by
  intro c d
  change Decidable (c ≠ d)
  infer_instance

/-- A single measured dependency contributes one unit of fanout risk. -/
theorem v0_boolForward :
    v0OfFinite boolForwardGraph [false, true] (fun _ _ => True) (fun _ _ => True) =
      { hasCycle := 0
        sccMaxSize := 1
        maxDepth := 1
        fanoutRisk := 1
        boundaryViolationCount := 0
        abstractionViolationCount := 0 } := by
  native_decide

/-- A no-edge singleton has zero v1 core excess, fanout concentration, and cone risk. -/
theorem v1Core_unitNoEdge :
    sccExcessSizeOfFinite unitNoEdgeGraph [()] = 0 ∧
      maxFanoutOfFinite unitNoEdgeGraph [()] = 0 ∧
      reachableConeSizeOfFinite unitNoEdgeGraph [()] = 0 := by
  native_decide

/-- The v1 core schema embeds the existing v0 signature and the derived core axes. -/
theorem v1CoreSchema_unitNoEdge :
    v1CoreOfFinite unitNoEdgeGraph [()] (fun _ _ => True) (fun _ _ => True) =
      { v0 :=
          { hasCycle := 0
            sccMaxSize := 1
            maxDepth := 0
            fanoutRisk := 0
            boundaryViolationCount := 0
            abstractionViolationCount := 0 }
        sccExcessSize := 0
        maxFanout := 0
        reachableConeSize := 0 } := by
  rfl

/-- Unmeasured v1 extension axes remain absent rather than being encoded as zero. -/
theorem v1Schema_unitNoEdge_unmeasured :
    (v1OfFinite unitNoEdgeGraph [()] (fun _ _ => True) (fun _ _ => True)).nilpotencyIndex =
      none ∧
    (v1OfFinite unitNoEdgeGraph [()] (fun _ _ => True) (fun _ _ => True)).runtimePropagation =
      none := by
  exact ⟨rfl, rfl⟩

/-- A one-way dependency has one unit of max fanout and reachable-cone risk. -/
theorem v1Core_boolForward :
    sccExcessSizeOfFinite boolForwardGraph [false, true] = 0 ∧
      maxFanoutOfFinite boolForwardGraph [false, true] = 1 ∧
      reachableConeSizeOfFinite boolForwardGraph [false, true] = 1 := by
  native_decide

/-- Acyclic singleton SCCs contribute zero weighted SCC risk. -/
theorem weightedSccRisk_boolForward :
    weightedSccRiskOfFinite boolForwardGraph [false, true]
      (fun c => if c then 3 else 2) = 0 := by
  native_decide

/--
In a two-component cycle, each component contributes its supplied weight once.
-/
theorem weightedSccRisk_boolCycle :
    weightedSccRiskOfFinite boolCycleGraph [false, true]
      (fun c => if c then 3 else 2) = 5 := by
  native_decide

/-- The weighted SCC entry point populates only the weighted SCC extension axis. -/
theorem v1Schema_boolCycle_weightedScc :
    (v1OfFiniteWithWeightedSccRisk boolCycleGraph [false, true]
      (fun _ _ => True) (fun _ _ => True)
      (fun c => if c then 3 else 2)).weightedSccRisk =
      some 5 := by
  native_decide

/-- The runtime propagation entry point populates only the runtime axis. -/
theorem v1Schema_boolForward_runtimePropagation :
    (v1OfFiniteWithRuntimePropagation boolForwardGraph boolForwardGraph
      [false, true] (fun _ _ => True) (fun _ _ => True)).runtimePropagation =
      some 1 := by
  native_decide

end Examples

end ArchitectureSignature

end Formal.Arch
