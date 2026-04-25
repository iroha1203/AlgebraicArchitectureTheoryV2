import Formal.Arch.Finite

namespace Formal.Arch

universe u

/-- A finite-universe matrix with natural-number entries. -/
abbrev NatMatrix (C : Type u) := C → C → Nat

namespace NatMatrix

/-- Identity matrix over a component type. -/
def id {C : Type u} [DecidableEq C] : NatMatrix C :=
  fun c d => if c = d then 1 else 0

/--
Matrix multiplication where the finite summation range is provided by a
proof-carrying component universe.
-/
def mul {C : Type u} {G : ArchGraph C} (U : ComponentUniverse G)
    (A B : NatMatrix C) : NatMatrix C :=
  fun c d => (U.components.map (fun mid => A c mid * B mid d)).sum

/-- Matrix powers over the finite component universe. -/
def pow {C : Type u} {G : ArchGraph C} [DecidableEq C]
    (U : ComponentUniverse G) (A : NatMatrix C) : Nat → NatMatrix C
  | 0 => id
  | k + 1 => mul U A (pow U A k)

end NatMatrix

/-- The 0/1 adjacency matrix of an architecture graph. -/
def adjacencyMatrix {C : Type u} (G : ArchGraph C) [DecidableRel G.edge] :
    NatMatrix C :=
  fun c d => if G.edge c d then 1 else 0

/-- The `(c,d)` entry of `A^k` for the graph adjacency matrix. -/
def adjacencyPowerEntry {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (k : Nat) (c d : C) : Nat :=
  NatMatrix.pow U (adjacencyMatrix G) k c d

/--
Adjacency-matrix nilpotence as eventual zero of all sufficiently large powers.

This avoids adding nilpotence to `Decomposable`; it is a bridge property over a
finite measurement universe.
-/
def AdjacencyNilpotent {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G) : Prop :=
  ∃ cutoff : Nat, ∀ {k : Nat} {c d : C},
    cutoff ≤ k → adjacencyPowerEntry U k c d = 0

/--
Executable zero test for one adjacency power on the finite measurement universe.

This checks only the supplied `ComponentUniverse.components` list. Graph-level
statements use `ComponentUniverse.covers` to lift the result to all components.
-/
def adjacencyPowerZeroOnComponentsBool {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (k : Nat) : Bool :=
  U.components.all (fun c =>
    U.components.all (fun d => decide (adjacencyPowerEntry U k c d = 0)))

/--
The executable zero test is true exactly when every measured entry of `A^k`
is zero.
-/
theorem adjacencyPowerZeroOnComponentsBool_eq_true_iff {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (k : Nat) :
    adjacencyPowerZeroOnComponentsBool U k = true ↔
      ∀ {c : C}, c ∈ U.components →
        ∀ {d : C}, d ∈ U.components → adjacencyPowerEntry U k c d = 0 := by
  simp [adjacencyPowerZeroOnComponentsBool, List.all_eq_true]

/--
Because a `ComponentUniverse` covers the graph, the measured zero test is a
graph-level zero test for that adjacency power.
-/
theorem adjacencyPowerZeroOnComponentsBool_iff_zero {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (k : Nat) :
    adjacencyPowerZeroOnComponentsBool U k = true ↔
      ∀ c d : C, adjacencyPowerEntry U k c d = 0 := by
  constructor
  · intro h c d
    exact (adjacencyPowerZeroOnComponentsBool_eq_true_iff U k).mp h
      (U.covers c) (U.covers d)
  · intro h
    exact (adjacencyPowerZeroOnComponentsBool_eq_true_iff U k).mpr
      (fun {c} _ {d} _ => h c d)

/--
Find the first candidate power whose adjacency matrix is zero on the measured
component universe.
-/
def firstZeroPowerIndex {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) : List Nat → Option Nat
  | [] => none
  | k :: ks =>
      if adjacencyPowerZeroOnComponentsBool U k then
        some k
      else
        firstZeroPowerIndex U ks

private theorem firstZeroPowerIndex_isSome_of_mem {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) {candidates : List Nat} {k : Nat}
    (hMem : k ∈ candidates)
    (hZero : adjacencyPowerZeroOnComponentsBool U k = true) :
    ∃ found, firstZeroPowerIndex U candidates = some found := by
  induction candidates with
  | nil =>
      cases hMem
  | cons head tail ih =>
      by_cases hHead : adjacencyPowerZeroOnComponentsBool U head = true
      · exact ⟨head, by simp [firstZeroPowerIndex, hHead]⟩
      · simp [firstZeroPowerIndex, hHead]
        simp at hMem
        cases hMem with
        | inl hEq =>
            subst head
            contradiction
        | inr hTailMem =>
            exact ih hTailMem

/--
Bound used by the executable nilpotency-index search.

For an acyclic graph, `A^(components.length + 1)` is zero, so searching through
this bound is enough to find a witness. Cyclic graphs return `none` unless a
zero power is actually observed within the same finite universe.
-/
def nilpotencyIndexSearchBound {C : Type u} {G : ArchGraph C}
    (U : ComponentUniverse G) : Nat :=
  U.components.length + 2

/--
Executable nilpotency-index candidate for a finite component universe.

`some k` means `k` is the first searched power whose adjacency matrix is zero.
`none` means no zero power was found in the finite DAG-complete search window;
the v1 signature keeps this distinct from risk zero.
-/
def nilpotencyIndexOfFinite {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) : Option Nat :=
  firstZeroPowerIndex U (List.range (nilpotencyIndexSearchBound U))

namespace ArchitectureSignature

/--
Build a Signature v1 value and populate the matrix-bridge `nilpotencyIndex`
axis from a proof-carrying finite component universe.

The other extension axes remain `none`; they are projection, behavioral, runtime
or empirical metrics with separate extraction rules.
-/
def v1OfComponentUniverseWithNilpotencyIndex {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1 where
  core := v1CoreOfFinite G U.components boundaryAllowed abstractionAllowed
  weightedSccRisk := none
  projectionSoundnessViolation := none
  lspViolationCount := none
  nilpotencyIndex := nilpotencyIndexOfFinite U
  runtimePropagation := none
  relationComplexity := none
  empiricalChangeCost := none

end ArchitectureSignature

namespace Walk

/-- Concatenate two walks. -/
def append {C : Type u} {G : ArchGraph C} {a b c : C} :
    Walk G a b → Walk G b c → Walk G a c
  | nil _, tail => tail
  | cons hEdge rest, tail => cons hEdge (append rest tail)

/-- Length is additive under walk concatenation. -/
theorem length_append {C : Type u} {G : ArchGraph C}
    {a b c : C} (w1 : Walk G a b) (w2 : Walk G b c) :
    (append w1 w2).length = w1.length + w2.length := by
  induction w1 with
  | nil a =>
      simp [append, length]
  | cons hEdge rest ih =>
      simp [append, length, ih, Nat.add_assoc]
      omega

/-- Repeat a closed walk `n` times. -/
def repeatClosed {C : Type u} {G : ArchGraph C} {c : C} :
    Nat → Walk G c c → Walk G c c
  | 0, _ => nil c
  | n + 1, w => append w (repeatClosed n w)

/-- Repeating a closed walk multiplies its length. -/
theorem length_repeatClosed {C : Type u} {G : ArchGraph C}
    {c : C} (n : Nat) (w : Walk G c c) :
    (repeatClosed n w).length = n * w.length := by
  induction n with
  | zero =>
      simp [repeatClosed, length]
  | succ n ih =>
      rw [repeatClosed, length_append, ih, Nat.succ_mul]
      omega

end Walk

private theorem zero_lt_sum_iff_exists_pos :
    ∀ xs : List Nat, 0 < xs.sum ↔ ∃ n, n ∈ xs ∧ 0 < n
  | [] => by
      simp
  | x :: xs => by
      rw [List.sum_cons]
      constructor
      · intro h
        by_cases hx : 0 < x
        · exact ⟨x, by simp, hx⟩
        · have hxs : 0 < xs.sum := by omega
          rcases (zero_lt_sum_iff_exists_pos xs).mp hxs with ⟨n, hn, hpos⟩
          exact ⟨n, by simp [hn], hpos⟩
      · rintro ⟨n, hn, hpos⟩
        simp at hn
        cases hn with
        | inl hn =>
            subst n
            omega
        | inr hn =>
            have hxs : 0 < xs.sum :=
              (zero_lt_sum_iff_exists_pos xs).mpr ⟨n, hn, hpos⟩
            omega

private theorem zero_lt_sum_map_iff_exists_pos {C : Type u}
    (components : List C) (f : C → Nat) :
    0 < (components.map f).sum ↔ ∃ c, c ∈ components ∧ 0 < f c := by
  rw [zero_lt_sum_iff_exists_pos]
  constructor
  · rintro ⟨n, hn, hpos⟩
    rcases List.mem_map.mp hn with ⟨c, hc, rfl⟩
    exact ⟨c, hc, hpos⟩
  · rintro ⟨c, hc, hpos⟩
    exact ⟨f c, List.mem_map.mpr ⟨c, hc, rfl⟩, hpos⟩

/--
The graph adjacency entry is positive exactly when the corresponding edge
exists.
-/
theorem adjacencyMatrix_pos_iff {C : Type u} {G : ArchGraph C}
    [DecidableRel G.edge] {c d : C} :
    0 < adjacencyMatrix G c d ↔ G.edge c d := by
  by_cases hEdge : G.edge c d
  · simp [adjacencyMatrix, hEdge]
  · simp [adjacencyMatrix, hEdge]

/--
The `(c,d)` entry of `A^k` is positive exactly when there is a walk from `c`
to `d` with length `k`.
-/
theorem adjacencyPowerEntry_pos_iff_walk_length {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    ∀ {k : Nat} {c d : C},
      0 < adjacencyPowerEntry U k c d ↔
        ∃ w : Walk G c d, w.length = k := by
  intro k
  induction k with
  | zero =>
      intro c d
      constructor
      · intro hPos
        by_cases hEq : c = d
        · subst d
          exact ⟨Walk.nil c, rfl⟩
        · simp [adjacencyPowerEntry, NatMatrix.pow, NatMatrix.id, hEq] at hPos
      · rintro ⟨w, hLen⟩
        cases w with
        | nil c =>
            simp [adjacencyPowerEntry, NatMatrix.pow, NatMatrix.id]
        | cons hEdge rest =>
            simp [Walk.length] at hLen
  | succ k ih =>
      intro c d
      constructor
      · intro hPos
        have hExists :
            ∃ mid, mid ∈ U.components ∧
              0 <
                adjacencyMatrix G c mid *
                  adjacencyPowerEntry U k mid d := by
          simpa [adjacencyPowerEntry, NatMatrix.pow, NatMatrix.mul]
            using
              (zero_lt_sum_map_iff_exists_pos U.components
                (fun mid =>
                  adjacencyMatrix G c mid *
                    adjacencyPowerEntry U k mid d)).mp hPos
        rcases hExists with ⟨mid, _hMem, hTerm⟩
        have hEdgeAndRest :
            G.edge c mid ∧ 0 < adjacencyPowerEntry U k mid d := by
          by_cases hEdge : G.edge c mid
          · have hRestPos :
                0 < adjacencyPowerEntry U k mid d := by
              simpa [adjacencyMatrix, hEdge] using hTerm
            exact ⟨hEdge, hRestPos⟩
          · simp [adjacencyMatrix, hEdge] at hTerm
        rcases hEdgeAndRest with ⟨hEdge, hRestPos⟩
        rcases (ih (c := mid) (d := d)).mp hRestPos with ⟨rest, hRestLen⟩
        exact ⟨Walk.cons hEdge rest, by
          simp [Walk.length, hRestLen]⟩
      · rintro ⟨w, hLen⟩
        cases w with
        | nil c =>
            simp [Walk.length] at hLen
        | @cons c mid d hEdge rest =>
            have hRestLen : rest.length = k := by
              simpa [Walk.length, Nat.succ_eq_add_one] using hLen
            have hRestPos :
                0 < adjacencyPowerEntry U k mid d :=
              (ih (c := mid) (d := d)).mpr ⟨rest, hRestLen⟩
            have hTerm :
                0 <
                  adjacencyMatrix G c mid *
                    adjacencyPowerEntry U k mid d := by
              simpa [adjacencyMatrix, hEdge] using hRestPos
            have hMem : mid ∈ U.components := (U.edgeClosed hEdge).2
            have hSum :
                0 <
                  (U.components.map
                    (fun x =>
                      adjacencyMatrix G c x *
                        adjacencyPowerEntry U k x d)).sum :=
              (zero_lt_sum_map_iff_exists_pos U.components
                (fun x =>
                  adjacencyMatrix G c x *
                    adjacencyPowerEntry U k x d)).mpr
                ⟨mid, hMem, hTerm⟩
            simpa [adjacencyPowerEntry, NatMatrix.pow, NatMatrix.mul] using hSum

/--
Finite acyclicity forces sufficiently large adjacency powers to be zero.
-/
theorem adjacencyNilpotent_of_acyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    AdjacencyNilpotent U := by
  refine ⟨U.components.length + 1, ?_⟩
  intro k c d hCutoff
  by_cases hZero : adjacencyPowerEntry U k c d = 0
  · exact hZero
  · have hPos : 0 < adjacencyPowerEntry U k c d := Nat.pos_of_ne_zero hZero
    rcases (adjacencyPowerEntry_pos_iff_walk_length U).mp hPos with ⟨w, hLen⟩
    have hBound :
        w.length ≤ U.components.length :=
      ComponentUniverse.walk_length_le_components_length_of_acyclic U hAcyclic w
    omega

/-- At the finite acyclic cutoff, every adjacency-power entry is zero. -/
theorem adjacencyPowerEntry_zero_at_acyclic_cutoff {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    ∀ c d : C,
      adjacencyPowerEntry U (U.components.length + 1) c d = 0 := by
  intro c d
  by_cases hZero :
      adjacencyPowerEntry U (U.components.length + 1) c d = 0
  · exact hZero
  · have hPos :
        0 < adjacencyPowerEntry U (U.components.length + 1) c d :=
      Nat.pos_of_ne_zero hZero
    rcases (adjacencyPowerEntry_pos_iff_walk_length U).mp hPos with
      ⟨w, _hLen⟩
    have hBound :
        w.length ≤ U.components.length :=
      ComponentUniverse.walk_length_le_components_length_of_acyclic U hAcyclic w
    omega

/--
Finite acyclic graphs always populate the executable nilpotency-index axis.
-/
theorem nilpotencyIndexOfFinite_isSome_of_acyclic {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    ∃ k, nilpotencyIndexOfFinite U = some k := by
  let cutoff := U.components.length + 1
  have hZero :
      adjacencyPowerZeroOnComponentsBool U cutoff = true := by
    exact (adjacencyPowerZeroOnComponentsBool_iff_zero U cutoff).mpr
      (adjacencyPowerEntry_zero_at_acyclic_cutoff U hAcyclic)
  have hMem : cutoff ∈ List.range (nilpotencyIndexSearchBound U) := by
    simp [cutoff, nilpotencyIndexSearchBound]
  exact firstZeroPowerIndex_isSome_of_mem U hMem hZero

/--
If all sufficiently large adjacency powers are zero, then there is no nonempty
closed walk.
-/
theorem walkAcyclic_of_adjacencyNilpotent {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hNil : AdjacencyNilpotent U) :
    WalkAcyclic G := by
  intro hClosed
  rcases hNil with ⟨cutoff, hZero⟩
  rcases hClosed with ⟨c, w, hLen⟩
  let repeated : Walk G c c := Walk.repeatClosed (cutoff + 1) w
  have hRepeatedLen :
      repeated.length = (cutoff + 1) * w.length :=
    Walk.length_repeatClosed (cutoff + 1) w
  have hOne : 1 ≤ w.length := hLen
  have hCutoffLe : cutoff ≤ repeated.length := by
    have hLeMul : cutoff + 1 ≤ (cutoff + 1) * w.length := by
      simpa using Nat.mul_le_mul_left (cutoff + 1) hOne
    rw [hRepeatedLen]
    exact Nat.le_trans (Nat.le_succ cutoff) hLeMul
  have hEntryPos :
      0 < adjacencyPowerEntry U repeated.length c c :=
    (adjacencyPowerEntry_pos_iff_walk_length U).mpr ⟨repeated, rfl⟩
  have hEntryZero :
      adjacencyPowerEntry U repeated.length c c = 0 :=
    hZero hCutoffLe
  omega

/-- On a finite component universe, adjacency nilpotence implies acyclicity. -/
theorem acyclic_of_adjacencyNilpotent {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hNil : AdjacencyNilpotent U) :
    Acyclic G :=
  acyclic_of_walkAcyclic (walkAcyclic_of_adjacencyNilpotent U hNil)

/--
On a finite component universe, adjacency nilpotence is equivalent to
walk-level acyclicity.
-/
theorem adjacencyNilpotent_iff_walkAcyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    AdjacencyNilpotent U ↔ WalkAcyclic G :=
  ⟨walkAcyclic_of_adjacencyNilpotent U,
    fun hWalkAcyclic =>
      adjacencyNilpotent_of_acyclic U (acyclic_of_walkAcyclic hWalkAcyclic)⟩

/--
On a finite component universe, adjacency nilpotence is equivalent to the
graph-level acyclicity predicate.
-/
theorem adjacencyNilpotent_iff_acyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    AdjacencyNilpotent U ↔ Acyclic G :=
  ⟨acyclic_of_adjacencyNilpotent U, adjacencyNilpotent_of_acyclic U⟩

namespace ArchitectureSignature.Examples

/-- Full finite universe for the one-way Boolean dependency graph. -/
def boolForwardUniverse : ComponentUniverse boolForwardGraph :=
  ComponentUniverse.full boolForwardGraph [false, true] (by simp) (by
    intro c
    cases c <;> simp)

/-- Full finite universe for the two-component cycle graph. -/
def boolCycleUniverse : ComponentUniverse boolCycleGraph :=
  ComponentUniverse.full boolCycleGraph [false, true] (by simp) (by
    intro c
    cases c <;> simp)

/-- The one-way Boolean graph has nilpotency index 2. -/
theorem nilpotencyIndex_boolForward :
    nilpotencyIndexOfFinite boolForwardUniverse = some 2 := by
  native_decide

/-- The two-component cycle has no zero adjacency power in the finite search window. -/
theorem nilpotencyIndex_boolCycle :
    nilpotencyIndexOfFinite boolCycleUniverse = none := by
  native_decide

/-- The matrix-bridge v1 entry point populates the `nilpotencyIndex` axis. -/
theorem v1Schema_boolForward_nilpotencyIndex :
    (v1OfComponentUniverseWithNilpotencyIndex boolForwardUniverse
      (fun _ _ => True) (fun _ _ => True)).nilpotencyIndex =
      some 2 := by
  native_decide

end ArchitectureSignature.Examples

namespace FiniteArchGraph

/-- Finite acyclic architecture graphs have nilpotent adjacency matrices. -/
theorem adjacencyNilpotent_of_acyclic {C : Type u} [DecidableEq C]
    (FG : FiniteArchGraph C) [DecidableRel FG.graph.edge]
    (hAcyclic : Acyclic FG.graph) :
    AdjacencyNilpotent FG.componentUniverse :=
  Formal.Arch.adjacencyNilpotent_of_acyclic FG.componentUniverse hAcyclic

/-- Nilpotent adjacency matrices rule out cycles in finite architecture graphs. -/
theorem acyclic_of_adjacencyNilpotent {C : Type u} [DecidableEq C]
    (FG : FiniteArchGraph C) [DecidableRel FG.graph.edge]
    (hNil : AdjacencyNilpotent FG.componentUniverse) :
    Acyclic FG.graph :=
  Formal.Arch.acyclic_of_adjacencyNilpotent FG.componentUniverse hNil

end FiniteArchGraph

end Formal.Arch
