import Formal.Arch.Layering
import Formal.Arch.Signature

namespace Formal.Arch

universe u

/-- A vertex listed in a walk is reachable from the walk source. -/
theorem reachable_of_mem_walk_vertices {C : Type u} {G : ArchGraph C}
    {x c d : C} (w : Walk G c d) (hMem : x ∈ w.vertices) :
    Reachable G c x := by
  induction w with
  | nil c =>
      have hx : x = c := by
        simpa [Walk.vertices] using hMem
      simpa [hx] using (Reachable.refl c : Reachable G c c)
  | @cons c next d hEdge rest ih =>
      have hMem' : x = c ∨ x ∈ rest.vertices := by
        simpa [Walk.vertices] using hMem
      cases hMem' with
      | inl hx =>
          simpa [hx] using (Reachable.refl c : Reachable G c c)
      | inr hTail =>
          exact Reachable.step hEdge (ih hTail)

/--
A finite measurement universe for an architecture graph.

`components` is the executable list used by v0 metrics. `nodup`, `covers`, and
`edgeClosed` make explicit which assumptions are needed before list-based
metrics are treated as graph-level facts. In this full-universe version,
`edgeClosed` follows from `covers`; it remains explicit to leave room for future
closed measurement sub-universes.
-/
structure ComponentUniverse {C : Type u} (G : ArchGraph C) where
  components : List C
  nodup : components.Nodup
  covers : ∀ c : C, c ∈ components
  edgeClosed : ∀ {c d : C}, G.edge c d → c ∈ components ∧ d ∈ components

namespace ComponentUniverse

/--
For a full finite component universe, edge-closedness follows from coverage.

`ComponentUniverse` keeps `edgeClosed` explicit so future closed measurement
sub-universes can use the same theorem interfaces without requiring full
coverage.
-/
theorem edgeClosed_of_covers {C : Type u} {G : ArchGraph C} {components : List C}
    (covers : ∀ c : C, c ∈ components) :
    ∀ {c d : C}, G.edge c d → c ∈ components ∧ d ∈ components := by
  intro c d _hEdge
  exact ⟨covers c, covers d⟩

/-- Build a full component universe from a duplicate-free covering list. -/
def full {C : Type u} (G : ArchGraph C) (components : List C)
    (nodup : components.Nodup) (covers : ∀ c : C, c ∈ components) :
    ComponentUniverse G where
  components := components
  nodup := nodup
  covers := covers
  edgeClosed := edgeClosed_of_covers covers

/-- Build the v0 signature using the finite universe's component list. -/
def v0 {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignature :=
  ArchitectureSignature.v0OfFinite G U.components boundaryAllowed abstractionAllowed

/-- If `a` occurs in `l` and `a ≠ b`, then `a` still occurs after erasing `b`. -/
private theorem mem_erase_of_ne_of_mem {C : Type u} [DecidableEq C]
    {a b : C} {l : List C} (hne : a ≠ b) (hmem : a ∈ l) :
    a ∈ l.erase b := by
  induction l with
  | nil =>
      cases hmem
  | cons c cs ih =>
      by_cases hcb : c = b
      · subst c
        simp [List.erase_cons_head, hne] at hmem ⊢
        exact hmem
      · rw [List.erase_cons_tail]
        · simp at hmem ⊢
          cases hmem with
          | inl hca => exact Or.inl hca
          | inr hincs => exact Or.inr (ih hincs)
        · simp [hcb]

/--
A duplicate-free list included in another duplicate-free list cannot be longer
than that containing list.
-/
private theorem length_le_of_nodup_subset {C : Type u} [DecidableEq C]
    {xs ys : List C} (hxs : xs.Nodup) (hys : ys.Nodup)
    (hSub : ∀ a, a ∈ xs → a ∈ ys) : xs.length ≤ ys.length := by
  revert ys
  induction xs with
  | nil =>
      intro ys _hys _hSub
      simp
  | cons x xs ih =>
      intro ys hys hSub
      have hxNot : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxsNodup : xs.Nodup := (List.nodup_cons.mp hxs).2
      have hxMem : x ∈ ys := hSub x (by simp)
      have hSubErase : ∀ a, a ∈ xs → a ∈ ys.erase x := by
        intro a ha
        exact mem_erase_of_ne_of_mem
          (by
            intro h
            exact hxNot (by simpa [h] using ha))
          (hSub a (by simp [ha]))
      have ihLen : xs.length ≤ (ys.erase x).length :=
        ih hxsNodup (List.Nodup.erase x hys) hSubErase
      have hEraseLen : (ys.erase x).length = ys.length - 1 :=
        List.length_erase_of_mem hxMem
      have hPos : 0 < ys.length := List.length_pos_of_mem hxMem
      have hSucc : xs.length + 1 ≤ (ys.erase x).length + 1 :=
        Nat.succ_le_succ ihLen
      calc
        (x :: xs).length = xs.length + 1 := rfl
        _ ≤ (ys.erase x).length + 1 := hSucc
        _ = ys.length := by omega

/--
Every simple walk over a component universe is bounded by the universe list
length.
-/
theorem simpleWalk_length_le_components_length {C : Type u} {G : ArchGraph C}
    [DecidableEq C] (U : ComponentUniverse G) {c d : C}
    (p : SimpleWalk G c d) : p.length ≤ U.components.length := by
  have hVerticesLen : p.vertices.length ≤ U.components.length :=
    length_le_of_nodup_subset p.nodup_vertices U.nodup
      (fun a _ha => U.covers a)
  have hWalkLen : p.length ≤ p.vertices.length := by
    rw [SimpleWalk.vertices_length]
    exact Nat.le_succ p.length
  exact Nat.le_trans hWalkLen hVerticesLen

/-- In an acyclic graph, every walk visits each vertex at most once. -/
theorem walk_vertices_nodup_of_acyclic {C : Type u} {G : ArchGraph C}
    (hAcyclic : Acyclic G) :
    ∀ {c d : C} (w : Walk G c d), w.vertices.Nodup
  | _, _, Walk.nil _ => by
      simp [Walk.vertices]
  | _, _, @Walk.cons _ _ src _ _ hEdge rest => by
      have hRest : rest.vertices.Nodup :=
        walk_vertices_nodup_of_acyclic hAcyclic rest
      have hFresh : src ∉ rest.vertices := by
        intro hMem
        exact hAcyclic hEdge (reachable_of_mem_walk_vertices rest hMem)
      simpa [Walk.vertices] using List.nodup_cons.mpr ⟨hFresh, hRest⟩

/--
Every walk in an acyclic finite component universe is bounded by the universe
size.
-/
theorem walk_length_le_components_length_of_acyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] (U : ComponentUniverse G) (hAcyclic : Acyclic G)
    {c d : C} (w : Walk G c d) : w.length ≤ U.components.length := by
  have hVerticesLen : w.vertices.length ≤ U.components.length :=
    length_le_of_nodup_subset (walk_vertices_nodup_of_acyclic hAcyclic w)
      U.nodup (fun a _ha => U.covers a)
  have hWalkLen : w.length ≤ w.vertices.length := by
    rw [Walk.vertices_length]
    exact Nat.le_succ w.length
  exact Nat.le_trans hWalkLen hVerticesLen

/--
Reachability over a finite component universe has a simple path representative
whose length is bounded by `components.length`.
-/
theorem reachable_exists_bounded_path {C : Type u} {G : ArchGraph C}
    [DecidableEq C] (U : ComponentUniverse G) {c d : C}
    (h : Reachable G c d) :
    ∃ p : Path G c d, p.length ≤ U.components.length := by
  rcases Reachable.exists_path h with ⟨p, _⟩
  exact ⟨p, simpleWalk_length_le_components_length U p⟩

end ComponentUniverse

/--
A finite architecture graph is a graph bundled with the proof-carrying finite
measurement universe used by executable metrics and finite-graph theorems.

The bundle is deliberately thin: `ComponentUniverse` remains the owner of
coverage, duplicate-freeness, and edge-closedness assumptions, while list-based
metric APIs remain available for raw executable measurements.
-/
structure FiniteArchGraph (C : Type u) where
  graph : ArchGraph C
  componentUniverse : ComponentUniverse graph

namespace FiniteArchGraph

/-- Bundle an existing graph and component universe as a finite architecture graph. -/
def ofComponentUniverse {C : Type u} {G : ArchGraph C}
    (U : ComponentUniverse G) : FiniteArchGraph C where
  graph := G
  componentUniverse := U

/-- The executable measurement list carried by a finite architecture graph. -/
def components {C : Type u} (FG : FiniteArchGraph C) : List C :=
  FG.componentUniverse.components

/-- The component list carried by a finite architecture graph is duplicate-free. -/
theorem nodup_components {C : Type u} (FG : FiniteArchGraph C) :
    FG.components.Nodup :=
  FG.componentUniverse.nodup

/-- The component list carried by a finite architecture graph covers every vertex. -/
theorem covers_components {C : Type u} (FG : FiniteArchGraph C) (c : C) :
    c ∈ FG.components :=
  FG.componentUniverse.covers c

/-- Edges of a finite architecture graph stay inside its component universe. -/
theorem edgeClosed_components {C : Type u} (FG : FiniteArchGraph C)
    {c d : C} (hEdge : FG.graph.edge c d) :
    c ∈ FG.components ∧ d ∈ FG.components :=
  FG.componentUniverse.edgeClosed hEdge

/-- Build the v0 signature from the bundled component universe. -/
def v0 {C : Type u} (FG : FiniteArchGraph C)
    [DecidableEq C] [DecidableRel FG.graph.edge]
    (boundaryAllowed abstractionAllowed : C → C → Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignature :=
  FG.componentUniverse.v0 boundaryAllowed abstractionAllowed

end FiniteArchGraph

namespace ArchitectureSignature

/-- Two components are in the same graph-level SCC when each reaches the other. -/
def MutuallyReachable {C : Type u} (G : ArchGraph C) (c d : C) : Prop :=
  Reachable G c d ∧ Reachable G d c

/-- Noncomputable Boolean view of propositional reachability. -/
noncomputable def reachableBool {C : Type u} (G : ArchGraph C) (c d : C) : Bool := by
  classical
  exact decide (Reachable G c d)

/-- Noncomputable Boolean view of graph-level mutual reachability. -/
noncomputable def mutualReachableBool {C : Type u} (G : ArchGraph C)
    (c d : C) : Bool := by
  classical
  exact decide (MutuallyReachable G c d)

/-- The noncomputable reachability Boolean reflects `Reachable`. -/
theorem reachableBool_eq_true_iff {C : Type u} {G : ArchGraph C} {c d : C} :
    reachableBool G c d = true ↔ Reachable G c d := by
  classical
  simp [reachableBool]

/-- The noncomputable mutual-reachability Boolean reflects `MutuallyReachable`. -/
theorem mutualReachableBool_eq_true_iff {C : Type u} {G : ArchGraph C} {c d : C} :
    mutualReachableBool G c d = true ↔ MutuallyReachable G c d := by
  classical
  simp [mutualReachableBool]

/-- Mutual reachability is reflexive. -/
theorem mutuallyReachable_refl {C : Type u} {G : ArchGraph C} (c : C) :
    MutuallyReachable G c c :=
  ⟨Reachable.refl c, Reachable.refl c⟩

/-- Mutual reachability is symmetric. -/
theorem mutuallyReachable_symm {C : Type u} {G : ArchGraph C} {c d : C}
    (h : MutuallyReachable G c d) : MutuallyReachable G d c :=
  ⟨h.2, h.1⟩

/-- Mutual reachability is transitive. -/
theorem mutuallyReachable_trans {C : Type u} {G : ArchGraph C} {a b c : C}
    (hab : MutuallyReachable G a b) (hbc : MutuallyReachable G b c) :
    MutuallyReachable G a c :=
  ⟨Reachable.trans hab.1 hbc.1, Reachable.trans hbc.2 hab.2⟩

/--
The graph-level SCC class of `c` inside a supplied finite measurement list.

This is intentionally noncomputable: it uses propositional `Reachable`, while
`sccSizeAt` remains the executable bounded-search metric.
-/
noncomputable def mutualReachableClass {C : Type u} (G : ArchGraph C)
    (components : List C) (c : C) : List C :=
  components.filter (fun d => mutualReachableBool G c d)

/-- Graph-level SCC class size inside a supplied finite measurement list. -/
noncomputable def mutualReachableClassSize {C : Type u} (G : ArchGraph C)
    (components : List C) (c : C) : Nat :=
  (mutualReachableClass G components c).length

/-- Membership in the graph-level SCC class is exactly mutual reachability. -/
theorem mem_mutualReachableClass_iff {C : Type u} {G : ArchGraph C}
    {components : List C} {c d : C} :
    d ∈ mutualReachableClass G components c ↔
      d ∈ components ∧ MutuallyReachable G c d := by
  classical
  simp [mutualReachableClass, mutualReachableBool_eq_true_iff]

/--
The graph-level strict reachable cone of `c` inside a supplied finite
measurement list.

This is intentionally noncomputable: it uses propositional `Reachable`, while
`reachableConeSizeAt` remains the executable bounded-search metric. The source
component itself is excluded.
-/
noncomputable def reachableCone {C : Type u} (G : ArchGraph C)
    [DecidableEq C]
    (components : List C) (c : C) : List C :=
  components.filter (fun d => decide (c ≠ d) && reachableBool G c d)

/-- Graph-level strict reachable cone size inside a supplied finite list. -/
noncomputable def reachableConeSize {C : Type u} (G : ArchGraph C)
    [DecidableEq C]
    (components : List C) (c : C) : Nat :=
  (reachableCone G components c).length

/-- Membership in the graph-level strict reachable cone is exactly reachability. -/
theorem mem_reachableCone_iff {C : Type u} {G : ArchGraph C}
    [DecidableEq C]
    {components : List C} {c d : C} :
    d ∈ reachableCone G components c ↔
      d ∈ components ∧ c ≠ d ∧ Reachable G c d := by
  classical
  simp [reachableCone, reachableBool_eq_true_iff]

/-- Folding `Nat.max` never decreases its accumulator. -/
private theorem acc_le_foldl_max (xs : List Nat) (acc : Nat) :
    acc ≤ xs.foldl Nat.max acc := by
  induction xs generalizing acc with
  | nil =>
      exact Nat.le_refl _
  | cons x xs ih =>
      exact Nat.le_trans (Nat.le_max_left acc x) (ih (Nat.max acc x))

/-- Every element of a finite list is bounded by a `Nat.max` fold. -/
private theorem le_foldl_max_of_mem {n acc : Nat} :
    ∀ {xs : List Nat}, n ∈ xs → n ≤ xs.foldl Nat.max acc := by
  intro xs hMem
  induction xs generalizing n acc with
  | nil =>
      cases hMem
  | cons x xs ih =>
      simp at hMem
      cases hMem with
      | inl hn =>
          subst n
          exact Nat.le_trans (Nat.le_max_right acc x)
            (acc_le_foldl_max xs (Nat.max acc x))
      | inr hTail =>
          exact ih (acc := Nat.max acc x) hTail

/-- Every element of a finite list is bounded by `maxNatList`. -/
private theorem le_maxNatList_of_mem {xs : List Nat} {n : Nat}
    (hMem : n ∈ xs) : n ≤ maxNatList xs := by
  simpa [maxNatList] using (le_foldl_max_of_mem (acc := 0) hMem)

private theorem foldl_max_le_of_forall_le {bound : Nat} :
    ∀ (xs : List Nat) (acc : Nat),
      acc ≤ bound → (∀ n, n ∈ xs → n ≤ bound) →
        xs.foldl Nat.max acc ≤ bound := by
  intro xs
  induction xs with
  | nil =>
      intro acc hAcc _hAll
      exact hAcc
  | cons x xs ih =>
      intro acc hAcc hAll
      apply ih
      · exact (Nat.max_le).2 ⟨hAcc, hAll x (by simp)⟩
      · intro n hn
        exact hAll n (by simp [hn])

private theorem maxNatList_le_of_forall_le {xs : List Nat} {bound : Nat}
    (hAll : ∀ n, n ∈ xs → n ≤ bound) : maxNatList xs ≤ bound := by
  simpa [maxNatList] using
    foldl_max_le_of_forall_le xs 0 (Nat.zero_le bound) hAll

/--
Bounded Boolean reachability is sound with respect to propositional
`Reachable`.

This theorem does not need a finite-universe coverage assumption: any successful
bounded search exposes a concrete chain of graph edges.
-/
theorem reachesWithin_sound {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] {components : List C} :
    ∀ {fuel : Nat} {c d : C},
      reachesWithin G components fuel c d = true → Reachable G c d := by
  intro fuel
  induction fuel with
  | zero =>
      intro c d h
      by_cases hEq : c = d
      · cases hEq
        exact Reachable.refl c
      · simp [reachesWithin, hEq] at h
  | succ fuel ih =>
      intro c d h
      by_cases hEq : c = d
      · cases hEq
        exact Reachable.refl c
      · simp [reachesWithin, hEq, List.any_eq_true] at h
        rcases h with ⟨next, _hMem, hEdge, hRest⟩
        exact Reachable.step hEdge (ih hRest)

/-- A true cycle indicator gives a generating edge followed by reachability back. -/
theorem edge_reachable_of_hasCycleBool {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] {components : List C}
    (h : hasCycleBool G components = true) :
    ∃ c d : C, G.edge c d ∧ Reachable G d c := by
  simp [hasCycleBool, List.any_eq_true] at h
  rcases h with ⟨c, _hc, d, _hd, hEdge, hReach⟩
  exact ⟨c, d, hEdge, reachesWithin_sound hReach⟩

/-- A true cycle indicator gives a nonempty closed walk. -/
theorem hasClosedWalk_of_hasCycleBool {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] {components : List C}
    (h : hasCycleBool G components = true) : HasClosedWalk G := by
  rcases edge_reachable_of_hasCycleBool h with ⟨c, d, hEdge, hReach⟩
  exact hasClosedWalk_of_edge_reachable hEdge hReach

/--
A concrete walk of length at most `fuel` is found by bounded Boolean
reachability, assuming the finite universe contains edge targets.
-/
theorem reachesWithin_complete_of_walk {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G) :
    ∀ {c d : C} (w : Walk G c d) {fuel : Nat},
      w.length ≤ fuel → reachesWithin G U.components fuel c d = true := by
  intro c d w
  induction w with
  | nil c =>
      intro fuel _hLen
      cases fuel <;> simp [reachesWithin]
  | @cons c d e hEdge rest ih =>
      intro fuel hLen
      cases fuel with
      | zero =>
          cases hLen
      | succ fuel =>
          by_cases hEq : c = e
          · cases hEq
            simp [reachesWithin]
          · have hRest : rest.length ≤ fuel := by
              exact Nat.le_of_succ_le_succ (by
                simpa [Walk.length, Nat.succ_eq_add_one] using hLen)
            have hAny :
                U.components.any
                    (fun next =>
                      decide (G.edge c next) &&
                        reachesWithin G U.components fuel next e) = true := by
              rw [List.any_eq_true]
              exact ⟨d, (U.edgeClosed hEdge).2, by
                simp [decide_eq_true hEdge, ih hRest]⟩
            simp [reachesWithin, hEq, hAny]

/--
Under a finite component universe, propositional reachability is complete for
the executable bounded search at `components.length` fuel.
-/
theorem reachesWithin_complete_of_reachable_under_universe
    {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G)
    {c d : C} (h : Reachable G c d) :
    reachesWithin G U.components U.components.length c d = true := by
  rcases ComponentUniverse.reachable_exists_bounded_path U h with ⟨p, hLen⟩
  exact reachesWithin_complete_of_walk U p.walk hLen

/--
Under a finite component universe, bounded Boolean reachability at the standard
fuel is exactly propositional `Reachable`.
-/
theorem reachesWithin_eq_reachableBool_under_universe {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) {c d : C} :
    reachesWithin G U.components U.components.length c d =
      reachableBool G c d := by
  classical
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact reachableBool_eq_true_iff.mpr (reachesWithin_sound h)
  · intro h
    exact reachesWithin_complete_of_reachable_under_universe U
      (reachableBool_eq_true_iff.mp h)

/--
Under a finite component universe, the executable bounded SCC size at `c`
equals the graph-level mutual-reachability class size of `c`.
-/
theorem sccSizeAt_eq_mutualReachableClassSize_under_universe {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (c : C) :
    sccSizeAt G U.components c =
      mutualReachableClassSize G U.components c := by
  classical
  simp [sccSizeAt, countWhere, mutualReachableClassSize,
    mutualReachableClass, mutualReachableBool, reachableBool, MutuallyReachable,
    reachesWithin_eq_reachableBool_under_universe U]

/--
Under a finite component universe, the executable maximum SCC size is the
maximum graph-level mutual-reachability class size over the universe.
-/
theorem sccMaxSizeOfFinite_eq_max_mutualReachableClassSize_under_universe
    {C : Type u} {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    sccMaxSizeOfFinite G U.components =
      maxNatList
        (U.components.map (fun c =>
          mutualReachableClassSize G U.components c)) := by
  classical
  simp [sccMaxSizeOfFinite,
    sccSizeAt_eq_mutualReachableClassSize_under_universe U]

/--
The SCC excess metric is exactly the graph-level maximum mutual-reachability
class size, normalized by subtracting one.
-/
theorem sccExcessSizeOfFinite_eq_max_mutualReachableClassSize_sub_one_under_universe
    {C : Type u} {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    sccExcessSizeOfFinite G U.components =
      maxNatList
        (U.components.map (fun c =>
          mutualReachableClassSize G U.components c)) - 1 := by
  rw [sccExcessSizeOfFinite,
    sccMaxSizeOfFinite_eq_max_mutualReachableClassSize_under_universe U]

/--
The SCC excess metric is zero exactly when the measured maximum SCC size is at
most one. This covers empty measurement lists and singleton SCCs by Nat
subtraction.
-/
theorem sccExcessSizeOfFinite_eq_zero_iff_sccMaxSizeOfFinite_le_one
    {C : Type u} (G : ArchGraph C) [DecidableEq C] [DecidableRel G.edge]
    (components : List C) :
    sccExcessSizeOfFinite G components = 0 ↔
      sccMaxSizeOfFinite G components ≤ 1 := by
  simp [sccExcessSizeOfFinite, Nat.sub_eq_zero_iff_le]

/--
Under a finite component universe, the SCC excess metric is zero whenever every
graph-level mutual-reachability class has size at most one.
-/
theorem sccExcessSizeOfFinite_eq_zero_of_max_mutualReachableClassSize_le_one_under_universe
    {C : Type u} {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G)
    (h :
      maxNatList
        (U.components.map (fun c =>
          mutualReachableClassSize G U.components c)) ≤ 1) :
    sccExcessSizeOfFinite G U.components = 0 := by
  rw [sccExcessSizeOfFinite_eq_max_mutualReachableClassSize_sub_one_under_universe U]
  exact Nat.sub_eq_zero_of_le h

/--
Under a finite component universe, the executable bounded reachable cone size at
`c` equals the graph-level strict reachable cone size of `c`.
-/
theorem reachableConeSizeAt_eq_reachableConeSize_under_universe {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (c : C) :
    reachableConeSizeAt G U.components c =
      reachableConeSize G U.components c := by
  classical
  simp [reachableConeSizeAt, countWhere, reachableConeSize, reachableCone,
    reachableBool, reachesWithin_eq_reachableBool_under_universe U]

/--
Under a finite component universe, the executable reachable-cone metric is the
maximum graph-level strict reachable cone size over the universe.
-/
theorem reachableConeSizeOfFinite_eq_max_reachableConeSize_under_universe
    {C : Type u} {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    reachableConeSizeOfFinite G U.components =
      maxNatList
        (U.components.map (fun c =>
          reachableConeSize G U.components c)) := by
  classical
  simp [reachableConeSizeOfFinite,
    reachableConeSizeAt_eq_reachableConeSize_under_universe U]

/--
Under a finite component universe, v0 `fanoutRiskOfFinite` counts exactly the
measured dependency edges inside the universe.
-/
theorem fanoutRiskOfFinite_eq_measuredDependencyEdges_length_under_universe
    {C : Type u} {G : ArchGraph C} [DecidableRel G.edge]
    (U : ComponentUniverse G) :
    fanoutRiskOfFinite G U.components =
      (measuredDependencyEdges G U.components).length := by
  exact fanoutRiskOfFinite_eq_measuredDependencyEdges_length G U.components

/--
An edge followed by a bounded return walk is detected by the cycle indicator
under a finite component universe.
-/
theorem hasCycleBool_complete_of_bounded_return_walk {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G)
    {c d : C} (hEdge : G.edge c d) (w : Walk G d c)
    (hLen : w.length ≤ U.components.length) :
    hasCycleBool G U.components = true := by
  rw [hasCycleBool, List.any_eq_true]
  refine ⟨c, (U.edgeClosed hEdge).1, ?_⟩
  rw [List.any_eq_true]
  exact ⟨d, (U.edgeClosed hEdge).2, by
    simp [decide_eq_true hEdge, reachesWithin_complete_of_walk U w hLen]⟩

/--
A nonempty closed walk is detected by the cycle indicator under a finite
component universe.
-/
theorem hasCycleBool_complete_of_hasClosedWalk {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G)
    (h : HasClosedWalk G) : hasCycleBool G U.components = true := by
  rcases h with ⟨c, w, hLen⟩
  rcases edge_reachable_of_closed_walk w hLen with ⟨d, hEdge, hReach⟩
  rw [hasCycleBool, List.any_eq_true]
  refine ⟨c, (U.edgeClosed hEdge).1, ?_⟩
  rw [List.any_eq_true]
  exact ⟨d, (U.edgeClosed hEdge).2, by
    simp [decide_eq_true hEdge,
      reachesWithin_complete_of_reachable_under_universe U hReach]⟩

/--
Correctness of the executable cycle indicator under a finite component
universe.
-/
theorem hasCycleBool_correct_under_finite_universe {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G) :
    hasCycleBool G U.components = true ↔ HasClosedWalk G :=
  ⟨hasClosedWalk_of_hasCycleBool, hasCycleBool_complete_of_hasClosedWalk U⟩

/-- `bound` is a global upper bound for all dependency-walk lengths. -/
def IsGlobalWalkDepthBound {C : Type u} (G : ArchGraph C) (bound : Nat) : Prop :=
  ∀ {c d : C} (w : Walk G c d), w.length ≤ bound

/--
`depth` is the least natural-number upper bound for all dependency-walk
lengths.
-/
def IsExactGlobalWalkDepth {C : Type u} (G : ArchGraph C) (depth : Nat) : Prop :=
  IsGlobalWalkDepthBound G depth ∧
    ∀ bound : Nat, IsGlobalWalkDepthBound G bound → depth ≤ bound

/--
The bounded DFS depth covers every concrete walk whose length fits in the fuel.
-/
theorem walk_length_le_boundedDepthFrom_of_walk {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge] (U : ComponentUniverse G) :
    ∀ {fuel : Nat} {c d : C} (w : Walk G c d),
      w.length ≤ fuel → w.length ≤ boundedDepthFrom G U.components fuel c
  | 0, _, _, Walk.nil _, _ => by
      simp [Walk.length, boundedDepthFrom]
  | 0, _, _, Walk.cons _ _, hLen => by
      cases hLen
  | fuel + 1, _, _, Walk.nil _, _ => by
      simp [Walk.length]
  | fuel + 1, _, _, Walk.cons (c := src) (d := next) hEdge rest, hLen => by
      have hRestLen : rest.length ≤ fuel := by
        exact Nat.le_of_succ_le_succ (by
          simpa [Walk.length, Nat.succ_eq_add_one] using hLen)
      have hRestDepth :
          rest.length ≤ boundedDepthFrom G U.components fuel next :=
        walk_length_le_boundedDepthFrom_of_walk U rest hRestLen
      have hMeasureMem :
          boundedDepthFrom G U.components fuel next + 1 ∈
            U.components.map (fun d =>
              if decide (G.edge src d) then
                boundedDepthFrom G U.components fuel d + 1
              else
                0) := by
        exact List.mem_map.mpr
          ⟨next, (U.edgeClosed hEdge).2, by
            simp [decide_eq_true hEdge]⟩
      have hMeasureLe :
          boundedDepthFrom G U.components fuel next + 1 ≤
            maxNatList (U.components.map (fun d =>
              if decide (G.edge src d) then
                boundedDepthFrom G U.components fuel d + 1
              else
                0)) :=
        le_maxNatList_of_mem hMeasureMem
      have hWalkLe :
          (Walk.cons hEdge rest).length ≤
            boundedDepthFrom G U.components fuel next + 1 := by
        simpa [Walk.length, Nat.succ_eq_add_one] using
          Nat.succ_le_succ hRestDepth
      exact Nat.le_trans hWalkLe (by
        simpa [boundedDepthFrom] using hMeasureLe)

/--
If `bound` is a walk-depth bound from `c`, bounded DFS from `c` never reports a
larger depth.
-/
theorem boundedDepthFrom_le_of_walk_depth_bound {C : Type u}
    {G : ArchGraph C} [DecidableRel G.edge] {components : List C}
    {bound : Nat} :
    ∀ {fuel : Nat} {c : C},
      (∀ {d : C} (w : Walk G c d), w.length ≤ bound) →
        boundedDepthFrom G components fuel c ≤ bound
  | 0, _ => by
      intro _hBound
      simp [boundedDepthFrom]
  | fuel + 1, c => by
      intro hBound
      simp only [boundedDepthFrom]
      apply maxNatList_le_of_forall_le
      intro n hn
      rcases List.mem_map.mp hn with ⟨next, _hMem, hEq⟩
      by_cases hEdge : G.edge c next
      · have hNextBound :
            ∀ {terminal : C} (walk : Walk G next terminal),
              walk.length ≤ bound - 1 := by
          intro terminal walk
          have hCons :
              (Walk.cons hEdge walk).length ≤ bound :=
            hBound (Walk.cons hEdge walk)
          have hCons' : walk.length + 1 ≤ bound := by
            simpa [Walk.length, Nat.succ_eq_add_one] using hCons
          omega
        have hDepth :
            boundedDepthFrom G components fuel next ≤ bound - 1 :=
          boundedDepthFrom_le_of_walk_depth_bound hNextBound
        have hPositive : 0 < bound := by
          have hOne : (Walk.cons hEdge (Walk.nil next)).length ≤ bound :=
            hBound (Walk.cons hEdge (Walk.nil next))
          have hOne' : 1 ≤ bound := by
            simpa [Walk.length] using hOne
          omega
        subst n
        have hStep :
            boundedDepthFrom G components fuel next + 1 ≤ bound := by
          omega
        simpa [hEdge] using hStep
      · subst n
        simp [hEdge]

/--
If `bound` is a graph-level walk-depth bound, bounded DFS never reports a
larger depth.
-/
theorem boundedDepthFrom_le_of_global_walk_depth_bound {C : Type u}
    {G : ArchGraph C} [DecidableRel G.edge] {components : List C}
    {bound : Nat} (hBound : IsGlobalWalkDepthBound G bound) :
    ∀ {fuel : Nat} {c : C},
      boundedDepthFrom G components fuel c ≤ bound := by
  intro fuel c
  exact boundedDepthFrom_le_of_walk_depth_bound
    (fun w => hBound w)

/--
Under a finite acyclic component universe, `maxDepthOfFinite` bounds every
walk length.
-/
theorem maxDepthOfFinite_is_global_walk_depth_bound_of_acyclic {C : Type u}
    {G : ArchGraph C} [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    IsGlobalWalkDepthBound G (maxDepthOfFinite G U.components) := by
  intro c d w
  have hFuel : w.length ≤ U.components.length :=
    ComponentUniverse.walk_length_le_components_length_of_acyclic U hAcyclic w
  have hDepth :
      w.length ≤ boundedDepthFrom G U.components U.components.length c :=
    walk_length_le_boundedDepthFrom_of_walk U w hFuel
  have hSourceMem :
      boundedDepthFrom G U.components U.components.length c ∈
        U.components.map (fun c =>
          boundedDepthFrom G U.components U.components.length c) := by
    exact List.mem_map.mpr ⟨c, U.covers c, rfl⟩
  have hMax :
      boundedDepthFrom G U.components U.components.length c ≤
        maxDepthOfFinite G U.components := by
    simpa [maxDepthOfFinite] using le_maxNatList_of_mem hSourceMem
  exact Nat.le_trans hDepth hMax

/--
Any graph-level walk-depth bound is also an upper bound for
`maxDepthOfFinite`.
-/
theorem maxDepthOfFinite_le_of_global_walk_depth_bound {C : Type u}
    {G : ArchGraph C} [DecidableRel G.edge] {components : List C}
    {bound : Nat} (hBound : IsGlobalWalkDepthBound G bound) :
    maxDepthOfFinite G components ≤ bound := by
  simp only [maxDepthOfFinite]
  apply maxNatList_le_of_forall_le
  intro n hn
  rcases List.mem_map.mp hn with ⟨c, _hMem, hEq⟩
  subst n
  exact boundedDepthFrom_le_of_global_walk_depth_bound hBound

/--
Correctness of `maxDepthOfFinite` on acyclic finite component universes:
it is the least upper bound of all concrete dependency-walk lengths.
-/
theorem maxDepthOfFinite_correct_of_acyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    IsExactGlobalWalkDepth G (maxDepthOfFinite G U.components) := by
  exact ⟨maxDepthOfFinite_is_global_walk_depth_bound_of_acyclic U hAcyclic,
    fun _ hBound => maxDepthOfFinite_le_of_global_walk_depth_bound hBound⟩

end ArchitectureSignature

namespace ComponentUniverse

/--
Layer assignment induced by finite bounded dependency depth from each source.

This is an executable depth measure over the proof-carrying component universe;
acyclicity is used by the theorem below to show that it is a strict layering.
-/
def sourceDepthLayer {C : Type u} {G : ArchGraph C}
    [DecidableRel G.edge] (U : ComponentUniverse G) : Layering C :=
  fun c => ArchitectureSignature.boundedDepthFrom G U.components U.components.length c

/--
In a finite acyclic component universe, source depth strictly decreases along
each dependency edge.
-/
theorem sourceDepthLayer_strictLayering_of_acyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    StrictLayering G (sourceDepthLayer U) := by
  intro c d hEdge
  simp only [sourceDepthLayer]
  have hSourceBoundC :
      ∀ {terminal : C} (walk : Walk G c terminal),
        walk.length ≤
          ArchitectureSignature.boundedDepthFrom G U.components U.components.length c := by
    intro terminal walk
    have hFuel : walk.length ≤ U.components.length :=
      walk_length_le_components_length_of_acyclic U hAcyclic walk
    exact ArchitectureSignature.walk_length_le_boundedDepthFrom_of_walk U walk hFuel
  have hPositive :
      0 < ArchitectureSignature.boundedDepthFrom G U.components U.components.length c := by
    have hOne :
        (Walk.cons hEdge (Walk.nil d)).length ≤
          ArchitectureSignature.boundedDepthFrom G U.components U.components.length c :=
      hSourceBoundC (Walk.cons hEdge (Walk.nil d))
    have hOne' :
        1 ≤ ArchitectureSignature.boundedDepthFrom G U.components U.components.length c := by
      simpa [Walk.length] using hOne
    exact hOne'
  have hDepthDLePred :
      ArchitectureSignature.boundedDepthFrom G U.components U.components.length d ≤
        ArchitectureSignature.boundedDepthFrom G U.components U.components.length c - 1 := by
    exact ArchitectureSignature.boundedDepthFrom_le_of_walk_depth_bound
      (components := U.components)
      (bound :=
        ArchitectureSignature.boundedDepthFrom G U.components U.components.length c - 1)
      (fuel := U.components.length) (c := d)
      (by
        intro terminal walk
        have hCons :
            (Walk.cons hEdge walk).length ≤
              ArchitectureSignature.boundedDepthFrom G U.components U.components.length c :=
          hSourceBoundC (Walk.cons hEdge walk)
        have hCons' :
            walk.length + 1 ≤
              ArchitectureSignature.boundedDepthFrom G U.components U.components.length c := by
          simpa [Walk.length, Nat.succ_eq_add_one] using hCons
        omega)
  omega

/-- Finite acyclic component universes are strictly layered. -/
theorem strictLayered_of_acyclic {C : Type u} {G : ArchGraph C}
    [DecidableEq C] [DecidableRel G.edge]
    (U : ComponentUniverse G) (hAcyclic : Acyclic G) :
    StrictLayered G :=
  ⟨sourceDepthLayer U, sourceDepthLayer_strictLayering_of_acyclic U hAcyclic⟩

end ComponentUniverse

namespace FiniteArchGraph

/-- Finite acyclic architecture graphs are strictly layered. -/
theorem strictLayered_of_acyclic {C : Type u} [DecidableEq C]
    (FG : FiniteArchGraph C) [DecidableRel FG.graph.edge]
    (hAcyclic : Acyclic FG.graph) :
    StrictLayered FG.graph :=
  ComponentUniverse.strictLayered_of_acyclic FG.componentUniverse hAcyclic

end FiniteArchGraph

end Formal.Arch
