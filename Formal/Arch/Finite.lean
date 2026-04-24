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

namespace ArchitectureSignature

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

end Formal.Arch
