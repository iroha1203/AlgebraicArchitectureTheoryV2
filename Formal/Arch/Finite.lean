import Formal.Arch.Layering
import Formal.Arch.Signature

namespace Formal.Arch

universe u

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

end ArchitectureSignature

end Formal.Arch
