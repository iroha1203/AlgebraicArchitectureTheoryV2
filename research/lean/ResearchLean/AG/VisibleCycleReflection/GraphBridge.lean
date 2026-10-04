import ResearchLean.AG.VisibleCycleReflection.GraphChains
import Mathlib.SetTheory.Cardinal.Finite
import Formal.Util.AssertStandardAxioms

/-!
# Bridge cuts and once-through nonbridge cycles

## Implementation notes

Mathlib IsBridge is used directly. Deletion reachability gives a cut potential,
whose differential is the bridge's edge delta. This also proves that cycle chains
have zero bridge coefficient, without a connectedness hypothesis on the full graph.
For nonbridges a deleted-edge path is shortened with mathlib toPath and closed by the
missing step. Choosing an arbitrary H1 element would not provide the requested walk
or its once-through evidence. Component counts are compared via the canonical quotient
map, rather than assuming that endpoint disconnection already means a count increase.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection.Graph
open SimpleGraph Classical
universe u
variable {V : Type u} [LinearOrder V] (G : SimpleGraph V)

/-- Sorted endpoint pairs identify their underlying unoriented edge injectively. -/
theorem unoriented_injective : Function.Injective (unoriented G) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with h | h
  · exact edge_ext G h.1 h.2
  · have he := left_lt_right G e
    have hf := left_lt_right G f
    rw [h.1, h.2] at he
    exact False.elim (lt_asymm he hf)

/-- Delete exactly this actual unoriented edge. -/
def withoutEdge (e : Edge G) : SimpleGraph V := G.deleteEdges {unoriented G e}

/-- Public adjacency formula after deleting one edge. -/
theorem withoutEdge_adj (e : Edge G) (a b : V) :
    (withoutEdge G e).Adj a b ↔ G.Adj a b ∧ s(a,b) ≠ unoriented G e := by
  simp [withoutEdge, SimpleGraph.deleteEdges_adj]

/-- Deletion only removes edges. -/
theorem withoutEdge_le (e : Edge G) : withoutEdge G e ≤ G := G.deleteEdges_le _

/-- Mathlib's bridge predicate on an oriented existing edge. -/
theorem isBridge_iff_not_reachable (e : Edge G) :
    G.IsBridge (unoriented G e) ↔
      ¬(withoutEdge G e).Reachable (left G e) (right G e) := by
  change G.IsBridge s(left G e, right G e) ↔
    ¬(G \ SimpleGraph.fromEdgeSet {s(left G e, right G e)}).Reachable (left G e) (right G e)
  rw [SimpleGraph.isBridge_iff]
  exact and_iff_right (adj G e)

/-- The deleted graph connects every other edge's endpoints. -/
theorem other_edge_reachable (e f : Edge G) (h : f ≠ e) :
    (withoutEdge G e).Reachable (left G f) (right G f) := by
  apply SimpleGraph.Adj.reachable
  rw [withoutEdge_adj]
  exact ⟨adj G f, fun hh => h (unoriented_injective G hh)⟩

/-- A bridge cut records the side reachable from its source after deletion. -/
def cutPotential (e : Edge G) (v : V) : ℚ :=
  if (withoutEdge G e).Reachable (left G e) v then 0 else 1

/-- Public formula for the deletion cut potential. -/
theorem cutPotential_apply (e : Edge G) (v : V) :
    cutPotential G e v =
      if (withoutEdge G e).Reachable (left G e) v then 0 else 1 := rfl

/-- Reachability makes the deletion cut constant. -/
theorem cutPotential_eq_of_reachable (e : Edge G) {a b : V}
    (h : (withoutEdge G e).Reachable a b) : cutPotential G e a = cutPotential G e b := by
  have he : (withoutEdge G e).Reachable (left G e) a ↔
      (withoutEdge G e).Reachable (left G e) b :=
    ⟨fun ha => ha.trans h, fun hb => hb.trans h.symm⟩
  simp only [cutPotential_apply, he]

variable [Fintype V]

omit [Fintype V] in
/-- A bridge's cut differential is exactly its oriented unit edge cochain. -/
theorem d0_cutPotential (e : Edge G) (he : G.IsBridge (unoriented G e)) :
    d0 G (cutPotential G e) = edgeUnit G e := by
  classical
  ext f
  by_cases hf : f = e
  · subst f
    rw [d0_apply, cutPotential_apply, cutPotential_apply, edgeUnit_apply]
    simp [(isBridge_iff_not_reachable G e).mp he]
  · rw [d0_apply, edgeUnit_apply, if_neg hf]
    exact sub_eq_zero.mpr (cutPotential_eq_of_reachable G e (other_edge_reachable G e f hf)).symm

/-- A chain cycle has zero coefficient on every bridge. -/
theorem cycle_bridge_coefficient (c : H1 G) (e : Edge G)
    (he : G.IsBridge (unoriented G e)) : c.1 e = 0 := by
  classical
  have h := cycle_pairing_d0 G c (cutPotential G e)
  rw [d0_cutPotential G e he] at h
  simpa only [edgeUnit_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

omit [Fintype V] in
/-- Nonbridge edges have a simple closed walk using the edge exactly once,
with signed chain coefficient minus one in the chosen orientation. -/
theorem exists_once_cycle (e : Edge G) (he : ¬G.IsBridge (unoriented G e)) :
    ∃ p : G.Walk (right G e) (right G e), p.IsCycle ∧
      p.edges.count (unoriented G e) = 1 ∧ walkChain G p e = -1 := by
  classical
  have hr : (withoutEdge G e).Reachable (left G e) (right G e) := by
    simpa only [isBridge_iff_not_reachable, not_not] using he
  obtain ⟨p, hp⟩ := SimpleGraph.reachable_delete_edges_iff_exists_walk.mp hr
  have hpath : unoriented G e ∉ (p.toPath : G.Walk (left G e) (right G e)).edges :=
    fun h => hp (SimpleGraph.Walk.edges_toPath_subset p h)
  let closed : G.Walk (right G e) (right G e) := .cons (adj G e).symm p.toPath
  refine ⟨closed, ?_, ?_, ?_⟩
  · apply SimpleGraph.Path.cons_isCycle
    simpa only [Sym2.eq_swap] using hpath
  · change (s(right G e,left G e) :: (p.toPath : G.Walk (left G e) (right G e)).edges).count (unoriented G e) = 1
    rw [Sym2.eq_swap]
    change (unoriented G e :: (p.toPath : G.Walk (left G e) (right G e)).edges).count (unoriented G e) = 1
    rw [List.count_cons_self, List.count_eq_zero.mpr hpath]
  · rw [walkChain_cons, Pi.add_apply, walkChain_eq_zero G _ e hpath, add_zero]
    rw [hopChain_of_not_lt G _ (not_lt_of_ge (le_of_lt (left_lt_right G e)))]
    rw [Pi.neg_apply, edgeUnit_apply, if_pos]
    apply edge_ext G <;> rfl

omit [Fintype V] in
/-- If the deleted endpoints remain connected, all original reachability remains. -/
theorem reachable_withoutEdge_of_endpoints (e : Edge G)
    (he : (withoutEdge G e).Reachable (left G e) (right G e))
    {a b : V} (h : G.Reachable a b) : (withoutEdge G e).Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    apply SimpleGraph.Reachable.trans (v := b) _ ih
    by_cases hh : s(a,b) = unoriented G e
    · rcases Sym2.eq_iff.mp hh with hh | hh
      · simpa only [hh.1, hh.2] using he
      · simpa only [hh.1, hh.2] using he.symm
    · exact SimpleGraph.Adj.reachable ((withoutEdge_adj G e a b).mpr ⟨hab,hh⟩)

/-- The canonical deletion-to-original map of connected components. -/
def componentMap (e : Edge G) :
    (withoutEdge G e).ConnectedComponent → G.ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (withoutEdge_le G e))

omit [Fintype V] in
/-- Public action of the component map on vertices. -/
@[simp] theorem componentMap_mk (e : Edge G) (v : V) :
    componentMap G e ((withoutEdge G e).connectedComponentMk v) = G.connectedComponentMk v := rfl

omit [Fintype V] in
/-- The deletion-to-original component map is surjective. -/
theorem componentMap_surjective (e : Edge G) : Function.Surjective (componentMap G e) :=
  SimpleGraph.ConnectedComponent.surjective_map_ofLE (withoutEdge_le G e)

omit [Fintype V] in
/-- Nonbridges give bijective component maps. -/
theorem componentMap_injective_of_not_bridge (e : Edge G)
    (he : ¬G.IsBridge (unoriented G e)) : Function.Injective (componentMap G e) := by
  intro c d h
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ a =>
    induction d using SimpleGraph.ConnectedComponent.ind with
    | _ b =>
      apply SimpleGraph.ConnectedComponent.sound
      apply reachable_withoutEdge_of_endpoints G e
      · simpa only [isBridge_iff_not_reachable, not_not] using he
      · simp only [componentMap_mk] at h
        exact SimpleGraph.ConnectedComponent.eq.mp h

omit [Fintype V] in
/-- Bridges give distinct deleted components whose original components agree. -/
theorem componentMap_not_injective_of_bridge (e : Edge G)
    (he : G.IsBridge (unoriented G e)) : ¬Function.Injective (componentMap G e) := by
  intro h
  have hh := h (a₁ := (withoutEdge G e).connectedComponentMk (left G e))
    (a₂ := (withoutEdge G e).connectedComponentMk (right G e))
    (by simp only [componentMap_mk]; exact SimpleGraph.ConnectedComponent.sound (adj G e).reachable)
  exact (isBridge_iff_not_reachable G e).mp he (SimpleGraph.ConnectedComponent.eq.mp hh)

/-- B's component-count definition of bridge is exactly Mathlib IsBridge. -/
theorem isBridge_iff_component_count (e : Edge G) :
    G.IsBridge (unoriented G e) ↔
      Nat.card G.ConnectedComponent < Nat.card (withoutEdge G e).ConnectedComponent := by
  constructor
  · intro he
    by_contra hc
    have hle := Nat.le_of_not_gt hc
    have hb := (componentMap_surjective G e).bijective_of_nat_card_le hle
    exact componentMap_not_injective_of_bridge G e he hb.1
  · intro hc
    by_contra he
    have hle := Nat.card_le_card_of_injective (componentMap G e)
      (componentMap_injective_of_not_bridge G e he)
    exact Nat.not_lt_of_ge hle hc

end AAT.AG.VisibleCycleReflection.Graph
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
