import Formal.Arch.Core.Reachability

namespace Formal.Arch

universe u

/-- Layer assignment for architecture components. Higher numbers depend on lower numbers. -/
abbrev Layering (C : Type u) := C → Nat

/-- A specific layer assignment strictly decreases along every dependency edge. -/
def StrictLayering {C : Type u} (G : ArchGraph C) (layer : Layering C) : Prop :=
  ∀ {c d : C}, G.edge c d → layer d < layer c

/-- A graph is strictly layered when some strict layer assignment exists. -/
def StrictLayered {C : Type u} (G : ArchGraph C) : Prop :=
  ∃ layer : Layering C, StrictLayering G layer

/-- Acyclicity as absence of a nonempty cycle through one generating edge. -/
def Acyclic {C : Type u} (G : ArchGraph C) : Prop :=
  ∀ {c d : C}, G.edge c d → ¬ Reachable G d c

/-- A closed walk with positive length. -/
def HasClosedWalk {C : Type u} (G : ArchGraph C) : Prop :=
  ∃ c : C, ∃ w : Walk G c c, 0 < w.length

/-- Walk-level acyclicity: no nonempty closed walk exists. -/
def WalkAcyclic {C : Type u} (G : ArchGraph C) : Prop :=
  ¬ HasClosedWalk G

/-- Every walk family has a finite length bound depending on its source. -/
def FinitePropagation {C : Type u} (G : ArchGraph C) : Prop :=
  ∃ bound : C → Nat, ∀ {c d : C} (w : Walk G c d), w.length ≤ bound c

/-- Strict layering is preserved when dependency edges are deleted. -/
theorem strictLayering_of_edgeSubset {C : Type u} {H G : ArchGraph C}
    (hSubset : EdgeSubset H G) {layer : Layering C}
    (hLayer : StrictLayering G layer) : StrictLayering H layer :=
  fun hEdge => hLayer (hSubset hEdge)

/-- Strictly layered graphs remain strictly layered under edge subset restriction. -/
theorem strictLayered_of_edgeSubset {C : Type u} {H G : ArchGraph C}
    (hSubset : EdgeSubset H G) (hLayered : StrictLayered G) :
    StrictLayered H := by
  rcases hLayered with ⟨layer, hLayer⟩
  exact ⟨layer, strictLayering_of_edgeSubset hSubset hLayer⟩

/-- A strict layer assignment is monotone along reachability. -/
theorem layer_le_of_reachable {C : Type u} {G : ArchGraph C} {layer : Layering C}
    (hLayer : StrictLayering G layer) :
    ∀ {c d : C}, Reachable G c d → layer d ≤ layer c
  | _, _, Reachable.refl _ => Nat.le_refl _
  | _, _, Reachable.step hEdge hRest =>
      Nat.le_trans (layer_le_of_reachable hLayer hRest)
        (Nat.le_of_lt (hLayer hEdge))

/-- Strict layering rules out dependency cycles. -/
theorem acyclic_of_strictLayering {C : Type u} {G : ArchGraph C}
    {layer : Layering C} (hLayer : StrictLayering G layer) :
    Acyclic G := by
  intro c d hEdge hReach
  exact Nat.not_lt_of_ge (layer_le_of_reachable hLayer hReach) (hLayer hEdge)

/-- Strictly layered graphs are acyclic. -/
theorem strictLayered_acyclic {C : Type u} {G : ArchGraph C}
    (h : StrictLayered G) : Acyclic G := by
  rcases h with ⟨layer, hLayer⟩
  exact acyclic_of_strictLayering hLayer

/-- Acyclic graphs remain acyclic under edge subset restriction. -/
theorem acyclic_of_edgeSubset {C : Type u} {H G : ArchGraph C}
    (hSubset : EdgeSubset H G) (hAcyclic : Acyclic G) :
    Acyclic H := by
  intro c d hEdge hReach
  exact hAcyclic (hSubset hEdge) (Reachable.map_edgeSubset hSubset hReach)

/-- A nonempty closed walk exposes one generating edge followed by reachability back. -/
theorem edge_reachable_of_closed_walk {C : Type u} {G : ArchGraph C}
    {c : C} (w : Walk G c c) (hLen : 0 < w.length) :
    ∃ d : C, G.edge c d ∧ Reachable G d c := by
  cases w with
  | nil c =>
      cases hLen
  | @cons c d e hEdge rest =>
      exact ⟨d, hEdge, Reachable.of_walk rest⟩

/-- Edge-cycle acyclicity rules out nonempty closed walks. -/
theorem walkAcyclic_of_acyclic {C : Type u} {G : ArchGraph C}
    (h : Acyclic G) : WalkAcyclic G := by
  intro hClosed
  rcases hClosed with ⟨c, w, hLen⟩
  rcases edge_reachable_of_closed_walk w hLen with ⟨d, hEdge, hReach⟩
  exact h hEdge hReach

/-- Reachability contains at least one concrete walk, when used inside `Prop`. -/
theorem exists_walk_of_reachable {C : Type u} {G : ArchGraph C} :
    ∀ {c d : C}, Reachable G c d → ∃ _ : Walk G c d, True
  | _, _, Reachable.refl c => ⟨Walk.nil c, trivial⟩
  | _, _, Reachable.step hEdge hRest =>
      let ⟨w, _⟩ := exists_walk_of_reachable hRest
      ⟨Walk.cons hEdge w, trivial⟩

/-- A generating edge followed by reachability back gives a nonempty closed walk. -/
theorem hasClosedWalk_of_edge_reachable {C : Type u} {G : ArchGraph C}
    {c d : C} (hEdge : G.edge c d) (hReach : Reachable G d c) :
    HasClosedWalk G := by
  rcases exists_walk_of_reachable hReach with ⟨w, _⟩
  exact ⟨c, Walk.cons hEdge w, by simp [Walk.length]⟩

/-- Walk-level acyclicity rules out generating-edge cycles. -/
theorem acyclic_of_walkAcyclic {C : Type u} {G : ArchGraph C}
    (h : WalkAcyclic G) : Acyclic G := by
  intro c d hEdge hReach
  exact h (hasClosedWalk_of_edge_reachable hEdge hReach)

/-- Edge-cycle acyclicity and walk-level acyclicity coincide. -/
theorem acyclic_iff_walkAcyclic {C : Type u} {G : ArchGraph C} :
    Acyclic G ↔ WalkAcyclic G :=
  ⟨walkAcyclic_of_acyclic, acyclic_of_walkAcyclic⟩

/-- Strict layering bounds the length of every walk by the source layer. -/
theorem walk_length_le_layer {C : Type u} {G : ArchGraph C} {layer : Layering C}
    (hLayer : StrictLayering G layer) :
    ∀ {c d : C} (w : Walk G c d), w.length ≤ layer c
  | _, _, Walk.nil _ => Nat.zero_le _
  | _, _, Walk.cons hEdge rest =>
      Nat.succ_le_of_lt
        (Nat.lt_of_le_of_lt (walk_length_le_layer hLayer rest) (hLayer hEdge))

/-- Strict layering gives finite propagation, with the layer as a source bound. -/
theorem finitePropagation_of_strictLayered {C : Type u} {G : ArchGraph C}
    (h : StrictLayered G) : FinitePropagation G := by
  rcases h with ⟨layer, hLayer⟩
  exact ⟨layer, fun w => walk_length_le_layer hLayer w⟩

end Formal.Arch
