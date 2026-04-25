import Formal.Arch.Graph

namespace Formal.Arch

universe u

/-- Reachability is the propositional truncation of dependency walks. -/
inductive Reachable {C : Type u} (G : ArchGraph C) : C → C → Prop where
  | refl (c : C) : Reachable G c c
  | step {c d e : C} : G.edge c d → Reachable G d e → Reachable G c e

namespace Reachable

/-- Every component reaches itself. -/
theorem refl' {C : Type u} {G : ArchGraph C} (c : C) : Reachable G c c :=
  Reachable.refl c

/-- A generating dependency edge gives reachability. -/
theorem of_edge {C : Type u} {G : ArchGraph C} {c d : C}
    (h : G.edge c d) : Reachable G c d :=
  Reachable.step h (Reachable.refl d)

/-- Reachability is transitive. -/
def trans {C : Type u} {G : ArchGraph C} {a b c : C} :
    Reachable G a b → Reachable G b c → Reachable G a c
  | refl _, h₂ => h₂
  | step h hd, h₂ => step h (trans hd h₂)

/-- An edge subset turns reachability in the smaller graph into reachability in the larger graph. -/
def map_edgeSubset {C : Type u} {H G : ArchGraph C} (hSubset : EdgeSubset H G) :
    ∀ {c d : C}, Reachable H c d → Reachable G c d
  | _, _, refl c => refl c
  | _, _, step hEdge hRest => step (hSubset hEdge) (map_edgeSubset hSubset hRest)

/-- Walks imply reachability, but reachability forgets walk length and count. -/
def of_walk {C : Type u} {G : ArchGraph C} {c d : C} :
    Walk G c d → Reachable G c d
  | Walk.nil _ => Reachable.refl _
  | Walk.cons h rest => Reachable.step h (of_walk rest)

/-- Simple walks imply reachability through their underlying walk. -/
def of_simpleWalk {C : Type u} {G : ArchGraph C} {c d : C}
    (p : SimpleWalk G c d) : Reachable G c d :=
  of_walk p.walk

/-- Paths imply reachability through their underlying simple walk. -/
def of_path {C : Type u} {G : ArchGraph C} {c d : C}
    (p : Path G c d) : Reachable G c d :=
  of_simpleWalk p

/--
Reachability admits a simple path representative.

If adding a new leading edge would repeat the source, the construction keeps
the already-simple suffix starting at that repeated source instead.
-/
theorem exists_path {C : Type u} [DecidableEq C] {G : ArchGraph C} :
    ∀ {c d : C}, Reachable G c d → ∃ _ : Path G c d, True
  | _, _, Reachable.refl c => ⟨SimpleWalk.nil c, trivial⟩
  | c, _e, Reachable.step (d := d) hEdge hRest => by
      rcases exists_path hRest with ⟨p, _⟩
      by_cases hMem : c ∈ p.vertices
      · exact ⟨SimpleWalk.suffixFrom p hMem, trivial⟩
      · exact ⟨SimpleWalk.cons hEdge p hMem, trivial⟩

end Reachable

end Formal.Arch
