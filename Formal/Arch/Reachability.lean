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

/-- Walks imply reachability, but reachability forgets walk length and count. -/
def of_walk {C : Type u} {G : ArchGraph C} {c d : C} :
    Walk G c d → Reachable G c d
  | Walk.nil _ => Reachable.refl _
  | Walk.cons h rest => Reachable.step h (of_walk rest)

end Reachable

end Formal.Arch
