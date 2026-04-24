namespace Formal.Arch

universe u

/--
Dependency graph for architecture components.

Convention: `edge c d` means component `c` depends on component `d`.
-/
structure ArchGraph (C : Type u) where
  edge : C → C → Prop

/--
A walk preserves path-level information that is intentionally forgotten by
`Reachable` and the thin category built from it.
-/
inductive Walk {C : Type u} (G : ArchGraph C) : C → C → Type u where
  | nil (c : C) : Walk G c c
  | cons {c d e : C} : G.edge c d → Walk G d e → Walk G c e

namespace Walk

/-- Number of generating dependency edges used by a walk. -/
def length {C : Type u} {G : ArchGraph C} {c d : C} : Walk G c d → Nat
  | nil _ => 0
  | cons _ rest => rest.length + 1

end Walk

end Formal.Arch

