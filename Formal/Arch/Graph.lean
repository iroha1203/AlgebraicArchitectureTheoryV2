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

/-- Vertices visited by a walk, including both endpoints. -/
def vertices {C : Type u} {G : ArchGraph C} {c d : C} : Walk G c d → List C
  | nil c => [c]
  | cons (c := c) _ rest => c :: rest.vertices

/-- A walk with `n` edges visits `n + 1` vertices, counting repetitions. -/
theorem vertices_length {C : Type u} {G : ArchGraph C} {c d : C}
    (w : Walk G c d) : w.vertices.length = w.length + 1 := by
  induction w with
  | nil c =>
      rfl
  | cons hEdge rest ih =>
      simp [vertices, length, ih]

end Walk

/--
A simple walk is a walk whose visited vertex list has no duplicates.

This keeps the existing `Walk` as the count-preserving object and adds only the
extra no-repeated-vertices invariant needed for future path-shortening lemmas.
-/
structure SimpleWalk {C : Type u} (G : ArchGraph C) (c d : C) where
  walk : Walk G c d
  nodup_vertices : walk.vertices.Nodup

/--
Path is the canonical no-repeated-vertices representative used by bounded
reachability arguments.

At this stage it is an alias for `SimpleWalk`; future work may add additional
path-specific API without changing the underlying invariant.
-/
abbrev Path {C : Type u} (G : ArchGraph C) (c d : C) := SimpleWalk G c d

namespace SimpleWalk

/-- The zero-length simple walk at a component. -/
def nil {C : Type u} {G : ArchGraph C} (c : C) : SimpleWalk G c c where
  walk := Walk.nil c
  nodup_vertices := by
    simp [Walk.vertices]

/-- Add one fresh source vertex to the front of a simple walk. -/
def cons {C : Type u} {G : ArchGraph C} {c d e : C}
    (hEdge : G.edge c d) (rest : SimpleWalk G d e)
    (hFresh : c ∉ rest.walk.vertices) : SimpleWalk G c e where
  walk := Walk.cons hEdge rest.walk
  nodup_vertices := by
    simpa [Walk.vertices] using List.nodup_cons.mpr ⟨hFresh, rest.nodup_vertices⟩

/-- Number of generating dependency edges used by a simple walk. -/
def length {C : Type u} {G : ArchGraph C} {c d : C}
    (p : SimpleWalk G c d) : Nat :=
  p.walk.length

/-- Vertices visited by a simple walk. -/
def vertices {C : Type u} {G : ArchGraph C} {c d : C}
    (p : SimpleWalk G c d) : List C :=
  p.walk.vertices

/-- A simple walk has the same edge/vertex count relation as its underlying walk. -/
theorem vertices_length {C : Type u} {G : ArchGraph C} {c d : C}
    (p : SimpleWalk G c d) : p.vertices.length = p.length + 1 :=
  Walk.vertices_length p.walk

end SimpleWalk

end Formal.Arch
