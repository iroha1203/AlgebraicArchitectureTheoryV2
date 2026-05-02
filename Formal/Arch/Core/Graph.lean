namespace Formal.Arch

universe u

/--
Dependency graph for architecture components.

Convention: `edge c d` means component `c` depends on component `d`.
-/
structure ArchGraph (C : Type u) where
  edge : C → C → Prop

/--
`EdgeSubset H G` means every dependency edge of `H` is also present in `G`.
This is the graph-level relation used for dependency deletion and subgraph
preservation theorems.
-/
def EdgeSubset {C : Type u} (H G : ArchGraph C) : Prop :=
  ∀ {c d : C}, H.edge c d → G.edge c d

namespace EdgeSubset

/-- Every graph is an edge subset of itself. -/
theorem refl {C : Type u} (G : ArchGraph C) : EdgeSubset G G :=
  fun hEdge => hEdge

/-- Edge subset inclusion is transitive. -/
theorem trans {C : Type u} {G₁ G₂ G₃ : ArchGraph C}
    (h₁₂ : EdgeSubset G₁ G₂) (h₂₃ : EdgeSubset G₂ G₃) :
    EdgeSubset G₁ G₃ :=
  fun hEdge => h₂₃ (h₁₂ hEdge)

end EdgeSubset

/--
Static dependencies such as imports, type references, inheritance, and package
dependencies.

This is intentionally an alias for `ArchGraph`: existing reachability,
layering, and Signature v0 theorems apply without duplicating graph theory.
-/
abbrev StaticDependencyGraph (C : Type u) := ArchGraph C

/--
Runtime dependencies such as RPC calls, message queues, shared databases, and
timeout propagation.

The Lean core records only the existence of a runtime dependency edge here.
Labels, weights, failure modes, and empirical extraction metadata remain
tooling-side data until a later bridge turns them into explicit definitions.
-/
abbrev RuntimeDependencyGraph (C : Type u) := ArchGraph C

/--
The two dependency roles used by Signature v1 design.

`static` is the graph used for structural decomposition and boundary checks.
`runtime` is a separate graph for runtime coupling and failure propagation.
Keeping them separate prevents static architecture constraints from being
mixed with operational propagation metrics.
-/
structure ArchitectureDependencyGraphs (C : Type u) where
  static : StaticDependencyGraph C
  runtime : RuntimeDependencyGraph C

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

/-- An edge subset turns every walk in the smaller graph into a walk in the larger graph. -/
def map_edgeSubset {C : Type u} {H G : ArchGraph C} (hSubset : EdgeSubset H G) :
    ∀ {c d : C}, Walk H c d → Walk G c d
  | _, _, nil c => nil c
  | _, _, cons hEdge rest => cons (hSubset hEdge) (map_edgeSubset hSubset rest)

/-- Mapping a walk along an edge subset preserves its length. -/
theorem length_map_edgeSubset {C : Type u} {H G : ArchGraph C}
    (hSubset : EdgeSubset H G) :
    ∀ {c d : C} (w : Walk H c d),
      (map_edgeSubset hSubset w).length = w.length
  | _, _, nil _ => rfl
  | _, _, cons _ rest => by
      simp [map_edgeSubset, length, length_map_edgeSubset hSubset rest]

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

/-- Suffix of a walk starting at a vertex already visited by the walk. -/
noncomputable def suffixFrom {C : Type u} [DecidableEq C] {G : ArchGraph C}
    {x c d : C} : (w : Walk G c d) → x ∈ w.vertices → Walk G x d
  | nil c, hMem => by
      have hx : x = c := by
        simpa [vertices] using hMem
      cases hx
      exact nil x
  | @cons _ G c next d hEdge rest, hMem => by
      by_cases hx : x = c
      · cases hx
        exact cons hEdge rest
      · have hTail : x ∈ rest.vertices := by
          simpa [vertices, hx] using hMem
        exact suffixFrom rest hTail

/-- The vertices of a walk suffix form a sublist of the original walk vertices. -/
theorem suffixFrom_vertices_sublist {C : Type u} [DecidableEq C]
    {G : ArchGraph C} {x c d : C} (w : Walk G c d)
    (hMem : x ∈ w.vertices) : (suffixFrom w hMem).vertices.Sublist w.vertices := by
  induction w with
  | nil c =>
      have hx : x = c := by
        simpa [vertices] using hMem
      cases hx
      simp [suffixFrom]
  | @cons c next d hEdge rest ih =>
      by_cases hx : x = c
      · cases hx
        simp [suffixFrom]
      · have hTail : x ∈ rest.vertices := by
          simpa [vertices, hx] using hMem
        have hSub := ih hTail
        simpa [suffixFrom, hx, vertices] using hSub.cons c

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

/-- Suffix of a simple walk starting at a vertex already visited by it. -/
noncomputable def suffixFrom {C : Type u} [DecidableEq C] {G : ArchGraph C}
    {x c d : C} (p : SimpleWalk G c d) (hMem : x ∈ p.vertices) :
    SimpleWalk G x d where
  walk := Walk.suffixFrom p.walk hMem
  nodup_vertices :=
    p.nodup_vertices.sublist (Walk.suffixFrom_vertices_sublist p.walk hMem)

end SimpleWalk

end Formal.Arch
