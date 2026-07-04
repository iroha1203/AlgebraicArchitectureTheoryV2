import Formal.AG.Research.Basic

/-!
SFT v2 Lean tower, target **L1** (skeleton note `docs/note/
sft_development_spacetime_dynamics_skeleton.md` §10; SFT v2 text Part I).

This file fixes finite record carriers for the development-spacetime layer of
SFT v2 (`docs/sft/software_field_theory.md`):

* finite trace DAGs with a rank certificate for acyclicity (SFT 定義 7.2:
  forward transitions only; a revert is a new forward edge),
* declared merge families with selected base data (SFT 原則 7.4「Base Is
  Data」, 原則 7.5「マージ被覆」),
* diamonds (the span-plus-merge shape used by Part III),
* field configurations as coefficient assignments on contexts (SFT 定義 8.2
  の有限読み),
* generative step relations and finite trajectories (SFT 定義 9.2–9.3 の
  record 水準).

The canonical 4-vertex diamond of SFT 付録 D.2 is instantiated at the end and
its well-formedness facts are discharged by `decide`.

Claim boundary: these are finite record carriers only.  No Grothendieck
topology axioms are claimed here — the generated coverage with saturation
(SFT 定義 7.3), transport data on edges (SFT 定義 8.3), frontier-typed
generators, and the TraceRealization theorem (SFT 定理 9.4) are future Lean
targets, not consequences of this file.  Nothing here asserts anything about
real repositories, extraction completeness, or the old `Formal/Arch/Evolution`
surface (which stays frozen).
-/

namespace Formal.AG.Research
namespace SFTDynamics

/--
A finite trace DAG (SFT 定義 7.2 の有限キャリア).

Vertices are `Nat` indices below `vertexCount`; edges are selected forward
transitions.  Acyclicity is certified by a rank function that strictly
increases along every edge.
-/
structure TraceDag where
  vertexCount : Nat
  edges : List (Nat × Nat)
  edges_bounded : ∀ e ∈ edges, e.1 < vertexCount ∧ e.2 < vertexCount
  rank : Nat → Nat
  edges_monotone : ∀ e ∈ edges, rank e.1 < rank e.2

/--
A declared merge family: a target vertex covered by its parent edges, together
with selected base data (SFT 原則 7.5「マージ点はその親 branch たちに被覆され
る」; 原則 7.4 base はデータであり、pullback からは計算しない).
-/
structure MergeFamily (T : TraceDag) where
  target : Nat
  parents : List Nat
  base : Nat
  target_bounded : target < T.vertexCount
  parents_edges : ∀ p ∈ parents, (p, target) ∈ T.edges
  base_bounded : base < T.vertexCount

/--
A diamond: span `base → branchA`, `base → branchC` with a merge vertex covered
by both branches (SFT 第III部 §20 の対象).
-/
structure Diamond (T : TraceDag) where
  base : Nat
  branchA : Nat
  branchC : Nat
  merge : Nat
  edge_ba : (base, branchA) ∈ T.edges
  edge_bc : (base, branchC) ∈ T.edges
  edge_am : (branchA, merge) ∈ T.edges
  edge_cm : (branchC, merge) ∈ T.edges

/--
A field configuration assigns coefficient data to each context (SFT 定義 8.2
の有限読み; the sheaf-data tuple of the text is truncated to one selected
coefficient reading).
-/
abbrev FieldConfig (Ctx : Type u) (Coeff : Type v) :=
  Ctx → Coeff

/--
A generative step relation (SFT 定義 9.2 の record 水準).  The frontier-typed
closed-loop generator of the text refines this carrier and is a future target.
-/
structure GenerativeModel (Cfg : Type u) where
  step : Cfg → Cfg → Prop

/--
A finite trajectory of a generative model (SFT 定義 9.3 の有限読み).
-/
structure FiniteTrajectory {Cfg : Type u} (M : GenerativeModel Cfg) (n : Nat) where
  states : Fin (n + 1) → Cfg
  steps : ∀ i : Fin n, M.step (states i.castSucc) (states i.succ)

/-- Every diamond induces a merge family covered by its two branches. -/
def Diamond.toMergeFamily {T : TraceDag} (D : Diamond T)
    (target_bounded : D.merge < T.vertexCount)
    (base_bounded : D.base < T.vertexCount) : MergeFamily T where
  target := D.merge
  parents := [D.branchA, D.branchC]
  base := D.base
  target_bounded := target_bounded
  parents_edges := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h
    · simpa [h] using D.edge_am
    · simpa [h] using D.edge_cm
  base_bounded := base_bounded

/-! ## Canonical instance: the 4-vertex diamond of SFT 付録 D.2 -/

/-- The canonical trace DAG `B = 0, A = 1, C = 2, M = 3` (SFT 付録 D.2). -/
def canonicalDag : TraceDag where
  vertexCount := 4
  edges := [(0, 1), (0, 2), (1, 3), (2, 3)]
  edges_bounded := by decide
  rank := fun v => v
  edges_monotone := by decide

/-- The canonical diamond of SFT 付録 D.2. -/
def canonicalDiamond : Diamond canonicalDag where
  base := 0
  branchA := 1
  branchC := 2
  merge := 3
  edge_ba := by decide
  edge_bc := by decide
  edge_am := by decide
  edge_cm := by decide

/-- The canonical declared merge family `{A → M, C → M}` with base `B`. -/
def canonicalMerge : MergeFamily canonicalDag :=
  canonicalDiamond.toMergeFamily (by decide) (by decide)

/-- The canonical merge is covered by exactly the two branches. -/
theorem canonicalMerge_parents :
    canonicalMerge.parents = [1, 2] := rfl

/-- The canonical base selection is the vertex `B = 0` (base is data). -/
theorem canonicalMerge_base :
    canonicalMerge.base = 0 := rfl

end SFTDynamics
end Formal.AG.Research
