import ResearchLean.AG.VisibleCycleReflection.GraphH1Comparison
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Pi
import Formal.Util.AssertStandardAxioms

/-!
# Ordered graph chains and the complete geometric nerve

## Implementation notes

Mathlib SimpleGraph supplies the unoriented adjacency and walks. Ordered endpoint
pairs supply the orientation required by T0; adjacency witnesses remain propositions,
so they do not duplicate edges. Chains are finite functions with the ordinary incidence
map, not a supplied cycle certificate. H1 is its kernel because there are no two-cells.
Mathlib IncMatrix is unoriented, so using its two positive endpoint entries would
change this differential. LinearMap and its kernel supply the standard algebraic
objects here, with the specified signed incidence rather than a new homology postulate.
Using vertex-induced visibility would add edges whose target witnesses differ, so later
visible inclusions will instead use the existing same-target edge subset.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge Cohomology
universe u

namespace Graph
variable {V : Type u} [LinearOrder V] (G : SimpleGraph V)

/-- T0 orientation on every edge of a simple graph. -/
abbrev Edge := {ij : V × V // ij.1 < ij.2 ∧ G.Adj ij.1 ij.2}

/-- Finite ordered edges are obtained from the finite vertex pairs. -/
instance edgeFintype [Fintype V] : Fintype (Edge G) := Fintype.ofFinite _

/-- The geometric source of an oriented edge. -/
def left (e : Edge G) : V := e.1.1
/-- The geometric target of an oriented edge. -/
def right (e : Edge G) : V := e.1.2
/-- The underlying unoriented mathlib edge. -/
def unoriented (e : Edge G) : Sym2 V := s(left G e, right G e)

/-- Ordered edges retain their strict endpoint order. -/
theorem left_lt_right (e : Edge G) : left G e < right G e := e.2.1
/-- Ordered edges retain their actual adjacency. -/
theorem adj (e : Edge G) : G.Adj (left G e) (right G e) := e.2.2
/-- No edge is repeated when its endpoints agree. -/
theorem edge_ext {e f : Edge G} (hl : left G e = left G f)
    (hr : right G e = right G f) : e = f := Subtype.ext (Prod.ext hl hr)

/-- Vertex delta chain, in the finite function presentation. -/
def vertexUnit (v : V) : V → ℚ := Pi.single v 1
/-- Edge delta chain, in the finite function presentation. -/
def edgeUnit (e : Edge G) : Edge G → ℚ := Pi.single e 1

/-- Public evaluation of a vertex delta. -/
@[simp] theorem vertexUnit_apply (v w : V) :
    vertexUnit v w = if w = v then 1 else 0 := by
  classical
  simp [vertexUnit, Pi.single_apply, eq_comm]
/-- Public evaluation of an edge delta. -/
@[simp] theorem edgeUnit_apply (e f : Edge G) :
    edgeUnit G e f = if f = e then 1 else 0 := by
  classical
  simp [edgeUnit, Pi.single_apply, eq_comm]

variable [Fintype V]

/-- The standard oriented chain differential: target delta minus source delta. -/
def boundary : (Edge G → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun c := ∑ e, c e • (vertexUnit (right G e) - vertexUnit (left G e))
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Public incidence formula for a chain. -/
theorem boundary_apply (c : Edge G → ℚ) :
    boundary G c = ∑ e, c e • (vertexUnit (right G e) - vertexUnit (left G e)) := rfl

/-- The incidence differential on a single oriented edge. -/
@[simp] theorem boundary_edgeUnit (e : Edge G) :
    boundary G (edgeUnit G e) = vertexUnit (right G e) - vertexUnit (left G e) := by
  classical
  rw [boundary_apply]
  simp [edgeUnit]

/-- Graph H1 is the ordinary chain kernel, since no two-cells are present. -/
abbrev H1 := LinearMap.ker (boundary G)

/-- The ordinary scalar vertex-difference cochain differential. -/
def d0 : (V → ℚ) →ₗ[ℚ] (Edge G → ℚ) where
  toFun b e := b (right G e) - b (left G e)
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

omit [Fintype V] in
/-- Public vertex-difference formula. -/
@[simp] theorem d0_apply (b : V → ℚ) (e : Edge G) :
    d0 G b e = b (right G e) - b (left G e) := rfl

/-- A directed step selects its sorted edge with the corresponding sign. -/
def hopChain {a b : V} (h : G.Adj a b) : Edge G → ℚ :=
  if hab : a < b then edgeUnit G ⟨(a,b), hab, h⟩
  else -edgeUnit G ⟨(b,a), lt_of_le_of_ne (le_of_not_gt hab) h.ne.symm, h.symm⟩

omit [Fintype V] in
/-- Public generation formula for a step in the sorted edge direction. -/
theorem hopChain_of_lt {a b : V} (h : G.Adj a b) (hab : a < b) :
    hopChain G h = edgeUnit G ⟨(a,b), hab, h⟩ := by
  rw [hopChain, dif_pos hab]

omit [Fintype V] in
/-- Public generation formula for a step opposite to the sorted edge direction. -/
theorem hopChain_of_not_lt {a b : V} (h : G.Adj a b) (hab : ¬a < b) :
    hopChain G h =
      -edgeUnit G ⟨(b,a), lt_of_le_of_ne (le_of_not_gt hab) h.ne.symm, h.symm⟩ := by
  rw [hopChain, dif_neg hab]

/-- The chain differential of a directed step is its endpoint difference. -/
theorem boundary_hopChain {a b : V} (h : G.Adj a b) :
    boundary G (hopChain G h) = vertexUnit b - vertexUnit a := by
  unfold hopChain
  split_ifs
  · exact boundary_edgeUnit G _
  · rw [map_neg, boundary_edgeUnit]
    change -(vertexUnit a - vertexUnit b) = _
    abel

/-- The usual signed edge chain of a mathlib walk. -/
def walkChain {a b : V} : G.Walk a b → (Edge G → ℚ)
  | .nil => 0
  | .cons h p => hopChain G h + walkChain p

omit [Fintype V] in
/-- The empty walk has zero chain. -/
@[simp] theorem walkChain_nil (a : V) : walkChain G (.nil : G.Walk a a) = 0 := rfl
omit [Fintype V] in
/-- The chain of a walk beginning with one step. -/
@[simp] theorem walkChain_cons {a b c : V} (h : G.Adj a b) (p : G.Walk b c) :
    walkChain G (.cons h p) = hopChain G h + walkChain G p := rfl

/-- Telescoping of the ordinary walk incidence chain. -/
theorem boundary_walkChain {a b : V} (p : G.Walk a b) :
    boundary G (walkChain G p) = vertexUnit b - vertexUnit a := by
  induction p with
  | nil => simp
  | cons h p ih => rw [walkChain_cons, map_add, boundary_hopChain, ih]; abel

/-- The incidence pairing is the transpose of the ordinary vertex differential. -/
theorem boundary_pairing (c : Edge G → ℚ) (b : V → ℚ) :
    (∑ v, boundary G c v * b v) = ∑ e, c e * d0 G b e := by
  classical
  simp only [boundary_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [vertexUnit_apply]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, d0_apply, mul_sub]

/-- A vertex-difference cochain has zero evaluation on every cycle. -/
theorem cycle_pairing_d0 (c : H1 G) (b : V → ℚ) :
    ∑ e, c.1 e * d0 G b e = 0 := by
  rw [← boundary_pairing, (LinearMap.mem_ker.mp c.2)]
  simp

omit [Fintype V] in
/-- A directed step cannot use an edge absent from its unoriented step. -/
theorem hopChain_eq_zero {a b : V} (h : G.Adj a b) (e : Edge G)
    (he : unoriented G e ≠ s(a,b)) : hopChain G h e = 0 := by
  classical
  unfold hopChain
  split_ifs with hab
  · rw [edgeUnit_apply, if_neg]
    intro hh
    exact he (by rw [hh]; rfl)
  · rw [Pi.neg_apply, edgeUnit_apply, if_neg, neg_zero]
    intro hh
    exact he (by rw [hh]; exact Sym2.eq_swap)

omit [Fintype V] in
/-- A walk chain vanishes on an edge absent from that walk. -/
theorem walkChain_eq_zero {a b : V} (p : G.Walk a b) (e : Edge G)
    (he : unoriented G e ∉ p.edges) : walkChain G p e = 0 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at he
    rw [walkChain_cons, Pi.add_apply, hopChain_eq_zero G h e he.1, ih he.2, zero_add]

/-- Closed mathlib walks give cycles in the standard chain kernel. -/
def closedWalkH1 {a : V} (p : G.Walk a a) : H1 G :=
  ⟨walkChain G p, by rw [LinearMap.mem_ker, boundary_walkChain, sub_self]⟩

end Graph

namespace GeometricCover
variable {X I : Type u} [TopologicalSpace X] [LinearOrder I]

/-- T0's simple graph is generated by all distinct actual chart intersections. -/
def graph (K : GeometricCover X I) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ((K.patch i ⊓ K.patch j : TopologicalSpace.Opens X) : Set X).Nonempty
  symm := by intro i j h; exact ⟨h.1.symm, by simpa [inf_comm] using h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Public adjacency formula retains the full actual geometric intersections. -/
@[simp] theorem graph_adj (K : GeometricCover X I) (i j : I) :
    K.graph.Adj i j ↔ i ≠ j ∧
      ((K.patch i ⊓ K.patch j : TopologicalSpace.Opens X) : Set X).Nonempty := Iff.rfl

/-- A/B: the complete actual nerve edges are exactly the oriented simple-graph edges. -/
def graphEdgeEquiv (K : GeometricCover X I) : K.Edge ≃ Graph.Edge K.graph where
  toFun e := ⟨e.1, e.2.1, ne_of_lt e.2.1, e.2.2⟩
  invFun e := ⟨e.1, e.2.1, e.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The oriented graph identification preserves source endpoints. -/
@[simp] theorem graphEdgeEquiv_left (K : GeometricCover X I) (e : K.Edge) :
    Graph.left K.graph (K.graphEdgeEquiv e) = K.nerve.edgeLeft e := rfl
/-- The oriented graph identification preserves target endpoints. -/
@[simp] theorem graphEdgeEquiv_right (K : GeometricCover X I) (e : K.Edge) :
    Graph.right K.graph (K.graphEdgeEquiv e) = K.nerve.edgeRight e := rfl

end GeometricCover
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
