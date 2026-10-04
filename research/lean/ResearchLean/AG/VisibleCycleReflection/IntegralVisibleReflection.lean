import ResearchLean.AG.VisibleCycleReflection.VisibleCycleCriterion
import ResearchLean.AG.ObstructionDiagnosticBridge.IntegralReflection
import Formal.Util.AssertStandardAxioms

/-!
# Extending visible potentials and recovering integral corrections

## Implementation notes

A visible potential is first extended by zero, then its residual is corrected by
bridge cut potentials. Only after proving the full edge-difference equation is the
G-125 coordinatewise floor construction applied. Flooring the zero extension alone
would not control invisible edges. The cut sum is a finite, input-generated witness;
no global potential or reflection certificate is assumed. It works componentwise
without choosing a connected root or a spanning tree.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection.Graph
open Classical ObstructionDiagnosticBridge
universe u
variable {V : Type u} [LinearOrder V] [Fintype V] (G : SimpleGraph V)

/-- A finite cut-potential sum for a cochain supported only on bridges. -/
def bridgePrimitive (r : Edge G → ℚ) : V → ℚ := ∑ e, r e • cutPotential G e

/-- Public formula for the finite bridge primitive. -/
theorem bridgePrimitive_apply (r : Edge G → ℚ) :
    bridgePrimitive G r = ∑ e, r e • cutPotential G e := rfl

/-- Every cochain supported on bridges is a vertex difference. -/
theorem d0_bridgePrimitive (r : Edge G → ℚ)
    (hr : ∀ e, ¬G.IsBridge (unoriented G e) → r e = 0) :
    d0 G (bridgePrimitive G r) = r := by
  rw [bridgePrimitive_apply,map_sum]
  ext f
  simp only [Finset.sum_apply,map_smul,Pi.smul_apply]
  calc
    ∑ e, r e * d0 G (cutPotential G e) f = ∑ e, r e * edgeUnit G e f := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : G.IsBridge (unoriented G e)
      · rw [d0_cutPotential G e he]
      · simp only [hr e he,zero_mul]
    _ = r f := by simp [edgeUnit_apply]

variable (verts : Set V) (edges : Set (Edge G))
variable (hl : ∀ e ∈ edges, left G e ∈ verts) (hr : ∀ e ∈ edges, right G e ∈ verts)

/-- Visible vertex differences use the same actual oriented endpoints. -/
def visibleD0 : (verts → ℚ) →ₗ[ℚ] (edges → ℚ) where
  toFun b e := b ⟨right G e.1,hr e.1 e.2⟩ - b ⟨left G e.1,hl e.1 e.2⟩
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

omit [Fintype V] in
/-- Public evaluation of the visible vertex differential. -/
@[simp] theorem visibleD0_apply (b : verts → ℚ) (e : edges) :
    visibleD0 G verts edges hl hr b e =
      b ⟨right G e.1,hr e.1 e.2⟩ - b ⟨left G e.1,hl e.1 e.2⟩ := rfl

omit [Fintype V] in
/-- Zero extension agrees with the visible differential on every visible edge. -/
theorem d0_zeroExtend_visible (b : verts → ℚ) (e : edges) :
    d0 G (zeroExtend verts b) e.1 = visibleD0 G verts edges hl hr b e := by
  rw [d0_apply,visibleD0_apply,zeroExtend_mem verts b ⟨_,hr e.1 e.2⟩,
    zeroExtend_mem verts b ⟨_,hl e.1 e.2⟩]

/-- B3 extends any visible coboundary witness to a potential on every full edge. -/
theorem exists_full_potential (hvisible : ∀ e, ¬G.IsBridge (unoriented G e) → e ∈ edges)
    (z : Edge G → ℚ) (b : verts → ℚ)
    (hb : ∀ e : edges, z e.1 = visibleD0 G verts edges hl hr b e) :
    ∃ a : V → ℚ, d0 G a = z := by
  let b0 := zeroExtend verts b
  let r := z - d0 G b0
  have hr0 : ∀ e, ¬G.IsBridge (unoriented G e) → r e = 0 := by
    intro e he
    have hi := hvisible e he
    change z e - d0 G (zeroExtend verts b) e = 0
    rw [d0_zeroExtend_visible G verts edges hl hr b ⟨e,hi⟩,hb ⟨e,hi⟩,sub_self]
  refine ⟨b0 + bridgePrimitive G r,?_⟩
  rw [map_add,d0_bridgePrimitive G r hr0]
  exact add_sub_cancel _ _

/-- B3 and visible rational witnesses yield integral corrections for all label coordinates. -/
theorem exists_integral_correction {Label : Type u}
    (vertex : Label → Set V) (edge : Label → Set (Edge G))
    (hleft : ∀ l e, e ∈ edge l → left G e ∈ vertex l)
    (hright : ∀ l e, e ∈ edge l → right G e ∈ vertex l)
    (hvisible : ∀ l e, ¬G.IsBridge (unoriented G e) → e ∈ edge l)
    (z : Edge G → Label → ℤ)
    (hz : ∀ l, ∃ b : vertex l → ℚ, ∀ e : edge l,
      (z e.1 l : ℚ) = visibleD0 G (vertex l) (edge l) (hleft l) (hright l) b e) :
    ∃ n : V → Label → ℤ, ∀ e l, n (right G e) l - n (left G e) l = z e l := by
  have hh : ∀ l, ∃ a : V → ℚ, d0 G a = fun e => (z e l : ℚ) := by
    intro l
    obtain ⟨b,hb⟩ := hz l
    exact exists_full_potential G (vertex l) (edge l) (hleft l) (hright l)
      (hvisible l) (fun e => (z e l : ℚ)) b hb
  choose a ha using hh
  apply IntegralReflection.exists_integral_correction (left G) (right G) z
    (fun v l => a l v)
  intro e l
  exact congrFun (ha l) e

end AAT.AG.VisibleCycleReflection.Graph
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
