import ResearchLean.AG.VisibleCycleReflection.GraphBridge
import Formal.Util.AssertStandardAxioms

/-!
# Cycle inclusion and visibility of all nonbridge edges

## Implementation notes

The visible vertex and edge sets are separate subgraph data. Endpoint membership
is the ordinary subgraph closure condition; the actual AAT instantiation derives it
from a single intersection target. Chain inclusion is zero extension, while visible
incidence is full incidence restricted to visible vertices. The incidence formula and
its vanishing off the visible vertices justify that presentation. Replacing the edge
set by the induced graph on visible vertices would change the specified visibility.
No surjectivity or reflection property is stored in the input.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection
open Classical
universe u

/-- Standard zero extension from a subset, as a rational linear map. -/
def zeroExtend {A : Type u} (s : Set A) : (s → ℚ) →ₗ[ℚ] (A → ℚ) where
  toFun c a := if ha : a ∈ s then c ⟨a,ha⟩ else 0
  map_add' c d := by ext a; dsimp; split_ifs <;> simp
  map_smul' a c := by ext x; dsimp; split_ifs <;> simp

/-- Public evaluation on the supplied subset. -/
@[simp] theorem zeroExtend_mem {A : Type u} (s : Set A) (c : s → ℚ) (a : s) :
    zeroExtend s c a.1 = c a := by simp [zeroExtend]
/-- Public evaluation outside the subset. -/
@[simp] theorem zeroExtend_not_mem {A : Type u} (s : Set A) (c : s → ℚ)
    (a : A) (ha : a ∉ s) : zeroExtend s c a = 0 := by simp [zeroExtend,ha]

/-- Finite zero-extension sums are the ordinary subset sums. -/
theorem sum_zeroExtend {A : Type u} [Fintype A] (s : Set A) (c : s → ℚ) :
    ∑ a, zeroExtend s c a = ∑ a : s, c a := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => a ∈ s) (zeroExtend s c)]
  have hz : (∑ a : {a : A // a ∉ s}, zeroExtend s c a.1) = 0 :=
    Finset.sum_eq_zero (fun a _ => zeroExtend_not_mem s c a.1 a.2)
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro a _
  exact zeroExtend_mem s c a

namespace Graph
variable {V : Type u} [LinearOrder V] [Fintype V] (G : SimpleGraph V)
variable (verts : Set V) (edges : Set (Edge G))
variable (hl : ∀ e ∈ edges, left G e ∈ verts) (hr : ∀ e ∈ edges, right G e ∈ verts)

/-- The ordinary incidence on visible chains, restricted to their vertex set. -/
def visibleBoundary : (edges → ℚ) →ₗ[ℚ] (verts → ℚ) where
  toFun c v := boundary G (zeroExtend edges c) v.1
  map_add' c d := by ext v; simp only [map_add, Pi.add_apply]
  map_smul' a c := by ext v; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- Public visible incidence evaluation. -/
@[simp] theorem visibleBoundary_apply (c : edges → ℚ) (v : verts) :
    visibleBoundary G verts edges c v = boundary G (zeroExtend edges c) v.1 := rfl

/-- The restricted incidence is the ordinary sum of visible endpoint deltas. -/
theorem visibleBoundary_formula (c : edges → ℚ) (v : verts) :
    visibleBoundary G verts edges c v = ∑ e : edges, c e *
      (vertexUnit (right G e.1) v.1 - vertexUnit (left G e.1) v.1) := by
  rw [visibleBoundary_apply,boundary_apply]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
  let f : edges → ℚ := fun e => c e *
    (vertexUnit (right G e.1) v.1 - vertexUnit (left G e.1) v.1)
  calc
    ∑ e, zeroExtend edges c e *
        (vertexUnit (right G e) v.1 - vertexUnit (left G e) v.1) =
        ∑ e, zeroExtend edges f e := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ edges
      · rw [zeroExtend_mem edges c ⟨e,he⟩,zeroExtend_mem edges f ⟨e,he⟩]
      · rw [zeroExtend_not_mem edges c e he,zeroExtend_not_mem edges f e he,zero_mul]
    _ = ∑ e : edges, f e := sum_zeroExtend edges f

include hl hr in
/-- The included visible chain has no incidence outside visible vertices. -/
theorem boundary_zeroExtend_outside (c : edges → ℚ) (v : V) (hv : v ∉ verts) :
    boundary G (zeroExtend edges c) v = 0 := by
  rw [boundary_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : e ∈ edges
  · have hleft : v ≠ left G e := fun hh => hv (hh ▸ hl e he)
    have hright : v ≠ right G e := fun hh => hv (hh ▸ hr e he)
    simp only [vertexUnit_apply, if_neg hleft, if_neg hright, sub_self, mul_zero]
  · rw [zeroExtend_not_mem edges c e he, zero_mul]

include hl hr in
/-- Zero extension is the specified chain map, including degree zero. -/
theorem boundary_zeroExtend_comm (c : edges → ℚ) :
    boundary G (zeroExtend edges c) = zeroExtend verts (visibleBoundary G verts edges c) := by
  ext v
  by_cases hv : v ∈ verts
  · rw [zeroExtend_mem verts _ ⟨v,hv⟩,visibleBoundary_apply]
  · rw [zeroExtend_not_mem verts _ v hv,boundary_zeroExtend_outside G verts edges hl hr c v hv]

/-- Visible H1 is the standard visible incidence kernel. -/
abbrev VisibleH1 := LinearMap.ker (visibleBoundary G verts edges)

/-- B2's chain-induced H1 inclusion, obtained by zero extension. -/
def h1Inclusion : VisibleH1 G verts edges →ₗ[ℚ] H1 G where
  toFun c := ⟨zeroExtend edges c.1, by
    rw [LinearMap.mem_ker]
    ext v
    by_cases hv : v ∈ verts
    · exact congrFun (LinearMap.mem_ker.mp c.2) ⟨v,hv⟩
    · exact boundary_zeroExtend_outside G verts edges hl hr c.1 v hv⟩
  map_add' c d := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a c := by apply Subtype.ext; exact map_smul _ _ _

/-- Public formula for the chain-induced H1 inclusion. -/
@[simp] theorem h1Inclusion_val (c : VisibleH1 G verts edges) :
    (h1Inclusion G verts edges hl hr c).1 = zeroExtend edges c.1 := rfl

/-- The included cycle has zero coefficient on an invisible edge. -/
theorem h1Inclusion_outside (c : VisibleH1 G verts edges) (e : Edge G) (he : e ∉ edges) :
    (h1Inclusion G verts edges hl hr c).1 e = 0 := by
  rw [h1Inclusion_val, zeroExtend_not_mem edges c.1 e he]

/-- Chain H1 inclusion is surjective exactly when every cycle is supported visibly. -/
theorem h1Inclusion_surjective_iff : Function.Surjective (h1Inclusion G verts edges hl hr) ↔
    ∀ c : H1 G, ∀ e : Edge G, e ∉ edges → c.1 e = 0 := by
  constructor
  · intro h c e he
    obtain ⟨d,rfl⟩ := h c
    exact h1Inclusion_outside G verts edges hl hr d e he
  · intro h c
    let d : edges → ℚ := fun e => c.1 e.1
    have hd : zeroExtend edges d = c.1 := by
      ext e
      by_cases he : e ∈ edges
      · exact zeroExtend_mem edges d ⟨e,he⟩
      · rw [zeroExtend_not_mem edges d e he, h c e he]
    have hc : d ∈ VisibleH1 G verts edges := by
      rw [LinearMap.mem_ker]
      ext v
      rw [visibleBoundary_apply,hd]
      exact congrFun (LinearMap.mem_ker.mp c.2) v.1
    refine ⟨⟨d,hc⟩,?_⟩
    apply Subtype.ext
    exact hd

/-- B2 iff B3, without requiring a connected or nonempty visible graph. -/
theorem h1Inclusion_surjective_iff_nonbridge_visible :
    Function.Surjective (h1Inclusion G verts edges hl hr) ↔
      ∀ e : Edge G, ¬G.IsBridge (unoriented G e) → e ∈ edges := by
  rw [h1Inclusion_surjective_iff]
  constructor
  · intro h e he
    by_contra hi
    obtain ⟨p,hcycle,honce,hcoeff⟩ := exists_once_cycle G e he
    have hz := h (closedWalkH1 G p) e hi
    change walkChain G p e = 0 at hz
    rw [hcoeff] at hz
    norm_num at hz
  · intro h c e he
    apply cycle_bridge_coefficient G c e
    by_contra hb
    exact he (h e hb)

end Graph
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
