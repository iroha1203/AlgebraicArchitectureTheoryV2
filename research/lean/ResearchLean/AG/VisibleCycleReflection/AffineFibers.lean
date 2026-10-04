import ResearchLean.AG.VisibleCycleReflection.AffineTransition
import Formal.Util.AssertStandardAxioms

/-!
# Affine fibers in original presentation coefficients

## Implementation notes

A fiber records compatible coordinates only in charts containing its point.
One chart coordinate determines all others by the generated translations.
The inverse coordinate map constructs every fiber value; compatibility is
proved from the atlas cocycle. This avoids selecting a preferred chart or
supplying a global state. Translation acts on every coordinate by the same
primitive coefficient, so its free and transitive behavior is explicit.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection.AffineAtlas
universe u
variable {X I M : Type u} [TopologicalSpace X] [AddCommGroup M]
variable (A : AffineAtlas X I M)

/-- Compatible primitive affine coordinates at a geometric point. -/
def Fiber (x : X) :=
  {r : {i : I // x ∈ A.patch i} → M //
    ∀ i j, r i = A.transition i.1 j.1 + r j}

/-- Read a fiber value in any chart that contains its point. -/
def coordinate (x : X) (i : I) (hi : x ∈ A.patch i) (r : A.Fiber x) : M :=
  r.1 ⟨i,hi⟩

/-- Public change of chart coordinates, with the original affine translation. -/
theorem coordinate_change (x : X) (i j : I) (hi : x ∈ A.patch i) (hj : x ∈ A.patch j)
    (r : A.Fiber x) :
    A.coordinate x i hi r = A.transition i j + A.coordinate x j hj r :=
  r.2 ⟨i,hi⟩ ⟨j,hj⟩

/-- Construct a fiber from an arbitrary primitive value in any containing chart. -/
def fiberFromCoordinate (x : X) (i : I) (hi : x ∈ A.patch i) (m : M) : A.Fiber x :=
  ⟨fun j => A.transition j.1 i + m, by
    intro j k
    change A.transition j.1 i + m = A.transition j.1 k.1 + (A.transition k.1 i + m)
    rw [← A.cocycle j.1 k.1 i x j.2 k.2 hi]
    abel⟩

/-- Public coordinates of the generated fiber value. -/
theorem coordinate_fiberFromCoordinate (x : X) (i j : I)
    (hi : x ∈ A.patch i) (hj : x ∈ A.patch j) (m : M) :
    A.coordinate x j hj (A.fiberFromCoordinate x i hi m) = A.transition j i + m := rfl

/-- A containing chart gives a genuine coordinate equivalence for the fiber. -/
def fiberEquiv (x : X) (i : I) (hi : x ∈ A.patch i) : A.Fiber x ≃ M where
  toFun := A.coordinate x i hi
  invFun := A.fiberFromCoordinate x i hi
  left_inv r := by
    apply Subtype.ext
    funext j
    exact (r.2 j ⟨i,hi⟩).symm
  right_inv m := by
    rw [coordinate_fiberFromCoordinate,A.self,zero_add]

/-- Public evaluation of the fiber coordinate equivalence. -/
@[simp] theorem fiberEquiv_apply (x : X) (i : I) (hi : x ∈ A.patch i) (r : A.Fiber x) :
    A.fiberEquiv x i hi r = A.coordinate x i hi r := rfl

/-- Public evaluation of its inverse, without expanding the equivalence. -/
@[simp] theorem fiberEquiv_symm_apply (x : X) (i : I) (hi : x ∈ A.patch i) (m : M) :
    (A.fiberEquiv x i hi).symm m = A.fiberFromCoordinate x i hi m := rfl

/-- Equality in one containing chart determines the entire fiber value. -/
theorem fiber_ext (x : X) (i : I) (hi : x ∈ A.patch i) {r s : A.Fiber x}
    (h : A.coordinate x i hi r = A.coordinate x i hi s) : r = s :=
  (A.fiberEquiv x i hi).injective h

/-- All fibers are inhabited by local primitive values, using the actual cover. -/
theorem fiber_nonempty (x : X) : Nonempty (A.Fiber x) := by
  obtain ⟨i,hi⟩ := A.covers x
  exact ⟨A.fiberFromCoordinate x i hi 0⟩

/-- Primitive coefficients translate every coordinate by the same amount. -/
def translateFiber (x : X) (m : M) (r : A.Fiber x) : A.Fiber x :=
  ⟨fun i => r.1 i + m, by
    intro i j
    change r.1 i + m = A.transition i.1 j.1 + (r.1 j + m)
    rw [r.2 i j]
    abel⟩

/-- Translation has the specified value in each actual chart coordinate. -/
@[simp] theorem coordinate_translateFiber (x : X) (i : I) (hi : x ∈ A.patch i)
    (m : M) (r : A.Fiber x) :
    A.coordinate x i hi (A.translateFiber x m r) = A.coordinate x i hi r + m := rfl

/-- Zero coefficients act as the identity. -/
@[simp] theorem translateFiber_zero (x : X) (r : A.Fiber x) :
    A.translateFiber x 0 r = r := by
  apply Subtype.ext
  funext i
  exact add_zero _

/-- Addition of primitive coefficients is composition of their translations. -/
theorem translateFiber_add (x : X) (m n : M) (r : A.Fiber x) :
    A.translateFiber x (m+n) r = A.translateFiber x m (A.translateFiber x n r) := by
  apply Subtype.ext
  funext i
  change _ + (m+n) = (_ + n) + m
  abel

/-- The coefficient translation on each fiber is free and transitive. -/
theorem existsUnique_translateFiber (x : X) (r s : A.Fiber x) :
    ∃! m : M, A.translateFiber x m r = s := by
  obtain ⟨i,hi⟩ := A.covers x
  refine ⟨A.coordinate x i hi s - A.coordinate x i hi r, ?_, ?_⟩
  · apply A.fiber_ext x i hi
    rw [coordinate_translateFiber]
    abel
  · intro m hm
    have h := congrArg (A.coordinate x i hi) hm
    rw [coordinate_translateFiber] at h
    exact eq_sub_of_add_eq' h

end AAT.AG.VisibleCycleReflection.AffineAtlas
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
