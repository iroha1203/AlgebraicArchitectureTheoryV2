import Formal.Util.AssertStandardAxioms
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# The full native affine projection and its whole translation kernel

Every operation is a native affine equivalence. The kernel and centralizer
are computed from this full projection, including zero-dimensional modules.

## Implementation notes

The projection is the native linear homomorphism on all affine equivalences. Its
kernel equivalence is constructed from that entire kernel, so later categorical
coefficients inherit the original inclusion. Starting with a selected translation
subgroup would leave the whole-kernel and centralizer converse to be supplied
separately; the native projection makes both statements about the same group.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine

universe uk uA
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]

/-- The full group of invertible affine operations on the original module. -/
abbrev Operations (k : Type uk) (A : Type uA) [Field k] [AddCommGroup A] [Module k A] :=
  A ≃ᵃ[k] A

/-- Projection retains the linear component of every original affine operation. -/
def projection : Operations k A →* (A ≃ₗ[k] A) := AffineEquiv.linearHom

/-- Every linear operation occurs as the projection of its native affine operation. -/
theorem projection_surjective : Function.Surjective (projection (k := k) (A := A)) := by
  intro M
  exact ⟨M.toAffineEquiv, rfl⟩

/-- The full translation operation by the given original vector. -/
def translation (a : A) : Operations k A := AffineEquiv.constVAdd k A a

/-- A translation evaluates the original vector addition. -/
@[simp] theorem translation_apply (a x : A) : translation (k := k) a x = a + x := rfl

/-- Translation has the identity linear component. -/
@[simp] theorem projection_translation (a : A) : projection (translation (k := k) a) = 1 := rfl

/-- An affine operation is determined by its original linear part and value at zero. -/
theorem operation_apply (g : Operations k A) (x : A) : g x = g.linear x + g 0 := by
  simpa using g.map_vadd (0 : A) x

/-- Membership in the whole projection kernel means exactly translation by the value at zero. -/
theorem projection_eq_one_iff (g : Operations k A) :
    projection g = 1 ↔ g = translation (k := k) (g 0) := by
  constructor
  · intro h
    apply AffineEquiv.ext
    intro x
    rw [operation_apply]
    have hx : g.linear x = x := congrArg (fun M : A ≃ₗ[k] A => M x) h
    rw [hx, translation_apply, add_comm]
  · intro h
    rw [h, projection_translation]

/-- Original translations embed into the entire native projection kernel. -/
def translationKernel (a : Multiplicative A) : (projection (k := k) (A := A)).ker :=
  ⟨translation (k := k) a.toAdd, projection_translation _⟩

/-- The whole kernel is the full translation group, without taking an effective subgroup. -/
def kernelEquiv : (projection (k := k) (A := A)).ker ≃* Multiplicative A where
  toFun g := Multiplicative.ofAdd (g.1 0)
  invFun := translationKernel
  left_inv g := by
    apply Subtype.ext
    exact ((projection_eq_one_iff g.1).mp g.2).symm
  right_inv a := by simp [translationKernel]
  map_mul' g h := by
    change (g.1 * h.1) 0 = g.1 0 + h.1 0
    rw [AffineEquiv.coe_mul, Function.comp_apply, operation_apply]
    have hh : g.1.linear (h.1 0) = h.1 0 :=
      congrArg (fun M : A ≃ₗ[k] A => M (h.1 0)) g.2
    rw [hh, add_comm]

/-- Kernel reconstruction preserves the same original translation operation. -/
@[simp] theorem kernelEquiv_symm_val (a : A) :
    ((kernelEquiv (k := k)).symm (Multiplicative.ofAdd a)).1 = translation (k := k) a := rfl

/-- The original projection kernel is abelian because all of its elements are translations. -/
theorem kernel_comm (g h : (projection (k := k) (A := A)).ker) : g * h = h * g := by
  apply kernelEquiv.injective
  rw [map_mul, map_mul, mul_comm]

/-- Real affine conjugation transports a full translation by the original linear component. -/
theorem conjugation_translation (g : Operations k A) (a : A) :
    g * translation (k := k) a * g⁻¹ = translation (k := k) (g.linear a) := by
  apply AffineEquiv.ext
  intro x
  change g (a + g.symm x) = g.linear a + x
  simpa using g.map_vadd (g.symm x) a

/-- An affine operation centralizes every translation exactly when its linear component is identity. -/
theorem centralizes_translations_iff (g : Operations k A) :
    (∀ a : A, g * translation (k := k) a = translation (k := k) a * g) ↔
      projection g = 1 := by
  constructor
  · intro h
    apply LinearEquiv.ext
    intro a
    have ha := congrArg (fun f : Operations k A => f 0) (h a)
    change g (a + 0) = a + g 0 at ha
    rw [add_zero, operation_apply] at ha
    exact add_right_cancel ha
  · intro h a
    have hg := (projection_eq_one_iff g).mp h
    rw [hg]
    apply AffineEquiv.ext
    intro x
    change g 0 + (a + x) = a + (g 0 + x)
    exact add_left_comm _ _ _

/-- Centralizing the whole actual kernel is equivalent to being a translation. -/
theorem centralizes_kernel_iff (g : Operations k A) :
    (∀ a : (projection (k := k) (A := A)).ker, g * a.1 = a.1 * g) ↔
      g = translation (k := k) (g 0) := by
  rw [← projection_eq_one_iff, ← centralizes_translations_iff]
  constructor
  · intro h a
    exact h (translationKernel (Multiplicative.ofAdd a))
  · intro h a
    rw [(projection_eq_one_iff a.1).mp a.2]
    exact h _

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
