import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.AffineEquation
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Complete local interfaces of a linear differential

## Implementation notes

The generic section law is discharged by the generated finite matrix section
in the original-coordinate application. Interface objects retain every public
coordinate and every internal kernel vector. No orbit quotient is taken.
-/
namespace AAT.AG.RelativeRepairComposition.LinearInterface
open CategoryTheory
universe uk ux uz uv
variable {k : Type uk} [Field k]
variable {X : Type ux} {Z : Type uz} {V : Type uv}
variable [AddCommGroup X] [Module k X] [AddCommGroup Z] [Module k Z]
variable [AddCommGroup V] [Module k V]
variable (D : X →ₗ[k] V) (F : Z →ₗ[k] V) (σ : V →ₗ[k] X)
variable (hσ : ∀ x, D (σ (D x)) = D x) (r : V)

/-- The computed normal-form projection detects the complete cokernel class. -/
def projection : V →ₗ[k] V := LinearMap.id - D.comp σ

include hσ in
/-- All internal columns map to zero under the projection. -/
theorem projection_D (x : X) : projection D σ (D x) = 0 := by
  change D x - D (σ (D x)) = 0
  rw [hσ,sub_self]

include hσ in
/-- Projection zero is exactly membership in the entire original image. -/
theorem projection_eq_zero_iff (v : V) :
    projection D σ v = 0 ↔ v ∈ LinearMap.range D := by
  constructor
  · intro h
    refine ⟨σ v,?_⟩
    exact (sub_eq_zero.mp h).symm
  · rintro ⟨x,rfl⟩
    exact projection_D D σ hσ x

/-- The original quotient map onto the complete cokernel. -/
def q : V →ₗ[k] V ⧸ LinearMap.range D := (LinearMap.range D).mkQ

include hσ in
/-- The executable projection and the native cokernel have the same equality test. -/
theorem q_eq_iff_projection_eq (v w : V) :
    q D v = q D w ↔ projection D σ v = projection D σ w := by
  have hv : q D v = q D w ↔ v - w ∈ LinearMap.range D :=
    Submodule.Quotient.eq (LinearMap.range D)
  have hp : projection D σ v = projection D σ w ↔ v - w ∈ LinearMap.range D := by
    rw [← sub_eq_zero,← map_sub]
    exact projection_eq_zero_iff D σ hσ (v - w)
  exact hv.trans hp.symm

/-- The computed internal projection retains precisely the complete kernel freedom. -/
def kernelProjection : X →ₗ[k] X := LinearMap.id - σ.comp D

include hσ in
/-- Every generated internal projection value belongs to the whole original kernel. -/
theorem kernel_projection_mem (x : X) : kernelProjection D σ x ∈ LinearMap.ker D := by
  change D (x - σ (D x)) = 0
  rw [map_sub,hσ,sub_self]

/-- Every original kernel vector is fixed by the same generated projection. -/
theorem kernel_projection_fixed (x : LinearMap.ker D) : kernelProjection D σ x.1 = x.1 := by
  change x.1 - σ (D x.1) = x.1
  rw [x.2,map_zero,sub_zero]

include hσ in
/-- The computed projection image is the entire original kernel. -/
theorem kernel_projection_range : LinearMap.range (kernelProjection D σ) = LinearMap.ker D := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact kernel_projection_mem D σ hσ y
  · intro hx
    exact ⟨x,kernel_projection_fixed D σ ⟨x,hx⟩⟩

/-- Public coordinates obey the computed affine relation. -/
def Relation : Set Z := {z | projection D σ (F z) = projection D σ r}

include hσ in
/-- The public relation is exactly the stated cokernel equation. -/
theorem mem_relation (z : Z) : z ∈ Relation D F σ r ↔ q D (F z) = q D r :=
  (q_eq_iff_projection_eq D σ hσ (F z) r).symm

/-- Independent full solutions before elimination. -/
def Solution := {xz : X × Z // D xz.1 + F xz.2 = r}

/-- Every public value and every internal kernel vector are retained. -/
abbrev Coordinates := ↥(Relation D F σ r) × LinearMap.ker D

/-- Public values provide a section preimage of the complete affine residual. -/
theorem section_residual (z : ↥(Relation D F σ r)) :
    D (σ (r - F z.1)) = r - F z.1 := by
  have h : projection D σ (r - F z.1) = 0 := by
    rw [map_sub,z.2,sub_self]
  exact (sub_eq_zero.mp h).symm

/-- Restore every internal degree of freedom without searching for a repair. -/
def rec (y : Coordinates D F σ r) : Solution D F r :=
  ⟨(σ (r - F y.1.1) + y.2.1,y.1.1),by
    change D (σ (r - F y.1.1) + y.2.1) + F y.1.1 = r
    rw [map_add,section_residual D F σ r y.1,y.2.2]
    abel⟩

/-- Every independent solution has its complete public and kernel coordinates. -/
def coord (h : Solution D F r) : Coordinates D F σ r := by
  have hd : D h.1.1 = r - F h.1.2 := eq_sub_iff_add_eq.mpr h.2
  have hz : h.1.2 ∈ Relation D F σ r := by
    have hh := congrArg (projection D σ) h.2
    rw [map_add,projection_D D σ hσ,zero_add] at hh
    exact hh
  refine (⟨h.1.2,hz⟩,⟨h.1.1 - σ (r - F h.1.2),?_⟩)
  change D (h.1.1 - σ (r - F h.1.2)) = 0
  rw [map_sub,← hd,hσ,sub_self]

/-- Reconstruction restores both original coordinates of every independent solution. -/
theorem rec_coord (h : Solution D F r) : rec D F σ r (coord D F σ hσ r h) = h := by
  apply Subtype.ext
  apply Prod.ext
  · change σ (r - F h.1.2) + (h.1.1 - σ (r - F h.1.2)) = h.1.1
    abel
  · rfl

/-- Coordinate extraction restores every public value and every internal vector. -/
theorem coord_rec (y : Coordinates D F σ r) : coord D F σ hσ r (rec D F σ r y) = y := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    change (σ (r - F y.1.1) + y.2.1) - σ (r - F y.1.1) = y.2.1
    abel

/-- Full mutually inverse coordinates, including all internal freedom. -/
def coordinateEquiv : Solution D F r ≃ Coordinates D F σ r where
  toFun := coord D F σ hσ r
  invFun := rec D F σ r
  left_inv := rec_coord D F σ hσ r
  right_inv := coord_rec D F σ hσ r

include hσ in
/-- Existence depends only on the public relation; zero internal freedom gives a repair. -/
theorem solution_nonempty_iff : Nonempty (Solution D F r) ↔ Nonempty ↥(Relation D F σ r) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨(coord D F σ hσ r h).1⟩
  · rintro ⟨z⟩
    exact ⟨rec D F σ r (z,0)⟩

/-- With zero right-hand side the public relation contains zero. -/
theorem relation_zero_nonempty : Nonempty ↥(Relation D F σ (0 : V)) :=
  ⟨⟨0,by change projection D σ (F 0) = projection D σ 0; rw [map_zero]⟩⟩

/-- A zero public differential and nonzero projected residual give an empty relation. -/
theorem relation_empty (hr : projection D σ r ≠ 0) :
    ¬ Nonempty ↥(Relation D (0 : Z →ₗ[k] V) σ r) := by
  rintro ⟨z⟩
  exact hr (by simpa [Relation] using z.2.symm)

end AAT.AG.RelativeRepairComposition.LinearInterface

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
