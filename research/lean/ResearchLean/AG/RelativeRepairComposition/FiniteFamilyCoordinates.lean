import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.RelativeFamilies
import Mathlib.LinearAlgebra.Pi

/-!
# Original-cell coordinates from full coefficient bases

## Implementation notes

The input coordinate isomorphisms cover the entire original kernel at each
cell. Fixed cells alone are removed. Every remaining coordinate retains both
its original cell and its kernel-basis index; candidate/shared cells cannot
be silently omitted.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteFamily
universe uk ui ua
variable {k : Type uk} [Field k]
variable {I : Type ui} (A : I → Type ua)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]

/-- Explicit full bases of the input coefficient groups as finite vectors. -/
structure Bases where
  dimension : I → Nat
  coordinate : ∀ i, A i ≃ₗ[k] (Fin (dimension i) → k)

/-- Pull the same full vertex bases back to the original target of each named cell. -/
def Bases.comap {J : Type*} (B : Bases (k := k) A) (target : J → I) :
    Bases (k := k) (fun j => A (target j)) where
  dimension j := B.dimension (target j)
  coordinate j := B.coordinate (target j)

variable (B : Bases (k := k) A) (s p : Set I)
variable [DecidablePred (· ∈ s)] [DecidablePred (· ∈ p)]

/-- All nonfixed original cells, each with every full kernel basis coordinate. -/
abbrev Index := Σ i : {i : I // i ∈ s ∧ i ∉ p}, Fin (B.dimension i.1)

/-- Pointwise scalar multiplication preserves the original fixed-cell zero condition. -/
instance relativeSMul : SMul k (Family.relative A s p) where
  smul t b := ⟨t • b.1,by intro i hi; change t • b.1 i = 0; rw [b.2 i hi,smul_zero]⟩

/-- The relative module is generated from the same full pointwise module. -/
instance relativeModule : Module k (Family.relative A s p) :=
  Function.Injective.module k (Family.relative A s p).subtype Subtype.val_injective (fun _ _ => rfl)

/-- Read every full kernel coordinate at its original nonfixed cell. -/
def coordinate (h : Family.relative A s p) : Index A B s p → k :=
  fun j => B.coordinate j.1.1 (h.1 ⟨j.1.1,j.1.2.1⟩) j.2

/-- Restore all original cells, with exactly zero on the fixed cells. -/
def restore (x : Index A B s p → k) : Family.relative A s p :=
  ⟨fun i => if hi : i.1 ∈ p then 0 else
    (B.coordinate i.1).symm (fun j => x ⟨⟨i.1,i.2,hi⟩,j⟩),by
      intro i hi
      simp [hi]⟩

omit [DecidablePred (· ∈ s)] in
/-- Coordinate reconstruction returns every original kernel value. -/
theorem restore_coordinate (h : Family.relative A s p) : restore A B s p (coordinate A B s p h) = h := by
  apply Subtype.ext
  funext i
  change (if hi : i.1 ∈ p then 0 else _) = h.1 i
  by_cases hi : i.1 ∈ p
  · simp only [dif_pos hi]
    exact (h.2 i hi).symm
  · simp only [dif_neg hi]
    exact (B.coordinate i.1).symm_apply_apply (h.1 i)

omit [DecidablePred (· ∈ s)] in
/-- All full coordinate values survive the reconstruction. -/
theorem coordinate_restore (x : Index A B s p → k) : coordinate A B s p (restore A B s p x) = x := by
  funext j
  change B.coordinate j.1.1 (if hi : j.1.1 ∈ p then 0 else _) j.2 = x j
  simp only [dif_neg j.1.2.2]
  exact congrFun ((B.coordinate j.1.1).apply_symm_apply _) j.2

/-- Full finite coordinates are a linear isomorphism of the original relative families. -/
def equivalence : Family.relative A s p ≃ₗ[k] (Index A B s p → k) where
  toFun := coordinate A B s p
  invFun := restore A B s p
  left_inv := restore_coordinate A B s p
  right_inv := coordinate_restore A B s p
  map_add' h h' := by funext j; exact congrFun ((B.coordinate j.1.1).map_add _ _) j.2
  map_smul' t h := by funext j; exact congrFun ((B.coordinate j.1.1).map_smul t _) j.2

omit [DecidablePred (· ∈ s)] in
/-- Reading a coordinate uses its same original cell and complete input basis. -/
theorem coordinate_value (h : Family.relative A s p) (j : Index A B s p) :
    equivalence A B s p h j = B.coordinate j.1.1 (h.1 ⟨j.1.1,j.1.2.1⟩) j.2 := rfl

omit [DecidablePred (· ∈ s)] in
/-- Restoration preserves every nonfixed original kernel value. -/
theorem restore_value (x : Index A B s p → k) (i : s) (hi : i.1 ∉ p) :
    ((equivalence A B s p).symm x).1 i =
      (B.coordinate i.1).symm (fun j => x ⟨⟨i.1,i.2,hi⟩,j⟩) := by
  change (if hi' : i.1 ∈ p then 0 else _) = _
  simp only [dif_neg hi]

end AAT.AG.RelativeRepairComposition.FiniteFamily

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
