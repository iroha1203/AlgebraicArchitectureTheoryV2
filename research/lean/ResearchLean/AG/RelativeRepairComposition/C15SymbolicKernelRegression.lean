import ResearchLean.AG.RelativeRepairComposition.SymbolicInterfaceAction
import ResearchLean.AG.RelativeRepairComposition.FiniteMatrixInterface
import Mathlib.Data.ZMod.Basic

/-!
# Generated section, a full private kernel and a nonzero stabilizer label

## Implementation notes

The same full two-column matrix generates its section before the parameter is
chosen. The unused original column is retained as a whole nonzero private kernel.
Two independent label coordinates give both a nontrivial action and a nonzero
stabilizer; evaluation keeps the complete label instead of its effective image.
-/
namespace AAT.AG.RelativeRepairComposition.C15SymbolicKernelRegression
open CategoryTheory LinearInterface SymbolicInterface FiniteElimination

/-- The full finite field has all three original values. -/
abbrev k := ZMod 3
/-- The actual finite field list supplies the full generated elimination input. -/
def fieldValues : Enumeration k := ⟨[0,1,2],by decide⟩
/-- The actual single row has its entire input list. -/
def rows : Enumeration Unit := ⟨[()],by intro a; cases a; simp⟩
/-- Both original private columns occur in the actual input list. -/
def columns : Enumeration Bool := ⟨[false,true],by intro a; cases a <;> simp⟩
/-- The complete original private matrix keeps its zero true column. -/
def matrix : Matrix Unit Bool k := fun _ b => if b = false then 1 else 0
/-- The private differential is the full original matrix, including its unused column. -/
def D : (Bool → k) →ₗ[k] (Unit → k) := Matrix.toLin' matrix
/-- The same actual full matrix generates its section once. -/
def generatedSection : (Unit → k) →ₗ[k] (Bool → k) := FiniteMatrixInterface.linearSection fieldValues rows columns matrix
/-- The generated section law is discharged by the original finite algorithm. -/
theorem regular (a : Bool → k) : D (generatedSection (D a)) = D a :=
  FiniteMatrixInterface.section_regular fieldValues rows columns matrix a
/-- The original true column gives the explicit nonzero whole-kernel freedom. -/
def kernelVector : Bool → k := fun b => if b = true then 1 else 0
/-- The retained full private vector satisfies the actual full matrix equation. -/
theorem kernel_mem : kernelVector ∈ LinearMap.ker D := by
  change D kernelVector = 0
  ext row
  cases row
  decide
/-- The original true-column kernel vector is nonzero. -/
theorem kernel_nonzero : kernelVector ≠ 0 := by decide
/-- The public differential keeps its full single public coordinate even when its column is zero. -/
def F : (Unit → k) →ₗ[k] (Unit → k) := 0
/-- The external parameter has zero face effect in this whole-private-kernel fixture. -/
def B : k →ₗ[k] (Unit → k) := 0
/-- The full original two-coordinate label maps its first value into the entire private kernel. -/
def a : (k × k) →ₗ[k] (Bool → k) where
  toFun g b := if b = true then g.1 else 0
  map_add' g h := by funext b; cases b <;> simp
  map_smul' t g := by funext b; cases b <;> simp
/-- Every original label retains the same zero public increment. -/
def c : (k × k) →ₗ[k] (Unit → k) := 0
/-- The entire original label family satisfies the same differential identity. -/
theorem label_zero (g : k × k) : D (a g) + F (c g) = 0 := by
  exact (by decide : ∀ g : k × k, D (a g) + F (c g) = 0) g

/-- Every parameter fibre contains the retained full nonzero private vector. -/
def nonzeroObject (v : k) : FiberObjects D F generatedSection B 0 regular a c label_zero v :=
  (⟨0,rfl⟩,⟨kernelVector,kernel_mem⟩)
/-- Every parameter fibre also contains the full zero private vector. -/
def zeroObject (v : k) : FiberObjects D F generatedSection B 0 regular a c label_zero v := (⟨0,rfl⟩,0)

/-- Evaluation at a nonzero parameter retains the original nonzero private kernel vector. -/
theorem nonzero_evaluation :
    (coordinateFiberEquiv D F generatedSection B 0 (1 : k) (nonzeroObject 1)).2.1 = kernelVector := rfl
/-- Full reconstruction restores the original nonzero private value from the same generated section at a nonzero parameter. -/
theorem nonzero_reconstruction :
    (rec D F generatedSection (rhs B 0 (1 : k))
      (coordinateFiberEquiv D F generatedSection B 0 (1 : k) (nonzeroObject 1))).1.1 = kernelVector := by
  change generatedSection (0 - 0) + kernelVector = kernelVector
  rw [sub_self, map_zero, zero_add]

/-- The nonzero second original label is a genuine retained stabilizer in every parameter fibre. -/
theorem nonzero_stabilizer (v : k) :
    fiberGauge D F generatedSection regular B 0 a c label_zero v (0,1) (zeroObject v) = zeroObject v := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    change 0 + (a (0,1) - generatedSection (D (a (0,1)))) = 0
    have ha : a (0,1) = 0 := by funext b; cases b <;> rfl
    rw [ha, map_zero, map_zero, sub_self, add_zero]

/-- The nonzero first original label acts on the entire retained nonzero private-kernel direction. -/
theorem nonzero_effect (v : k) :
    fiberGauge D F generatedSection regular B 0 a c label_zero v (1,0) (zeroObject v) = nonzeroObject v := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    change 0 + (a (1,0) - generatedSection (D (a (1,0)))) = kernelVector
    have ha : a (1,0) = kernelVector := rfl
    have hd : D kernelVector = 0 := kernel_mem
    rw [ha, hd, map_zero, sub_zero, zero_add]

/-- The nonzero parameter uses the whole original native fibre groupoid. -/
abbrev NativeGroupoid := FiberGroupoid D F generatedSection regular B 0 a c label_zero (1 : k)

/-- The existing full-label ActionCategory supplies the category on this same native parameter fibre. -/
local instance nativeCategory : Category NativeGroupoid :=
  inferInstanceAs (Category (ActionCategory (Multiplicative (k × k))
    (FiberObjects D F generatedSection B 0 regular a c label_zero (1 : k))))

/-- The zero coordinate object is an actual native object at the nonzero parameter. -/
def zeroNative : NativeGroupoid := zeroObject 1

/-- The retained nonzero stabilizer is an actual original native arrow at a nonzero parameter. -/
def stabilizerArrow : zeroNative ⟶ zeroNative :=
  ⟨Multiplicative.ofAdd (0,1),nonzero_stabilizer 1⟩

/-- Evaluating a genuine stabilizer arrow preserves its full nonzero original label. -/
theorem evaluated_stabilizer_label :
    ((fiberEquivalence D F generatedSection regular B 0 a c label_zero 1).functor.map stabilizerArrow).1 =
      Multiplicative.ofAdd ((0,1) : k × k) := rfl

/-- The retained nonzero stabilizer arrow differs from the identity arrow despite having the same object effect. -/
theorem stabilizer_not_identity : stabilizerArrow ≠ 𝟙 zeroNative := by
  intro h
  have hv := congrArg (fun f : zeroNative ⟶ zeroNative => f.1.toAdd.2) h
  change (1 : k) = 0 at hv
  exact (by decide : (1 : k) ≠ 0) hv

end AAT.AG.RelativeRepairComposition.C15SymbolicKernelRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C15SymbolicKernelRegression
