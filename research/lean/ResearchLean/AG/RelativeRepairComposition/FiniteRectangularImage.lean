import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteImageBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Generated full image coordinates for rectangular matrices

## Implementation notes

The square extension only adds zero rows and unused input coordinates. Its
image is identified with the full original rectangular image, before applying
the same finite elimination and reading its generated pivots.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteElimination
open Matrix Module
universe uk un
variable {k : Type uk} [Field k] [DecidableEq k]
variable {m n : Type un} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : Matrix m n k)

omit [DecidableEq k] [DecidableEq m] [DecidableEq n] in
/-- The square extension preserves exactly the original output and adds zero rows. -/
theorem squareExtension_mulVec (v : m ⊕ n → k) :
    squareExtension M *ᵥ v = Sum.elim (M *ᵥ (v ∘ Sum.inr)) 0 := by
  simp [squareExtension,Matrix.fromBlocks_mulVec]

/-- Embed the complete rectangular image without adding any image dimension. -/
def rectangleImageToSquare (h : LinearMap.range (Matrix.toLin' M)) :
    LinearMap.range (Matrix.toLin' (squareExtension M)) :=
  ⟨Sum.elim h.1 0,by
    obtain ⟨x,hx⟩ := h.2
    refine ⟨Sum.elim 0 x,?_⟩
    simpa only [Matrix.toLin'_apply,squareExtension_mulVec,Function.comp_def] using
      congrArg (fun y => Sum.elim y (0 : n → k)) hx⟩

/-- Read the original output of every square-extension image value. -/
def squareImageToRectangle (h : LinearMap.range (Matrix.toLin' (squareExtension M))) :
    LinearMap.range (Matrix.toLin' M) :=
  ⟨h.1 ∘ Sum.inl,by
    obtain ⟨x,hx⟩ := h.2
    refine ⟨x ∘ Sum.inr,?_⟩
    exact congrArg (fun y => y ∘ Sum.inl)
      (by simpa only [Matrix.toLin'_apply,squareExtension_mulVec] using hx)⟩

/-- Both full original images are linearly identified in both directions. -/
def rectangleImageEquivalence : LinearMap.range (Matrix.toLin' M) ≃ₗ[k]
    LinearMap.range (Matrix.toLin' (squareExtension M)) where
  toFun := rectangleImageToSquare M
  invFun := squareImageToRectangle M
  left_inv h := Subtype.ext rfl
  right_inv h := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := h.2
    change Sum.elim (h.1 ∘ Sum.inl) 0 = h.1
    rw [← hx]
    simp only [Matrix.toLin'_apply,squareExtension_mulVec]
    rfl
  map_add' h h' := Subtype.ext (by funext i; cases i <;> simp [rectangleImageToSquare])
  map_smul' t h := Subtype.ext (by funext i; cases i <;> simp [rectangleImageToSquare])

variable [Fintype k]
variable (enumK : Enumeration k) (enumM : Enumeration m) (enumN : Enumeration n)

/-- All rectangular image pivots are generated from the complete original matrix. -/
def rectangularReduction : Reduction (squareExtension M) :=
  reduce enumK (sumEnumeration enumN enumM) (squareExtension M)

/-- The generated pivot index retains the original reduced row. -/
abbrev RectangularActive := Active (squareExtension M) (rectangularReduction M enumK enumM enumN)

/-- Full rectangular image coordinates are computed from the same generated elimination. -/
def rectangularImageEquivalence : LinearMap.range (Matrix.toLin' M) ≃ₗ[k]
    (RectangularActive M enumK enumM enumN → k) :=
  (rectangleImageEquivalence M).trans
    (imageEquivalence (squareExtension M) (rectangularReduction M enumK enumM enumN))

/-- Every original rectangular image basis vector is effectively restored from a generated pivot. -/
def rectangularBasisValue (i : RectangularActive M enumK enumM enumN) :
    LinearMap.range (Matrix.toLin' M) :=
  (rectangularImageEquivalence M enumK enumM enumN).symm (Pi.single i 1)

/-- Native basis packaging uses precisely the generated complete-image coordinate map. -/
noncomputable def rectangularBasis : Basis (RectangularActive M enumK enumM enumN) k
    (LinearMap.range (Matrix.toLin' M)) :=
  Basis.ofEquivFun (rectangularImageEquivalence M enumK enumM enumN)

/-- All native basis values are the same computed original image vectors. -/
theorem rectangular_basis_value (i : RectangularActive M enumK enumM enumN) :
    rectangularBasis M enumK enumM enumN i = rectangularBasisValue M enumK enumM enumN i :=
  congrFun (Basis.coe_ofEquivFun (rectangularImageEquivalence M enumK enumM enumN)) i

end AAT.AG.RelativeRepairComposition.FiniteElimination

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
