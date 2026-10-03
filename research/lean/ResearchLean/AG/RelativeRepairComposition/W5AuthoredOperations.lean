import ResearchLean.AG.RelativeRepairComposition.W5AffineInput
import Mathlib.Tactic.FinCases

/-!
# W5's local equations from whole original affine maps

The operation family precedes the two face conditions. Only the shared e
correction varies. Both physical input operations remain the same references;
the complete affine equalities derive the two original scalar equations.
-/
namespace AAT.AG.RelativeRepairComposition.W5AuthoredOperations
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput

/-- The actual physical input selected by an original authored face. -/
def inputValue (b₁ b₂ : ZMod 2) (f : Bool) : ZMod 2 := if f then b₂ else b₁
/-- All original edge corrections retain u on e and zero on the physical input edges. -/
def correctionValue (u : ZMod 2) (e : Fin 3) : ZMod 2 := if e = edgeE then u else 0
/-- Whole corrected original affine operations, before imposing either face equality. -/
noncomputable def operation (b₁ b₂ u : ZMod 2) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => translation (k := ZMod 2) (correctionValue u e.1) * reference b₁ b₂ e

/-- The complete actual shared-edge map is translation by u. -/
theorem operation_e_apply (b₁ b₂ u x : ZMod 2) :
    operation b₁ b₂ u (name edgeE).2.2 x = x + u := by
  simp [operation,correctionValue,reference,name,edgeE,edgeA,edgeB,add_comm]
/-- The complete actual fixed a-map is the original input translation. -/
theorem operation_a_apply (b₁ b₂ u x : ZMod 2) :
    operation b₁ b₂ u (name edgeA).2.2 x = x + b₁ := by
  simp [operation,correctionValue,reference,name,edgeE,edgeA,
    AffineEquiv.coe_mul,Function.comp_apply,add_comm]
/-- The complete actual fixed b-map is the other original input translation. -/
theorem operation_b_apply (b₁ b₂ u x : ZMod 2) :
    operation b₁ b₂ u (name edgeB).2.2 x = x + b₂ := by
  simp [operation,correctionValue,reference,name,edgeE,edgeA,edgeB,
    AffineEquiv.coe_mul,Function.comp_apply,add_comm]

/-- Every original operation retains the prescribed full linear component. -/
theorem operation_linear (b₁ b₂ u : ZMod 2)
    {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (operation b₁ b₂ u e).linear = (reference b₁ b₂ e).linear := by
  change projection (operation b₁ b₂ u e) = projection (reference b₁ b₂ e)
  rw [operation,map_mul,projection_translation,one_mul]
/-- Every original reference linear component is the full identity transport. -/
theorem reference_linear (b₁ b₂ : ZMod 2)
    {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (reference b₁ b₂ e).linear = (1 : ZMod 2 ≃ₗ[ZMod 2] ZMod 2) := by
  rcases e with ⟨e,hs,ht⟩
  fin_cases e <;> simp [reference,edgeA,edgeB] <;> rfl

/-- Each whole original left affine word evaluates using the same shared e. -/
theorem left_apply (b₁ b₂ u x : ZMod 2) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (operation b₁ b₂ u) (geometry.twoLeft f) x = x + u := by
  change operation b₁ b₂ u (name edgeE).2.2 x = _
  exact operation_e_apply b₁ b₂ u x
/-- Each whole original right affine word keeps its physically fixed input. -/
theorem right_apply (b₁ b₂ u x : ZMod 2) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (operation b₁ b₂ u) (geometry.twoRight f) x =
      x + inputValue b₁ b₂ f := by
  cases f
  · exact operation_a_apply b₁ b₂ u x
  · exact operation_b_apply b₁ b₂ u x
/-- Identity comparison is the actual zero translation in the full operation group. -/
theorem zero_translation : translation (k := ZMod 2) (0 : ZMod 2) = (1 : Op) := by
  apply AffineEquiv.ext
  intro x
  exact zero_add x
/-- Each original affine face equality derives precisely its scalar input equation, in both directions. -/
theorem face_iff (b₁ b₂ u : ZMod 2) (f : geometry.TwoCell) :
    translation (k := ZMod 2) (comparison f) *
        GroupExtension.pathValue geometry (operation b₁ b₂ u) (geometry.twoLeft f) =
      GroupExtension.pathValue geometry (operation b₁ b₂ u) (geometry.twoRight f) ↔
        u = inputValue b₁ b₂ f := by
  rw [comparison,zero_translation,one_mul]
  constructor
  · intro h
    have hz := congrArg (fun g : Op => g 0) h
    simpa only [left_apply,right_apply,zero_add] using hz
  · intro h
    apply AffineEquiv.ext
    intro x
    rw [left_apply,right_apply,h]

end AAT.AG.RelativeRepairComposition.W5AuthoredOperations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5AuthoredOperations
