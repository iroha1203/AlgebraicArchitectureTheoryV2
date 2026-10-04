import ResearchLean.AG.ObstructionDiagnosticBridge.CoefficientComparison
import Mathlib.LinearAlgebra.Finsupp.Pi
import Formal.Util.AssertStandardAxioms

/-! # Integral label coordinates derived from the primitive presentation

## Implementation notes

The presentation quotient is transported through its relation blocks before using
finite label functions. This retains the primitive relations and gives pointwise
integer coordinates. Starting with a label group as input would lose that provenance.
Finsupp is the intermediate free-group presentation; finiteness permits full functions
without imposing a further support certificate. The basis is the inverse image of a
delta function, so it belongs to the original presentation rather than a new group.
-/

noncomputable section

namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge
universe u
variable {Source : Type u} [Fintype Source] {laws : FiniteLawFamily Source}
local instance : DecidableEq (LawValueLabel laws) := Classical.decEq _

/-- A: the primitive presentation is the integer coordinate group on generated labels. -/
def integralLabelEquiv (P : GeneratorPresentation laws) (hR : P.ReflectionCondition) :
    P.PresentationGroup ≃+ (LawValueLabel laws → ℤ) :=
  P.presentationGroupEquivBlocks.trans ((FreeAbelianGroup.equivFinsupp P.Block).trans
    ((Finsupp.domCongr (P.blockLabelEquiv hR)).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (LawValueLabel laws)).toAddEquiv))

/-- A: each coordinate recovers the corresponding relation-block multiplicity. -/
@[simp]
theorem integralLabelEquiv_apply (P : GeneratorPresentation laws) (hR : P.ReflectionCondition)
    (m : P.PresentationGroup) (label : LawValueLabel laws) :
    integralLabelEquiv P hR m label =
      FreeAbelianGroup.coeff ((P.blockLabelEquiv hR).symm label) (P.presentationToBlocks m) := rfl

/-- A: the existing coefficient comparison is integer-to-rational coefficient change. -/
theorem coefficientComparison_eq_cast (P : GeneratorPresentation laws)
    (hR : P.ReflectionCondition) (m : P.PresentationGroup) (label : LawValueLabel laws) :
    P.coefficientComparison m label = (integralLabelEquiv P hR m label : ℚ) := by
  have hh := P.blockToLawCoefficients_apply_blockLabel hR (P.presentationToBlocks m)
    ((P.blockLabelEquiv hR).symm label)
  have hl : P.blockLabel ((P.blockLabelEquiv hR).symm label) = label :=
    (P.blockLabelEquiv hR).apply_symm_apply label
  rw [hl] at hh
  exact hh

/-- B: the basis element is constructed in the original primitive presentation. -/
def labelBasis (P : GeneratorPresentation laws) (hR : P.ReflectionCondition)
    (label : LawValueLabel laws) : P.PresentationGroup :=
  (integralLabelEquiv P hR).symm (fun current => if current = label then 1 else 0)

/-- The input-generated basis has exactly its integer delta coordinates. -/
@[simp]
theorem integralLabelEquiv_labelBasis (P : GeneratorPresentation laws)
    (hR : P.ReflectionCondition) (label current : LawValueLabel laws) :
    integralLabelEquiv P hR (labelBasis P hR label) current =
      if current = label then 1 else 0 := by
  exact congrFun ((integralLabelEquiv P hR).apply_symm_apply _) current

/-- B: no source-generated label basis vanishes. -/
theorem labelBasis_ne_zero (P : GeneratorPresentation laws) (hR : P.ReflectionCondition)
    (label : LawValueLabel laws) : labelBasis P hR label ≠ 0 := by
  intro h
  have hh := integralLabelEquiv_labelBasis P hR label label
  rw [h, map_zero] at hh
  simp at hh

/-- A/B: the existing Law evaluation of a generated basis is its rational delta. -/
@[simp]
theorem coefficientComparison_labelBasis (P : GeneratorPresentation laws)
    (hR : P.ReflectionCondition) (label current : LawValueLabel laws) :
    P.coefficientComparison (labelBasis P hR label) current =
      if current = label then 1 else 0 := by
  rw [coefficientComparison_eq_cast P hR, integralLabelEquiv_labelBasis]
  split_ifs <;> norm_num

end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
