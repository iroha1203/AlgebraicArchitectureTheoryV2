import ResearchLean.AG.RealizationReconstruction.G122GeneratedComparisonCongruence
import Formal.Util.AssertStandardAxioms

/-!
# Syntax evaluation for the three fixed finite-axis-fold comparisons

Cycle 45 indexed the required five-factor, generated-cochain, and constant-one
comparisons but evaluated its three codes directly to already constructed
semantic arrows.  Cycles 51--52 now supply source-provenanced typed syntax.
This module sends the same three codes through those actual syntax leaves and
places their evaluations in the common underlying endpoint-package Hom type.

The generated and constant-one cell inputs differ only in their cochain, so
their direct and via-base package values are definitionally the same.  Their
syntax terms nevertheless retain the distinct original inputs.  On the common
semantic surface, the generated term remains different from the five-factor
term, while the constant-one term agrees with it; both exact case fibers and
the noninjectivity result are recovered.

## Implementation notes

No transport proof, target arrow, or equality certificate is stored in a
syntax term.  The common codomain is the independently defined Hom between the
generated-cochain endpoint packages, and definitional equality of the two
fixed package constructions permits the constant-one syntax evaluation to
inhabit it.  This is the required fixed three-case connection only, not a
general transport or a full presentation decoder.
-/

namespace AAT.AG.RealizationReconstruction

open GeometryTransport

/-- Transport a morphism evaluated from the constant-one syntax endpoints to
the definitionally equal fixed generated-cochain endpoint-package Hom type. -/
noncomputable def finiteAxisFoldTransportIdentityCochainHom
    (f : G122GeneratedGeometryObject.Hom finiteAxisFoldG122FamilyInput
      (.direct finiteAxisFoldIdentityCochainG122CellInput)
      (.viaBase finiteAxisFoldIdentityCochainG122CellInput)) :
    G122GeneratedGeometryObject.Hom finiteAxisFoldG122FamilyInput
      (.direct finiteAxisFoldG122CellInput)
      (.viaBase finiteAxisFoldG122CellInput) := by
  change GeometryTotalHom
      ((G122GeneratedGeometryObject.direct
        finiteAxisFoldIdentityCochainG122CellInput).package
          finiteAxisFoldG122FamilyInput)
      ((G122GeneratedGeometryObject.viaBase
        finiteAxisFoldIdentityCochainG122CellInput).package
          finiteAxisFoldG122FamilyInput) at f
  change GeometryTotalHom
      ((G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput).package
        finiteAxisFoldG122FamilyInput)
      ((G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput).package
        finiteAxisFoldG122FamilyInput)
  rw [finiteAxisFold_direct_package_identityCochain,
    finiteAxisFold_viaBase_package_identityCochain]
  exact f

/-- Evaluate each fixed comparison code through its source-provenanced Cycle
51 syntax leaf on the common generated-cochain endpoint-package Hom type. -/
noncomputable def finiteAxisFoldComparisonSyntaxEvaluate :
    FiniteAxisFoldComparisonCode →
      G122GeneratedGeometryObject.Hom finiteAxisFoldG122FamilyInput
        (.direct finiteAxisFoldG122CellInput)
        (.viaBase finiteAxisFoldG122CellInput)
  | .barAlpha => G122GeneratedComparisonSyntax.evaluate
      (.barAlpha finiteAxisFoldG122CellInput)
  | .generatedBarBeta => G122GeneratedComparisonSyntax.evaluate
      (.barBeta finiteAxisFoldG122CellInput)
  | .identityBarBeta => finiteAxisFoldTransportIdentityCochainHom
      (G122GeneratedComparisonSyntax.evaluate
        (.barBeta finiteAxisFoldIdentityCochainG122CellInput))

/-- Every fixed case is represented by one source-provenanced syntax leaf. -/
noncomputable def finiteAxisFoldComparisonSyntaxSize :
    FiniteAxisFoldComparisonCode → Nat
  | .barAlpha => G122GeneratedComparisonSyntax.size
      (.barAlpha finiteAxisFoldG122CellInput)
  | .generatedBarBeta => G122GeneratedComparisonSyntax.size
      (.barBeta finiteAxisFoldG122CellInput)
  | .identityBarBeta => G122GeneratedComparisonSyntax.size
      (.barBeta finiteAxisFoldIdentityCochainG122CellInput)

/-- The three fixed terms each have exactly one syntax node. -/
@[simp] theorem finiteAxisFoldComparisonSyntaxSize_eq_one
    (code : FiniteAxisFoldComparisonCode) :
    finiteAxisFoldComparisonSyntaxSize code = 1 := by
  cases code <;> rfl

/-- Syntax-mediated evaluation agrees exactly with the Cycle 45 semantic
evaluator on every fixed code. -/
@[simp] theorem finiteAxisFoldComparisonSyntaxEvaluate_eq_evaluate
    (code : FiniteAxisFoldComparisonCode) :
    finiteAxisFoldComparisonSyntaxEvaluate code = code.evaluate := by
  cases code <;> rfl

/-- The generated-cochain syntax term evaluates differently from the actual
five-factor syntax term on the common endpoints. -/
theorem finiteAxisFoldSyntax_generatedBarBeta_ne_barAlpha :
    finiteAxisFoldComparisonSyntaxEvaluate .generatedBarBeta ≠
      finiteAxisFoldComparisonSyntaxEvaluate .barAlpha := by
  simpa using FiniteAxisFoldComparisonCode.generatedBarBeta_ne_barAlpha

/-- The constant-one syntax term evaluates to the same actual comparison as
the five-factor syntax term on the common endpoints. -/
theorem finiteAxisFoldSyntax_identityBarBeta_eq_barAlpha :
    finiteAxisFoldComparisonSyntaxEvaluate .identityBarBeta =
      finiteAxisFoldComparisonSyntaxEvaluate .barAlpha := by
  simpa using FiniteAxisFoldComparisonCode.evaluate_identityBarBeta_eq_barAlpha

/-- Exact syntax-mediated fiber over the five-factor comparison. -/
theorem finiteAxisFoldSyntax_evaluate_eq_barAlpha_iff
    (code : FiniteAxisFoldComparisonCode) :
    finiteAxisFoldComparisonSyntaxEvaluate code =
        finiteAxisFoldComparisonSyntaxEvaluate .barAlpha ↔
      code = .barAlpha ∨ code = .identityBarBeta := by
  simpa using FiniteAxisFoldComparisonCode.evaluate_eq_barAlpha_iff code

/-- Exact syntax-mediated fiber over the generated noninvertible comparison. -/
theorem finiteAxisFoldSyntax_evaluate_eq_generatedBarBeta_iff
    (code : FiniteAxisFoldComparisonCode) :
    finiteAxisFoldComparisonSyntaxEvaluate code =
        finiteAxisFoldComparisonSyntaxEvaluate .generatedBarBeta ↔
      code = .generatedBarBeta := by
  simpa using FiniteAxisFoldComparisonCode.evaluate_eq_generatedBarBeta_iff code

/-- The syntax-mediated evaluator is not injective because the constant-one
and five-factor source-provenanced leaves have the same semantic value. -/
theorem finiteAxisFoldComparisonSyntaxEvaluate_not_injective :
    ¬ Function.Injective finiteAxisFoldComparisonSyntaxEvaluate := by
  intro injective
  have equalCodes :
      FiniteAxisFoldComparisonCode.identityBarBeta = .barAlpha :=
    injective finiteAxisFoldSyntax_identityBarBeta_eq_barAlpha
  cases equalCodes

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
