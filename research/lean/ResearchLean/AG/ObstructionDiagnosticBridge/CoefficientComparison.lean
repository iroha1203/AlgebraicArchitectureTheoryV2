import ResearchLean.AG.ObstructionDiagnosticBridge.PresentationGroup
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Formal.Util.AssertStandardAxioms

/-!
# Integral presentation coefficients compared with rational law-value coefficients

This module constructs the coefficient map from G-125 paper design equation
(4).  A relation component contributes the rational delta function at its
source-generated law-value label.  Composing this map with the derived normal
form `M_R ≃+ FreeAbelianGroup B` gives the comparison

`M_R →+ (LawValueLabel laws → ℚ)`.

The map is defined without a reflection hypothesis.  Under the structural
condition `R_q`, evaluation at the label of a block recovers its integer
coefficient, so the comparison is injective.  Thus `R_q` is materially used
to reflect coefficient equality; injectivity is not stored in the input.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution ResolutionInvariance

universe u

namespace GeneratorPresentation

variable {Source : Type u} {laws : FiniteLawFamily Source}

local instance : DecidableEq (LawValueLabel laws) := Classical.decEq _

/--
Equation (5) on the component normal form: a basis component maps to the
rational delta function at its law-value label.
-/
def blockToLawCoefficients (P : GeneratorPresentation laws) :
    FreeAbelianGroup P.Block →+ (LawValueLabel laws → ℚ) := by
  classical
  exact FreeAbelianGroup.lift fun block label =>
    if P.blockLabel block = label then 1 else 0

/-- Computation of the component coefficient map on one basis element. -/
@[simp]
theorem blockToLawCoefficients_of_apply (P : GeneratorPresentation laws)
    (block : P.Block) (label : LawValueLabel laws) :
    P.blockToLawCoefficients (FreeAbelianGroup.of block) label =
      if P.blockLabel block = label then 1 else 0 := by
  classical
  simp [blockToLawCoefficients]

/--
Under `R_q`, evaluating at a block's label recovers exactly the integer
coefficient of that block, embedded in `ℚ`.
-/
theorem blockToLawCoefficients_apply_blockLabel
    (P : GeneratorPresentation laws) (hReflection : P.ReflectionCondition)
    (x : FreeAbelianGroup P.Block) (block : P.Block) :
    P.blockToLawCoefficients x (P.blockLabel block) =
      (FreeAbelianGroup.coeff block x : ℚ) := by
  classical
  induction x using FreeAbelianGroup.induction_on with
  | C0 => simp [blockToLawCoefficients, FreeAbelianGroup.coeff]
  | C1 generator =>
      by_cases h : generator = block
      · subst generator
        simp [blockToLawCoefficients, FreeAbelianGroup.coeff]
      · have hlabel : P.blockLabel generator ≠ P.blockLabel block := fun heq =>
          h (P.blockLabel_injective hReflection heq)
        simp [blockToLawCoefficients, FreeAbelianGroup.coeff, h, hlabel]
  | Cn generator ih =>
      simp only [map_neg, Pi.neg_apply, Int.cast_neg, ih]
  | Cp left right ihLeft ihRight =>
      simp only [map_add, Pi.add_apply, Int.cast_add, ihLeft, ihRight]

/-- `R_q` makes the component-to-law-value coefficient map injective. -/
theorem blockToLawCoefficients_injective
    (P : GeneratorPresentation laws) (hReflection : P.ReflectionCondition) :
    Function.Injective P.blockToLawCoefficients := by
  intro left right h
  apply (FreeAbelianGroup.equivFinsupp P.Block).injective
  ext block
  have hcoordinate := congrFun h (P.blockLabel block)
  rw [P.blockToLawCoefficients_apply_blockLabel hReflection,
    P.blockToLawCoefficients_apply_blockLabel hReflection] at hcoordinate
  exact_mod_cast hcoordinate

/--
G-125(A)'s coefficient comparison `ε_R`, obtained by composing the derived
presentation normal form with rational law-value delta functions.
-/
def coefficientComparison (P : GeneratorPresentation laws) :
    P.PresentationGroup →+ (LawValueLabel laws → ℚ) :=
  P.blockToLawCoefficients.comp P.presentationToBlocks

/-- Equation (4): a primitive generator class maps to its law-value delta function. -/
@[simp]
theorem coefficientComparison_generatorClass_apply
    (P : GeneratorPresentation laws)
    (generator : PrimitiveGenerator laws) (label : LawValueLabel laws) :
    P.coefficientComparison (P.generatorClass generator) label =
      if generator.label laws = label then 1 else 0 := by
  classical
  simp [coefficientComparison]

/--
G-125(B)'s coefficient-level reflection: `R_q` and the derived presentation
normal form make `ε_R` injective.  No rational-to-integer additive inverse is
assumed or constructed.
-/
theorem coefficientComparison_injective
    (P : GeneratorPresentation laws) (hReflection : P.ReflectionCondition) :
    Function.Injective P.coefficientComparison := by
  intro left right h
  apply P.presentationGroupEquivBlocks.injective
  exact P.blockToLawCoefficients_injective hReflection h

end GeneratorPresentation

/-! ## Positive and negative reflection fixtures -/

namespace CoefficientComparisonFixtures

open GeneratorPresentation ReflectionConditionFixtures

/-- The connected fixture satisfies `R_q`, so its coefficient comparison is injective. -/
theorem connected_coefficientComparison_injective :
    Function.Injective connected.coefficientComparison :=
  connected.coefficientComparison_injective connected_reflectionCondition

/--
Without `R_q`, distinct relation components may have the same law-value label,
and their two basis elements have the same rational coefficient image.
-/
theorem disconnected_blockToLawCoefficients_not_injective :
    ¬ Function.Injective disconnected.blockToLawCoefficients := by
  let leftGenerator : PrimitiveGenerator laws := ⟨PUnit.unit, false⟩
  let rightGenerator : PrimitiveGenerator laws := ⟨PUnit.unit, true⟩
  let leftBlock := disconnected.blockOf leftGenerator
  let rightBlock := disconnected.blockOf rightGenerator
  have hGeneratorNe : leftGenerator ≠ rightGenerator := by
    intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
  have hBlockNe : leftBlock ≠ rightBlock := by
    intro h
    have hrelated : disconnected.Related leftGenerator rightGenerator :=
      Quotient.exact h
    exact hGeneratorNe (eq_of_empty_related hrelated)
  have hLabel : disconnected.blockLabel leftBlock =
      disconnected.blockLabel rightBlock := by
    apply LawValueLabel.ext laws
    · rfl
    · exact HEq.rfl
  intro hinjective
  have hImages :
      disconnected.blockToLawCoefficients (FreeAbelianGroup.of leftBlock) =
        disconnected.blockToLawCoefficients (FreeAbelianGroup.of rightBlock) := by
    ext label
    classical
    simp only [disconnected.blockToLawCoefficients_of_apply]
    rw [hLabel]
  have hBasis := hinjective hImages
  exact hBlockNe (FreeAbelianGroup.of_injective hBasis)

/-- The full presentation coefficient comparison can likewise fail without `R_q`. -/
theorem disconnected_coefficientComparison_not_injective :
    ¬ Function.Injective disconnected.coefficientComparison := by
  intro hComparison
  apply disconnected_blockToLawCoefficients_not_injective
  intro left right h
  have hLeft : disconnected.presentationToBlocks
      (disconnected.blocksToPresentation left) = left := by
    exact congrArg (fun f => f left)
      disconnected.presentationToBlocks_comp_blocksToPresentation
  have hRight : disconnected.presentationToBlocks
      (disconnected.blocksToPresentation right) = right := by
    exact congrArg (fun f => f right)
      disconnected.presentationToBlocks_comp_blocksToPresentation
  have hPresentation : disconnected.blocksToPresentation left =
      disconnected.blocksToPresentation right := by
    apply hComparison
    change disconnected.blockToLawCoefficients
        (disconnected.presentationToBlocks
          (disconnected.blocksToPresentation left)) =
      disconnected.blockToLawCoefficients
        (disconnected.presentationToBlocks
          (disconnected.blocksToPresentation right))
    rw [hLeft, hRight]
    exact h
  have := congrArg disconnected.presentationToBlocks hPresentation
  simpa only [hLeft, hRight] using this

end CoefficientComparisonFixtures

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge

end AAT.AG.ObstructionDiagnosticBridge
