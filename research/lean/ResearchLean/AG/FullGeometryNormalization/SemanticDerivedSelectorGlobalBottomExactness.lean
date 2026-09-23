import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorGlobalImageBottom

/-!
# Exactness of the bottom-fixed full complete-geometry comparison

The actual bottom kernels of the unrestricted endpoint and image comparison
groups form a split short exact sequence.  Its lift fibers are right torsors
for the restricted kernel.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 3000000

section

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) =
    input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- Split short exactness for the genuine bottom kernels of the unrestricted
complete-geometry comparison. -/
theorem semanticExactGlobalBottomComparison_shortExact :
    let p := semanticExactGlobalBottomCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := semanticExactGlobalBottomCompatibleRestrictionHom input
    interpretation z omega k g endpoint_eq square_isPullback
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · rw [MonoidHom.mulExact_iff]
    exact p.ker.range_subtype.symm
  · intro pair
    exact ⟨semanticExactGlobalBottomComparisonSectionHom input interpretation z
      omega k g endpoint_eq square_isPullback pair,
      semanticExactGlobalBottomComparisonSection_rightInverse input
        interpretation z omega k g endpoint_eq square_isPullback pair⟩

/-- Raw bottom-fixed lifts of one image-side bottom-fixed comparison. -/
noncomputable abbrev SemanticExactGlobalBottomComparisonLiftFiber
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback) :=
  {raw : SemanticExactGlobalBottomRawComparison input interpretation z omega k
      g endpoint_eq square_isPullback //
    semanticExactGlobalBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback raw = pair}

/-- Every bottom-fixed image comparison has a bottom-fixed raw lift. -/
theorem semanticExactGlobalBottomComparisonLiftFiber_nonempty
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback) :
    Nonempty (SemanticExactGlobalBottomComparisonLiftFiber input interpretation
      z omega k g endpoint_eq square_isPullback pair) :=
  ⟨⟨semanticExactGlobalBottomComparisonSectionHom input interpretation z omega
      k g endpoint_eq square_isPullback pair,
    semanticExactGlobalBottomComparisonSection_rightInverse input
      interpretation z omega k g endpoint_eq square_isPullback pair⟩⟩

/-- Two bottom-fixed lifts differ by a unique right kernel factor. -/
theorem semanticExactGlobalBottomComparisonLiftFiber_unique_rightKernel
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback)
    (first second : SemanticExactGlobalBottomComparisonLiftFiber input
      interpretation z omega k g endpoint_eq square_isPullback pair) :
    let p := semanticExactGlobalBottomCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback
    ∃! kernelValue : p.ker,
      first.1 * (kernelValue : SemanticExactGlobalBottomRawComparison input
        interpretation z omega k g endpoint_eq square_isPullback) = second.1 := by
  dsimp
  let p := semanticExactGlobalBottomCompatibleRestrictionHom input interpretation
    z omega k g endpoint_eq square_isPullback
  let displacement : SemanticExactGlobalBottomRawComparison input interpretation
      z omega k g endpoint_eq square_isPullback := first.1⁻¹ * second.1
  have inKernel : displacement ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      first.property, second.property, inv_mul_cancel]
  refine ⟨⟨displacement, inKernel⟩, ?_, ?_⟩
  · simp [displacement]
  · intro other otherEquality
    apply Subtype.ext
    exact mul_left_cancel (otherEquality.trans (by simp [displacement] :
      second.1 = first.1 * displacement))

/-- Right multiplication by the restricted bottom kernel. -/
noncomputable instance semanticExactGlobalBottomComparisonLiftFiberSMul
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback) :
    let p := semanticExactGlobalBottomCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback
    SMul p.kerᵐᵒᵖ (SemanticExactGlobalBottomComparisonLiftFiber input
      interpretation z omega k g endpoint_eq square_isPullback pair) := by
  dsimp
  let p := semanticExactGlobalBottomCompatibleRestrictionHom input interpretation
    z omega k g endpoint_eq square_isPullback
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- The opposite kernel acts on each lift fiber by right multiplication. -/
noncomputable instance semanticExactGlobalBottomComparisonLiftFiberMulAction
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback) :
    let p := semanticExactGlobalBottomCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback
    MulAction p.kerᵐᵒᵖ (SemanticExactGlobalBottomComparisonLiftFiber input
      interpretation z omega k g endpoint_eq square_isPullback pair) := by
  dsimp
  letI := semanticExactGlobalBottomComparisonLiftFiberSMul input interpretation
    z omega k g endpoint_eq square_isPullback pair
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 *
        (((MulOpposite.unop second).1 :
          SemanticExactGlobalBottomRawComparison input interpretation z omega
            k g endpoint_eq square_isPullback) *
          ((MulOpposite.unop first).1 :
            SemanticExactGlobalBottomRawComparison input interpretation z omega
              k g endpoint_eq square_isPullback)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : SemanticExactGlobalBottomRawComparison input interpretation z omega
        k g endpoint_eq square_isPullback) = lift.1
    simp

/-- Each bottom-fixed lift fiber is a right torsor for the restricted
kernel. -/
theorem semanticExactGlobalBottomComparisonLiftFiber_existsUnique_smul_eq
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback)
    (first second : SemanticExactGlobalBottomComparisonLiftFiber input
      interpretation z omega k g endpoint_eq square_isPullback pair) :
    let p := semanticExactGlobalBottomCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases semanticExactGlobalBottomComparisonLiftFiber_unique_rightKernel input
      interpretation z omega k g endpoint_eq square_isPullback pair first
      second with ⟨displacement, hdisplacement, hunique⟩
  refine ⟨MulOpposite.op displacement, ?_, ?_⟩
  · apply Subtype.ext
    exact hdisplacement
  · intro other hother
    apply MulOpposite.unop_injective
    apply hunique
    have hvalue := congrArg
      (fun lift : SemanticExactGlobalBottomComparisonLiftFiber input
        interpretation z omega k g endpoint_eq square_isPullback pair =>
        lift.1) hother
    exact hvalue

end

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
