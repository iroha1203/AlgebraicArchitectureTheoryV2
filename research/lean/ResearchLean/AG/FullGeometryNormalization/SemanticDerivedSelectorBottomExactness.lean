import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorBottomSection

/-!
# Bottom-qualified exactness of the semantic selector comparison

For every semantic input and diagnostic selector, the actual bottom-fixed
comparison restriction is split exact. Its lift fibers carry the right
torsor action of the restricted kernel.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

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

/-- The bottom-fixed selector comparison is a split group short exact sequence. -/
theorem semanticExactBottomComparison_shortExact :
    let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
    omega k g endpoint_eq square_isPullback
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · rw [MonoidHom.mulExact_iff]
    exact p.ker.range_subtype.symm
  · intro pair
    exact ⟨semanticExactBottomComparisonSectionHom input interpretation z
      omega k g endpoint_eq square_isPullback pair,
      semanticExactBottomComparisonSection_rightInverse input interpretation z
        omega k g endpoint_eq square_isPullback pair⟩

/-- Bottom-fixed raw compatible lifts of one image comparison change. -/
noncomputable abbrev SemanticExactBottomComparisonLiftFiber
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) :=
  {raw : SemanticExactBottomRawComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback //
    semanticExactBottomCompatibleRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback raw = pair}

/-- Every bottom-fixed image comparison change has a raw compatible lift. -/
theorem semanticExactBottomComparisonLiftFiber_nonempty
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) :
    Nonempty (SemanticExactBottomComparisonLiftFiber input interpretation z
      omega k g endpoint_eq square_isPullback pair) :=
  ⟨⟨semanticExactBottomComparisonSectionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair,
    semanticExactBottomComparisonSection_rightInverse input interpretation z
      omega k g endpoint_eq square_isPullback pair⟩⟩

/-- Two bottom-fixed lifts differ by a unique right kernel factor. -/
theorem semanticExactBottomComparisonLiftFiber_unique_rightKernel
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback)
    (first second : SemanticExactBottomComparisonLiftFiber input interpretation z
      omega k g endpoint_eq square_isPullback pair) :
    let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback
    ∃! kernelValue : p.ker,
      first.1 * (kernelValue : SemanticExactBottomRawComparisonSubgroup input
        interpretation z omega k g endpoint_eq square_isPullback) = second.1 := by
  dsimp
  let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
    omega k g endpoint_eq square_isPullback
  let displacement : SemanticExactBottomRawComparisonSubgroup input
      interpretation z omega k g endpoint_eq square_isPullback :=
    first.1⁻¹ * second.1
  have inKernel : displacement ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      first.property, second.property, inv_mul_cancel]
  refine ⟨⟨displacement, inKernel⟩, ?_, ?_⟩
  · simp [displacement]
  · intro other otherEquality
    apply Subtype.ext
    exact mul_left_cancel (otherEquality.trans (by simp [displacement] :
      second.1 = first.1 * displacement))

/-- Right multiplication by the restricted bottom-fixed kernel. -/
noncomputable instance semanticExactBottomComparisonLiftFiberSMul
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) :
    let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback
    SMul p.kerᵐᵒᵖ (SemanticExactBottomComparisonLiftFiber input interpretation z
      omega k g endpoint_eq square_isPullback pair) := by
  dsimp
  let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
    omega k g endpoint_eq square_isPullback
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- Opposite-kernel multiplication satisfies the right action laws. -/
noncomputable instance semanticExactBottomComparisonLiftFiberMulAction
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) :
    let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback
    MulAction p.kerᵐᵒᵖ (SemanticExactBottomComparisonLiftFiber input interpretation z
      omega k g endpoint_eq square_isPullback pair) := by
  dsimp
  letI := semanticExactBottomComparisonLiftFiberSMul input interpretation z
    omega k g endpoint_eq square_isPullback pair
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 *
        (((MulOpposite.unop second).1 :
          SemanticExactBottomRawComparisonSubgroup input interpretation z omega
            k g endpoint_eq square_isPullback) *
          ((MulOpposite.unop first).1 :
            SemanticExactBottomRawComparisonSubgroup input interpretation z omega
              k g endpoint_eq square_isPullback)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : SemanticExactBottomRawComparisonSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback) = lift.1
    simp

/-- The bottom-fixed lift fiber is a right torsor for the restricted kernel. -/
theorem semanticExactBottomComparisonLiftFiber_existsUnique_smul_eq
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback)
    (first second : SemanticExactBottomComparisonLiftFiber input interpretation z
      omega k g endpoint_eq square_isPullback pair) :
    let p := semanticExactBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases semanticExactBottomComparisonLiftFiber_unique_rightKernel input
      interpretation z omega k g endpoint_eq square_isPullback pair first second with
    ⟨displacement, hdisplacement, hunique⟩
  refine ⟨MulOpposite.op displacement, ?_, ?_⟩
  · apply Subtype.ext
    exact hdisplacement
  · intro other hother
    apply MulOpposite.unop_injective
    apply hunique
    have hvalue := congrArg
      (fun lift : SemanticExactBottomComparisonLiftFiber input interpretation z
        omega k g endpoint_eq square_isPullback pair => lift.1) hother
    exact hvalue

end

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
