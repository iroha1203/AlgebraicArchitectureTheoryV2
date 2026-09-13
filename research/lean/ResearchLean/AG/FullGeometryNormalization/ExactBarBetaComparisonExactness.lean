import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaComparisonSection
import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction

/-!
# Exactness and lift fibers for the actual selector comparison

The selector-wise section of the actual restricted comparison homomorphism
makes that homomorphism split-surjective.  This module records the resulting
group short exact sequence and the free, transitive right action of its
restricted kernel on every lift fiber.

The kernel here is the kernel on the raw-comparison-compatible domain
`AuthoredExactCentralizingRawComparisonSubgroup`.  It is deliberately distinct
from the ambient endpoint kernel `authoredExactEndpointRestrictionHom.ker` used
by the selector-reflection witness.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct TransportCoherence ComparisonInformationLoss

set_option synthInstance.maxHeartbeats 200000

/-- The actual selector comparison restriction is surjective, with every
preimage supplied by the constructed selector-wise section. -/
theorem authoredExactCompatibleRestrictionHom_surjective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Function.Surjective
      (authoredExactCompatibleRestrictionHom A z omega k g) := by
  intro pair
  exact ⟨authoredExactComparisonSectionHom A z omega k g pair,
    authoredExactComparisonSection_rightInverse A z omega k g pair⟩

/-- The literal restricted-kernel inclusion followed by the actual selector
comparison restriction is a split short exact sequence of groups.  Its kernel
is taken inside the raw-compatible domain, not inside the ambient endpoint
group used in the reflection theorem. -/
theorem authoredExactCompatibleRestriction_shortExact
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    let p := authoredExactCompatibleRestrictionHom A z omega k g
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := authoredExactCompatibleRestrictionHom A z omega k g
  exact ⟨Subtype.val_injective,
    by
      rw [MonoidHom.mulExact_iff]
      exact p.ker.range_subtype.symm,
    authoredExactCompatibleRestrictionHom_surjective A z omega k g⟩

/-- The fiber of raw-compatible actual comparison lifts over one Karoubi
comparison automorphism. -/
noncomputable abbrev AuthoredExactComparisonLiftFiber
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :=
  {a : AuthoredExactCentralizingRawComparisonSubgroup A z omega k g //
    authoredExactCompatibleRestrictionHom A z omega k g a = t}

/-- Right multiplication by the restricted kernel acts on every actual
selector lift fiber.  This is not an action of the ambient endpoint kernel. -/
noncomputable instance authoredExactComparisonLiftFiberSMul
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    let p := authoredExactCompatibleRestrictionHom A z omega k g
    SMul p.kerᵐᵒᵖ
      (AuthoredExactComparisonLiftFiber A z omega k g t) := by
  dsimp
  let p := authoredExactCompatibleRestrictionHom A z omega k g
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- The right action of the actual restricted kernel satisfies the group
action laws. -/
noncomputable instance authoredExactComparisonLiftFiberMulAction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    let p := authoredExactCompatibleRestrictionHom A z omega k g
    MulAction p.kerᵐᵒᵖ
      (AuthoredExactComparisonLiftFiber A z omega k g t) := by
  dsimp
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 *
        (((MulOpposite.unop second).1 :
          AuthoredExactCentralizingRawComparisonSubgroup A z omega k g) *
          ((MulOpposite.unop first).1 :
            AuthoredExactCentralizingRawComparisonSubgroup A z omega k g)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : AuthoredExactCentralizingRawComparisonSubgroup A z omega k g) = lift.1
    simp

/-- The restricted-kernel action is free on every actual selector lift
fiber. -/
theorem authoredExactComparisonLiftFiber_action_free
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactKaroubiComparisonSubgroup A z omega k g)
    (lift : AuthoredExactComparisonLiftFiber A z omega k g t) :
    let p := authoredExactCompatibleRestrictionHom A z omega k g
    Function.Injective (fun kernelValue : p.kerᵐᵒᵖ => kernelValue • lift) := by
  dsimp
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have underlying := congrArg
    (fun value : AuthoredExactComparisonLiftFiber A z omega k g t => value.1)
    equality
  exact mul_left_cancel underlying

/-- The restricted-kernel action is transitive on every actual selector lift
fiber. -/
theorem authoredExactComparisonLiftFiber_action_transitive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactKaroubiComparisonSubgroup A z omega k g)
    (first second : AuthoredExactComparisonLiftFiber A z omega k g t) :
    let p := authoredExactCompatibleRestrictionHom A z omega k g
    ∃ kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  let displacement : AuthoredExactCentralizingRawComparisonSubgroup
      A z omega k g := first.1⁻¹ * second.1
  have inKernel : displacement ∈
      (authoredExactCompatibleRestrictionHom A z omega k g).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, first.property, second.property,
      inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, inKernel⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Every two actual selector lifts have a unique displacement in the
restricted kernel on the raw-compatible domain. -/
theorem authoredExactComparisonLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactKaroubiComparisonSubgroup A z omega k g)
    (first second : AuthoredExactComparisonLiftFiber A z omega k g t) :
    let p := authoredExactCompatibleRestrictionHom A z omega k g
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases authoredExactComparisonLiftFiber_action_transitive
      A z omega k g t first second with ⟨kernelValue, equality⟩
  refine ⟨kernelValue, equality, ?_⟩
  intro other otherEquality
  exact authoredExactComparisonLiftFiber_action_free
    A z omega k g t first (otherEquality.trans equality.symm)

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
