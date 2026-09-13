import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonSection
import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction

/-!
# Exactness and lift fibers for the actual canonical comparison section

The actual `barAlpha` comparison section makes the restricted normalization
homomorphism split-surjective.  This module records the resulting group short
exact sequence and the free, transitive right action of its kernel on every
lift fiber.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct ComparisonInformationLoss

/-- Raw comparison-preserving changes for the actual admissible `barAlpha`. -/
noncomputable abbrev AuthoredExactCanonicalRawComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :=
  rawGeometryNormalizationComparisonSubgroup
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom

/-- Normalized comparison-preserving changes for the actual admissible
`barAlpha`. -/
noncomputable abbrev AuthoredExactCanonicalNormalizedComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :=
  normalizedGeometryComparisonSubgroup
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom

/-- The actual restricted canonical-normalization homomorphism is surjective,
with its preimage supplied by the constructed section. -/
theorem authoredExactCanonicalComparisonHom_surjective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    Function.Surjective
      (geometryNormalizationComparisonSubgroupHom
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) := by
  intro pair
  exact ⟨authoredExactCanonicalComparisonSectionHom A z k g admissible pair,
    authoredExactCanonicalComparisonSection_rightInverse
      A z k g admissible pair⟩

/-- The kernel inclusion followed by the actual restricted normalization is a
split short exact sequence of groups. -/
theorem authoredExactCanonicalComparison_shortExact
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    let p := geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := geometryNormalizationComparisonSubgroupHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
  exact ⟨Subtype.val_injective,
    by
      rw [MonoidHom.mulExact_iff]
      exact p.ker.range_subtype.symm,
    authoredExactCanonicalComparisonHom_surjective A z k g admissible⟩

/-- The fiber of actual raw comparison lifts over one normalized compatible
change. -/
noncomputable abbrev AuthoredExactCanonicalComparisonLiftFiber
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedComparisonSubgroup
      A z k g admissible) :=
  {a : AuthoredExactCanonicalRawComparisonSubgroup A z k g admissible //
    geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom a = t}

/-- Right multiplication by the restricted kernel acts on every actual lift
fiber. -/
noncomputable instance authoredExactCanonicalComparisonLiftFiberSMul
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedComparisonSubgroup
      A z k g admissible) :
    let p := geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    SMul p.kerᵐᵒᵖ
      (AuthoredExactCanonicalComparisonLiftFiber A z k g admissible t) := by
  dsimp
  let p := geometryNormalizationComparisonSubgroupHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- The actual right-kernel action satisfies the group action laws. -/
noncomputable instance authoredExactCanonicalComparisonLiftFiberMulAction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedComparisonSubgroup
      A z k g admissible) :
    let p := geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    MulAction p.kerᵐᵒᵖ
      (AuthoredExactCanonicalComparisonLiftFiber A z k g admissible t) := by
  dsimp
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 *
        (((MulOpposite.unop second).1 :
          AuthoredExactCanonicalRawComparisonSubgroup A z k g admissible) *
          ((MulOpposite.unop first).1 :
            AuthoredExactCanonicalRawComparisonSubgroup A z k g admissible)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : AuthoredExactCanonicalRawComparisonSubgroup A z k g admissible) = lift.1
    simp

/-- The restricted kernel action is free on every actual lift fiber. -/
theorem authoredExactCanonicalComparisonLiftFiber_action_free
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedComparisonSubgroup
      A z k g admissible)
    (lift : AuthoredExactCanonicalComparisonLiftFiber A z k g admissible t) :
    let p := geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    Function.Injective (fun kernelValue : p.kerᵐᵒᵖ => kernelValue • lift) := by
  dsimp
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have underlying := congrArg
    (fun value : AuthoredExactCanonicalComparisonLiftFiber
      A z k g admissible t => value.1) equality
  exact mul_left_cancel underlying

/-- The restricted kernel action is transitive on every actual lift fiber. -/
theorem authoredExactCanonicalComparisonLiftFiber_action_transitive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedComparisonSubgroup
      A z k g admissible)
    (first second : AuthoredExactCanonicalComparisonLiftFiber
      A z k g admissible t) :
    let p := geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    ∃ kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  let displacement : AuthoredExactCanonicalRawComparisonSubgroup
      A z k g admissible := first.1⁻¹ * second.1
  have inKernel : displacement ∈
      (geometryNormalizationComparisonSubgroupHom
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, first.property, second.property,
      inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, inKernel⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Every two actual lifts have a unique right-kernel displacement. -/
theorem authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedComparisonSubgroup
      A z k g admissible)
    (first second : AuthoredExactCanonicalComparisonLiftFiber
      A z k g admissible t) :
    let p := geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases authoredExactCanonicalComparisonLiftFiber_action_transitive
      A z k g admissible t first second with ⟨kernelValue, equality⟩
  refine ⟨kernelValue, equality, ?_⟩
  intro other otherEquality
  exact authoredExactCanonicalComparisonLiftFiber_action_free
    A z k g admissible t first (otherEquality.trans equality.symm)

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
