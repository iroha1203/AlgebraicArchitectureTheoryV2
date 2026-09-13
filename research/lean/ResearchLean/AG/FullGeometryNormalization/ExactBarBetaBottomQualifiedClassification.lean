import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaBottomQualifiedGroups
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaComparisonExactness
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaReflection

/-!
# Bottom-qualified selector classification for the actual exact comparison

This module restricts the already constructed selector section to the literal
package-bottom endpoint subgroups.  It also transports the selected ambient
normalization-kernel witness into that typed hierarchy and proves the two
reflection cases there.  Finally it records split exactness and the free,
transitive restricted-kernel action on every bottom-qualified lift fiber.

The selected ambient witness belongs to the kernel of the ambient endpoint
restriction but not to the raw-compatible domain.  The lift-fiber action uses
the different kernel of the restricted comparison homomorphism.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 3000000

/-! ## Bottom-qualified section and endpoint retention -/

/-- The actual selector section restricted to the typed bottom-qualified
comparison groups. -/
noncomputable def authoredExactBottomComparisonSectionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g →*
      AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g :=
  (authoredExactBottomRawComparisonEquiv A z omega k g).symm.toMonoidHom.comp
    ((authoredExactComparisonSectionHom A z omega k g).comp
      (authoredExactBottomKaroubiComparisonEquiv A z omega k g).toMonoidHom)

/-- Forgetting the bottom-qualified wrapper gives the accepted selector
section on the accepted comparison groups. -/
@[simp]
theorem authoredExactBottomComparisonSectionHom_reassociates
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    authoredExactBottomRawComparisonEquiv A z omega k g
        (authoredExactBottomComparisonSectionHom A z omega k g pair) =
      authoredExactComparisonSectionHom A z omega k g
        (authoredExactBottomKaroubiComparisonEquiv A z omega k g pair) := by
  rfl

/-- The bottom-qualified selector section is a right inverse of the actual
bottom-qualified comparison restriction. -/
theorem authoredExactBottomComparisonSection_rightInverse
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    authoredExactBottomCompatibleRestrictionHom A z omega k g
        (authoredExactBottomComparisonSectionHom A z omega k g pair) = pair := by
  apply (authoredExactBottomKaroubiComparisonEquiv A z omega k g).injective
  rw [authoredExactBottomCompatibleRestriction_reassociates,
    authoredExactBottomComparisonSectionHom_reassociates]
  exact authoredExactComparisonSection_rightInverse A z omega k g _

/-- The bottom-qualified section retains the source package-bottom map. -/
theorem authoredExactBottomComparisonSection_source_packageBase
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactBottomComparisonSectionHom
      A z omega k g pair).1.1.1.1.hom.1.base.base =
        pair.1.1.1.hom.f.1.base.base := by
  change (authoredExactComparisonSectionHom A z omega k g
      (authoredExactBottomKaroubiComparisonEquiv A z omega k g pair)).1.1.1.hom.1.base.base = _
  exact authoredExactComparisonSection_source_packageBase A z omega k g _

/-- The bottom-qualified section retains the source coefficient map. -/
theorem authoredExactBottomComparisonSection_source_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactBottomComparisonSectionHom
      A z omega k g pair).1.1.1.1.hom.1.geometry.coefficientHom =
        pair.1.1.1.hom.f.1.geometry.coefficientHom := by
  change (authoredExactComparisonSectionHom A z omega k g
      (authoredExactBottomKaroubiComparisonEquiv A z omega k g pair)).1.1.1.hom.1.geometry.coefficientHom = _
  exact authoredExactComparisonSection_source_coefficientHom A z omega k g _

/-- The bottom-qualified section retains the target package-bottom map. -/
theorem authoredExactBottomComparisonSection_target_packageBase
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactBottomComparisonSectionHom
      A z omega k g pair).1.1.1.2.hom.1.base.base =
        pair.1.1.2.hom.f.1.base.base := by
  change (authoredExactComparisonSectionHom A z omega k g
      (authoredExactBottomKaroubiComparisonEquiv A z omega k g pair)).1.1.2.hom.1.base.base = _
  exact authoredExactComparisonSection_target_packageBase A z omega k g _

/-- The bottom-qualified section retains the target coefficient map. -/
theorem authoredExactBottomComparisonSection_target_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactBottomComparisonSectionHom
      A z omega k g pair).1.1.1.2.hom.1.geometry.coefficientHom =
        pair.1.1.2.hom.f.1.geometry.coefficientHom := by
  change (authoredExactComparisonSectionHom A z omega k g
      (authoredExactBottomKaroubiComparisonEquiv A z omega k g pair)).1.1.2.hom.1.geometry.coefficientHom = _
  exact authoredExactComparisonSection_target_coefficientHom A z omega k g _

/-! ## Typed selected witness and reflection -/

/-- The selected ambient normalization-kernel pair, transported into the
actual bottom-qualified centralizing endpoint group. -/
noncomputable def authoredExactSelectedBottomAmbientKernelPair
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g :=
  (authoredExactBottomCentralizingEquiv A z omega k g).symm
    (authoredExactSelectedAmbientKernelCentralizingPair
      A z omega k g selected)

/-- The source component of the typed selected witness is nonidentity. -/
theorem authoredExactSelectedBottomAmbientKernelPair_source_ne_one
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactSelectedBottomAmbientKernelPair
      A z omega k g selected).1.1.1 ≠ 1 := by
  change (ambientKernelGeometryFiberAut
    (authoredExactDirectGeometryAt A z k g)
    (authoredExactDirectGeometryAt_admissible A z k g selected.2)) ≠ 1
  exact ambientKernelGeometryFiberAut_ne_one _ _

/-- The typed selected witness has identity package-bottom and coefficient
maps at both endpoints. -/
theorem authoredExactSelectedBottomAmbientKernelPair_bottom_coefficient
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    let pair := authoredExactSelectedBottomAmbientKernelPair
      A z omega k g selected
    pair.1.1.1.hom.1.base.base =
        𝟙 (packagePoint (authoredExactDirectGeometryAt A z k g).1.core) ∧
      pair.1.1.1.hom.1.geometry.coefficientHom = RingHom.id k ∧
      pair.1.1.2.hom.1.base.base =
        𝟙 (packagePoint (authoredExactViaBaseGeometryAt A z k g).1.core) ∧
      pair.1.1.2.hom.1.geometry.coefficientHom = RingHom.id k := by
  dsimp only
  refine ⟨(authoredExactSelectedBottomAmbientKernelPair A z omega k g selected).2.1,
    ?_, (authoredExactSelectedBottomAmbientKernelPair A z omega k g selected).2.2,
    ?_⟩
  · exact ambientKernelGeometryFiberHom_coefficientHom _ _
  · rfl

/-- The typed selected witness lies in the ambient bottom endpoint kernel. -/
theorem authoredExactSelectedBottomAmbientKernelPair_mem_ambient_ker
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactSelectedBottomAmbientKernelPair A z omega k g selected ∈
      (authoredExactBottomEndpointRestrictionHom A z omega k g).ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  exact authoredExactSelectedAmbientKernelCentralizingPair_restriction
    A z omega k g selected

/-- The typed selected witness belongs to the bottom-qualified ambient
preimage of the Karoubi comparison group. -/
theorem authoredExactSelectedBottomAmbientKernelPair_mem_preimage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactSelectedBottomAmbientKernelPair A z omega k g selected ∈
      (AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactBottomEndpointRestrictionHom A z omega k g) := by
  rw [authoredExactBottomEndpointRestriction_preimage_eq_barBeta]
  change authoredExactSelectedAmbientKernelCentralizingPair
      A z omega k g selected ∈
    centralizingCompatibleSubgroup
      (authoredExactBarBetaAt A z omega k g)
      (authoredExactBarEAt A z omega k g)
      (authoredExactBarDAt A z omega k g)
  have h := authoredExactSelectedAmbientKernelCentralizingPair_mem_preimage
    A z omega k g selected
  rw [authoredExactEndpointRestriction_preimage_eq_barBeta] at h
  exact h

/-- The typed selected witness does not belong to the bottom-qualified raw
comparison subgroup. -/
theorem authoredExactSelectedBottomAmbientKernelPair_not_mem_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactSelectedBottomAmbientKernelPair A z omega k g selected ∉
      AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g := by
  intro h
  exact authoredExactSelectedAmbientKernelCentralizingPair_not_mem_raw
    A z omega k g selected h

/-- On the selected branch, bottom-qualified reflection fails by the explicit
typed ambient witness. -/
theorem authoredExactBottomEndpointRestriction_preimage_ne_raw_of_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactBottomEndpointRestrictionHom A z omega k g) ≠
      AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g := by
  intro hEq
  have hmem := authoredExactSelectedBottomAmbientKernelPair_mem_preimage
    A z omega k g selected
  rw [hEq] at hmem
  exact authoredExactSelectedBottomAmbientKernelPair_not_mem_raw
    A z omega k g selected hmem

/-- Off the selector, the typed bottom-qualified ambient preimage is exactly
the typed bottom-qualified raw comparison subgroup. -/
theorem authoredExactBottomEndpointRestriction_preimage_eq_raw_of_not_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))) :
    (AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactBottomEndpointRestrictionHom A z omega k g) =
      AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g := by
  have hbeta : authoredExactBarBetaAt A z omega k g =
      (authoredExactBarAlphaIsoAt A z k g).hom := by
    rw [authoredExactBarBetaAt_factor,
      authoredExactBarDAt_eq_id A z omega k g notSelected]
    simp
  rw [authoredExactBottomEndpointRestriction_preimage_eq_barBeta]
  ext pair
  change
    pair.1.1.1.hom ≫ authoredExactBarBetaAt A z omega k g =
        authoredExactBarBetaAt A z omega k g ≫ pair.1.1.2.hom ↔
      pair.1.1.1.hom ≫ (authoredExactBarAlphaIsoAt A z k g).hom =
        (authoredExactBarAlphaIsoAt A z k g).hom ≫ pair.1.1.2.hom
  rw [hbeta]

/-- The selector reflection classification inside the actual bottom-qualified
endpoint hierarchy. -/
theorem authoredExactBottomEndpointRestriction_preimage_eq_raw_iff_not_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactBottomEndpointRestrictionHom A z omega k g) =
      AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g) ↔
      ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)) := by
  constructor
  · intro hEq selected
    exact authoredExactBottomEndpointRestriction_preimage_ne_raw_of_selected
      A z omega k g selected hEq
  · exact authoredExactBottomEndpointRestriction_preimage_eq_raw_of_not_selected
      A z omega k g

/-! ## Split exactness and typed lift fibers -/

/-- The bottom-qualified selector comparison restriction is split-surjective. -/
theorem authoredExactBottomCompatibleRestrictionHom_surjective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Function.Surjective
      (authoredExactBottomCompatibleRestrictionHom A z omega k g) := by
  intro pair
  exact ⟨authoredExactBottomComparisonSectionHom A z omega k g pair,
    authoredExactBottomComparisonSection_rightInverse A z omega k g pair⟩

/-- The restricted bottom-qualified kernel inclusion and comparison map form
a split short exact sequence. -/
theorem authoredExactBottomCompatibleRestriction_shortExact
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
  exact ⟨Subtype.val_injective,
    by
      rw [MonoidHom.mulExact_iff]
      exact p.ker.range_subtype.symm,
    authoredExactBottomCompatibleRestrictionHom_surjective A z omega k g⟩

/-- The fiber of bottom-qualified raw lifts over a fixed bottom-qualified
Karoubi comparison change. -/
noncomputable abbrev AuthoredExactBottomComparisonLiftFiber
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :=
  {a : AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g //
    authoredExactBottomCompatibleRestrictionHom A z omega k g a = t}

/-- Right multiplication by the restricted bottom-qualified kernel acts on
each typed lift fiber. -/
noncomputable instance authoredExactBottomComparisonLiftFiberSMul
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
    SMul p.kerᵐᵒᵖ
      (AuthoredExactBottomComparisonLiftFiber A z omega k g t) := by
  dsimp
  let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- The restricted bottom-qualified kernel action satisfies the group action
laws. -/
noncomputable instance authoredExactBottomComparisonLiftFiberMulAction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g) :
    let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
    MulAction p.kerᵐᵒᵖ
      (AuthoredExactBottomComparisonLiftFiber A z omega k g t) := by
  dsimp
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 * (((MulOpposite.unop second).1 :
        AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g) *
      ((MulOpposite.unop first).1 :
        AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : AuthoredExactBottomCentralizingRawComparisonSubgroup
        A z omega k g) = lift.1
    simp

/-- The restricted-kernel action is free on every bottom-qualified lift
fiber. -/
theorem authoredExactBottomComparisonLiftFiber_action_free
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g)
    (lift : AuthoredExactBottomComparisonLiftFiber A z omega k g t) :
    let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
    Function.Injective (fun kernelValue : p.kerᵐᵒᵖ => kernelValue • lift) := by
  dsimp
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have underlying := congrArg
    (fun value : AuthoredExactBottomComparisonLiftFiber
      A z omega k g t => value.1) equality
  exact mul_left_cancel underlying

/-- The restricted-kernel action is transitive on every bottom-qualified lift
fiber. -/
theorem authoredExactBottomComparisonLiftFiber_action_transitive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g)
    (first second : AuthoredExactBottomComparisonLiftFiber A z omega k g t) :
    let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
    ∃ kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  let displacement : AuthoredExactBottomCentralizingRawComparisonSubgroup
      A z omega k g := first.1⁻¹ * second.1
  have inKernel : displacement ∈
      (authoredExactBottomCompatibleRestrictionHom A z omega k g).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, first.property, second.property,
      inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, inKernel⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Every two bottom-qualified lifts have a unique displacement in the
restricted comparison kernel. -/
theorem authoredExactBottomComparisonLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (t : AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g)
    (first second : AuthoredExactBottomComparisonLiftFiber A z omega k g t) :
    let p := authoredExactBottomCompatibleRestrictionHom A z omega k g
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases authoredExactBottomComparisonLiftFiber_action_transitive
      A z omega k g t first second with ⟨kernelValue, equality⟩
  exact ⟨kernelValue, equality, fun other otherEquality =>
    authoredExactBottomComparisonLiftFiber_action_free
      A z omega k g t first (otherEquality.trans equality.symm)⟩

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
