import ResearchLean.AG.RealizationComparisonIdempotents.GeneratedQualifiedComparison
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeKaroubiImage

/-!
# Placement of the G-116 Karoubi comparison

This file constructs the first part of G-119(C).  The actual G-116 Karoubi
isomorphism is placed as a comparison object in the northeast core fiber and
then mapped, by the fiber inclusion, to the core-package comparison category.
The two endpoint projectors retain their existing formulas and become
identities after package projection.

## Implementation notes

The comparison object uses the existing Karoubi isomorphism's hom rather than
reconstructing a raw isomorphism.  Fiber verticality, not an added certificate,
proves the two base-identity statements.  No identity condition is imposed on
the comparison morphism itself.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation CrossStageCoherence TransportCoherence
open DoctrineFiberProduct

universe u

/-- The comparison-category functor induced by forgetting a core-fiber object
to its underlying core package. -/
noncomputable def coreFiberComparisonInclusion
    {U : AtomCarrier.{u}} (X : ExtractionInstance U) :
    RealizationComparisonCategory (CoreFiber X) ⥤
      RealizationComparisonCategory (AATCorePackage U) :=
  arrowKaroubiMap
    (CategoryTheory.Functor.Fiber.fiberInclusion : CoreFiber X ⥤ AATCorePackage U)

/-- Place the hom of the existing G-116 Karoubi isomorphism as a comparison
object in the northeast core fiber. -/
noncomputable def authoredDiagnosticKaroubiComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    RealizationComparisonCategory
      (CoreFiber input.context.square.semantic.square.northeast) :=
  Arrow.mk (authoredDiagnosticObjectCollapseKaroubiIso input cochain cell).hom

/-- Normalization rule: the placed comparison retains the existing source
Karoubi object. -/
@[simp]
theorem authoredDiagnosticKaroubiComparison_left
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticKaroubiComparison input cochain cell).left =
      authoredDiagnosticImageSourceKaroubi input cochain cell :=
  rfl

/-- Normalization rule: the placed comparison retains the existing target
Karoubi object. -/
@[simp]
theorem authoredDiagnosticKaroubiComparison_right
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticKaroubiComparison input cochain cell).right =
      authoredDiagnosticImageTargetKaroubi input cochain cell :=
  rfl

/-- Normalization rule: the placed comparison's underlying fiber morphism is
the existing authored diagnostic comparison `β`. -/
@[simp]
theorem authoredDiagnosticKaroubiComparison_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticKaroubiComparison input cochain cell).hom.f =
      (authoredDiagnosticObjectCollapseComparisonAtCochain input cochain).app cell :=
  rfl

/-- The inverse of the existing Karoubi isomorphism has underlying component
`E ≫ α⁻¹`. -/
@[simp]
theorem authoredDiagnosticObjectCollapseKaroubiIso_inv_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticObjectCollapseKaroubiIso input cochain cell).inv.f =
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell ≫
        inv ((authoredSupportCanonicalMate input.context).app cell) :=
  rfl

/-- Forget the placed G-116 comparison from the northeast core fiber to the
core-package comparison category `M(E_core)`. -/
noncomputable def authoredDiagnosticCoreComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    RealizationComparisonCategory (AATCorePackage U) :=
  (coreFiberComparisonInclusion input.context.square.semantic.square.northeast).obj
    (authoredDiagnosticKaroubiComparison input cochain cell)

/-- Normalization rule: forgetting retains the source route's underlying core package. -/
@[simp]
theorem authoredDiagnosticCoreComparison_left_X
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).left.X =
      ((authoredSupportDirectRoute input.context).obj cell).1 :=
  rfl

/-- Normalization rule: forgetting retains the source projector `α⁻¹β` in
Lean's composition order `β ≫ α⁻¹`. -/
@[simp]
theorem authoredDiagnosticCoreComparison_left_p
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).left.p =
      ((authoredDiagnosticObjectCollapseComparisonAtCochain input cochain).app cell ≫
        inv ((authoredSupportCanonicalMate input.context).app cell)).1 :=
  rfl

/-- Normalization rule: forgetting retains the target route's underlying core package. -/
@[simp]
theorem authoredDiagnosticCoreComparison_right_X
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).right.X =
      ((authoredSupportViaBaseRoute input.context).obj cell).1 :=
  rfl

/-- Normalization rule: forgetting retains the target cell projector `E`. -/
@[simp]
theorem authoredDiagnosticCoreComparison_right_p
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).right.p =
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell).1 :=
  rfl

/-- Normalization rule: forgetting retains the complete underlying comparison `β`. -/
@[simp]
theorem authoredDiagnosticCoreComparison_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).hom.f =
      ((authoredDiagnosticObjectCollapseComparisonAtCochain input cochain).app cell).1 :=
  rfl

/-- Every endomorphism inside a core fiber becomes the identity under package
projection. -/
theorem coreFiberEndomorphism_packageProjection_identity
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : CoreFiber X) (f : P ⟶ P) :
    f.1.base = 𝟙 (packagePoint P.1) := by
  letI := f.2
  have h := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (𝟙 X) f.1
  rw [packageProjection_map] at h
  simpa using h

/-- The forgotten source projector becomes the identity at the bottom category. -/
theorem authoredDiagnosticCoreComparison_source_projected_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).left.p.base =
      𝟙 (packagePoint (authoredDiagnosticCoreComparison input cochain cell).left.X) :=
  coreFiberEndomorphism_packageProjection_identity _ _

/-- The forgotten target projector becomes the identity at the bottom category. -/
theorem authoredDiagnosticCoreComparison_target_projected_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticCoreComparison input cochain cell).right.p.base =
      𝟙 (packagePoint (authoredDiagnosticCoreComparison input cochain cell).right.X) :=
  coreFiberEndomorphism_packageProjection_identity _ _

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
