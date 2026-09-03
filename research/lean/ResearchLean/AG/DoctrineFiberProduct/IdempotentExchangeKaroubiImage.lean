import Mathlib.CategoryTheory.Idempotents.Karoubi
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationNaturality

/-!
# G-116 Karoubi image exactness

This module discharges G-116(d) at each authored diagnostic cell.  The source
idempotent is the cochain-indexed authored diagnostic comparison followed by
the inverse canonical mate; the target idempotent is the selected cell
projector.  Their comparison is an isomorphism in the Karoubi envelope.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open CategoryTheory.Idempotents
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 1000000

/-- G-116(d) source object in the Karoubi envelope, with projector
`β_c ≫ inv α_c`.  Idempotence is generated from the component factorization
and G-116(c1). -/
noncomputable def authoredDiagnosticImageSourceKaroubi
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    Karoubi (CoreFiber input.context.square.semantic.square.northeast) where
  X := (authoredSupportDirectRoute input.context).obj cell
  p := (authoredDiagnosticObjectCollapseComparisonAtCochain
      input cochain).app cell ≫
    inv ((authoredSupportCanonicalMate input.context).app cell)
  idem := by
    rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun morphism =>
        (authoredSupportCanonicalMate input.context).app cell ≫ morphism ≫
          inv ((authoredSupportCanonicalMate input.context).app cell))
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp
        input cochain cell)

/-- G-116(d) target object in the Karoubi envelope, with projector `E_c`. -/
noncomputable def authoredDiagnosticImageTargetKaroubi
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    Karoubi (CoreFiber input.context.square.semantic.square.northeast) where
  X := (authoredSupportViaBaseRoute input.context).obj cell
  p := authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
    input cochain cell
  idem := authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp
    input cochain cell

/-- Evaluation API for the source-image projector. -/
theorem authoredDiagnosticImageSourceKaroubi_p
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticImageSourceKaroubi input cochain cell).p =
      (authoredDiagnosticObjectCollapseComparisonAtCochain
          input cochain).app cell ≫
        inv ((authoredSupportCanonicalMate input.context).app cell) :=
  rfl

/-- Evaluation API for the target-image projector. -/
theorem authoredDiagnosticImageTargetKaroubi_p
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticImageTargetKaroubi input cochain cell).p =
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell :=
  rfl

/-- G-116(d): `β_c` is an isomorphism from its conjugate source image to the
`E_c` image in the Karoubi envelope.  Its inverse is
`E_c ≫ inv α_c`; no splitting data is supplied. -/
noncomputable def authoredDiagnosticObjectCollapseKaroubiIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredDiagnosticImageSourceKaroubi input cochain cell ≅
      authoredDiagnosticImageTargetKaroubi input cochain cell where
  hom :=
    { f := (authoredDiagnosticObjectCollapseComparisonAtCochain
          input cochain).app cell
      comm := by
        rw [authoredDiagnosticImageSourceKaroubi_p,
          authoredDiagnosticImageTargetKaroubi_p]
        rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
        simp [Category.assoc,
          authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp] }
  inv :=
    { f := authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell ≫
        inv ((authoredSupportCanonicalMate input.context).app cell)
      comm := by
        rw [authoredDiagnosticImageSourceKaroubi_p,
          authoredDiagnosticImageTargetKaroubi_p]
        rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
        simp [Category.assoc,
          authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp] }
  hom_inv_id := by
    have beta_comp :
        (authoredDiagnosticObjectCollapseComparisonAtCochain
            input cochain).app cell ≫
          authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
            input cochain cell =
        (authoredDiagnosticObjectCollapseComparisonAtCochain
            input cochain).app cell := by
      rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
      simp [Category.assoc,
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp]
    apply Karoubi.Hom.ext
    change ((authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell ≫
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell) ≫
          inv ((authoredSupportCanonicalMate input.context).app cell) =
      (authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell ≫
          inv ((authoredSupportCanonicalMate input.context).app cell)
    rw [beta_comp]
  inv_hom_id := by
    have inv_beta :
        (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
            input cochain cell ≫
          inv ((authoredSupportCanonicalMate input.context).app cell)) ≫
            (authoredDiagnosticObjectCollapseComparisonAtCochain
              input cochain).app cell =
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell := by
      rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
      simp [Category.assoc,
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp]
    apply Karoubi.Hom.ext
    exact inv_beta

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
