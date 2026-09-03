import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeKaroubiImage
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeObservableExactness
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeRawFailureLocus
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeTransportIdentityClassification

/-!
# G-116 arbitrary-carrier target surface

The selector implementation is computationally parameterized by decidable Atom
equality.  The mathematical G-116 targets quantify over every Atom carrier, so
this module chooses classical decidable equality internally and exposes the
target clauses without a caller-supplied typeclass premise.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence
open CategoryTheory.Idempotents

noncomputable section

local instance {U : AtomCarrier.{u}} : DecidableEq U.Atom :=
  Classical.decEq U.Atom

/-- G-116(c1), arbitrary-carrier form: every transported cell projector is
idempotent. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell :=
  authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp input cochain cell

/-- G-116(c1), arbitrary-carrier form: the projector has identity Atom
equivalence. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
      input cochain cell).1.upper.atomEquiv = Equiv.refl U.Atom :=
  authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv
    input cochain cell

/-- G-116(d), arbitrary-carrier form of the explicit Karoubi image
isomorphism. -/
noncomputable def authoredDiagnosticObjectCollapseKaroubiIso_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredDiagnosticImageSourceKaroubi input cochain cell ≅
      authoredDiagnosticImageTargetKaroubi input cochain cell :=
  authoredDiagnosticObjectCollapseKaroubiIso input cochain cell

/-- G-116(f), arbitrary-carrier coordinate preservation by `E_c`. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (object : ArchitectureObject U)
    (axis : ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.Axis) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        ((authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell).1.upper.objectMap object) axis =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        object axis :=
  authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate
    input cochain cell fires admissible object axis

/-- G-116(f), arbitrary-carrier equation-residual preservation by `E_c`. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (W : Site.ContextCategoryObject
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.Index)
    (atom : U.Atom) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        ((authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell).1.upper.objectMap object) index atom =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        object index atom :=
  authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual
    input cochain cell fires admissible W object index atom

/-- G-116(f), arbitrary-carrier coordinate comparison of `β_c` and `α_c`. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (object : ArchitectureObject U)
    (axis : ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.Axis) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        (((authoredDiagnosticObjectCollapseComparisonAtCochain
          input cochain).app cell).1.upper.objectMap object) axis =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
          object) axis :=
  authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate
    input cochain cell fires admissible object axis

/-- G-116(f), arbitrary-carrier residual comparison of `β_c` and `α_c`. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (W : Site.ContextCategoryObject
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.Index)
    (atom : U.Atom) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        (((authoredDiagnosticObjectCollapseComparisonAtCochain
          input cochain).app cell).1.upper.objectMap object) index atom =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
          object) index atom :=
  authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual
    input cochain cell fires admissible W object index atom

/-- G-116(g), arbitrary-carrier cellwise raw-failure chain. -/
theorem authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (IsIso ((authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell) ↔
      IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell)) ∧
    (IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell) ↔
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell =
        𝟙 ((authoredSupportViaBaseRoute input.context).obj cell)) :=
  authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus input cochain cell

/-- G-116(g2), arbitrary-carrier positive classification branch. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff_universal
    {U : AtomCarrier.{u}}
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell =
      𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) ↔
    ¬ (cochain cell.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible
        (input.context.supportPackage cell.as) ∧
      ¬ Function.Injective (canonicalObjectNormalization
        (input.context.supportPackage cell.as))) :=
  authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff
    input cochain cell

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end

end AAT.AG.DoctrineFiberProduct
