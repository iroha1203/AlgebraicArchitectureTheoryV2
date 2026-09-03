import ResearchLean.AG.DoctrineFiberProduct.DistinctArchitectureObjects
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationAPI
import ResearchLean.AG.DoctrineFiberProduct.DiagnosticObjectCollapseSelectorAPI
import ResearchLean.AG.DoctrineFiberProduct.BCProvenanceViaBaseRouteAPI
import ResearchLean.AG.DiagnosticConservativity.TransportEquivalence

/-!
# G-116 transport identity-reflection classification

This module discharges the positive branch of G-116(g2).  The via-base
transport functor is an equivalence: canonical covariant transport is the
forward functor of the G-113 equivalence, while selected cartesian reindexing
is the right adjoint of such a forward equivalence.  It therefore reflects the
identity of the raw selected endomorphism.  The selector's three branches then
give the fixed classification.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Selected cartesian reindexing along every realized presentation is an
equivalence.  Its left adjoint is the G-113 canonical transport equivalence. -/
theorem selectedCoreFiberReindexFunctor_isEquivalence
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    (selectedCoreFiberReindexFunctor input).IsEquivalence := by
  letI : (coreFiberTransportFunctor input.semantic.hom).IsEquivalence :=
    semanticGlobalTransport_isEquivalence input.semantic.hom
  exact (coreTransportReindexAdjunction input).isEquivalence_right_of_isEquivalence_left

/-- The provenance-indexed via-base route is an equivalence for every finite
presentation, not only for an identity presentation. -/
theorem bcProvenanceViaBaseRoute_isEquivalence
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    (bcProvenanceViaBaseRoute provenance).IsEquivalence := by
  letI : (coreFiberTransportFunctor input.square.bottom).IsEquivalence :=
    semanticGlobalTransport_isEquivalence input.square.bottom
  letI : (selectedCoreFiberReindexFunctor
      provenance.rightProvenance.toRealizableHom).IsEquivalence :=
    selectedCoreFiberReindexFunctor_isEquivalence
      provenance.rightProvenance.toRealizableHom
  rw [bcProvenanceViaBaseRoute_eq]
  infer_instance

/-- A faithful functor reflects equality of an endomorphism with the identity. -/
theorem functor_map_eq_id_iff_of_faithful
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) [F.Faithful] {X : C} (endomorphism : X ⟶ X) :
    F.map endomorphism = 𝟙 (F.obj X) ↔ endomorphism = 𝟙 X := by
  constructor
  · intro equality
    apply F.map_injective
    simpa only [F.map_id] using equality
  · rintro rfl
    exact F.map_id X

/-- Conjugation by an isomorphism reflects equality with the identity. -/
theorem iso_conjugate_eq_id_iff
    {C : Type u} [Category C] {X Y : C} (iso : X ≅ Y)
    (endomorphism : Y ⟶ Y) :
    iso.hom ≫ endomorphism ≫ iso.inv = 𝟙 X ↔
      endomorphism = 𝟙 Y := by
  constructor
  · intro equality
    apply (cancel_epi iso.hom).1
    apply (cancel_mono iso.inv).1
    simpa only [Category.assoc, Category.comp_id, Category.id_comp,
      Iso.hom_inv_id] using equality
  · rintro rfl
    simpa only [Category.id_comp, Category.comp_id] using iso.hom_inv_id

/-- The transported projector is the identity exactly when the raw selected
support endomorphism is the identity.  Faithfulness of the G-113 route is the
identity-reflection step. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell =
      𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) ↔
    authoredDiagnosticObjectCollapseComponentAtCochain
        input cochain cell.as =
      𝟙 (input.context.supportObject cell.as) := by
  rw [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance]
  let route := bcProvenanceViaBaseRoute input.context.realizationProvenance
  let routeIso := authoredSupportViaBaseRouteProvenanceIso input.context
  have conjugation := iso_conjugate_eq_id_iff
    (routeIso.app cell)
    (route.map (authoredDiagnosticObjectCollapseComponentAtCochain
      input cochain cell.as))
  have reflection :
      route.map (authoredDiagnosticObjectCollapseComponentAtCochain
          input cochain cell.as) =
          𝟙 (route.obj (input.context.supportObject cell.as)) ↔
        authoredDiagnosticObjectCollapseComponentAtCochain
            input cochain cell.as =
          𝟙 (input.context.supportObject cell.as) := by
    letI : route.IsEquivalence :=
      bcProvenanceViaBaseRoute_isEquivalence
        input.context.realizationProvenance
    letI : route.Faithful := by infer_instance
    exact functor_map_eq_id_iff_of_faithful route _
  exact conjugation.trans reflection

/-- Canonical normalization is never injective: it identifies the two
different decorations supplied by G-116(e1) over any fixed configuration. -/
theorem canonicalObjectNormalization_not_injective
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ¬ Function.Injective (canonicalObjectNormalization P) := by
  rcases exists_distinct_architectureObjects_over_configuration P.configuration with
    ⟨first, second, distinct, firstConfiguration, secondConfiguration⟩
  intro injective
  apply distinct
  apply injective
  exact canonicalObjectNormalization_eq_of_configuration_eq P
    (firstConfiguration.trans secondConfiguration.symm)

/-- The raw selector is the identity exactly outside the simultaneous firing,
admissible, noninjective branch.  The case split follows the selector's own
definition, and noninjectivity is generated by G-116(e1). -/
theorem authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell =
        𝟙 (input.context.supportObject cell) ↔
      ¬ (cochain cell ≠ 1 ∧
        CanonicalObjectNormalizationAdmissible
          (input.context.supportPackage cell) ∧
        ¬ Function.Injective (canonicalObjectNormalization
          (input.context.supportPackage cell))) := by
  classical
  by_cases vanishes : cochain cell = 1
  · constructor
    · intro _ selectedBranch
      exact selectedBranch.1 vanishes
    · intro _
      exact authoredDiagnosticObjectCollapseComponentAtCochain_eq_id
        input cochain cell vanishes
  · by_cases admissible : CanonicalObjectNormalizationAdmissible
        (input.context.supportPackage cell)
    · rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
          input cochain cell vanishes admissible]
      constructor
      · intro equality selectedBranch
        rcases selectedBranch with ⟨_, _, notInjective⟩
        apply notInjective
        have objectMapEquality := congrArg
          (fun morphism : input.context.supportObject cell ⟶
              input.context.supportObject cell => morphism.1.upper.objectMap)
          equality
        change canonicalObjectNormalization
            (input.context.supportPackage cell) = _root_.id at objectMapEquality
        rw [objectMapEquality]
        exact Function.injective_id
      · intro outsideSelectedBranch
        exact (outsideSelectedBranch ⟨vanishes, admissible,
          canonicalObjectNormalization_not_injective
            (input.context.supportPackage cell)⟩).elim
    · have selectedIdentity :
          authoredDiagnosticObjectCollapseComponentAtCochain
              input cochain cell = 𝟙 (input.context.supportObject cell) := by
          exact
            authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_of_not_admissible
              input cochain cell vanishes admissible
      constructor
      · intro _ selectedBranch
        exact admissible selectedBranch.2.1
      · intro _
        exact selectedIdentity

/-- G-116(g2), positive branch: for every authored input, cochain, and cell,
the transported projector is the identity exactly outside the firing,
admissible, noninjective selector branch. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
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
  (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff_raw
    input cochain cell).trans
      (authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_iff
        input cochain cell.as)

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
