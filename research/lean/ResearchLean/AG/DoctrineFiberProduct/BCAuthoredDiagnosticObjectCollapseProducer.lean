import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticPresentationReplacement
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalization

/-!
# All-input diagnostic object-collapse producer

This module generates an authored-support comparison for every authored BC
datum without adding a collapse morphism to the input schema. At each raw
diagnostic component, identity selects identity. A nonidentity component uses
the support package's canonical object normalization when its explicit reading
laws are admissible, and otherwise selects identity. The selected object map is
therefore fixed by the package rather than chosen from an existential.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The package-selected canonical normalization as an endomorphism in the
southwest fiber. -/
noncomputable def authoredSupportCanonicalNormalizationComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell)) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨canonicalObjectNormalizationTotal
      (input.context.supportPackage cell) admissible,
    by
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U)
        (𝟙 input.context.square.semantic.square.southwest)
        (canonicalObjectNormalizationTotal
          (input.context.supportPackage cell) admissible)
        (input.context.endpoint_eq cell)
        (input.context.endpoint_eq cell)
      rw [packageProjection_map]
      exact Category.id_comp _⟩

/-- Select a support endomorphism from the raw diagnostic.  The selection has
no caller-supplied firing or collapse certificate. -/
noncomputable def authoredDiagnosticObjectCollapseComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell := by
  classical
  exact if cochain cell = 1 then
    𝟙 _
  else if admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell) then
    authoredSupportCanonicalNormalizationComponent input cell admissible
  else
    𝟙 _

/-- A vanishing diagnostic component selects identity. -/
theorem authoredDiagnosticObjectCollapseComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (vanishes : cochain cell = 1) :
    authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      𝟙 _ := by
  simp [authoredDiagnosticObjectCollapseComponentAtCochain, vanishes]

/-- A firing component with admissible support readings selects exactly the
package-selected canonical normalization. -/
theorem authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (fires : cochain cell ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell)) :
    authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      authoredSupportCanonicalNormalizationComponent input cell admissible := by
  classical
  rw [authoredDiagnosticObjectCollapseComponentAtCochain]
  simp only [fires, ↓reduceIte, admissible]
  congr

/-- Transport the selected support factor through the authored via-base route. -/
noncomputable def authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredSupportViaBaseRoute input.context).obj cell ⟶
      (authoredSupportViaBaseRoute input.context).obj cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  exact
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
        (authoredDiagnosticObjectCollapseComponentAtCochain
          normalizedInput cochain cell.as))

/-- Normalize the transported selected factor onto the provenance-indexed
via-base route. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell =
      (authoredSupportViaBaseRouteProvenanceIso input.context).hom.app cell ≫
        (bcProvenanceViaBaseRoute input.context.realizationProvenance).map
          (authoredDiagnosticObjectCollapseComponentAtCochain
            input cochain cell.as) ≫
        (authoredSupportViaBaseRouteProvenanceIso input.context).inv.app cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  simp [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain,
    authoredSupportViaBaseRouteProvenanceIso,
    bcProvenanceViaBaseRoute, AuthoredSupportContext.realizationProvenance]
  rfl

/-- Identity raw data remains identity after transport to the via-base route. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cochain_eq : cochain = identityDefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell =
      𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) := by
  rw [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance]
  have component_eq :
      authoredDiagnosticObjectCollapseComponentAtCochain
          input cochain cell.as =
        𝟙 (input.context.supportObject cell.as) := by
    apply authoredDiagnosticObjectCollapseComponentAtCochain_eq_id
    rw [congrFun cochain_eq cell.as]
    rfl
  rw [component_eq]
  have map_identity :
      (bcProvenanceViaBaseRoute input.context.realizationProvenance).map
          (𝟙 (input.context.supportObject cell.as)) =
        𝟙 ((bcProvenanceViaBaseRoute
          input.context.realizationProvenance).obj
            (input.context.supportObject cell.as)) :=
    (bcProvenanceViaBaseRoute
      input.context.realizationProvenance).map_id _
  rw [map_identity]
  simpa only [Category.comp_id] using
    (authoredSupportViaBaseRouteProvenanceIso input.context).hom_inv_id_app cell

/-- The transported selected factor is natural under finite presentation
replacement. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance input.context.square.semantic)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell ≫
        (authoredSupportViaBaseRouteReplacementComparison
          input.context replacement).hom.app cell =
      (authoredSupportViaBaseRouteReplacementComparison
          input.context replacement).hom.app cell ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          (input.replacePresentation replacement) cochain cell := by
  rcases replacement with ⟨replacementPresentation, replacement_eq⟩
  rw [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance,
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance]
  dsimp only [AuthoredBCDatumSquare.replacePresentation]
  have replacementProvenance :
      (input.context.replacePresentation
          ⟨replacementPresentation, replacement_eq⟩).realizationProvenance =
        (⟨replacementPresentation, replacement_eq⟩ :
          BCRealizationProvenance input.context.square.semantic) := by
    congr
  have factorComponent :
      authoredDiagnosticObjectCollapseComponentAtCochain
          ⟨input.context.replacePresentation
              ⟨replacementPresentation, replacement_eq⟩,
            input.twoCellBase, input.authored⟩ cochain cell.as =
        authoredDiagnosticObjectCollapseComponentAtCochain
          input cochain cell.as := rfl
  rw [replacementProvenance, factorComponent]
  unfold authoredSupportViaBaseRouteReplacementComparison
  simp [Category.assoc]
  have naturality :=
    (bcProvenanceViaBaseRouteComparison input.context.realizationProvenance
      ⟨replacementPresentation, replacement_eq⟩).hom.naturality
        (authoredDiagnosticObjectCollapseComponentAtCochain
          input cochain cell.as)
  simpa only [Category.assoc] using congrArg (fun morphism =>
    morphism ≫
      (authoredSupportViaBaseRouteProvenanceIso
        (input.context.replacePresentation
          ⟨replacementPresentation, replacement_eq⟩)).inv.app cell) naturality

/-- The all-input diagnostic object-collapse comparison on a supplied cochain. -/
noncomputable def authoredDiagnosticObjectCollapseComparisonAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredComparisonOfComponents (fun cell =>
    (authoredSupportCanonicalMate input.context).app cell ≫
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell)

@[simp]
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticObjectCollapseComparisonAtCochain
      input cochain).app cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell := rfl

/-- The all-input comparison commutes with finite presentation replacement. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance input.context.square.semantic)
    (cochain : DefectCochain input.toTransportData) :
    (authoredSupportDirectRouteReplacementComparison
        input.context replacement).hom ≫
      authoredDiagnosticObjectCollapseComparisonAtCochain
        (input.replacePresentation replacement) cochain =
    authoredDiagnosticObjectCollapseComparisonAtCochain input cochain ≫
      (authoredSupportViaBaseRouteReplacementComparison
        input.context replacement).hom := by
  apply NatTrans.ext
  funext cell
  rw [NatTrans.comp_app, NatTrans.comp_app,
    authoredDiagnosticObjectCollapseComparisonAtCochain_app,
    authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  have canonicalComponent := congrArg (fun transformation =>
    transformation.app cell)
      (authoredSupportCanonicalMate_replacement input.context replacement)
  simp only [NatTrans.comp_app] at canonicalComponent
  have canonicalComponent' :
      (authoredSupportDirectRouteReplacementComparison
          input.context replacement).hom.app cell ≫
        (authoredSupportCanonicalMate
          (input.replacePresentation replacement).context).app cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        (authoredSupportViaBaseRouteReplacementComparison
          input.context replacement).hom.app cell := by
    simpa only [AuthoredBCDatumSquare.replacePresentation] using
      canonicalComponent
  have factorComponent :=
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_replacement
      input replacement cochain cell
  calc
    _ = ((authoredSupportDirectRouteReplacementComparison
            input.context replacement).hom.app cell ≫
          (authoredSupportCanonicalMate
            (input.replacePresentation replacement).context).app cell) ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          (input.replacePresentation replacement) cochain cell := by
      simp only [Category.assoc]
    _ = ((authoredSupportCanonicalMate input.context).app cell ≫
          (authoredSupportViaBaseRouteReplacementComparison
            input.context replacement).hom.app cell) ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          (input.replacePresentation replacement) cochain cell := by
      rw [canonicalComponent']
    _ = (authoredSupportCanonicalMate input.context).app cell ≫
        ((authoredSupportViaBaseRouteReplacementComparison
            input.context replacement).hom.app cell ≫
          authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
            (input.replacePresentation replacement) cochain cell) := by
      simp only [Category.assoc]
    _ = (authoredSupportCanonicalMate input.context).app cell ≫
        (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell ≫
          (authoredSupportViaBaseRouteReplacementComparison
            input.context replacement).hom.app cell) := by
      rw [factorComponent]
    _ = _ := by simp only [Category.assoc]

/-- Identity raw data makes the all-input generated comparison canonical. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cochain_eq : cochain = identityDefectCochain input.toTransportData) :
    authoredDiagnosticObjectCollapseComparisonAtCochain input cochain =
      authoredSupportCanonicalMate input.context := by
  apply NatTrans.ext
  funext cell
  rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app,
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id
      input cochain cochain_eq cell]
  simp

/-- The named all-input K2 authored comparison producer. -/
noncomputable def generatedAuthoredDiagnosticObjectCollapseComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    AuthoredComparisonProducerSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  fun input => authoredDiagnosticObjectCollapseComparisonAtCochain input
    (initialRawDefectCochain input.toTransportData)

@[simp]
theorem generatedAuthoredDiagnosticObjectCollapseComparison_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    generatedAuthoredDiagnosticObjectCollapseComparison input =
      authoredDiagnosticObjectCollapseComparisonAtCochain input
        (initialRawDefectCochain input.toTransportData) := rfl

/-- The fixed public authored-relative coherence predicate. -/
def MateCoherentRel
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    MateCoherentRelSignature U :=
  mateCoherentRelEquation generatedAuthoredDiagnosticObjectCollapseComparison
    (authoredSupportCanonicalMateFamily U)

@[simp]
theorem MateCoherentRel_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    MateCoherentRel U input =
      AuthoredSupportComparison.Agrees
        (generatedAuthoredDiagnosticObjectCollapseComparison input)
        (authoredSupportCanonicalMate input.context) := rfl

/-- Any strict datum whose initial raw cochain is identity satisfies the fixed
public relation. -/
theorem mateCoherentRel_of_initialRawDefect_eq_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain_eq : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData) :
    MateCoherentRel U input := by
  rw [MateCoherentRel_apply]
  exact authoredDiagnosticObjectCollapseComparisonAtCochain_eq_canonical
    input _ cochain_eq

/-- The named all-input producer commutes with finite presentation replacement. -/
theorem generatedAuthoredDiagnosticObjectCollapseComparison_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance input.context.square.semantic) :
    (authoredSupportDirectRouteReplacementComparison
        input.context replacement).hom ≫
      generatedAuthoredDiagnosticObjectCollapseComparison
        (input.replacePresentation replacement) =
    generatedAuthoredDiagnosticObjectCollapseComparison input ≫
      (authoredSupportViaBaseRouteReplacementComparison
        input.context replacement).hom := by
  simpa only [AuthoredBCDatumSquare.replacePresentation_toTransportData] using
    authoredDiagnosticObjectCollapseComparisonAtCochain_replacement
      input replacement (initialRawDefectCochain input.toTransportData)

/-- The fixed public relation is invariant under finite presentation
replacement of the same semantic square and authored table. -/
theorem mateCoherentRel_replacePresentation_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance input.context.square.semantic) :
    MateCoherentRel U (input.replacePresentation replacement) ↔
      MateCoherentRel U input := by
  rw [MateCoherentRel_apply, MateCoherentRel_apply]
  unfold AuthoredSupportComparison.Agrees
  constructor
  · intro replaced_eq
    apply (cancel_mono
      (authoredSupportViaBaseRouteReplacementComparison
        input.context replacement).hom).1
    rw [← generatedAuthoredDiagnosticObjectCollapseComparison_replacement
      input replacement]
    rw [replaced_eq]
    exact authoredSupportCanonicalMate_replacement input.context replacement
  · intro original_eq
    apply (cancel_epi
      (authoredSupportDirectRouteReplacementComparison
        input.context replacement).hom).1
    rw [generatedAuthoredDiagnosticObjectCollapseComparison_replacement
      input replacement]
    rw [original_eq]
    exact (authoredSupportCanonicalMate_replacement
      input.context replacement).symm

/-! ## Genuine edge-reselection representatives of the public relation -/

/-- Change only the edge trivializations of an authored datum by the existing
G-106 reselection action. The authored comparator table and semantic square
remain fixed. -/
def AuthoredBCDatumSquare.reselectEdges
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (reselection : EdgeReselection input.context.lift) :
    AuthoredBCDatumSquare U where
  context := {
    square := input.context.square
    lift := reselectLiftData input.context.lift reselection
    endpoint_eq := input.context.endpoint_eq
  }
  twoCellBase := reselectedTwoCellBase input.toTransportData reselection
  authored := input.authored

@[simp]
theorem AuthoredBCDatumSquare.reselectEdges_context
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (reselection : EdgeReselection input.context.lift) :
    (input.reselectEdges reselection).context.square = input.context.square := rfl

/-- The initial canonical comparator of a reselected datum is the original
canonical comparator at that genuine G-106 reselection coordinate. -/
theorem AuthoredBCDatumSquare.canonicalTwoCellComparator_reselectEdges
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (reselection : EdgeReselection input.context.lift)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    canonicalTwoCellComparator
        (input.reselectEdges reselection).toTransportData 1 cell =
      canonicalTwoCellComparator input.toTransportData reselection cell := by
  let original := input.toTransportData
  have left_eq :
      reselectedPathLift (reselectLiftData original.lift reselection) 1
          (input.context.square.semantic.diagnostic.twoLeft cell) =
        reselectedPathLift original.lift reselection
          (input.context.square.semantic.diagnostic.twoLeft cell) := by
    simpa only [one_mul] using
      (reselectedPathLift_mul original.lift 1 reselection
        (input.context.square.semantic.diagnostic.twoLeft cell)).symm
  have right_eq :
      reselectedPathLift (reselectLiftData original.lift reselection) 1
          (input.context.square.semantic.diagnostic.twoRight cell) =
        reselectedPathLift original.lift reselection
          (input.context.square.semantic.diagnostic.twoRight cell) := by
    simpa only [one_mul] using
      (reselectedPathLift_mul original.lift 1 reselection
        (input.context.square.semantic.diagnostic.twoRight cell)).symm
  letI : (packageProjection U).IsStronglyCocartesian
      (reselectedPathLift original.lift reselection
        (input.context.square.semantic.diagnostic.twoLeft cell)).base
      (reselectedPathLift original.lift reselection
        (input.context.square.semantic.diagnostic.twoLeft cell)) :=
    reselectedPathLift_isStronglyCocartesian original.lift reselection
      (input.context.square.semantic.diagnostic.twoLeft cell)
  apply PackageFiberAut.ext_of_strong_fac
    (reselectedPathLift original.lift reselection
      (input.context.square.semantic.diagnostic.twoLeft cell))
  calc
    _ = (reselectedPathLift (reselectLiftData original.lift reselection) 1
          (input.context.square.semantic.diagnostic.twoLeft cell)).comp
        (PackageFiberAut.hom
          (canonicalTwoCellComparator
            (input.reselectEdges reselection).toTransportData 1 cell)) := by
      rw [left_eq]
    _ = reselectedPathLift (reselectLiftData original.lift reselection) 1
          (input.context.square.semantic.diagnostic.twoRight cell) := by
      exact canonicalTwoCellComparator_fac
        (input.reselectEdges reselection).toTransportData 1 cell
    _ = reselectedPathLift original.lift reselection
          (input.context.square.semantic.diagnostic.twoRight cell) := right_eq
    _ = _ := (canonicalTwoCellComparator_fac
      input.toTransportData reselection cell).symm

/-- The public relation's initial raw cochain on a reselected datum is exactly
the original datum's raw cochain at that orbit coordinate. -/
theorem AuthoredBCDatumSquare.initialRawDefectCochain_reselectEdges
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (reselection : EdgeReselection input.context.lift) :
    initialRawDefectCochain (input.reselectEdges reselection).toTransportData =
      rawDefectCochain input.toTransportData reselection := by
  funext cell
  unfold initialRawDefectCochain rawDefectCochain rawTwoCellDefect
  rw [input.canonicalTwoCellComparator_reselectEdges reselection cell]
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
