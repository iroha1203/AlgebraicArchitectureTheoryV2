import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticComparisonWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticPresentationReplacementWitnesses

/-!
# Public authored-support Beck--Chevalley coherence relation

This module closes the public K2 interface around the comparison constructed
directly from the G-106 authored defect.  At each cochain coordinate the
construction retains the actual raw component and follows it by the fixed
direct-first, same-boundary-pairwise diagnostic fold algorithm.  The public
producer is its initial raw-cochain specialization; the public relation is the
equation with the canonical mate on authored support.

The interface records the laws that make this more than a name for a natural
transformation: direct authored-comparator proof use, the exact initial-to-orbit
bridge, strict and lax controls over a nontrivial orbit, and finite-presentation
replacement.  No comparison, fold, expected equality, or noninvertibility
certificate is accepted from the caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Executable Atom equality for the finite public-relation witnesses. -/
local instance finiteAuthoredPublicMateAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Public generated comparison and relation -/

/-- The public authored comparison construction at one actual G-106 cochain. -/
noncomputable def authoredBCComparisonAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredDiagnosticComparisonAtCochain input cochain

/-- The K2 authored-table producer is the generated initial-cochain comparison. -/
noncomputable def authoredBCComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    AuthoredComparisonProducerSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  fun input => authoredBCComparisonAtCochain input
    (initialRawDefectCochain input.toTransportData)

/-- Relative coherence of the public construction at a supplied orbit coordinate. -/
def MateCoherentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) : Prop :=
  AuthoredSupportComparison.Agrees
    (authoredBCComparisonAtCochain input cochain)
    (authoredSupportCanonicalMate input.context)

/-- The fixed public authored-support coherence relation required by K2. -/
def MateCoherentRel
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    MateCoherentRelSignature U :=
  mateCoherentRelEquation authoredBCComparison
    (authoredSupportCanonicalMateFamily U)

/-! ## Application and proof-use laws -/

/-- The public producer is literally the initial coordinate of its orbit family. -/
@[simp]
theorem authoredBCComparison_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredBCComparison input =
      authoredBCComparisonAtCochain input
        (initialRawDefectCochain input.toTransportData) := rfl

/-- The public relation exposes exactly the two named K2 producer results. -/
@[simp]
theorem mateCoherentRel_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    MateCoherentRel U input =
      AuthoredSupportComparison.Agrees
        (authoredBCComparison input)
        (authoredSupportCanonicalMate input.context) := rfl

/-- The fixed public relation is the initial specialization of the orbit equation. -/
theorem mateCoherentRel_iff_initial
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    MateCoherentRel U input ↔
      MateCoherentAtCochain input
        (initialRawDefectCochain input.toTransportData) := by
  rfl

/-- The public comparison contains the authored comparator in its raw factor. -/
theorem authoredBCComparison_uses_authoredComparator
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredRawDefectTotalAtCochain input
        (initialRawDefectCochain input.toTransportData) cell =
      (canonicalTwoCellComparator input.toTransportData 1 cell).1.inv.comp
        (PackageFiberAut.hom (input.authored.comparator cell)) :=
  authoredInitialRawDefectTotal_uses_authoredComparator input cell

/-! ## Full-orbit negative and strict positive -/

/-- The fixed lax datum fails the public construction equation at every orbit point. -/
theorem finiteAxisFold_not_mateCoherentAtCochain_on_orbit
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (inOrbit : InReselectionOrbit
      finiteAxisFoldBCDatumSquare.toTransportData cochain) :
    ¬ MateCoherentAtCochain finiteAxisFoldBCDatumSquare cochain :=
  finiteAxisFold_not_mateCoherent_on_orbit cochain inOrbit

/-- The public K2 relation fails on the fixed lax datum. -/
theorem finiteAxisFoldBCDatumSquare_not_mateCoherentRel :
    ¬ MateCoherentRel FiniteModel.carrier finiteAxisFoldBCDatumSquare := by
  rw [mateCoherentRel_iff_initial]
  exact finiteAxisFold_not_mateCoherent
    (1 : EdgeReselection finiteAxisFoldBCDatumSquare.toTransportData.lift)

/-- The strict finite datum satisfies the same public K2 relation. -/
theorem finiteAuthoredBCDatumSquare_mateCoherentRel :
    MateCoherentRel FiniteModel.carrier finiteAuthoredBCDatumSquare := by
  rw [mateCoherentRel_iff_initial]
  apply authoredDiagnosticComparisonAtCochain_eq_canonical
  · simpa [finiteAuthoredFactorization_toTransportData] using
      finiteAuthoredFactorization_initialRawDefect_eq_identity
  · intro supportCell
    exact finiteAuthored_pairwiseUnavailable
      (initialRawDefectCochain finiteAuthoredBCDatumSquare.toTransportData)
      supportCell

/-- The lax full-orbit theorem is tested on more than the initial coordinate. -/
theorem finiteAxisFold_mateCoherentRel_orbit_nontrivial :
    ∃ cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData,
      InReselectionOrbit finiteAxisFoldBCDatumSquare.toTransportData cochain ∧
        cochain ≠
          initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData :=
  finiteAxisFold_authoredComparison_orbit_nontrivial

/-! ## Finite-presentation replacement -/

/-- The public authored comparison commutes with generated presentation replacement. -/
theorem authoredBCComparison_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic) :
    (authoredSupportDirectRouteReplacementComparison
        datum.context replacement).hom ≫
      authoredBCComparison (datum.replacePresentation replacement) =
    authoredBCComparison datum ≫
      (authoredSupportViaBaseRouteReplacementComparison
        datum.context replacement).hom := by
  simpa only [authoredBCComparison, authoredBCComparisonAtCochain] using
    generatedAuthoredDiagnosticComparison_replacement datum replacement

/-- Public mate coherence is invariant under finite presentation replacement. -/
theorem mateCoherentRel_replacePresentation_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic) :
    MateCoherentRel U (datum.replacePresentation replacement) ↔
      MateCoherentRel U datum := by
  rw [mateCoherentRel_apply, mateCoherentRel_apply]
  change authoredBCComparison (datum.replacePresentation replacement) =
      authoredSupportCanonicalMate
        (datum.context.replacePresentation replacement) ↔
    authoredBCComparison datum = authoredSupportCanonicalMate datum.context
  let direct := (authoredSupportDirectRouteReplacementComparison
    datum.context replacement).hom
  let viaBase := (authoredSupportViaBaseRouteReplacementComparison
    datum.context replacement).hom
  have authoredSquare := authoredBCComparison_replacement datum replacement
  have canonicalSquare :=
    authoredSupportCanonicalMate_replacement datum.context replacement
  constructor
  · intro equality
    apply (cancel_mono viaBase).1
    calc
      authoredBCComparison datum ≫ viaBase =
          direct ≫ authoredBCComparison
            (datum.replacePresentation replacement) := authoredSquare.symm
      _ = direct ≫ authoredSupportCanonicalMate
            (datum.context.replacePresentation replacement) := by rw [equality]
      _ = authoredSupportCanonicalMate datum.context ≫ viaBase := canonicalSquare
  · intro equality
    apply (cancel_epi direct).1
    calc
      direct ≫ authoredBCComparison (datum.replacePresentation replacement) =
          authoredBCComparison datum ≫ viaBase := authoredSquare
      _ = authoredSupportCanonicalMate datum.context ≫ viaBase := by rw [equality]
      _ = direct ≫ authoredSupportCanonicalMate
            (datum.context.replacePresentation replacement) := canonicalSquare.symm

/-- The public replacement law fires on the nonempty raw-distinct finite fixture. -/
theorem finiteAuthored_authoredBCComparison_replacement_nonvacuous :
    Nonempty finiteAuthoredBCDatumSquare.context.Category ∧
      finiteAuthoredBCDatumSquare.context.square.presentation ≠
        finitePaddedAuthoredSupportBCProvenance.presentation ∧
      (authoredSupportDirectRouteReplacementComparison
          finiteAuthoredBCDatumSquare.context
          finitePaddedAuthoredSupportBCProvenance).hom ≫
        authoredBCComparison
          (finiteAuthoredBCDatumSquare.replacePresentation
            finitePaddedAuthoredSupportBCProvenance) =
      authoredBCComparison finiteAuthoredBCDatumSquare ≫
        (authoredSupportViaBaseRouteReplacementComparison
          finiteAuthoredBCDatumSquare.context
          finitePaddedAuthoredSupportBCProvenance).hom := by
  simpa only [authoredBCComparison, authoredBCComparisonAtCochain] using
    finiteAuthored_generatedDiagnosticReplacement_nonvacuous

/-- The raw-distinct padded presentation retains the strict public relation. -/
theorem finitePaddedAuthoredBCDatumSquare_mateCoherentRel :
    MateCoherentRel FiniteModel.carrier
      (finiteAuthoredBCDatumSquare.replacePresentation
        finitePaddedAuthoredSupportBCProvenance) := by
  rw [mateCoherentRel_replacePresentation_iff]
  exact finiteAuthoredBCDatumSquare_mateCoherentRel

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
