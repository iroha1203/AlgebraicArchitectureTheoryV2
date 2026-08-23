import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticPresentationReplacement
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationWitnesses

/-!
# Nonvacuous finite witness for authored diagnostic presentation replacement

The existing nonempty authored datum uses an identity BC cospan at the finite
support endpoint.  This module replaces the first identity presentation by the
raw-distinct padded identity code.  Both presentations decode to the same
complete semantic BC input, so the generated authored diagnostic replacement
square fires on a literal nonempty support without changing its G-106 datum.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-- Executable Atom equality for the concrete authored replacement witness. -/
local instance finiteAuthoredReplacementAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A raw-distinct presentation of the authored identity cospan -/

/-- Replace only the first identity leg by its padded identity presentation. -/
def finitePaddedAuthoredSupportCospan :
    CartCospanPresentation FiniteModel.carrier where
  firstSource := finiteAuthoredSupportInstance
  secondSource := finiteAuthoredSupportInstance
  base := finiteAuthoredSupportInstance
  first := finitePaddedSupportIdentityPresentation
  second := idTypedPresentation finiteAuthoredSupportInstance

/-- The padded cospan with the same nonempty diagnostic presentation. -/
def finitePaddedAuthoredSupportBCPresentation :
    BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finitePaddedAuthoredSupportCospan
    finiteBCDiagnosticPresentation

/-- The canonical and padded authored BC presentations are raw-distinct. -/
theorem finiteAuthoredSupportBCPresentation_ne_padded :
    finiteAuthoredSupportBCPresentation ≠
      finitePaddedAuthoredSupportBCPresentation := by
  intro equality
  have supportEquality := congrArg
    (fun presentation : BCPresentation FiniteModel.carrier =>
      presentation.1.cospan.first.atomEquiv.support) equality
  have componentAMemPadded : FiniteModel.FiniteAtom.componentA ∈
      finitePaddedAuthoredSupportBCPresentation.1.cospan.first.atomEquiv.support := by
    change FiniteModel.FiniteAtom.componentA ∈
      finitePresentationPaddedIdentityAtomCode.support
    rw [finitePresentationPaddedIdentityAtomCode_support]
    simp
  have componentAMemCanonical : FiniteModel.FiniteAtom.componentA ∈
      finiteAuthoredSupportBCPresentation.1.cospan.first.atomEquiv.support :=
    Eq.mp
      (congrArg (fun support => FiniteModel.FiniteAtom.componentA ∈ support)
        supportEquality.symm)
      componentAMemPadded
  change FiniteModel.FiniteAtom.componentA ∈
    (∅ : Finset FiniteModel.FiniteAtom) at componentAMemCanonical
  simp at componentAMemCanonical

/-! ## Equality of complete semantic BC inputs -/

/-- The generated top projection is unchanged by the padded first identity. -/
theorem finiteAuthoredSupportPullbackSnd_semantic_eq :
    typedPresentationToSemantic
        (pullbackSndPresentation
          (idTypedPresentation finiteAuthoredSupportInstance)
          (idTypedPresentation finiteAuthoredSupportInstance)) =
      typedPresentationToSemantic
        (pullbackSndPresentation finitePaddedSupportIdentityPresentation
          (idTypedPresentation finiteAuthoredSupportInstance)) := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · change (AtomPermutationCode.refl.trans
        AtomPermutationCode.refl.symm).toEquiv =
      (finitePresentationPaddedIdentityAtomCode.trans
        AtomPermutationCode.refl.symm).toEquiv
    simp [finitePresentationPaddedIdentityAtomCode_toEquiv]

/-- Raw-distinct presentations decode to the same complete authored BC input. -/
theorem finiteAuthoredSupportBCPresentations_semantic_eq :
    toSemanticBC finiteAuthoredSupportBCPresentation =
      toSemanticBC finitePaddedAuthoredSupportBCPresentation := by
  apply BCSemanticInput.ext_heterogeneous
  · apply ExtInstSquare.ext_heterogeneous
    · rfl
    · rfl
    · rfl
    · rfl
    · exact heq_of_eq finiteAuthoredSupportPullbackSnd_semantic_eq
    · rfl
    · rfl
    · exact heq_of_eq finiteSupportIdentityPresentation_semanticHom_eq
  · exact compatiblePointSemanticInputOfSquare_heq (by
      apply ExtInstSquare.ext_heterogeneous
      · rfl
      · rfl
      · rfl
      · rfl
      · exact heq_of_eq finiteAuthoredSupportPullbackSnd_semantic_eq
      · rfl
      · rfl
      · exact heq_of_eq finiteSupportIdentityPresentation_semanticHom_eq)
  · rfl

/-! ## Nonvacuous firing of the generated authored comparison square -/

/-- Padded provenance over the exact semantic input of the nonempty authored datum. -/
def finitePaddedAuthoredSupportBCProvenance : BCRealizationProvenance
    finiteAuthoredBCDatumSquare.context.square.semantic where
  presentation := finitePaddedAuthoredSupportBCPresentation
  realization_eq := finiteAuthoredSupportBCPresentations_semantic_eq

/-- The replacement provenance is genuinely raw-distinct from the datum presentation. -/
theorem finiteAuthoredReplacement_presentations_ne :
    finiteAuthoredBCDatumSquare.context.square.presentation ≠
      finitePaddedAuthoredSupportBCProvenance.presentation :=
  finiteAuthoredSupportBCPresentation_ne_padded

/--
The generated authored diagnostic replacement square fires on the nonempty
authored support and the raw-distinct equal-decoding padded presentation.
-/
theorem finiteAuthored_generatedDiagnosticComparison_replacement :
    (authoredSupportDirectRouteReplacementComparison
        finiteAuthoredBCDatumSquare.context
        finitePaddedAuthoredSupportBCProvenance).hom ≫
      generatedAuthoredDiagnosticComparison
        (finiteAuthoredBCDatumSquare.replacePresentation
          finitePaddedAuthoredSupportBCProvenance) =
    generatedAuthoredDiagnosticComparison finiteAuthoredBCDatumSquare ≫
      (authoredSupportViaBaseRouteReplacementComparison
        finiteAuthoredBCDatumSquare.context
        finitePaddedAuthoredSupportBCProvenance).hom :=
  generatedAuthoredDiagnosticComparison_replacement
    finiteAuthoredBCDatumSquare finitePaddedAuthoredSupportBCProvenance

/-- One proposition records support inhabitation, raw distinction, and firing together. -/
theorem finiteAuthored_generatedDiagnosticReplacement_nonvacuous :
    Nonempty finiteAuthoredBCDatumSquare.context.Category ∧
      finiteAuthoredBCDatumSquare.context.square.presentation ≠
        finitePaddedAuthoredSupportBCProvenance.presentation ∧
      (authoredSupportDirectRouteReplacementComparison
          finiteAuthoredBCDatumSquare.context
          finitePaddedAuthoredSupportBCProvenance).hom ≫
        generatedAuthoredDiagnosticComparison
          (finiteAuthoredBCDatumSquare.replacePresentation
            finitePaddedAuthoredSupportBCProvenance) =
      generatedAuthoredDiagnosticComparison finiteAuthoredBCDatumSquare ≫
        (authoredSupportViaBaseRouteReplacementComparison
          finiteAuthoredBCDatumSquare.context
          finitePaddedAuthoredSupportBCProvenance).hom :=
  ⟨finiteAuthoredSupport_nonempty,
    finiteAuthoredReplacement_presentations_ne,
    finiteAuthored_generatedDiagnosticComparison_replacement⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
