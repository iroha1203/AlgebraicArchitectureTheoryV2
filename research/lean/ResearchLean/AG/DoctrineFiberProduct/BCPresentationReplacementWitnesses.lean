import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationWitnesses

/-!
# Finite witness for Beck--Chevalley presentation replacement

This module instantiates the public Cycle 53 replacement square on two raw-
distinct finite BC presentations.  Their first cospan legs use distinct Atom
permutation codes (empty versus singleton authored support), while both codes
decode to the identity permutation.  Endpoints, source maps, selected points,
and diagnostic geometry remain fixed.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-! ## Raw-distinct constant cospan legs -/

/-- Executable Atom equality for the concrete finite replacement witness. -/
local instance finiteBCReplacementAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/--
The constant noninvertible arrow with a nonempty authored identity-permutation
code.  Its semantic source map and Atom equivalence equal the canonical ones.
-/
def finitePaddedConstantPresentation :
    CartPresentationBetween finiteTwoSourceInstance finiteOneSourceInstance where
  sourceMap := finiteConstantSourceMap
  atomEquiv := finitePresentationPaddedIdentityAtomCode
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport
        finitePresentationPaddedIdentityAtomCode.toEquiv
    rw [finitePresentationPaddedIdentityAtomCode_toEquiv]
    simp
  source_eq := rfl

/-- The canonical and padded constant presentations are raw-distinct. -/
theorem finiteConstantPresentation_ne_padded :
    finiteConstantPresentation ≠ finitePaddedConstantPresentation := by
  intro equality
  have supportEquality := congrArg
    (fun presentation : CartPresentationBetween finiteTwoSourceInstance
        finiteOneSourceInstance => presentation.atomEquiv.support) equality
  have componentAMemPadded : FiniteModel.FiniteAtom.componentA ∈
      finitePaddedConstantPresentation.atomEquiv.support := by
    change FiniteModel.FiniteAtom.componentA ∈
      finitePresentationPaddedIdentityAtomCode.support
    rw [finitePresentationPaddedIdentityAtomCode_support]
    simp
  have componentAMem : FiniteModel.FiniteAtom.componentA ∈
      finiteConstantPresentation.atomEquiv.support :=
    Eq.mp
      (congrArg (fun support => FiniteModel.FiniteAtom.componentA ∈ support)
        supportEquality.symm)
      componentAMemPadded
  change FiniteModel.FiniteAtom.componentA ∈
    (∅ : Finset FiniteModel.FiniteAtom) at componentAMem
  simp at componentAMem

/-- The cospan with only its first raw Atom code replaced. -/
def finitePaddedConstantBCCospan : CartCospanPresentation FiniteModel.carrier where
  firstSource := finiteTwoSourceInstance
  secondSource := finiteTwoSourceInstance
  base := finiteOneSourceInstance
  first := finitePaddedConstantPresentation
  second := finiteConstantPresentation

/-- Canonical point-table BC presentation for the existing constant cospan. -/
def finiteCanonicalReplacementBCPresentation :
    BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finiteConstantBCCospan finiteBCDiagnosticPresentation

/-- Canonical point-table BC presentation for the padded constant cospan. -/
def finitePaddedReplacementBCPresentation :
    BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finitePaddedConstantBCCospan
    finiteBCDiagnosticPresentation

/-- The two BC presentations remain raw-distinct after canonical point generation. -/
theorem finiteReplacementBCPresentations_ne :
    finiteCanonicalReplacementBCPresentation ≠
      finitePaddedReplacementBCPresentation := by
  intro equality
  have supportEquality := congrArg
    (fun presentation : BCPresentation FiniteModel.carrier =>
      presentation.1.cospan.first.atomEquiv.support) equality
  have componentAMemPadded : FiniteModel.FiniteAtom.componentA ∈
      finitePaddedReplacementBCPresentation.1.cospan.first.atomEquiv.support := by
    change FiniteModel.FiniteAtom.componentA ∈
      finitePresentationPaddedIdentityAtomCode.support
    rw [finitePresentationPaddedIdentityAtomCode_support]
    simp
  have componentAMemCanonical : FiniteModel.FiniteAtom.componentA ∈
      finiteCanonicalReplacementBCPresentation.1.cospan.first.atomEquiv.support :=
    Eq.mp
      (congrArg (fun support => FiniteModel.FiniteAtom.componentA ∈ support)
        supportEquality.symm)
      componentAMemPadded
  change FiniteModel.FiniteAtom.componentA ∈
    (∅ : Finset FiniteModel.FiniteAtom) at componentAMemCanonical
  simp at componentAMemCanonical

/-! ## Equal complete semantic decoders -/

/-- The bottom semantic arrows agree although their raw Atom supports differ. -/
theorem finiteConstantPresentation_semantic_eq :
    typedPresentationToSemantic finiteConstantPresentation =
      typedPresentationToSemantic finitePaddedConstantPresentation := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · change AtomPermutationCode.refl.toEquiv =
      finitePresentationPaddedIdentityAtomCode.toEquiv
    rw [AtomPermutationCode.toEquiv_refl,
      finitePresentationPaddedIdentityAtomCode_toEquiv]

/-- The generated top pullback projections agree after the first leg replacement. -/
theorem finiteConstantPullbackSnd_semantic_eq :
    typedPresentationToSemantic
        (pullbackSndPresentation finiteConstantPresentation
          finiteConstantPresentation) =
      typedPresentationToSemantic
        (pullbackSndPresentation finitePaddedConstantPresentation
          finiteConstantPresentation) := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · change (AtomPermutationCode.refl.trans
        AtomPermutationCode.refl.symm).toEquiv =
      (finitePresentationPaddedIdentityAtomCode.trans
        AtomPermutationCode.refl.symm).toEquiv
    simp [finitePresentationPaddedIdentityAtomCode_toEquiv]

/-- The raw-distinct BC presentations decode to one complete semantic BC input. -/
theorem finiteReplacementBCPresentations_semantic_eq :
    toSemanticBC finiteCanonicalReplacementBCPresentation =
      toSemanticBC finitePaddedReplacementBCPresentation := by
  apply BCSemanticInput.ext_heterogeneous
  · apply ExtInstSquare.ext_heterogeneous
    · rfl
    · rfl
    · rfl
    · rfl
    · exact heq_of_eq finiteConstantPullbackSnd_semantic_eq
    · rfl
    · rfl
    · exact heq_of_eq finiteConstantPresentation_semantic_eq
  · exact compatiblePointSemanticInputOfSquare_heq (by
      apply ExtInstSquare.ext_heterogeneous
      · rfl
      · rfl
      · rfl
      · rfl
      · exact heq_of_eq finiteConstantPullbackSnd_semantic_eq
      · rfl
      · rfl
      · exact heq_of_eq finiteConstantPresentation_semantic_eq)
  · rfl

/-! ## Nonvacuous firing of the public route/mate square -/

/-- Canonical finite provenance over the shared semantic BC input. -/
def finiteCanonicalReplacementBCProvenance : BCRealizationProvenance
    (toSemanticBC finiteCanonicalReplacementBCPresentation) where
  presentation := finiteCanonicalReplacementBCPresentation
  realization_eq := rfl

/-- Raw-distinct padded provenance over the same complete semantic BC input. -/
def finitePaddedReplacementBCProvenance : BCRealizationProvenance
    (toSemanticBC finiteCanonicalReplacementBCPresentation) where
  presentation := finitePaddedReplacementBCPresentation
  realization_eq := finiteReplacementBCPresentations_semantic_eq

/--
The public route comparisons and reference-fixed mate square fire on a genuinely
raw-distinct finite BC presentation replacement.
-/
theorem finiteReplacementBCPresentation_mate_square :
    (bcProvenanceDirectRouteComparison finiteCanonicalReplacementBCProvenance
        finitePaddedReplacementBCProvenance).hom ≫
      bcSelectedRebasedReplacementMate finiteCanonicalReplacementBCProvenance
        finitePaddedReplacementBCProvenance =
    bcProvenanceCanonicalMate finiteCanonicalReplacementBCProvenance ≫
      (bcProvenanceViaBaseRouteComparison finiteCanonicalReplacementBCProvenance
        finitePaddedReplacementBCProvenance).hom :=
  bcProvenanceCanonicalMate_rebasedReplacement
    finiteCanonicalReplacementBCProvenance
    finitePaddedReplacementBCProvenance

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
