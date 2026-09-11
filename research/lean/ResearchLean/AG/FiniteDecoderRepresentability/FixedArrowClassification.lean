import ResearchLean.AG.FiniteDecoderRepresentability.PermutationCodeClassification
import Formal.Util.AssertStandardAxioms

/-!
# Fixed-endpoint morphism representability

This module proves the central classification in G-121(C).  For fixed finite
instance codes, a semantic arrow is decoded by an existing typed presentation
exactly when its actual Atom permutation has finite moved support and it
preserves the authored default values of the normalized extraction tables.

## Implementation notes

The sufficient constructor keeps the two endpoint codes literal and uses the
actual semantic source map and Atom permutation.  It does not choose endpoint
isomorphisms or accept component equalities as certificates: normalization,
extraction, point preservation, and decoder equality are derived from the
semantic morphism and the two classified conditions.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/--
G-121(C) notation API: `t_P(s)` is the actual authored extraction code after
the existing finite doctrine's normalization.  It introduces no new premise.
-/
def normalizedExtractionCode (code : FiniteInstanceCode U)
    (source : code.doctrine.Source) : AtomPredicateCode U :=
  code.doctrine.extraction (code.doctrine.normalize source)

/--
G-121(C) normalization API for authored defaults.  The `simp` direction exposes
the existing extraction table selected by normalization.
-/
@[simp]
theorem normalizedExtractionCode_defaultValue (code : FiniteInstanceCode U)
    (source : code.doctrine.Source) :
    (normalizedExtractionCode code source).defaultValue =
      (code.doctrine.extraction
        (code.doctrine.normalize source)).defaultValue :=
  rfl

/--
G-121(C) normalization API for evaluation.  `DecidableEq` comes from the
existing evaluator, and `simp` exposes the normalized authored table.
-/
@[simp]
theorem normalizedExtractionCode_eval [DecidableEq U.Atom]
    (code : FiniteInstanceCode U) (source : code.doctrine.Source)
    (atom : U.Atom) :
    (normalizedExtractionCode code source).eval atom =
      (code.doctrine.extraction (code.doctrine.normalize source)).eval atom :=
  rfl

/--
G-121(C) transport API: Atom transport preserves the authored default.  The
`simp` direction removes transport from the default-value observation.
-/
@[simp]
theorem atomPredicateCode_transport_defaultValue [DecidableEq U.Atom]
    (code : AtomPredicateCode U) (equiv : Equiv.Perm U.Atom) :
    (code.transport equiv).defaultValue = code.defaultValue :=
  rfl

/--
G-121(C) raw-code API: equal authored defaults and pointwise evaluations imply
equality of finite-exception tables.  No carrier finiteness is required.
-/
theorem atomPredicateCode_eq_of_defaultValue_eq_of_eval_eq
    [DecidableEq U.Atom] {first second : AtomPredicateCode U}
    (hdefault : first.defaultValue = second.defaultValue)
    (heval : ∀ atom, first.eval atom = second.eval atom) :
    first = second := by
  cases first with
  | mk firstDefault firstExceptions =>
    cases second with
    | mk secondDefault secondExceptions =>
      rw [AtomPredicateCode.mk.injEq]
      refine ⟨hdefault, ?_⟩
      have hdefaults : firstDefault = secondDefault := hdefault
      subst secondDefault
      ext atom
      have hatom := heval atom
      by_cases hfirst : atom ∈ firstExceptions <;>
        by_cases hsecond : atom ∈ secondExceptions <;>
        cases firstDefault <;>
        simp [AtomPredicateCode.eval, hfirst, hsecond] at hatom ⊢

/--
G-121(C) necessity: a typed presentation decoding `hom` forces finite actual
Atom support and preservation of normalized extraction-code defaults.
-/
theorem fixedPresentation_necessary [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (presentation : CartPresentationBetween source target)
    (hdecode : typedPresentationToSemantic presentation = hom) :
    (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite ∧
      ∀ input : source.doctrine.Source,
        (normalizedExtractionCode target
          (hom.doctrineHom.sourceMap input)).defaultValue =
        (normalizedExtractionCode source input).defaultValue := by
  have hatom : presentation.atomEquiv.toEquiv = hom.doctrineHom.atomEquiv := by
    simpa only [typedPresentationToSemantic_atomEquiv] using congrArg
      (fun arrow => arrow.doctrineHom.atomEquiv) hdecode
  have hsource : presentation.sourceMap = hom.doctrineHom.sourceMap := by
    simpa only [typedPresentationToSemantic_sourceMap] using congrArg
      (fun arrow => arrow.doctrineHom.sourceMap) hdecode
  constructor
  · rw [← hatom]
    exact atomPermutationSupport_finite_of_code presentation.atomEquiv
  · intro input
    rw [← hsource]
    have hcode := congrArg AtomPredicateCode.defaultValue
      (presentation.extraction_eq input)
    simpa only [normalizedExtractionCode,
      atomPredicateCode_transport_defaultValue] using hcode

/--
G-121(C) sufficiency constructor: finite actual Atom support and normalized
default preservation build a typed presentation with the semantic arrow's
source map and Atom permutation.  All three validation laws are derived.
-/
noncomputable def fixedPresentationOfFiniteSupport
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (hfinite : (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite)
    (hdefault : ∀ input : source.doctrine.Source,
      (normalizedExtractionCode target
        (hom.doctrineHom.sourceMap input)).defaultValue =
      (normalizedExtractionCode source input).defaultValue) :
    CartPresentationBetween source target where
  sourceMap := hom.doctrineHom.sourceMap
  atomEquiv := atomPermutationCodeOfFiniteSupport
    hom.doctrineHom.atomEquiv hfinite
  normalize_eq := hom.doctrineHom.normalize_eq
  extraction_eq := by
    intro input
    rw [atomPermutationCodeOfFiniteSupport_toEquiv]
    apply atomPredicateCode_eq_of_defaultValue_eq_of_eval_eq
      (first := normalizedExtractionCode target
        (hom.doctrineHom.sourceMap input))
      (second := (normalizedExtractionCode source input).transport
        hom.doctrineHom.atomEquiv)
      (by simpa only [atomPredicateCode_transport_defaultValue] using hdefault input)
    intro atom
    have hexact := hom.doctrineHom.extraction_iff input
      (hom.doctrineHom.atomEquiv.symm atom)
    change
      source.doctrine.toDoctrine.extracts input
          (hom.doctrineHom.atomEquiv.symm atom) ↔
        target.doctrine.toDoctrine.extracts
          (hom.doctrineHom.sourceMap input)
          (hom.doctrineHom.atomEquiv
            (hom.doctrineHom.atomEquiv.symm atom)) at hexact
    rw [FiniteDoctrineCode.toDoctrine_extracts_iff,
      FiniteDoctrineCode.toDoctrine_extracts_iff,
      hom.doctrineHom.atomEquiv.apply_symm_apply] at hexact
    have hexact' :
        (normalizedExtractionCode source input).eval
            (hom.doctrineHom.atomEquiv.symm atom) = true ↔
          (normalizedExtractionCode target
            (hom.doctrineHom.sourceMap input)).eval atom = true := by
      simpa only [AtomPredicateCode.Holds,
        normalizedExtractionCode_eval] using hexact
    have htransport :
        ((normalizedExtractionCode source input).transport
          hom.doctrineHom.atomEquiv).eval atom =
        (normalizedExtractionCode source input).eval
          (hom.doctrineHom.atomEquiv.symm atom) := by
      conv_lhs =>
        rw [← hom.doctrineHom.atomEquiv.apply_symm_apply atom]
      rw [AtomPredicateCode.eval_transport]
    apply Bool.eq_iff_iff.mpr
    rw [htransport]
    exact hexact'.symm
  source_eq := hom.source_eq

/--
G-121(C) constructor API: the sufficient presentation uses the semantic source
map literally.  The `simp` direction exposes that actual morphism component.
-/
@[simp]
theorem fixedPresentationOfFiniteSupport_sourceMap
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (hfinite : (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite)
    (hdefault : ∀ input : source.doctrine.Source,
      (normalizedExtractionCode target
        (hom.doctrineHom.sourceMap input)).defaultValue =
      (normalizedExtractionCode source input).defaultValue) :
    (fixedPresentationOfFiniteSupport hom hfinite hdefault).sourceMap =
      hom.doctrineHom.sourceMap :=
  rfl

/--
G-121(C) constructor API: the sufficient presentation's finite Atom table
decodes to the semantic permutation.  The `simp` direction exposes that component.
-/
@[simp]
theorem fixedPresentationOfFiniteSupport_atomEquiv_toEquiv
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (hfinite : (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite)
    (hdefault : ∀ input : source.doctrine.Source,
      (normalizedExtractionCode target
        (hom.doctrineHom.sourceMap input)).defaultValue =
      (normalizedExtractionCode source input).defaultValue) :
    (fixedPresentationOfFiniteSupport hom hfinite hdefault).atomEquiv.toEquiv =
      hom.doctrineHom.atomEquiv :=
  atomPermutationCodeOfFiniteSupport_toEquiv _ _

/--
G-121(C) constructor correctness: the sufficient presentation decodes to the
supplied semantic arrow itself.  The `simp` direction selects that semantic arrow;
`DecidableEq` is inherited from the existing typed decoder.
-/
@[simp]
theorem fixedPresentationOfFiniteSupport_decode
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic)
    (hfinite : (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite)
    (hdefault : ∀ input : source.doctrine.Source,
      (normalizedExtractionCode target
        (hom.doctrineHom.sourceMap input)).defaultValue =
      (normalizedExtractionCode source input).defaultValue) :
    typedPresentationToSemantic
        (fixedPresentationOfFiniteSupport hom hfinite hdefault) = hom := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · exact fixedPresentationOfFiniteSupport_sourceMap hom hfinite hdefault
  · exact fixedPresentationOfFiniteSupport_atomEquiv_toEquiv hom hfinite hdefault

/--
G-121(C) main fixed-presentation theorem: typed representability is equivalent
to finite actual Atom support and normalized default-value preservation.
-/
theorem exists_fixedPresentation_decode_iff [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic) :
    (∃ presentation : CartPresentationBetween source target,
      typedPresentationToSemantic presentation = hom) ↔
      (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite ∧
      ∀ input : source.doctrine.Source,
        (normalizedExtractionCode target
          (hom.doctrineHom.sourceMap input)).defaultValue =
        (normalizedExtractionCode source input).defaultValue := by
  constructor
  · rintro ⟨presentation, hdecode⟩
    exact fixedPresentation_necessary hom presentation hdecode
  · rintro ⟨hfinite, hdefault⟩
    exact ⟨fixedPresentationOfFiniteSupport hom hfinite hdefault,
      fixedPresentationOfFiniteSupport_decode hom hfinite hdefault⟩

/--
G-121(C) fixed-endpoint bridge: existence of a `D₀` morphism decoding `hom` is
equivalent to existence of a typed presentation with those literal endpoints.
-/
theorem exists_finiteCodeCartHom_map_iff_exists_fixedPresentation
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic) :
    (∃ codeHom : FiniteCodeCartHom source target,
      finiteCodeCartRealization.map codeHom = hom) ↔
      ∃ presentation : CartPresentationBetween source target,
        typedPresentationToSemantic presentation = hom := by
  constructor
  · rintro ⟨codeHom, hdecode⟩
    obtain ⟨presentation, hpresentation⟩ := Quotient.exists_rep codeHom
    have hp : FiniteCodeCartHom.ofPresentation presentation = codeHom :=
      hpresentation
    refine ⟨presentation, ?_⟩
    calc
      typedPresentationToSemantic presentation =
          finiteCodeCartRealization.map
            (FiniteCodeCartHom.ofPresentation presentation) :=
        (finiteCodeCartRealization_map_ofPresentation presentation).symm
      _ = finiteCodeCartRealization.map codeHom := congrArg _ hp
      _ = hom := hdecode
  · rintro ⟨presentation, hdecode⟩
    exact ⟨FiniteCodeCartHom.ofPresentation presentation, by
      rw [finiteCodeCartRealization_map_ofPresentation]
      exact hdecode⟩

/--
G-121(C) decoder-image classification for fixed code endpoints: a `D₀` arrow
exists over `hom` exactly under the finite-support and default-value conditions.
-/
theorem exists_finiteCodeCartHom_map_iff [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : source.toSemantic ⟶ target.toSemantic) :
    (∃ codeHom : FiniteCodeCartHom source target,
      finiteCodeCartRealization.map codeHom = hom) ↔
      (atomPermutationSupport hom.doctrineHom.atomEquiv).Finite ∧
      ∀ input : source.doctrine.Source,
        (normalizedExtractionCode target
          (hom.doctrineHom.sourceMap input)).defaultValue =
        (normalizedExtractionCode source input).defaultValue := by
  rw [exists_finiteCodeCartHom_map_iff_exists_fixedPresentation,
    exists_fixedPresentation_decode_iff]

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
