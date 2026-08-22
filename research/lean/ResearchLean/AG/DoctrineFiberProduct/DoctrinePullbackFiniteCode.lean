import ResearchLean.AG.DoctrineFiberProduct.DoctrinePullback
import ResearchLean.AG.DoctrineFiberProduct.Schema

/-!
# Representation-invariant finite-code doctrine pullbacks

This module connects the arbitrary semantic pullback in `Doct_U` with the
finite-code pullback presentation fixed by the G-110 schema.  It also exposes
the source-level invariant used to state a proper, nondegenerate doctrine
fiber independently of the chosen source representation.

## Implementation notes

`ProperDoctrineFiber` contains only properties of two supplied projections;
it stores no witness or pullback certificate.  Its invariance theorem derives
transport from isomorphisms of the three objects and commuting projection
graphs.  For finite codes, the internally generated rank/unrank equivalence
`compatibleSourceEquiv` supplies an isomorphism from the decoded finite-code
pullback to the arbitrary semantic pullback.  The doctrine-level pullback
theorem for the generated presentation is transported through that internal
isomorphism, rather than reproving a second universal property.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory CategoryTheory.Limits
open AtomFoundation

/-- The canonical source map from two doctrine projections to their component product. -/
def doctrineSourcePairMap
    {U : AtomCarrier.{u}} {P DOne DTwo : ExtractionDoctrine U}
    (piOne : P ⟶ DOne) (piTwo : P ⟶ DTwo) :
    P.Source → DOne.Source × DTwo.Source :=
  fun source => (piOne.sourceMap source, piTwo.sourceMap source)

/--
A proper doctrine fiber has a nonempty source, does not cover the component
source product, and has two noninvertible projections.

This is a property of projection data, not a certificate structure: each
conjunct must be derived by a producer or a concrete witness theorem.
-/
def ProperDoctrineFiber
    {U : AtomCarrier.{u}} {P DOne DTwo : ExtractionDoctrine U}
    (piOne : P ⟶ DOne) (piTwo : P ⟶ DTwo) : Prop :=
  Nonempty P.Source ∧
    ¬ Function.Surjective (doctrineSourcePairMap piOne piTwo) ∧
    ¬ IsIso piOne ∧
    ¬ IsIso piTwo

/-- An isomorphism of doctrines induces an equivalence of their source types. -/
def doctrineSourceEquiv
    {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U} (e : D ≅ E) :
    D.Source ≃ E.Source where
  toFun := e.hom.sourceMap
  invFun := e.inv.sourceMap
  left_inv source := by
    have hsource := congrArg
      (fun hom : D ⟶ D => hom.sourceMap source) e.hom_inv_id
    change e.inv.sourceMap (e.hom.sourceMap source) = source at hsource
    exact hsource
  right_inv source := by
    have hsource := congrArg
      (fun hom : E ⟶ E => hom.sourceMap source) e.inv_hom_id
    change e.hom.sourceMap (e.inv.sourceMap source) = source at hsource
    exact hsource

/-- The source map of an isomorphism in `Doct_U` is injective. -/
theorem exactDoctrineHom_sourceMap_injective_of_isIso
    {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U}
    (hom : D ⟶ E) [IsIso hom] : Function.Injective hom.sourceMap := by
  exact (doctrineSourceEquiv (asIso hom)).injective

/-- The source map of an isomorphism in `Doct_U` is surjective. -/
theorem exactDoctrineHom_sourceMap_surjective_of_isIso
    {U : AtomCarrier.{u}} {D E : ExtractionDoctrine U}
    (hom : D ⟶ E) [IsIso hom] : Function.Surjective hom.sourceMap := by
  exact (doctrineSourceEquiv (asIso hom)).surjective

/--
Properness of a doctrine fiber is invariant under isomorphisms of the source
and both component doctrines when the two projection graphs commute.

The commuting equations are ordinary diagram data.  No nonemptiness,
surjectivity, or invertibility conclusion is accepted from the caller.
-/
theorem properDoctrineFiber_iff_of_iso
    {U : AtomCarrier.{u}}
    {P P' DOne DOne' DTwo DTwo' : ExtractionDoctrine U}
    (eP : P ≅ P') (eOne : DOne ≅ DOne') (eTwo : DTwo ≅ DTwo')
    (piOne : P ⟶ DOne) (piTwo : P ⟶ DTwo)
    (piOne' : P' ⟶ DOne') (piTwo' : P' ⟶ DTwo')
    (hOne : piOne ≫ eOne.hom = eP.hom ≫ piOne')
    (hTwo : piTwo ≫ eTwo.hom = eP.hom ≫ piTwo') :
    ProperDoctrineFiber piOne piTwo ↔
      ProperDoctrineFiber piOne' piTwo' := by
  have hOneSource (source : P.Source) :
      eOne.hom.sourceMap (piOne.sourceMap source) =
        piOne'.sourceMap (eP.hom.sourceMap source) := by
    have hsource := congrArg
      (fun hom : P ⟶ DOne' => hom.sourceMap source) hOne
    change eOne.hom.sourceMap (piOne.sourceMap source) =
      piOne'.sourceMap (eP.hom.sourceMap source) at hsource
    exact hsource
  have hTwoSource (source : P.Source) :
      eTwo.hom.sourceMap (piTwo.sourceMap source) =
        piTwo'.sourceMap (eP.hom.sourceMap source) := by
    have hsource := congrArg
      (fun hom : P ⟶ DTwo' => hom.sourceMap source) hTwo
    change eTwo.hom.sourceMap (piTwo.sourceMap source) =
      piTwo'.sourceMap (eP.hom.sourceMap source) at hsource
    exact hsource
  have hNonempty : Nonempty P.Source ↔ Nonempty P'.Source := by
    constructor
    · rintro ⟨source⟩
      exact ⟨eP.hom.sourceMap source⟩
    · rintro ⟨source⟩
      exact ⟨eP.inv.sourceMap source⟩
  have hSurjective :
      Function.Surjective (doctrineSourcePairMap piOne piTwo) ↔
        Function.Surjective (doctrineSourcePairMap piOne' piTwo') := by
    constructor
    · intro hsurjective target
      let componentTarget : DOne.Source × DTwo.Source :=
        ((doctrineSourceEquiv eOne).symm target.1,
          (doctrineSourceEquiv eTwo).symm target.2)
      rcases hsurjective componentTarget with ⟨source, hsource⟩
      refine ⟨eP.hom.sourceMap source, ?_⟩
      apply Prod.ext
      · change piOne'.sourceMap (eP.hom.sourceMap source) = target.1
        have hsourceOne := congrArg Prod.fst hsource
        change piOne.sourceMap source =
          (doctrineSourceEquiv eOne).symm target.1 at hsourceOne
        rw [← hOneSource source, hsourceOne]
        exact (doctrineSourceEquiv eOne).apply_symm_apply target.1
      · change piTwo'.sourceMap (eP.hom.sourceMap source) = target.2
        have hsourceTwo := congrArg Prod.snd hsource
        change piTwo.sourceMap source =
          (doctrineSourceEquiv eTwo).symm target.2 at hsourceTwo
        rw [← hTwoSource source, hsourceTwo]
        exact (doctrineSourceEquiv eTwo).apply_symm_apply target.2
    · intro hsurjective target
      let componentTarget : DOne'.Source × DTwo'.Source :=
        (eOne.hom.sourceMap target.1, eTwo.hom.sourceMap target.2)
      rcases hsurjective componentTarget with ⟨source', hsource'⟩
      let source : P.Source := (doctrineSourceEquiv eP).symm source'
      refine ⟨source, ?_⟩
      apply Prod.ext
      · apply (doctrineSourceEquiv eOne).injective
        change eOne.hom.sourceMap (piOne.sourceMap source) =
          eOne.hom.sourceMap target.1
        rw [hOneSource source]
        have hPSource : eP.hom.sourceMap source = source' := by
          exact (doctrineSourceEquiv eP).apply_symm_apply source'
        rw [hPSource]
        have hsourceOne := congrArg Prod.fst hsource'
        change piOne'.sourceMap source' =
          eOne.hom.sourceMap target.1 at hsourceOne
        exact hsourceOne
      · apply (doctrineSourceEquiv eTwo).injective
        change eTwo.hom.sourceMap (piTwo.sourceMap source) =
          eTwo.hom.sourceMap target.2
        rw [hTwoSource source]
        have hPSource : eP.hom.sourceMap source = source' := by
          exact (doctrineSourceEquiv eP).apply_symm_apply source'
        rw [hPSource]
        have hsourceTwo := congrArg Prod.snd hsource'
        change piTwo'.sourceMap source' =
          eTwo.hom.sourceMap target.2 at hsourceTwo
        exact hsourceTwo
  have hIsIsoOne : IsIso piOne ↔ IsIso piOne' := by
    constructor
    · intro hIso
      letI : IsIso piOne := hIso
      haveI : IsIso (piOne ≫ eOne.hom) := inferInstance
      haveI : IsIso (eP.hom ≫ piOne') := by
        rw [← hOne]
        infer_instance
      exact IsIso.of_isIso_comp_left eP.hom piOne'
    · intro hIso
      letI : IsIso piOne' := hIso
      haveI : IsIso (eP.hom ≫ piOne') := inferInstance
      haveI : IsIso (piOne ≫ eOne.hom) := by
        rw [hOne]
        infer_instance
      exact IsIso.of_isIso_comp_right piOne eOne.hom
  have hIsIsoTwo : IsIso piTwo ↔ IsIso piTwo' := by
    constructor
    · intro hIso
      letI : IsIso piTwo := hIso
      haveI : IsIso (piTwo ≫ eTwo.hom) := inferInstance
      haveI : IsIso (eP.hom ≫ piTwo') := by
        rw [← hTwo]
        infer_instance
      exact IsIso.of_isIso_comp_left eP.hom piTwo'
    · intro hIso
      letI : IsIso piTwo' := hIso
      haveI : IsIso (eP.hom ≫ piTwo') := inferInstance
      haveI : IsIso (piTwo ≫ eTwo.hom) := by
        rw [hTwo]
        infer_instance
      exact IsIso.of_isIso_comp_right piTwo eTwo.hom
  constructor
  · rintro ⟨hnonempty, hnonsurjective, hnotIsoOne, hnotIsoTwo⟩
    refine ⟨hNonempty.mp hnonempty, ?_, ?_, ?_⟩
    · intro hsurjective
      exact hnonsurjective (hSurjective.mpr hsurjective)
    · intro hIso
      exact hnotIsoOne (hIsIsoOne.mpr hIso)
    · intro hIso
      exact hnotIsoTwo (hIsIsoTwo.mpr hIso)
  · rintro ⟨hnonempty, hnonsurjective, hnotIsoOne, hnotIsoTwo⟩
    refine ⟨hNonempty.mpr hnonempty, ?_, ?_, ?_⟩
    · intro hsurjective
      exact hnonsurjective (hSurjective.mp hsurjective)
    · intro hIso
      exact hnotIsoOne (hIsIsoOne.mp hIso)
    · intro hIso
      exact hnotIsoTwo (hIsIsoTwo.mp hIso)

/--
The decoded finite-code pullback is isomorphic to the arbitrary semantic
doctrine pullback.  The direction is finite-code realization to semantic
producer output.
-/
noncomputable def doctrinePullbackFiniteCodeIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    (pullbackDoctrineCode first second).toDoctrine ≅
      doctrinePullback
        (typedPresentationToSemantic first).doctrineHom
        (typedPresentationToSemantic second).doctrineHom := by
  let sigmaOne : left.doctrine.toDoctrine ⟶ base.doctrine.toDoctrine :=
    (typedPresentationToSemantic first).doctrineHom
  let sigmaTwo : right.doctrine.toDoctrine ⟶ base.doctrine.toDoctrine :=
    (typedPresentationToSemantic second).doctrineHom
  let sourceEquiv :
      ((pullbackDoctrineCode first second).toDoctrine).Source ≃
        (doctrinePullback sigmaOne sigmaTwo).Source :=
    compatibleSourceEquiv first second
  let forward :
      (pullbackDoctrineCode first second).toDoctrine ⟶
        doctrinePullback sigmaOne sigmaTwo :=
    { sourceMap := sourceEquiv
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := fun input => by
        apply Subtype.ext
        apply Prod.ext
        · change left.doctrine.normalize
              (compatibleSourceEquiv first second input).val.1 =
            (compatibleSourceEquiv first second
              ((pullbackDoctrineCode first second).normalize input)).val.1
          exact (pullbackDoctrineCode_normalize_fst
            first second input).symm
        · change right.doctrine.normalize
              (compatibleSourceEquiv first second input).val.2 =
            (compatibleSourceEquiv first second
              ((pullbackDoctrineCode first second).normalize input)).val.2
          exact (pullbackDoctrineCode_normalize_snd
            first second input).symm
      extraction_iff := fun input atom => by
        simpa [sourceEquiv] using
          pullbackDoctrineCode_extracts_iff first second input atom }
  let backward :
      doctrinePullback sigmaOne sigmaTwo ⟶
        (pullbackDoctrineCode first second).toDoctrine :=
    { sourceMap := sourceEquiv.symm
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := fun input => by
        apply sourceEquiv.injective
        rw [sourceEquiv.apply_symm_apply]
        calc
          sourceEquiv
                ((pullbackDoctrineCode first second).normalize
                  (sourceEquiv.symm input)) =
              (doctrinePullback sigmaOne sigmaTwo).normalize
                (sourceEquiv (sourceEquiv.symm input)) :=
            (forward.normalize_eq (sourceEquiv.symm input)).symm
          _ = (doctrinePullback sigmaOne sigmaTwo).normalize input := by
            rw [sourceEquiv.apply_symm_apply]
      extraction_iff := fun input atom => by
        rw [doctrinePullback_extracts_iff]
        have hextraction :=
          (pullbackDoctrineCode_extracts_iff first second
            (sourceEquiv.symm input) atom).symm
        change
          left.doctrine.toDoctrine.extracts
              (sourceEquiv (sourceEquiv.symm input)).val.1 atom ↔
            (pullbackDoctrineCode first second).toDoctrine.extracts
              (sourceEquiv.symm input) atom at hextraction
        rw [sourceEquiv.apply_symm_apply input] at hextraction
        exact hextraction }
  exact
    { hom := forward
      inv := backward
      hom_inv_id := by
        apply ExactDoctrineHom.ext
        · funext input
          exact sourceEquiv.symm_apply_apply input
        · apply Equiv.ext
          intro atom
          rfl
      inv_hom_id := by
        apply ExactDoctrineHom.ext
        · funext input
          exact sourceEquiv.apply_symm_apply input
        · apply Equiv.ext
          intro atom
          rfl }

/-- The finite-to-semantic pullback isomorphism preserves the first projection. -/
theorem doctrinePullbackFiniteCodeIso_hom_fst
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    (doctrinePullbackFiniteCodeIso first second).hom ≫
        doctrinePullbackFst
          (typedPresentationToSemantic first).doctrineHom
          (typedPresentationToSemantic second).doctrineHom =
      (typedPresentationToSemantic
        (pullbackFstPresentation first second)).doctrineHom := by
  apply ExactDoctrineHom.ext
  · simp only [doctrinePullbackFiniteCodeIso, doctrinePullbackFst,
      typedPresentationToSemantic, CartPresentationBetween.toPresentation,
      CartPresentationBetween.toRaw, toSemanticCart,
      FiniteInstanceCode.toSemantic, decodeCartDoctrineHom,
      pullbackFstPresentation,
      ExactDoctrineHom.comp_sourceMap]
    funext input
    rfl
  · simp only [doctrinePullbackFiniteCodeIso, doctrinePullbackFst,
      typedPresentationToSemantic, CartPresentationBetween.toPresentation,
      CartPresentationBetween.toRaw, toSemanticCart,
      FiniteInstanceCode.toSemantic, decodeCartDoctrineHom,
      pullbackFstPresentation,
      ExactDoctrineHom.comp_atomEquiv]
    change (Equiv.refl U.Atom).trans (Equiv.refl U.Atom) =
      (AtomPermutationCode.refl : AtomPermutationCode U).toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    apply Equiv.ext
    intro atom
    rfl

/-- The finite-to-semantic pullback isomorphism preserves the second projection. -/
theorem doctrinePullbackFiniteCodeIso_hom_snd
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    (doctrinePullbackFiniteCodeIso first second).hom ≫
        doctrinePullbackSnd
          (typedPresentationToSemantic first).doctrineHom
          (typedPresentationToSemantic second).doctrineHom =
      (typedPresentationToSemantic
        (pullbackSndPresentation first second)).doctrineHom := by
  apply ExactDoctrineHom.ext
  · simp only [doctrinePullbackFiniteCodeIso, doctrinePullbackSnd,
      typedPresentationToSemantic, CartPresentationBetween.toPresentation,
      CartPresentationBetween.toRaw, toSemanticCart,
      FiniteInstanceCode.toSemantic, decodeCartDoctrineHom,
      pullbackSndPresentation,
      ExactDoctrineHom.comp_sourceMap]
    funext input
    rfl
  · simp only [doctrinePullbackFiniteCodeIso, doctrinePullbackSnd,
      typedPresentationToSemantic, CartPresentationBetween.toPresentation,
      CartPresentationBetween.toRaw, toSemanticCart,
      FiniteInstanceCode.toSemantic, decodeCartDoctrineHom,
      pullbackSndPresentation,
      ExactDoctrineHom.comp_atomEquiv]
    change
      (Equiv.refl U.Atom).trans
          (first.atomEquiv.toEquiv.trans second.atomEquiv.toEquiv.symm) =
        (first.atomEquiv.trans second.atomEquiv.symm).toEquiv
    rw [AtomPermutationCode.toEquiv_trans,
      AtomPermutationCode.toEquiv_symm]
    apply Equiv.ext
    intro atom
    rfl

/--
The two decoded doctrine projections generated by `pullbackPresentation` form
a categorical pullback in `Doct_U`.

The proof transports `doctrinePullback_isPullback` through
`doctrinePullbackFiniteCodeIso` and its two projection graphs.
-/
theorem pullbackPresentation_doctrine_isPullback
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    @IsPullback
      (ExtractionDoctrine U) (ExactDoctrineHom.extractionDoctrineCategory U)
      (pullbackDoctrineCode first second).toDoctrine
      left.doctrine.toDoctrine right.doctrine.toDoctrine
      base.doctrine.toDoctrine
      (typedPresentationToSemantic
        (pullbackFstPresentation first second)).doctrineHom
      (typedPresentationToSemantic
        (pullbackSndPresentation first second)).doctrineHom
      (typedPresentationToSemantic first).doctrineHom
      (typedPresentationToSemantic second).doctrineHom := by
  let sigmaOne : left.doctrine.toDoctrine ⟶ base.doctrine.toDoctrine :=
    (typedPresentationToSemantic first).doctrineHom
  let sigmaTwo : right.doctrine.toDoctrine ⟶ base.doctrine.toDoctrine :=
    (typedPresentationToSemantic second).doctrineHom
  change @IsPullback
    (ExtractionDoctrine U) (ExactDoctrineHom.extractionDoctrineCategory U)
    (pullbackDoctrineCode first second).toDoctrine
    left.doctrine.toDoctrine right.doctrine.toDoctrine
    base.doctrine.toDoctrine
    (typedPresentationToSemantic
      (pullbackFstPresentation first second)).doctrineHom
    (typedPresentationToSemantic
      (pullbackSndPresentation first second)).doctrineHom
    sigmaOne sigmaTwo
  have genericPullback :
      IsPullback
        (doctrinePullbackFst sigmaOne sigmaTwo)
        (doctrinePullbackSnd sigmaOne sigmaTwo)
        sigmaOne sigmaTwo :=
    doctrinePullback_isPullback sigmaOne sigmaTwo
  let eOne : left.doctrine.toDoctrine ≅ left.doctrine.toDoctrine := Iso.refl _
  let eTwo : right.doctrine.toDoctrine ≅ right.doctrine.toDoctrine := Iso.refl _
  let eBase : base.doctrine.toDoctrine ≅ base.doctrine.toDoctrine := Iso.refl _
  refine IsPullback.of_iso'
    (P' := (pullbackDoctrineCode first second).toDoctrine)
    (X' := left.doctrine.toDoctrine)
    (Y' := right.doctrine.toDoctrine)
    (Z' := base.doctrine.toDoctrine)
    (fst' := (typedPresentationToSemantic
      (pullbackFstPresentation first second)).doctrineHom)
    (snd' := (typedPresentationToSemantic
      (pullbackSndPresentation first second)).doctrineHom)
    (f' := sigmaOne) (g' := sigmaTwo)
    genericPullback
    (doctrinePullbackFiniteCodeIso first second)
    eOne eTwo eBase ?_ ?_ ?_ ?_
  · simpa [sigmaOne, sigmaTwo, eOne] using
      doctrinePullbackFiniteCodeIso_hom_fst first second
  · simpa [sigmaOne, sigmaTwo, eTwo] using
      doctrinePullbackFiniteCodeIso_hom_snd first second
  · simp [eOne, eBase]
  · simp [eTwo, eBase]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
