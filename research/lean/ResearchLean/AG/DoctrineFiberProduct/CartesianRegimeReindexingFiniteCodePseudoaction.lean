import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationCoherence
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-!
# Finite-code quotient pseudoaction by selected cartesian reindexing

This module chooses `Quotient.out` as a distinguished typed-presentation
representative of every morphism in the finite-code cartesian category.  The
chosen representative generates the selected contravariant reindexing
functor.  Equality in the quotient is used only to derive equality of decoded
semantic arrows; cartesian uniqueness then generates every comparison,
compositor, unitor, and coherence map.

In particular, no `Quotient.lift` targets a functor type.  Quotient-related
presentations generally determine canonically isomorphic, rather than
definitionally equal, selected functors.  The public surface therefore records
representative independence by natural isomorphisms and their generated laws.

## Implementation notes

The only noncomputable choice in the quotient action is the selected
`Quotient.out` representative.  Public constructors accept quotient morphisms,
typed presentations, and proofs that those presentations represent the stated
quotient morphisms.  They accept no lift, cleavage, endpoint isomorphism,
comparison component, natural isomorphism, or coherence certificate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 3000000

local infixr:81 " ≫q " => FiniteCodeCartHom.comp

private theorem finiteCodeComp_assoc
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject) :
    (first ≫q second) ≫q third = first ≫q (second ≫q third) := by
  exact @Category.assoc (FiniteCodeCartCategory U) _ firstObject
    secondObject thirdObject fourthObject first second third

private theorem finiteCodeId_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    (𝟙 source : FiniteCodeCartHom source source) ≫q hom = hom := by
  change (𝟙 source : source ⟶ source) ≫
    (hom : source ⟶ target) = hom
  exact Category.id_comp _

private theorem finiteCodeComp_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    hom ≫q (𝟙 target : FiniteCodeCartHom target target) = hom := by
  change (hom : source ⟶ target) ≫
    (𝟙 target : target ⟶ target) = hom
  exact Category.comp_id _

/-! ## Canonical representatives and semantic equalities -/

namespace FiniteCodeCartHom

/-- The distinguished typed-presentation representative selected by `Quotient.out`. -/
noncomputable def representative
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    CartPresentationBetween source target :=
  Quotient.out hom

/-- The selected representative belongs to the quotient morphism it represents. -/
theorem ofPresentation_representative
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    ofPresentation hom.representative = hom :=
  Quotient.out_eq hom

/-- Decoding an inserted presentation is its typed semantic decoder. -/
theorem toSemantic_ofPresentation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    toSemantic (ofPresentation presentation) =
      typedPresentationToSemantic presentation :=
  rfl

/-- Membership in a quotient morphism generates the corresponding semantic equality. -/
theorem presentation_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (presentation : CartPresentationBetween source target)
    (presentation_eq : ofPresentation presentation = hom) :
    typedPresentationToSemantic presentation = toSemantic hom := by
  calc
    _ = toSemantic (ofPresentation presentation) := rfl
    _ = toSemantic hom := congrArg toSemantic presentation_eq

/-- The selected representative decodes to the semantic arrow of its quotient class. -/
theorem representative_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    typedPresentationToSemantic hom.representative = toSemantic hom :=
  presentation_semantic_eq hom hom.representative
    (ofPresentation_representative hom)

/-- Two presentations of one quotient morphism have equal semantic decoders. -/
theorem presentations_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : ofPresentation first = hom)
    (second_eq : ofPresentation second = hom) :
    typedPresentationToSemantic first =
      typedPresentationToSemantic second :=
  (presentation_semantic_eq hom first first_eq).trans
    (presentation_semantic_eq hom second second_eq).symm

/-- Equal semantic decoders insert as the same finite-code quotient morphism. -/
theorem ofPresentation_eq_of_semantic
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second) :
    ofPresentation first = ofPresentation second := by
  apply Quotient.sound
  change typedPresentationToSemantic first =
    typedPresentationToSemantic second
  exact semantic_eq

/-- Inserting an authored composite is quotient composition of the inserted legs. -/
theorem ofPresentation_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    ofPresentation (compPresentation first second) =
      ofPresentation first ≫q ofPresentation second :=
  rfl

/-- Inserting the authored identity is the identity quotient morphism. -/
theorem ofPresentation_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U) :
    ofPresentation (idTypedPresentation instanceCode) =
      𝟙 instanceCode :=
  rfl

/-- Semantic realization preserves quotient composition. -/
theorem toSemantic_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target) :
    toSemantic (first ≫q second) = toSemantic first ≫ toSemantic second := by
  change (finiteCodeCartRealization :
      FiniteCodeCartCategory U ⥤ ExtractionInstance U).map (first ≫q second) =
    (finiteCodeCartRealization :
      FiniteCodeCartCategory U ⥤ ExtractionInstance U).map first ≫
      (finiteCodeCartRealization :
        FiniteCodeCartCategory U ⥤ ExtractionInstance U).map second
  exact (finiteCodeCartRealization :
    FiniteCodeCartCategory U ⥤ ExtractionInstance U).map_comp first second

/-- Semantic realization preserves the quotient identity. -/
theorem toSemantic_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U) :
    toSemantic (𝟙 instanceCode :
      FiniteCodeCartHom instanceCode instanceCode) =
      𝟙 instanceCode.toSemantic := by
  change (finiteCodeCartRealization :
      FiniteCodeCartCategory U ⥤ ExtractionInstance U).map
        (𝟙 instanceCode) =
    𝟙 ((finiteCodeCartRealization :
      FiniteCodeCartCategory U ⥤ ExtractionInstance U).obj instanceCode)
  exact (finiteCodeCartRealization :
    FiniteCodeCartCategory U ⥤ ExtractionInstance U).map_id instanceCode

/-- The selected representative of a composite has the composite semantic decoder. -/
theorem representative_comp_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target) :
    typedPresentationToSemantic (first ≫q second).representative =
      typedPresentationToSemantic first.representative ≫
        typedPresentationToSemantic second.representative := by
  calc
    _ = toSemantic (first ≫q second) := representative_semantic_eq _
    _ = toSemantic first ≫ toSemantic second := toSemantic_comp first second
    _ = _ := by
      rw [representative_semantic_eq, representative_semantic_eq]

/-- The selected representative of an identity has the identity semantic decoder. -/
theorem representative_id_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U) :
    typedPresentationToSemantic
        ((𝟙 instanceCode :
          FiniteCodeCartHom instanceCode instanceCode).representative) =
      𝟙 instanceCode.toSemantic := by
  calc
    _ = toSemantic (𝟙 instanceCode :
        FiniteCodeCartHom instanceCode instanceCode) :=
      representative_semantic_eq _
    _ = _ := toSemantic_id instanceCode

/-- Equal quotient morphisms have canonically equal representative decoders. -/
theorem representative_semantic_eq_of_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : FiniteCodeCartHom source target}
    (hom_eq : first = second) :
    typedPresentationToSemantic first.representative =
      typedPresentationToSemantic second.representative := by
  calc
    _ = toSemantic first := representative_semantic_eq first
    _ = toSemantic second := congrArg toSemantic hom_eq
    _ = _ := (representative_semantic_eq second).symm

end FiniteCodeCartHom

/-! ## The selected quotient action and representative independence -/

/--
The selected contravariant reindexing functor generated by the distinguished
representative of a finite-code quotient morphism.
-/
noncomputable def finiteCodeSelectedCoreFiberReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    CoreFiber target.toSemantic ⥤ CoreFiber source.toSemantic :=
  selectedTypedCoreFiberReindexFunctor hom.representative

/-- The selected lift generated by the distinguished representative of a quotient morphism. -/
noncomputable def finiteCodeSelectedCoreFiberCartesianLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    StrongCartesianLift (typedCartSemanticInput hom.representative)
      targetPackage :=
  selectedTypedCoreFiberCartesianLift hom.representative targetPackage

/--
The canonical component comparing the selected functors generated by any two
typed presentations of one quotient morphism.
-/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeComparisonApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = hom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = hom)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberReindexFunctor first).obj targetPackage ≅
      (selectedTypedCoreFiberReindexFunctor second).obj targetPackage :=
  selectedTypedCoreFiberPresentationComparisonApp first second
    (FiniteCodeCartHom.presentations_semantic_eq hom first second
      first_eq second_eq) targetPackage

/-- The forward representative comparison satisfies the selected-lift triangle. -/
theorem finiteCodeSelectedCoreFiberRepresentativeComparisonApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = hom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = hom)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberRepresentativeComparisonApp hom first second
      first_eq second_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberCartesianLift second targetPackage).hom =
      (selectedTypedCoreFiberCartesianLift first targetPackage).hom :=
  selectedTypedCoreFiberPresentationComparisonApp_hom_fac first second
    (FiniteCodeCartHom.presentations_semantic_eq hom first second
      first_eq second_eq) targetPackage

/-- The inverse representative comparison satisfies the reverse selected-lift triangle. -/
theorem finiteCodeSelectedCoreFiberRepresentativeComparisonApp_inv_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = hom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = hom)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberRepresentativeComparisonApp hom first second
      first_eq second_eq targetPackage).inv.1 ≫
        (selectedTypedCoreFiberCartesianLift first targetPackage).hom =
      (selectedTypedCoreFiberCartesianLift second targetPackage).hom :=
  selectedTypedCoreFiberPresentationComparisonApp_inv_fac first second
    (FiniteCodeCartHom.presentations_semantic_eq hom first second
      first_eq second_eq) targetPackage

/-- The representative comparison is natural on every vertical target map. -/
theorem finiteCodeSelectedCoreFiberRepresentativeComparison_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (quotientHom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = quotientHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = quotientHom)
    {sourcePackage targetPackage : CoreFiber target.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (selectedTypedCoreFiberReindexFunctor first).map hom ≫
        (finiteCodeSelectedCoreFiberRepresentativeComparisonApp quotientHom
          first second first_eq second_eq targetPackage).hom =
      (finiteCodeSelectedCoreFiberRepresentativeComparisonApp quotientHom
        first second first_eq second_eq sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor second).map hom :=
  selectedTypedCoreFiberPresentationComparison_naturality first second
    (FiniteCodeCartHom.presentations_semantic_eq quotientHom first second
      first_eq second_eq) hom

/--
The canonical natural isomorphism comparing the selected functors generated by
any two typed representatives of one finite-code quotient morphism.
-/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = hom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = hom) :
    selectedTypedCoreFiberReindexFunctor first ≅
      selectedTypedCoreFiberReindexFunctor second :=
  selectedTypedCoreFiberPresentationComparison first second
    (FiniteCodeCartHom.presentations_semantic_eq hom first second
      first_eq second_eq)

/-- The whole representative comparison is reflexive. -/
theorem finiteCodeSelectedCoreFiberRepresentativeComparison_refl
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (presentation : CartPresentationBetween source target)
    (presentation_eq : FiniteCodeCartHom.ofPresentation presentation = hom) :
    finiteCodeSelectedCoreFiberRepresentativeComparison hom
        presentation presentation presentation_eq presentation_eq =
      Iso.refl (selectedTypedCoreFiberReindexFunctor presentation) := by
  simpa only [finiteCodeSelectedCoreFiberRepresentativeComparison] using
    selectedTypedCoreFiberPresentationComparison_refl presentation

/-- Reversing a representative comparison gives the comparison in the reverse order. -/
theorem finiteCodeSelectedCoreFiberRepresentativeComparison_symm
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = hom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = hom) :
    (finiteCodeSelectedCoreFiberRepresentativeComparison hom first second
      first_eq second_eq).symm =
      finiteCodeSelectedCoreFiberRepresentativeComparison hom second first
        second_eq first_eq := by
  simpa only [finiteCodeSelectedCoreFiberRepresentativeComparison] using
    selectedTypedCoreFiberPresentationComparison_symm first second
      (FiniteCodeCartHom.presentations_semantic_eq hom first second
        first_eq second_eq)

/-- Representative comparisons satisfy the three-representative cocycle. -/
theorem finiteCodeSelectedCoreFiberRepresentativeComparison_cocycle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (first second third : CartPresentationBetween source target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = hom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = hom)
    (third_eq : FiniteCodeCartHom.ofPresentation third = hom) :
    (finiteCodeSelectedCoreFiberRepresentativeComparison hom first second
      first_eq second_eq).trans
        (finiteCodeSelectedCoreFiberRepresentativeComparison hom second third
          second_eq third_eq) =
      finiteCodeSelectedCoreFiberRepresentativeComparison hom first third
        first_eq third_eq := by
  simpa only [finiteCodeSelectedCoreFiberRepresentativeComparison] using
    selectedTypedCoreFiberPresentationComparison_cocycle first second third
      (FiniteCodeCartHom.presentations_semantic_eq hom first second
        first_eq second_eq)
      (FiniteCodeCartHom.presentations_semantic_eq hom second third
        second_eq third_eq)

/-- A supplied representative is canonically compared with the chosen quotient action. -/
noncomputable def finiteCodeSelectedCoreFiberCanonicalComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (presentation : CartPresentationBetween source target)
    (presentation_eq : FiniteCodeCartHom.ofPresentation presentation = hom) :
    selectedTypedCoreFiberReindexFunctor presentation ≅
      finiteCodeSelectedCoreFiberReindexFunctor hom :=
  finiteCodeSelectedCoreFiberRepresentativeComparison hom presentation
    hom.representative presentation_eq
    (FiniteCodeCartHom.ofPresentation_representative hom)

/-- Equality of quotient morphisms generates a comparison of their selected actions. -/
noncomputable def finiteCodeSelectedCoreFiberHomComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : FiniteCodeCartHom source target}
    (hom_eq : first = second) :
    finiteCodeSelectedCoreFiberReindexFunctor first ≅
      finiteCodeSelectedCoreFiberReindexFunctor second :=
  selectedTypedCoreFiberPresentationComparison first.representative
    second.representative
    (FiniteCodeCartHom.representative_semantic_eq_of_eq hom_eq)

/-- The quotient-hom equality comparison satisfies its selected-lift triangle. -/
theorem finiteCodeSelectedCoreFiberHomComparison_hom_app_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : FiniteCodeCartHom source target}
    (hom_eq : first = second)
    (targetPackage : CoreFiber target.toSemantic) :
    ((finiteCodeSelectedCoreFiberHomComparison hom_eq).hom.app
        targetPackage).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift second targetPackage).hom =
      (finiteCodeSelectedCoreFiberCartesianLift first targetPackage).hom := by
  simpa only [finiteCodeSelectedCoreFiberHomComparison,
    finiteCodeSelectedCoreFiberCartesianLift] using
      selectedTypedCoreFiberPresentationComparisonApp_hom_fac
        first.representative second.representative
        (FiniteCodeCartHom.representative_semantic_eq_of_eq hom_eq)
        targetPackage

/-- The quotient-hom equality comparison is reflexive. -/
theorem finiteCodeSelectedCoreFiberHomComparison_refl
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target) :
    finiteCodeSelectedCoreFiberHomComparison (rfl : hom = hom) =
      Iso.refl (finiteCodeSelectedCoreFiberReindexFunctor hom) := by
  simpa only [finiteCodeSelectedCoreFiberHomComparison,
    finiteCodeSelectedCoreFiberReindexFunctor] using
      selectedTypedCoreFiberPresentationComparison_refl hom.representative

/--
The comparison generated by equality of quotient morphisms is the corresponding
equality isomorphism between their distinguished selected actions.

This bridge does not identify actions of different quotient morphisms.  It says
that, after a quotient equality has already been supplied, cartesian uniqueness
generates the same comparison as equality elimination on the selected action.
-/
theorem finiteCodeSelectedCoreFiberHomComparison_eqToIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : FiniteCodeCartHom source target}
    (hom_eq : first = second) :
    finiteCodeSelectedCoreFiberHomComparison hom_eq =
      eqToIso (congrArg finiteCodeSelectedCoreFiberReindexFunctor hom_eq) := by
  cases hom_eq
  rw [finiteCodeSelectedCoreFiberHomComparison_refl]
  rfl

private theorem finiteCodeSelectedCoreFiberHomComparison_hom_app_eqToHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : FiniteCodeCartHom source target}
    (hom_eq : first = second)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberHomComparison hom_eq).hom.app targetPackage =
      eqToHom (congrArg
        (fun hom : FiniteCodeCartHom source target =>
          (finiteCodeSelectedCoreFiberReindexFunctor hom).obj targetPackage)
        hom_eq) := by
  subst second
  simpa using congrArg (fun comparison => comparison.hom.app targetPackage)
    (finiteCodeSelectedCoreFiberHomComparison_refl first)

/-- Reversing quotient-hom equality reverses its generated comparison. -/
theorem finiteCodeSelectedCoreFiberHomComparison_symm
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second : FiniteCodeCartHom source target}
    (hom_eq : first = second) :
    (finiteCodeSelectedCoreFiberHomComparison hom_eq).symm =
      finiteCodeSelectedCoreFiberHomComparison hom_eq.symm := by
  simpa only [finiteCodeSelectedCoreFiberHomComparison] using
    selectedTypedCoreFiberPresentationComparison_symm first.representative
      second.representative
      (FiniteCodeCartHom.representative_semantic_eq_of_eq hom_eq)

/-- Quotient-hom equality comparisons satisfy the equality cocycle. -/
theorem finiteCodeSelectedCoreFiberHomComparison_cocycle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    {first second third : FiniteCodeCartHom source target}
    (first_second_eq : first = second)
    (second_third_eq : second = third) :
    (finiteCodeSelectedCoreFiberHomComparison first_second_eq).trans
        (finiteCodeSelectedCoreFiberHomComparison second_third_eq) =
      finiteCodeSelectedCoreFiberHomComparison
        (first_second_eq.trans second_third_eq) := by
  simpa only [finiteCodeSelectedCoreFiberHomComparison] using
    selectedTypedCoreFiberPresentationComparison_cocycle
      first.representative second.representative third.representative
      (FiniteCodeCartHom.representative_semantic_eq_of_eq first_second_eq)
      (FiniteCodeCartHom.representative_semantic_eq_of_eq second_third_eq)

/-! ## Quotient-level compositor and unitor -/

/-- The canonical quotient-level contravariant compositor component. -/
noncomputable def finiteCodeSelectedCoreFiberCompositorApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberReindexFunctor second ⋙
        finiteCodeSelectedCoreFiberReindexFunctor first).obj targetPackage ≅
      (finiteCodeSelectedCoreFiberReindexFunctor (first ≫q second)).obj
        targetPackage :=
  selectedTypedCoreFiberPresentationCompositorApp
    (first ≫q second).representative first.representative
      second.representative
      (FiniteCodeCartHom.representative_comp_semantic_eq first second)
      targetPackage

/-- The forward quotient compositor satisfies the two-step selected-lift triangle. -/
theorem finiteCodeSelectedCoreFiberCompositorApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberCompositorApp first second
      targetPackage).hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift (first ≫q second)
          targetPackage).hom =
      (selectedCoreFiberIteratedCartesianLift first.representative
        second.representative targetPackage).hom :=
  selectedTypedCoreFiberPresentationCompositorApp_hom_fac
    (first ≫q second).representative first.representative
      second.representative
      (FiniteCodeCartHom.representative_comp_semantic_eq first second)
      targetPackage

/-- The inverse quotient compositor satisfies the reverse two-step triangle. -/
theorem finiteCodeSelectedCoreFiberCompositorApp_inv_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberCompositorApp first second
      targetPackage).inv.1 ≫
        (selectedCoreFiberIteratedCartesianLift first.representative
          second.representative targetPackage).hom =
      (finiteCodeSelectedCoreFiberCartesianLift (first ≫q second)
        targetPackage).hom :=
  selectedTypedCoreFiberPresentationCompositorApp_inv_fac
    (first ≫q second).representative first.representative
      second.representative
      (FiniteCodeCartHom.representative_comp_semantic_eq first second)
      targetPackage

/-- The quotient compositor is natural on every vertical target map. -/
theorem finiteCodeSelectedCoreFiberCompositor_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    {sourcePackage targetPackage : CoreFiber target.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (finiteCodeSelectedCoreFiberReindexFunctor second ⋙
        finiteCodeSelectedCoreFiberReindexFunctor first).map hom ≫
        (finiteCodeSelectedCoreFiberCompositorApp first second
          targetPackage).hom =
      (finiteCodeSelectedCoreFiberCompositorApp first second
        sourcePackage).hom ≫
        (finiteCodeSelectedCoreFiberReindexFunctor (first ≫q second)).map
          hom :=
  selectedTypedCoreFiberPresentationCompositor_naturality
    (first ≫q second).representative first.representative
      second.representative
      (FiniteCodeCartHom.representative_comp_semantic_eq first second) hom

/-- The canonical quotient-level contravariant compositor. -/
noncomputable def finiteCodeSelectedCoreFiberCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target) :
    finiteCodeSelectedCoreFiberReindexFunctor second ⋙
        finiteCodeSelectedCoreFiberReindexFunctor first ≅
      finiteCodeSelectedCoreFiberReindexFunctor (first ≫q second) :=
  selectedTypedCoreFiberPresentationCompositor
    (first ≫q second).representative first.representative
      second.representative
      (FiniteCodeCartHom.representative_comp_semantic_eq first second)

/-- The quotient compositor has the explicitly generated component above. -/
theorem finiteCodeSelectedCoreFiberCompositor_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberCompositor first second).app targetPackage =
      finiteCodeSelectedCoreFiberCompositorApp first second targetPackage :=
  rfl

/-- Forward component projection of the quotient compositor. -/
theorem finiteCodeSelectedCoreFiberCompositor_hom_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberCompositor first second).hom.app targetPackage =
      (finiteCodeSelectedCoreFiberCompositorApp first second
        targetPackage).hom :=
  rfl

/-- Inverse component projection of the quotient compositor. -/
theorem finiteCodeSelectedCoreFiberCompositor_inv_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : FiniteCodeCartHom source middle)
    (second : FiniteCodeCartHom middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberCompositor first second).inv.app targetPackage =
      (finiteCodeSelectedCoreFiberCompositorApp first second
        targetPackage).inv :=
  rfl

/-- The canonical quotient-level contravariant unitor component. -/
noncomputable def finiteCodeSelectedCoreFiberUnitorApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    targetPackage ≅
      (finiteCodeSelectedCoreFiberReindexFunctor (𝟙 instanceCode)).obj
        targetPackage :=
  selectedTypedCoreFiberPresentationUnitorApp instanceCode
    (𝟙 instanceCode :
      FiniteCodeCartHom instanceCode instanceCode).representative
    (FiniteCodeCartHom.representative_id_semantic_eq instanceCode)
    targetPackage

/-- The forward quotient unitor satisfies the selected identity-lift triangle. -/
theorem finiteCodeSelectedCoreFiberUnitorApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberUnitorApp instanceCode
      targetPackage).hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift (𝟙 instanceCode)
          targetPackage).hom =
      𝟙 targetPackage.1 :=
  selectedTypedCoreFiberPresentationUnitorApp_hom_fac instanceCode
    (𝟙 instanceCode :
      FiniteCodeCartHom instanceCode instanceCode).representative
    (FiniteCodeCartHom.representative_id_semantic_eq instanceCode)
    targetPackage

/-- The inverse quotient unitor is the selected canonical identity lift. -/
theorem finiteCodeSelectedCoreFiberUnitorApp_inv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberUnitorApp instanceCode
      targetPackage).inv.1 =
      (finiteCodeSelectedCoreFiberCartesianLift (𝟙 instanceCode)
        targetPackage).hom :=
  selectedTypedCoreFiberPresentationUnitorApp_inv instanceCode
    (𝟙 instanceCode :
      FiniteCodeCartHom instanceCode instanceCode).representative
    (FiniteCodeCartHom.representative_id_semantic_eq instanceCode)
    targetPackage

/-- The quotient unitor is natural on every vertical map. -/
theorem finiteCodeSelectedCoreFiberUnitor_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    {sourcePackage targetPackage : CoreFiber instanceCode.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    hom ≫ (finiteCodeSelectedCoreFiberUnitorApp instanceCode
        targetPackage).hom =
      (finiteCodeSelectedCoreFiberUnitorApp instanceCode
        sourcePackage).hom ≫
        (finiteCodeSelectedCoreFiberReindexFunctor
          (𝟙 instanceCode)).map hom :=
  selectedTypedCoreFiberPresentationUnitor_naturality instanceCode
    (𝟙 instanceCode :
      FiniteCodeCartHom instanceCode instanceCode).representative
    (FiniteCodeCartHom.representative_id_semantic_eq instanceCode) hom

/-- The canonical quotient-level contravariant unitor. -/
noncomputable def finiteCodeSelectedCoreFiberUnitor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U) :
    Functor.id (CoreFiber instanceCode.toSemantic) ≅
      finiteCodeSelectedCoreFiberReindexFunctor (𝟙 instanceCode) :=
  selectedTypedCoreFiberPresentationUnitor instanceCode
    (𝟙 instanceCode :
      FiniteCodeCartHom instanceCode instanceCode).representative
    (FiniteCodeCartHom.representative_id_semantic_eq instanceCode)

/-- The quotient unitor has the explicitly generated component above. -/
theorem finiteCodeSelectedCoreFiberUnitor_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberUnitor instanceCode).app targetPackage =
      finiteCodeSelectedCoreFiberUnitorApp instanceCode targetPackage :=
  rfl

/-- Forward component projection of the quotient unitor. -/
theorem finiteCodeSelectedCoreFiberUnitor_hom_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberUnitor instanceCode).hom.app targetPackage =
      (finiteCodeSelectedCoreFiberUnitorApp instanceCode targetPackage).hom :=
  rfl

/-- Inverse component projection of the quotient unitor. -/
theorem finiteCodeSelectedCoreFiberUnitor_inv_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberUnitor instanceCode).inv.app targetPackage =
      (finiteCodeSelectedCoreFiberUnitorApp instanceCode targetPackage).inv :=
  rfl

/-! ## Arbitrary-representative composition and unit laws -/

namespace FiniteCodeCartHom

/--
Membership of three typed representatives in two quotient morphisms and their
composite generates the semantic composition equation.
-/
theorem presentations_comp_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : ofPresentation direct = firstHom ≫q secondHom)
    (first_eq : ofPresentation first = firstHom)
    (second_eq : ofPresentation second = secondHom) :
    typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second := by
  calc
    _ = toSemantic (firstHom ≫q secondHom) :=
      presentation_semantic_eq (firstHom ≫q secondHom) direct direct_eq
    _ = toSemantic firstHom ≫ toSemantic secondHom :=
      toSemantic_comp firstHom secondHom
    _ = _ := by
      rw [← presentation_semantic_eq firstHom first first_eq,
        ← presentation_semantic_eq secondHom second second_eq]

/-- Membership in the quotient identity generates the semantic identity equation. -/
theorem presentation_id_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : ofPresentation identityPresentation = 𝟙 instanceCode) :
    typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic := by
  calc
    _ = toSemantic (𝟙 instanceCode :
        FiniteCodeCartHom instanceCode instanceCode) :=
      presentation_semantic_eq (𝟙 instanceCode) identityPresentation
        identity_eq
    _ = _ := toSemantic_id instanceCode

end FiniteCodeCartHom

/--
The relative compositor component generated by arbitrary typed representatives
of two quotient morphisms and their composite.
-/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeCompositorApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : FiniteCodeCartHom.ofPresentation direct =
      firstHom ≫q secondHom)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first).obj targetPackage ≅
      (selectedTypedCoreFiberReindexFunctor direct).obj targetPackage :=
  selectedTypedCoreFiberPresentationCompositorApp direct first second
    (FiniteCodeCartHom.presentations_comp_semantic_eq firstHom secondHom
      direct first second direct_eq first_eq second_eq) targetPackage

/-- The arbitrary-representative compositor satisfies its forward lift triangle. -/
theorem finiteCodeSelectedCoreFiberRepresentativeCompositorApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : FiniteCodeCartHom.ofPresentation direct =
      firstHom ≫q secondHom)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberRepresentativeCompositorApp firstHom secondHom
      direct first second direct_eq first_eq second_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberCartesianLift direct targetPackage).hom =
      (selectedCoreFiberIteratedCartesianLift first second
        targetPackage).hom :=
  selectedTypedCoreFiberPresentationCompositorApp_hom_fac direct first second
    (FiniteCodeCartHom.presentations_comp_semantic_eq firstHom secondHom
      direct first second direct_eq first_eq second_eq) targetPackage

/-- The arbitrary-representative compositor satisfies its inverse lift triangle. -/
theorem finiteCodeSelectedCoreFiberRepresentativeCompositorApp_inv_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : FiniteCodeCartHom.ofPresentation direct =
      firstHom ≫q secondHom)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberRepresentativeCompositorApp firstHom secondHom
      direct first second direct_eq first_eq second_eq targetPackage).inv.1 ≫
        (selectedCoreFiberIteratedCartesianLift first second
          targetPackage).hom =
      (selectedTypedCoreFiberCartesianLift direct targetPackage).hom :=
  selectedTypedCoreFiberPresentationCompositorApp_inv_fac direct first second
    (FiniteCodeCartHom.presentations_comp_semantic_eq firstHom secondHom
      direct first second direct_eq first_eq second_eq) targetPackage

/-- The arbitrary-representative compositor is natural on vertical target maps. -/
theorem finiteCodeSelectedCoreFiberRepresentativeCompositor_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : FiniteCodeCartHom.ofPresentation direct =
      firstHom ≫q secondHom)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom)
    {sourcePackage targetPackage : CoreFiber target.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first).map hom ≫
        (finiteCodeSelectedCoreFiberRepresentativeCompositorApp firstHom
          secondHom direct first second direct_eq first_eq second_eq
          targetPackage).hom =
      (finiteCodeSelectedCoreFiberRepresentativeCompositorApp firstHom
        secondHom direct first second direct_eq first_eq second_eq
        sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor direct).map hom :=
  selectedTypedCoreFiberPresentationCompositor_naturality direct first second
    (FiniteCodeCartHom.presentations_comp_semantic_eq firstHom secondHom
      direct first second direct_eq first_eq second_eq) hom

/-- The relative compositor generated by arbitrary representatives of quotient data. -/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : FiniteCodeCartHom.ofPresentation direct =
      firstHom ≫q secondHom)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom) :
    selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first ≅
      selectedTypedCoreFiberReindexFunctor direct :=
  selectedTypedCoreFiberPresentationCompositor direct first second
    (FiniteCodeCartHom.presentations_comp_semantic_eq firstHom secondHom
      direct first second direct_eq first_eq second_eq)

/--
The horizontal comparison from arbitrary leg representatives to the canonical
representatives of the two quotient morphisms.
-/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeHorizontalComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom) :
    selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first ≅
      finiteCodeSelectedCoreFiberReindexFunctor secondHom ⋙
        finiteCodeSelectedCoreFiberReindexFunctor firstHom :=
  selectedTypedCoreFiberPresentationHorizontalComparison first
    firstHom.representative second secondHom.representative
    (FiniteCodeCartHom.presentations_semantic_eq firstHom first
      firstHom.representative first_eq
      (FiniteCodeCartHom.ofPresentation_representative firstHom))
    (FiniteCodeCartHom.presentations_semantic_eq secondHom second
      secondHom.representative second_eq
      (FiniteCodeCartHom.ofPresentation_representative secondHom))

/--
The arbitrary-representative compositor descends to the selected quotient
compositor through producer-generated representative comparisons.
-/
theorem finiteCodeSelectedCoreFiberRepresentativeCompositor_compatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (firstHom : FiniteCodeCartHom source middle)
    (secondHom : FiniteCodeCartHom middle target)
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (direct_eq : FiniteCodeCartHom.ofPresentation direct =
      firstHom ≫q secondHom)
    (first_eq : FiniteCodeCartHom.ofPresentation first = firstHom)
    (second_eq : FiniteCodeCartHom.ofPresentation second = secondHom) :
    (finiteCodeSelectedCoreFiberRepresentativeCompositor firstHom secondHom
      direct first second direct_eq first_eq second_eq).trans
        (finiteCodeSelectedCoreFiberCanonicalComparison (firstHom ≫q secondHom)
          direct direct_eq) =
      (finiteCodeSelectedCoreFiberRepresentativeHorizontalComparison firstHom
        secondHom first second first_eq second_eq).trans
        (finiteCodeSelectedCoreFiberCompositor firstHom secondHom) := by
  simpa only [finiteCodeSelectedCoreFiberRepresentativeCompositor,
    finiteCodeSelectedCoreFiberCanonicalComparison,
    finiteCodeSelectedCoreFiberRepresentativeComparison,
    finiteCodeSelectedCoreFiberRepresentativeHorizontalComparison,
    finiteCodeSelectedCoreFiberCompositor,
    finiteCodeSelectedCoreFiberReindexFunctor] using
      selectedTypedCoreFiberPresentationCompositor_compatibility direct
        (firstHom ≫q secondHom).representative first firstHom.representative
        second secondHom.representative
        (FiniteCodeCartHom.presentations_comp_semantic_eq firstHom secondHom
          direct first second direct_eq first_eq second_eq)
        (FiniteCodeCartHom.representative_comp_semantic_eq firstHom secondHom)
        (FiniteCodeCartHom.presentations_semantic_eq firstHom first
          firstHom.representative first_eq
          (FiniteCodeCartHom.ofPresentation_representative firstHom))
        (FiniteCodeCartHom.presentations_semantic_eq secondHom second
          secondHom.representative second_eq
          (FiniteCodeCartHom.ofPresentation_representative secondHom))

/-- The relative unitor component generated by an arbitrary identity representative. -/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeUnitorApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : FiniteCodeCartHom.ofPresentation identityPresentation =
      𝟙 instanceCode)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    targetPackage ≅
      (selectedTypedCoreFiberReindexFunctor identityPresentation).obj
        targetPackage :=
  selectedTypedCoreFiberPresentationUnitorApp instanceCode
    identityPresentation
    (FiniteCodeCartHom.presentation_id_semantic_eq instanceCode
      identityPresentation identity_eq) targetPackage

/-- The arbitrary identity representative satisfies the forward unitor triangle. -/
theorem finiteCodeSelectedCoreFiberRepresentativeUnitorApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : FiniteCodeCartHom.ofPresentation identityPresentation =
      𝟙 instanceCode)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberRepresentativeUnitorApp instanceCode
      identityPresentation identity_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberCartesianLift identityPresentation
          targetPackage).hom =
      𝟙 targetPackage.1 :=
  selectedTypedCoreFiberPresentationUnitorApp_hom_fac instanceCode
    identityPresentation
    (FiniteCodeCartHom.presentation_id_semantic_eq instanceCode
      identityPresentation identity_eq) targetPackage

/-- The inverse arbitrary-representative unitor is its generated identity lift. -/
theorem finiteCodeSelectedCoreFiberRepresentativeUnitorApp_inv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : FiniteCodeCartHom.ofPresentation identityPresentation =
      𝟙 instanceCode)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (finiteCodeSelectedCoreFiberRepresentativeUnitorApp instanceCode
      identityPresentation identity_eq targetPackage).inv.1 =
      (selectedTypedCoreFiberCartesianLift identityPresentation
        targetPackage).hom :=
  selectedTypedCoreFiberPresentationUnitorApp_inv instanceCode
    identityPresentation
    (FiniteCodeCartHom.presentation_id_semantic_eq instanceCode
      identityPresentation identity_eq) targetPackage

/-- The arbitrary-representative unitor is natural on vertical maps. -/
theorem finiteCodeSelectedCoreFiberRepresentativeUnitor_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : FiniteCodeCartHom.ofPresentation identityPresentation =
      𝟙 instanceCode)
    {sourcePackage targetPackage : CoreFiber instanceCode.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    hom ≫ (finiteCodeSelectedCoreFiberRepresentativeUnitorApp instanceCode
        identityPresentation identity_eq targetPackage).hom =
      (finiteCodeSelectedCoreFiberRepresentativeUnitorApp instanceCode
        identityPresentation identity_eq sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor identityPresentation).map hom :=
  selectedTypedCoreFiberPresentationUnitor_naturality instanceCode
    identityPresentation
    (FiniteCodeCartHom.presentation_id_semantic_eq instanceCode
      identityPresentation identity_eq) hom

/-- The relative unitor generated by an arbitrary quotient identity representative. -/
noncomputable def finiteCodeSelectedCoreFiberRepresentativeUnitor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : FiniteCodeCartHom.ofPresentation identityPresentation =
      𝟙 instanceCode) :
    Functor.id (CoreFiber instanceCode.toSemantic) ≅
      selectedTypedCoreFiberReindexFunctor identityPresentation :=
  selectedTypedCoreFiberPresentationUnitor instanceCode identityPresentation
    (FiniteCodeCartHom.presentation_id_semantic_eq instanceCode
      identityPresentation identity_eq)

/--
The arbitrary identity representative descends to the selected quotient
unitor through its producer-generated representative comparison.
-/
theorem finiteCodeSelectedCoreFiberRepresentativeUnitor_compatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation :
      CartPresentationBetween instanceCode instanceCode)
    (identity_eq : FiniteCodeCartHom.ofPresentation identityPresentation =
      𝟙 instanceCode) :
    (finiteCodeSelectedCoreFiberRepresentativeUnitor instanceCode
      identityPresentation identity_eq).trans
        (finiteCodeSelectedCoreFiberCanonicalComparison (𝟙 instanceCode)
          identityPresentation identity_eq) =
      finiteCodeSelectedCoreFiberUnitor instanceCode := by
  simpa only [finiteCodeSelectedCoreFiberRepresentativeUnitor,
    finiteCodeSelectedCoreFiberCanonicalComparison,
    finiteCodeSelectedCoreFiberRepresentativeComparison,
    finiteCodeSelectedCoreFiberUnitor,
    finiteCodeSelectedCoreFiberReindexFunctor] using
      selectedTypedCoreFiberPresentationUnitor_compatibility instanceCode
        identityPresentation
        (𝟙 instanceCode :
          FiniteCodeCartHom instanceCode instanceCode).representative
        (FiniteCodeCartHom.presentation_id_semantic_eq instanceCode
          identityPresentation identity_eq)
        (FiniteCodeCartHom.representative_id_semantic_eq instanceCode)

/-! ## Quotient-level associativity and unit coherence -/

/-- The literal three-step selected lift underlying quotient associativity. -/
noncomputable def finiteCodeSelectedCoreFiberTripleIteratedLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject)
    (targetPackage : CoreFiber fourthObject.toSemantic) :
    ((finiteCodeSelectedCoreFiberReindexFunctor first).obj
      ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
        ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
          targetPackage))).1 ⟶ targetPackage.1 :=
  (finiteCodeSelectedCoreFiberCartesianLift first
    ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
      ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
        targetPackage))).hom ≫
    ((finiteCodeSelectedCoreFiberCartesianLift second
      ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
        targetPackage)).hom ≫
      (finiteCodeSelectedCoreFiberCartesianLift third targetPackage).hom)

/-- The left-associated route through the two quotient compositors. -/
noncomputable def finiteCodeSelectedCoreFiberAssocLeftRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject)
    (targetPackage : CoreFiber fourthObject.toSemantic) :
    (finiteCodeSelectedCoreFiberReindexFunctor first).obj
        ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)) ⟶
      (finiteCodeSelectedCoreFiberReindexFunctor
        ((first ≫q second) ≫q third)).obj targetPackage :=
  (finiteCodeSelectedCoreFiberCompositorApp first second
      ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
        targetPackage)).hom ≫
    (finiteCodeSelectedCoreFiberCompositorApp (first ≫q second) third
      targetPackage).hom

/--
The right-associated quotient route, followed by the comparison generated by
categorical associativity of quotient morphisms.
-/
noncomputable def finiteCodeSelectedCoreFiberAssocRightRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject)
    (targetPackage : CoreFiber fourthObject.toSemantic) :
    (finiteCodeSelectedCoreFiberReindexFunctor first).obj
        ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)) ⟶
      (finiteCodeSelectedCoreFiberReindexFunctor
        ((first ≫q second) ≫q third)).obj targetPackage :=
  (finiteCodeSelectedCoreFiberReindexFunctor first).map
      (finiteCodeSelectedCoreFiberCompositorApp second third
        targetPackage).hom ≫
    (finiteCodeSelectedCoreFiberCompositorApp first (second ≫q third)
      targetPackage).hom ≫
    (finiteCodeSelectedCoreFiberHomComparison
      (finiteCodeComp_assoc first second third).symm).hom.app targetPackage

/-- The left quotient associativity route factors as the literal three-step lift. -/
theorem finiteCodeSelectedCoreFiberAssocLeftRoute_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject)
    (targetPackage : CoreFiber fourthObject.toSemantic) :
    (finiteCodeSelectedCoreFiberAssocLeftRoute first second third
      targetPackage).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift
          ((first ≫q second) ≫q third) targetPackage).hom =
      finiteCodeSelectedCoreFiberTripleIteratedLift first second third
        targetPackage := by
  change
    ((finiteCodeSelectedCoreFiberCompositorApp first second
        ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
          targetPackage)).hom.1 ≫
      (finiteCodeSelectedCoreFiberCompositorApp (first ≫q second) third
        targetPackage).hom.1) ≫
      (finiteCodeSelectedCoreFiberCartesianLift
        ((first ≫q second) ≫q third) targetPackage).hom =
    finiteCodeSelectedCoreFiberTripleIteratedLift first second third
      targetPackage
  calc
    _ = (finiteCodeSelectedCoreFiberCompositorApp first second
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom.1 ≫
        ((finiteCodeSelectedCoreFiberCompositorApp (first ≫q second) third
          targetPackage).hom.1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift
            ((first ≫q second) ≫q third) targetPackage).hom) :=
      Category.assoc _ _ _
    _ = (finiteCodeSelectedCoreFiberCompositorApp first second
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom.1 ≫
        (selectedCoreFiberIteratedCartesianLift
          (first ≫q second).representative third.representative
          targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberCompositorApp_hom_fac]
    _ = (finiteCodeSelectedCoreFiberCompositorApp first second
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom.1 ≫
        ((finiteCodeSelectedCoreFiberCartesianLift (first ≫q second)
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom ≫
          (finiteCodeSelectedCoreFiberCartesianLift third
            targetPackage).hom) := rfl
    _ = ((finiteCodeSelectedCoreFiberCompositorApp first second
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift (first ≫q second)
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom) ≫
          (finiteCodeSelectedCoreFiberCartesianLift third
            targetPackage).hom := (Category.assoc _ _ _).symm
    _ = (selectedCoreFiberIteratedCartesianLift first.representative
          second.representative
          ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
            targetPackage)).hom ≫
        (finiteCodeSelectedCoreFiberCartesianLift third
          targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberCompositorApp_hom_fac]
    _ = finiteCodeSelectedCoreFiberTripleIteratedLift first second third
        targetPackage := rfl

/-- The right quotient associativity route factors as the same three-step lift. -/
theorem finiteCodeSelectedCoreFiberAssocRightRoute_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject)
    (targetPackage : CoreFiber fourthObject.toSemantic) :
    (finiteCodeSelectedCoreFiberAssocRightRoute first second third
      targetPackage).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift
          ((first ≫q second) ≫q third) targetPackage).hom =
      finiteCodeSelectedCoreFiberTripleIteratedLift first second third
        targetPackage := by
  change
    ((((finiteCodeSelectedCoreFiberReindexFunctor first).map
        (finiteCodeSelectedCoreFiberCompositorApp second third
          targetPackage).hom).1 ≫
      (finiteCodeSelectedCoreFiberCompositorApp first (second ≫q third)
        targetPackage).hom.1) ≫
      ((finiteCodeSelectedCoreFiberHomComparison
        (finiteCodeComp_assoc first second third).symm).hom.app
          targetPackage).1) ≫
      (finiteCodeSelectedCoreFiberCartesianLift
        ((first ≫q second) ≫q third) targetPackage).hom =
    finiteCodeSelectedCoreFiberTripleIteratedLift first second third
      targetPackage
  calc
    _ = (((finiteCodeSelectedCoreFiberReindexFunctor first).map
          (finiteCodeSelectedCoreFiberCompositorApp second third
            targetPackage).hom).1 ≫
        (finiteCodeSelectedCoreFiberCompositorApp first (second ≫q third)
          targetPackage).hom.1) ≫
        (((finiteCodeSelectedCoreFiberHomComparison
          (finiteCodeComp_assoc first second third).symm).hom.app
            targetPackage).1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift
            ((first ≫q second) ≫q third) targetPackage).hom) :=
      Category.assoc _ _ _
    _ = (((finiteCodeSelectedCoreFiberReindexFunctor first).map
          (finiteCodeSelectedCoreFiberCompositorApp second third
            targetPackage).hom).1 ≫
        (finiteCodeSelectedCoreFiberCompositorApp first (second ≫q third)
          targetPackage).hom.1) ≫
        (finiteCodeSelectedCoreFiberCartesianLift
          (first ≫q (second ≫q third)) targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberHomComparison_hom_app_fac]
    _ = ((finiteCodeSelectedCoreFiberReindexFunctor first).map
          (finiteCodeSelectedCoreFiberCompositorApp second third
            targetPackage).hom).1 ≫
        ((finiteCodeSelectedCoreFiberCompositorApp first (second ≫q third)
          targetPackage).hom.1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift
            (first ≫q (second ≫q third)) targetPackage).hom) :=
      Category.assoc _ _ _
    _ = ((finiteCodeSelectedCoreFiberReindexFunctor first).map
          (finiteCodeSelectedCoreFiberCompositorApp second third
            targetPackage).hom).1 ≫
        (selectedCoreFiberIteratedCartesianLift first.representative
          (second ≫q third).representative targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberCompositorApp_hom_fac]
    _ = ((finiteCodeSelectedCoreFiberReindexFunctor first).map
          (finiteCodeSelectedCoreFiberCompositorApp second third
            targetPackage).hom).1 ≫
        ((finiteCodeSelectedCoreFiberCartesianLift first
          ((finiteCodeSelectedCoreFiberReindexFunctor
            (second ≫q third)).obj targetPackage)).hom ≫
          (finiteCodeSelectedCoreFiberCartesianLift (second ≫q third)
            targetPackage).hom) := rfl
    _ = (((finiteCodeSelectedCoreFiberReindexFunctor first).map
          (finiteCodeSelectedCoreFiberCompositorApp second third
            targetPackage).hom).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift first
          ((finiteCodeSelectedCoreFiberReindexFunctor
            (second ≫q third)).obj targetPackage)).hom) ≫
          (finiteCodeSelectedCoreFiberCartesianLift (second ≫q third)
            targetPackage).hom := (Category.assoc _ _ _).symm
    _ = ((finiteCodeSelectedCoreFiberCartesianLift first
          ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
            ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
              targetPackage))).hom ≫
        (finiteCodeSelectedCoreFiberCompositorApp second third
          targetPackage).hom.1) ≫
          (finiteCodeSelectedCoreFiberCartesianLift (second ≫q third)
            targetPackage).hom := by
      have hmap := selectedTypedCoreFiberReindexFunctor_map_fac
        first.representative
        (finiteCodeSelectedCoreFiberCompositorApp second third
          targetPackage).hom
      have hpost := congrArg
        (fun arrow => arrow ≫
          (finiteCodeSelectedCoreFiberCartesianLift (second ≫q third)
            targetPackage).hom)
        hmap
      simpa only [finiteCodeSelectedCoreFiberReindexFunctor,
        finiteCodeSelectedCoreFiberCartesianLift] using hpost
    _ = (finiteCodeSelectedCoreFiberCartesianLift first
          ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
            ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
              targetPackage))).hom ≫
        ((finiteCodeSelectedCoreFiberCompositorApp second third
          targetPackage).hom.1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift (second ≫q third)
            targetPackage).hom) := Category.assoc _ _ _
    _ = (finiteCodeSelectedCoreFiberCartesianLift first
          ((finiteCodeSelectedCoreFiberReindexFunctor second).obj
            ((finiteCodeSelectedCoreFiberReindexFunctor third).obj
              targetPackage))).hom ≫
        (selectedCoreFiberIteratedCartesianLift second.representative
          third.representative targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberCompositorApp_hom_fac]
    _ = finiteCodeSelectedCoreFiberTripleIteratedLift first second third
        targetPackage := rfl

/--
Quotient compositors satisfy the associativity pentagon component on every
target package.
-/
theorem finiteCodeSelectedCoreFiberCompositor_assoc
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {firstObject secondObject thirdObject fourthObject : FiniteInstanceCode U}
    (first : FiniteCodeCartHom firstObject secondObject)
    (second : FiniteCodeCartHom secondObject thirdObject)
    (third : FiniteCodeCartHom thirdObject fourthObject)
    (targetPackage : CoreFiber fourthObject.toSemantic) :
    finiteCodeSelectedCoreFiberAssocLeftRoute first second third
        targetPackage =
      finiteCodeSelectedCoreFiberAssocRightRoute first second third
        targetPackage := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let directLift := finiteCodeSelectedCoreFiberCartesianLift
    ((first ≫q second) ≫q third) targetPackage
  letI := directLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U)
    (typedCartSemanticInput ((first ≫q second) ≫q third).representative).hom
    directLift.hom (𝟙 firstObject.toSemantic)
  change
    (finiteCodeSelectedCoreFiberAssocLeftRoute first second third
      targetPackage).1 ≫ directLift.hom =
      (finiteCodeSelectedCoreFiberAssocRightRoute first second third
        targetPackage).1 ≫ directLift.hom
  rw [finiteCodeSelectedCoreFiberAssocLeftRoute_fac,
    finiteCodeSelectedCoreFiberAssocRightRoute_fac]

/-- The source-identity unitor/compositor route, normalized to the original action. -/
noncomputable def finiteCodeSelectedCoreFiberLeftUnitRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberReindexFunctor hom).obj targetPackage ⟶
      (finiteCodeSelectedCoreFiberReindexFunctor hom).obj targetPackage :=
  (finiteCodeSelectedCoreFiberUnitorApp source
    ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
      targetPackage)).hom ≫
    (finiteCodeSelectedCoreFiberCompositorApp (𝟙 source) hom
      targetPackage).hom ≫
    (finiteCodeSelectedCoreFiberHomComparison
      (finiteCodeId_comp hom)).hom.app targetPackage

/-- The target-identity unitor/compositor route, normalized to the original action. -/
noncomputable def finiteCodeSelectedCoreFiberRightUnitRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberReindexFunctor hom).obj targetPackage ⟶
      (finiteCodeSelectedCoreFiberReindexFunctor hom).obj targetPackage :=
  (finiteCodeSelectedCoreFiberReindexFunctor hom).map
      (finiteCodeSelectedCoreFiberUnitorApp target targetPackage).hom ≫
    (finiteCodeSelectedCoreFiberCompositorApp hom (𝟙 target)
      targetPackage).hom ≫
    (finiteCodeSelectedCoreFiberHomComparison
      (finiteCodeComp_id hom)).hom.app targetPackage

/-- The source-unit route factors to the original selected quotient lift. -/
theorem finiteCodeSelectedCoreFiberLeftUnitRoute_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberLeftUnitRoute hom targetPackage).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom =
      (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom := by
  change
    ((finiteCodeSelectedCoreFiberUnitorApp source
        ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
          targetPackage)).hom.1 ≫
      (finiteCodeSelectedCoreFiberCompositorApp (𝟙 source) hom
        targetPackage).hom.1) ≫
      ((finiteCodeSelectedCoreFiberHomComparison
        (finiteCodeId_comp hom)).hom.app targetPackage).1 ≫
      (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom =
    (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom
  calc
    _ = ((finiteCodeSelectedCoreFiberUnitorApp source
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom.1 ≫
        (finiteCodeSelectedCoreFiberCompositorApp (𝟙 source) hom
          targetPackage).hom.1) ≫
        (((finiteCodeSelectedCoreFiberHomComparison
          (finiteCodeId_comp hom)).hom.app targetPackage).1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift hom
            targetPackage).hom) := Category.assoc _ _ _
    _ = ((finiteCodeSelectedCoreFiberUnitorApp source
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom.1 ≫
        (finiteCodeSelectedCoreFiberCompositorApp (𝟙 source) hom
          targetPackage).hom.1) ≫
        (finiteCodeSelectedCoreFiberCartesianLift ((𝟙 source : FiniteCodeCartHom source source) ≫q hom)
          targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberHomComparison_hom_app_fac]
    _ = (finiteCodeSelectedCoreFiberUnitorApp source
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom.1 ≫
        ((finiteCodeSelectedCoreFiberCompositorApp (𝟙 source) hom
          targetPackage).hom.1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift ((𝟙 source : FiniteCodeCartHom source source) ≫q hom)
            targetPackage).hom) := Category.assoc _ _ _
    _ = (finiteCodeSelectedCoreFiberUnitorApp source
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom.1 ≫
        (selectedCoreFiberIteratedCartesianLift
          (𝟙 source : FiniteCodeCartHom source source).representative
          hom.representative targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberCompositorApp_hom_fac]
    _ = (finiteCodeSelectedCoreFiberUnitorApp source
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom.1 ≫
        ((finiteCodeSelectedCoreFiberCartesianLift (𝟙 source)
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom ≫
          (finiteCodeSelectedCoreFiberCartesianLift hom
            targetPackage).hom) := rfl
    _ = ((finiteCodeSelectedCoreFiberUnitorApp source
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift (𝟙 source)
          ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
            targetPackage)).hom) ≫
          (finiteCodeSelectedCoreFiberCartesianLift hom
            targetPackage).hom := (Category.assoc _ _ _).symm
    _ = 𝟙 ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
          targetPackage).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift hom
          targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberUnitorApp_hom_fac]
    _ = (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom :=
      Category.id_comp _

/-- The target-unit route factors to the original selected quotient lift. -/
theorem finiteCodeSelectedCoreFiberRightUnitRoute_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    (finiteCodeSelectedCoreFiberRightUnitRoute hom targetPackage).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom =
      (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom := by
  change
    (((finiteCodeSelectedCoreFiberReindexFunctor hom).map
        (finiteCodeSelectedCoreFiberUnitorApp target
          targetPackage).hom).1 ≫
      (finiteCodeSelectedCoreFiberCompositorApp hom (𝟙 target)
        targetPackage).hom.1) ≫
      ((finiteCodeSelectedCoreFiberHomComparison
        (finiteCodeComp_id hom)).hom.app targetPackage).1 ≫
      (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom =
    (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom
  calc
    _ = (((finiteCodeSelectedCoreFiberReindexFunctor hom).map
          (finiteCodeSelectedCoreFiberUnitorApp target
            targetPackage).hom).1 ≫
        (finiteCodeSelectedCoreFiberCompositorApp hom (𝟙 target)
          targetPackage).hom.1) ≫
        (((finiteCodeSelectedCoreFiberHomComparison
          (finiteCodeComp_id hom)).hom.app targetPackage).1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift hom
            targetPackage).hom) := Category.assoc _ _ _
    _ = (((finiteCodeSelectedCoreFiberReindexFunctor hom).map
          (finiteCodeSelectedCoreFiberUnitorApp target
            targetPackage).hom).1 ≫
        (finiteCodeSelectedCoreFiberCompositorApp hom (𝟙 target)
          targetPackage).hom.1) ≫
        (finiteCodeSelectedCoreFiberCartesianLift (hom ≫q (𝟙 target : FiniteCodeCartHom target target))
          targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberHomComparison_hom_app_fac]
    _ = ((finiteCodeSelectedCoreFiberReindexFunctor hom).map
          (finiteCodeSelectedCoreFiberUnitorApp target
            targetPackage).hom).1 ≫
        ((finiteCodeSelectedCoreFiberCompositorApp hom (𝟙 target)
          targetPackage).hom.1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift (hom ≫q (𝟙 target : FiniteCodeCartHom target target))
            targetPackage).hom) := Category.assoc _ _ _
    _ = ((finiteCodeSelectedCoreFiberReindexFunctor hom).map
          (finiteCodeSelectedCoreFiberUnitorApp target
            targetPackage).hom).1 ≫
        (selectedCoreFiberIteratedCartesianLift hom.representative
          (𝟙 target : FiniteCodeCartHom target target).representative
          targetPackage).hom := by
      rw [finiteCodeSelectedCoreFiberCompositorApp_hom_fac]
    _ = ((finiteCodeSelectedCoreFiberReindexFunctor hom).map
          (finiteCodeSelectedCoreFiberUnitorApp target
            targetPackage).hom).1 ≫
        ((finiteCodeSelectedCoreFiberCartesianLift hom
          ((finiteCodeSelectedCoreFiberReindexFunctor
            (𝟙 target)).obj targetPackage)).hom ≫
          (finiteCodeSelectedCoreFiberCartesianLift (𝟙 target)
            targetPackage).hom) := rfl
    _ = (((finiteCodeSelectedCoreFiberReindexFunctor hom).map
          (finiteCodeSelectedCoreFiberUnitorApp target
            targetPackage).hom).1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift hom
          ((finiteCodeSelectedCoreFiberReindexFunctor
            (𝟙 target)).obj targetPackage)).hom) ≫
          (finiteCodeSelectedCoreFiberCartesianLift (𝟙 target)
            targetPackage).hom := (Category.assoc _ _ _).symm
    _ = ((finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom ≫
        (finiteCodeSelectedCoreFiberUnitorApp target
          targetPackage).hom.1) ≫
          (finiteCodeSelectedCoreFiberCartesianLift (𝟙 target)
            targetPackage).hom := by
      have hmap := selectedTypedCoreFiberReindexFunctor_map_fac
        hom.representative
        (finiteCodeSelectedCoreFiberUnitorApp target targetPackage).hom
      have hpost := congrArg
        (fun arrow => arrow ≫
          (finiteCodeSelectedCoreFiberCartesianLift (𝟙 target)
            targetPackage).hom)
        hmap
      simpa only [finiteCodeSelectedCoreFiberReindexFunctor,
        finiteCodeSelectedCoreFiberCartesianLift] using hpost
    _ = (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom ≫
        ((finiteCodeSelectedCoreFiberUnitorApp target
          targetPackage).hom.1 ≫
          (finiteCodeSelectedCoreFiberCartesianLift (𝟙 target)
            targetPackage).hom) := Category.assoc _ _ _
    _ = (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom ≫
        𝟙 targetPackage.1 := by
      rw [finiteCodeSelectedCoreFiberUnitorApp_hom_fac]
    _ = (finiteCodeSelectedCoreFiberCartesianLift hom targetPackage).hom :=
      Category.comp_id _

/-- Quotient compositors and the unitor satisfy the source-unit triangle. -/
theorem finiteCodeSelectedCoreFiberCompositor_left_unit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    finiteCodeSelectedCoreFiberLeftUnitRoute hom targetPackage =
      𝟙 ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
        targetPackage) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let lift := finiteCodeSelectedCoreFiberCartesianLift hom targetPackage
  letI := lift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (typedCartSemanticInput hom.representative).hom
    lift.hom (𝟙 source.toSemantic)
  change
    (finiteCodeSelectedCoreFiberLeftUnitRoute hom targetPackage).1 ≫
      lift.hom = 𝟙 lift.domain ≫ lift.hom
  rw [finiteCodeSelectedCoreFiberLeftUnitRoute_fac, Category.id_comp]

/-- Quotient compositors and the unitor satisfy the target-unit triangle. -/
theorem finiteCodeSelectedCoreFiberCompositor_right_unit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (hom : FiniteCodeCartHom source target)
    (targetPackage : CoreFiber target.toSemantic) :
    finiteCodeSelectedCoreFiberRightUnitRoute hom targetPackage =
      𝟙 ((finiteCodeSelectedCoreFiberReindexFunctor hom).obj
        targetPackage) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let lift := finiteCodeSelectedCoreFiberCartesianLift hom targetPackage
  letI := lift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (typedCartSemanticInput hom.representative).hom
    lift.hom (𝟙 source.toSemantic)
  change
    (finiteCodeSelectedCoreFiberRightUnitRoute hom targetPackage).1 ≫
      lift.hom = 𝟙 lift.domain ≫ lift.hom
  rw [finiteCodeSelectedCoreFiberRightUnitRoute_fac, Category.id_comp]

/-! ## The selected quotient pseudoaction -/

/--
The selected finite-code reindexing pseudoaction.

The object action is the core fiber over a finite instance code.  A quotient
morphism acts contravariantly through the selected reindexing functor of its
distinguished representative.  The pseudofunctor compositor and unitor are the
inverses of the quotient-level comparison isomorphisms above, in the direction
required by Mathlib's covariant pseudofunctor convention on the opposite
category.  Its three coherence fields are discharged by the generated
cartesian-uniqueness pentagon and unit laws, rather than by a strict quotient
lift into `Functor`.
-/
noncomputable def finiteCodeSelectedCoreFiberReindexPseudoaction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    Pseudofunctor (LocallyDiscrete (FiniteCodeCartCategory U)ᵒᵖ) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun instanceCode => Cat.of (CoreFiber instanceCode.unop.toSemantic))
    (fun hom =>
      (finiteCodeSelectedCoreFiberReindexFunctor hom.unop).toCatHom)
    (fun instanceCode =>
      Cat.Hom.isoMk
        (finiteCodeSelectedCoreFiberUnitor instanceCode.unop).symm)
    (fun first second =>
      Cat.Hom.isoMk
        (finiteCodeSelectedCoreFiberCompositor second.unop first.unop).symm)
    ?_ ?_ ?_
  · intro _ _ _ _ first second third
    ext targetPackage
    simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.toCatHom₂_toNatTrans, Cat.Hom₂.comp_app,
      Cat.whiskerRight_app, Cat.whiskerLeft_app, Cat.associator_hom_app,
      Cat.eqToHom_app, Functor.comp_obj, Category.id_comp, eqToHom_refl,
      finiteCodeSelectedCoreFiberCompositor_hom_app,
      finiteCodeSelectedCoreFiberCompositor_inv_app]
    change
      (finiteCodeSelectedCoreFiberCompositor third.unop
        (second.unop ≫q first.unop)).inv.app targetPackage ≫
        (finiteCodeSelectedCoreFiberReindexFunctor third.unop).map
          ((finiteCodeSelectedCoreFiberCompositor second.unop
            first.unop).inv.app targetPackage) ≫
        finiteCodeSelectedCoreFiberAssocLeftRoute third.unop second.unop
          first.unop targetPackage = _
    calc
      _ = (finiteCodeSelectedCoreFiberCompositor third.unop
            (second.unop ≫q first.unop)).inv.app targetPackage ≫
          (finiteCodeSelectedCoreFiberReindexFunctor third.unop).map
            ((finiteCodeSelectedCoreFiberCompositor second.unop
              first.unop).inv.app targetPackage) ≫
          finiteCodeSelectedCoreFiberAssocRightRoute third.unop second.unop
            first.unop targetPackage := by
        rw [finiteCodeSelectedCoreFiberCompositor_assoc]
      _ = (finiteCodeSelectedCoreFiberHomComparison
          (finiteCodeComp_assoc third.unop second.unop first.unop).symm).hom.app
            targetPackage := by
        simp only [finiteCodeSelectedCoreFiberAssocRightRoute,
          finiteCodeSelectedCoreFiberCompositor_inv_app,
          Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
      _ = _ := by
        simpa only using
          finiteCodeSelectedCoreFiberHomComparison_hom_app_eqToHom
            (finiteCodeComp_assoc third.unop second.unop first.unop).symm
            targetPackage
  · intro source _ hom
    ext targetPackage
    simp only [Cat.Hom.isoMk_hom, Iso.symm_hom,
      NatTrans.toCatHom₂_toNatTrans, Cat.Hom₂.comp_app,
      Cat.whiskerRight_app, Cat.leftUnitor_hom_app, Cat.eqToHom_app,
      Functor.comp_obj, Category.comp_id, eqToHom_refl,
      finiteCodeSelectedCoreFiberCompositor_inv_app,
      finiteCodeSelectedCoreFiberUnitor_inv_app]
    change
      (finiteCodeSelectedCoreFiberCompositorApp hom.unop
        (𝟙 (Opposite.unop source)) targetPackage).inv ≫
        (finiteCodeSelectedCoreFiberReindexFunctor hom.unop).map
          (finiteCodeSelectedCoreFiberUnitorApp
            (Opposite.unop source) targetPackage).inv = _
    calc
      _ = ((finiteCodeSelectedCoreFiberCompositorApp hom.unop
              (𝟙 (Opposite.unop source)) targetPackage).inv ≫
            (finiteCodeSelectedCoreFiberReindexFunctor hom.unop).map
              (finiteCodeSelectedCoreFiberUnitorApp
                (Opposite.unop source) targetPackage).inv) ≫
          𝟙 _ := by
        simp only [Category.comp_id]
      _ = ((finiteCodeSelectedCoreFiberCompositorApp hom.unop
              (𝟙 (Opposite.unop source)) targetPackage).inv ≫
            (finiteCodeSelectedCoreFiberReindexFunctor hom.unop).map
              (finiteCodeSelectedCoreFiberUnitorApp
                (Opposite.unop source) targetPackage).inv) ≫
          finiteCodeSelectedCoreFiberRightUnitRoute hom.unop
            targetPackage := by
        rw [finiteCodeSelectedCoreFiberCompositor_right_unit]
      _ = (finiteCodeSelectedCoreFiberHomComparison
          (finiteCodeComp_id hom.unop)).hom.app targetPackage := by
        simp only [finiteCodeSelectedCoreFiberRightUnitRoute,
          Category.assoc, Iso.map_inv_hom_id_assoc,
          Iso.inv_hom_id_assoc]
      _ = _ := by
        simpa only using
          finiteCodeSelectedCoreFiberHomComparison_hom_app_eqToHom
            (finiteCodeComp_id hom.unop) targetPackage
  · intro _ target hom
    ext targetPackage
    simp only [Cat.Hom.isoMk_hom, Iso.symm_hom,
      NatTrans.toCatHom₂_toNatTrans, Cat.Hom₂.comp_app,
      Cat.whiskerLeft_app, Cat.rightUnitor_hom_app, Cat.eqToHom_app,
      Functor.comp_obj, Category.comp_id, eqToHom_refl,
      finiteCodeSelectedCoreFiberCompositor_inv_app,
      finiteCodeSelectedCoreFiberUnitor_inv_app]
    change
      (finiteCodeSelectedCoreFiberCompositorApp (𝟙 (Opposite.unop target))
        hom.unop targetPackage).inv ≫
        (finiteCodeSelectedCoreFiberUnitorApp
          (Opposite.unop target)
            ((finiteCodeSelectedCoreFiberReindexFunctor hom.unop).obj
              targetPackage)).inv = _
    calc
      _ = ((finiteCodeSelectedCoreFiberCompositorApp
              (𝟙 (Opposite.unop target)) hom.unop targetPackage).inv ≫
            (finiteCodeSelectedCoreFiberUnitorApp
              (Opposite.unop target)
                ((finiteCodeSelectedCoreFiberReindexFunctor hom.unop).obj
                  targetPackage)).inv) ≫
          𝟙 _ := by
        simp only [Category.comp_id]
      _ = ((finiteCodeSelectedCoreFiberCompositorApp
              (𝟙 (Opposite.unop target)) hom.unop targetPackage).inv ≫
            (finiteCodeSelectedCoreFiberUnitorApp
              (Opposite.unop target)
                ((finiteCodeSelectedCoreFiberReindexFunctor hom.unop).obj
                  targetPackage)).inv) ≫
          finiteCodeSelectedCoreFiberLeftUnitRoute hom.unop
            targetPackage := by
        rw [finiteCodeSelectedCoreFiberCompositor_left_unit]
      _ = (finiteCodeSelectedCoreFiberHomComparison
          (finiteCodeId_comp hom.unop)).hom.app targetPackage := by
        simp only [finiteCodeSelectedCoreFiberLeftUnitRoute,
          Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := by
        simpa only using
          finiteCodeSelectedCoreFiberHomComparison_hom_app_eqToHom
            (finiteCodeId_comp hom.unop) targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
