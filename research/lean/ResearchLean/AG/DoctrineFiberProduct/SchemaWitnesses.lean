import ResearchLean.AG.DoctrineFiberProduct.Schema
import ResearchLean.AG.AtomFoundation.Doctrine
import ResearchLean.AG.AtomFoundation.TransportLaws
import Formal.AG.Examples.FiniteModel

/-!
# Finite noninvertible witnesses for the G-110 schema

This module tests the F0 finite-code signature against the exact obstruction
that stopped the previous fixed-card head.  A two-source all-admitting doctrine
maps constantly to a one-source doctrine.  The decoded pointed exact morphism
is noninvertible, while its self-pullback remains in the same code family with
four compatible source pairs.

## Implementation notes

The all-admitting extraction predicate is used only to isolate source-table
behavior.  It is not an `H_cart` or `H_bc` condition and carries no target
conclusion.  The separate finite Atom swap supplies the negative instance for
the condition evaluator without changing the source-table witness.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-- Executable equality for the Atom projection of the concrete finite carrier. -/
local instance finiteModelCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A noninvertible finite-code exact bottom arrow -/

/-- The finite/cofinite code for the all-admitting Atom predicate. -/
def finiteAllAtomPredicate : AtomPredicateCode FiniteModel.carrier where
  defaultValue := true
  exceptions := ∅

/-- Finite predicate admitting every fixture Atom except `componentC`. -/
def finiteWithoutComponentCAtomPredicate :
    AtomPredicateCode FiniteModel.carrier where
  defaultValue := true
  exceptions := {FiniteModel.FiniteAtom.componentC}

/-- The finite predicate has an explicit positive `Holds` instance. -/
theorem finiteWithoutComponentC_holds_componentA :
    finiteWithoutComponentCAtomPredicate.Holds
      FiniteModel.FiniteAtom.componentA := by
  simp [finiteWithoutComponentCAtomPredicate, AtomPredicateCode.Holds,
    AtomPredicateCode.eval]

/-- The same finite predicate has an explicit negative `Holds` instance. -/
theorem finiteWithoutComponentC_not_holds_componentC :
    ¬ finiteWithoutComponentCAtomPredicate.Holds
      FiniteModel.FiniteAtom.componentC := by
  simp [finiteWithoutComponentCAtomPredicate, AtomPredicateCode.Holds,
    AtomPredicateCode.eval]

/-- All-admitting finite doctrine with a first-order source cardinality. -/
def finiteAllDoctrineCode (sourceCard : ℕ) :
    FiniteDoctrineCode FiniteModel.carrier where
  sourceCard := sourceCard
  normalize := id
  extraction := fun _ => finiteAllAtomPredicate

/-! ## The reviewed FiniteModel doctrine lies in the realization image up to isomorphism -/

/-- Decode a two-cell first-order source as the reviewed FiniteModel source type. -/
def finiteModelCodeSourceToFixture
    (source : FiniteSource 2) : FiniteModel.ExtractionSource :=
  if source.down.val = 0 then FiniteModel.ExtractionSource.all
  else FiniteModel.ExtractionSource.withoutComponentC

/-- Encode each reviewed FiniteModel source by its first-order source cell. -/
def finiteModelFixtureSourceToCode :
    FiniteModel.ExtractionSource → FiniteSource 2
  | .all => ULift.up 0
  | .withoutComponentC => ULift.up 1

/-- Source equivalence used to compare the code doctrine with the reviewed fixture. -/
def finiteModelSourceEquiv :
    FiniteSource 2 ≃ FiniteModel.ExtractionSource where
  toFun := finiteModelCodeSourceToFixture
  invFun := finiteModelFixtureSourceToCode
  left_inv source := by
    rcases source with ⟨source⟩
    apply ULift.ext
    apply Fin.ext
    fin_cases source <;> rfl
  right_inv source := by
    cases source <;> rfl

/-- The first code source corresponds to the all-admitting fixture source. -/
@[simp]
theorem finiteModelSourceEquiv_zero :
    finiteModelSourceEquiv (ULift.up (0 : Fin 2)) =
      FiniteModel.ExtractionSource.all :=
  rfl

/-- The second code source corresponds to the selective fixture source. -/
@[simp]
theorem finiteModelSourceEquiv_one :
    finiteModelSourceEquiv (ULift.up (1 : Fin 2)) =
      FiniteModel.ExtractionSource.withoutComponentC :=
  rfl

/-- The inverse source equivalence sends the all-admitting source to cell zero. -/
@[simp]
theorem finiteModelSourceEquiv_symm_all :
    finiteModelSourceEquiv.symm FiniteModel.ExtractionSource.all =
      ULift.up (0 : Fin 2) :=
  rfl

/-- The inverse source equivalence sends the selective source to cell one. -/
@[simp]
theorem finiteModelSourceEquiv_symm_withoutComponentC :
    finiteModelSourceEquiv.symm
        FiniteModel.ExtractionSource.withoutComponentC =
      ULift.up (1 : Fin 2) :=
  rfl

/-- Finite doctrine code whose decoding reproduces the reviewed fixture up to source renaming. -/
def finiteModelDoctrineCode : FiniteDoctrineCode FiniteModel.carrier where
  sourceCard := 2
  normalize := id
  extraction source :=
    match finiteModelSourceEquiv source with
    | .all => finiteAllAtomPredicate
    | .withoutComponentC => finiteWithoutComponentCAtomPredicate

/-- Exact comparison from the decoded finite code to the reviewed fixture doctrine. -/
def finiteModelDoctrineToFixture :
    finiteModelDoctrineCode.toDoctrine ⟶ FiniteModel.extractionDoctrine where
  sourceMap := finiteModelSourceEquiv
  atomEquiv := Equiv.refl _
  normalize_eq _ := rfl
  extraction_iff source atom := by
    rcases source with ⟨source⟩
    fin_cases source <;>
      simp [finiteModelDoctrineCode, finiteModelSourceEquiv,
        finiteModelCodeSourceToFixture,
        finiteWithoutComponentCAtomPredicate, finiteAllAtomPredicate,
        AtomPredicateCode.Holds, AtomPredicateCode.eval,
        ExtractionDoctrine.extracts, FiniteDoctrineCode.toDoctrine,
        FiniteModel.extractionDoctrine]

/-- Exact comparison from the reviewed fixture doctrine back to the finite code. -/
def finiteModelDoctrineFromFixture :
    FiniteModel.extractionDoctrine ⟶ finiteModelDoctrineCode.toDoctrine where
  sourceMap := finiteModelSourceEquiv.symm
  atomEquiv := Equiv.refl _
  normalize_eq _ := rfl
  extraction_iff source atom := by
    cases source <;>
      simp [finiteModelDoctrineCode, finiteModelSourceEquiv,
        finiteModelCodeSourceToFixture, finiteModelFixtureSourceToCode,
        finiteWithoutComponentCAtomPredicate, finiteAllAtomPredicate,
        AtomPredicateCode.Holds, AtomPredicateCode.eval,
        ExtractionDoctrine.extracts, FiniteDoctrineCode.toDoctrine,
        FiniteModel.extractionDoctrine]

/-- The concrete reverse schema comparison fixes the Atom carrier pointwise. -/
@[simp]
theorem finiteModelDoctrineFromFixture_atomEquiv :
    finiteModelDoctrineFromFixture.atomEquiv = Equiv.refl _ :=
  rfl

/-- The reverse schema comparison acts trivially on every finite configuration. -/
@[simp]
theorem finiteModelDoctrineFromFixture_configuration_transport
    (configuration : AtomConfiguration FiniteModel.carrier) :
    configuration.transport finiteModelDoctrineFromFixture.atomEquiv =
      configuration := by
  rw [finiteModelDoctrineFromFixture_atomEquiv]
  exact AtomFoundation.atomConfiguration_transport_id configuration

/--
The existing reviewed `FiniteModel.extractionDoctrine` is in the finite-code
object realization image up to an actual isomorphism in `Doct_U`; it is a
witness of coverage, not the schema's Source anchor.
-/
def finiteModelDoctrineRealizationIso :
    finiteModelDoctrineCode.toDoctrine ≅ FiniteModel.extractionDoctrine where
  hom := finiteModelDoctrineToFixture
  inv := finiteModelDoctrineFromFixture
  hom_inv_id := by
    apply ExactDoctrineHom.ext
    · funext source
      exact finiteModelSourceEquiv.symm_apply_apply source
    · rfl
  inv_hom_id := by
    apply ExactDoctrineHom.ext
    · funext source
      exact finiteModelSourceEquiv.apply_symm_apply source
    · rfl

/-- First point of the two-source doctrine. -/
def finiteTwoSourceZero : (finiteAllDoctrineCode 2).Source :=
  ULift.up ⟨0, by decide⟩

/-- Second point of the two-source doctrine. -/
def finiteTwoSourceOne : (finiteAllDoctrineCode 2).Source :=
  ULift.up ⟨1, by decide⟩

/-- Unique point of the one-source doctrine. -/
def finiteOneSourceZero : (finiteAllDoctrineCode 1).Source :=
  ULift.up ⟨0, by decide⟩

/-- Pointed two-source finite doctrine code. -/
def finiteTwoSourceInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteAllDoctrineCode 2
  point := finiteTwoSourceZero

/-- Pointed one-source finite doctrine code. -/
def finiteOneSourceInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteAllDoctrineCode 1
  point := finiteOneSourceZero

/-- Noninjective constant source table from the two-source code to the one-source code. -/
def finiteConstantSourceMap :
    finiteTwoSourceInstance.doctrine.Source →
      finiteOneSourceInstance.doctrine.Source :=
  fun _ => finiteOneSourceZero

/-- Validated finite-code presentation of the noninvertible constant bottom arrow. -/
def finiteConstantPresentation :
    CartPresentationBetween finiteTwoSourceInstance finiteOneSourceInstance where
  sourceMap := finiteConstantSourceMap
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- The well-formedness checker accepts the concrete noninvertible presentation. -/
theorem finiteConstantPresentation_check_true :
    finiteConstantPresentation.toRaw.checkWellFormed = true :=
  (CartRawCode.checkWellFormed_eq_true_iff
    finiteConstantPresentation.toRaw).mpr
      finiteConstantPresentation.toRaw_wellFormed

/--
Malformed four-field code whose source table sends the selected one-cell point
to the nonselected point of the two-cell target.
-/
def finiteBadPointRawCode : CartRawCode FiniteModel.carrier where
  source := finiteOneSourceInstance
  target := finiteTwoSourceInstance
  sourceMap := fun _ => finiteTwoSourceOne
  atomEquiv := AtomPermutationCode.refl

/-- The concrete bad-point raw code fails the selected-source decoder law. -/
theorem finiteBadPointRawCode_not_wellFormed :
    ¬ finiteBadPointRawCode.WellFormed := by
  intro hwellFormed
  have hpoint := hwellFormed.2.2
  change finiteTwoSourceOne = finiteTwoSourceZero at hpoint
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val) hpoint
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at hdown

/-- The executable validator rejects the same malformed raw code. -/
theorem finiteBadPointRawCode_check_false :
    finiteBadPointRawCode.checkWellFormed = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact finiteBadPointRawCode_not_wellFormed
    ((CartRawCode.checkWellFormed_eq_true_iff finiteBadPointRawCode).mp htrue)

/-- The two distinct source cells are identified by the authored constant table. -/
theorem finiteConstantSourceMap_not_injective :
    ¬ Function.Injective finiteConstantSourceMap := by
  intro hinjective
  have heq : finiteTwoSourceZero = finiteTwoSourceOne :=
    hinjective (by rfl)
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val) heq
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at hdown

/-- An isomorphism in `ExtInst_U` has an injective underlying source table. -/
theorem extInstHom_sourceMap_injective_of_isIso
    {U : AtomCarrier} {source target : ExtractionInstance U}
    (hom : source ⟶ target) [IsIso hom] :
    Function.Injective hom.doctrineHom.sourceMap := by
  intro first second heq
  have hleft (input : source.doctrine.Source) :
      (inv hom).doctrineHom.sourceMap
          (hom.doctrineHom.sourceMap input) = input := by
    have hid := congrArg
      (fun arrow => arrow.doctrineHom.sourceMap input)
      (IsIso.hom_inv_id hom)
    exact hid
  rw [← hleft first, ← hleft second, heq]

/-- The decoded constant finite-code bottom arrow is genuinely noninvertible. -/
theorem finiteConstantPresentation_not_isIso :
    ¬ IsIso (toSemanticCart finiteConstantPresentation.toPresentation).hom := by
  intro hiso
  letI : IsIso (toSemanticCart finiteConstantPresentation.toPresentation).hom :=
    hiso
  exact finiteConstantSourceMap_not_injective
    (extInstHom_sourceMap_injective_of_isIso
      (toSemanticCart finiteConstantPresentation.toPresentation).hom)

/-- Positive finite-code realization certificate for the noninvertible arrow. -/
def finiteConstantRealizableHom : RealizableHom FiniteModel.carrier :=
  realizableHomOf finiteConstantPresentation.toPresentation

/-! ## A semantic arrow outside the finite-code realization boundary -/

/-- All-admitting doctrine with an infinite source type. -/
def infiniteAllDoctrine : ExtractionDoctrine FiniteModel.carrier where
  Source := Nat
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- Pointed instance of the infinite-source doctrine. -/
def infiniteAllInstance : ExtractionInstance FiniteModel.carrier where
  doctrine := infiniteAllDoctrine
  source := (0 : Nat)

/-- Semantic identity arrow whose endpoints have infinite Source. -/
def infiniteIdentityInput : CartSemanticInput FiniteModel.carrier where
  source := infiniteAllInstance
  target := infiniteAllInstance
  hom := 𝟙 infiniteAllInstance

/-- No finite presentation decodes to the infinite-source semantic identity. -/
theorem infiniteIdentityInput_not_presented :
    ¬ ∃ presentation : CartPresentation FiniteModel.carrier,
      infiniteIdentityInput = toSemanticCart presentation := by
  rintro ⟨presentation, hsemantic⟩
  have hsource := congrArg
    (fun input : CartSemanticInput FiniteModel.carrier =>
      input.source.doctrine.Source) hsemantic
  change Nat = presentation.1.source.doctrine.Source at hsource
  letI : Fintype Nat := Fintype.ofEquiv
    presentation.1.source.doctrine.Source (Equiv.cast hsource.symm)
  exact Fintype.false (α := Nat) inferInstance

/--
Negative certificate instance: the infinite semantic arrow cannot be the
semantic component of any `RealizableHom` finite-code package.
-/
theorem infiniteIdentityInput_has_no_realizableHom :
    ¬ ∃ realization : RealizableHom FiniteModel.carrier,
      realization.semantic = infiniteIdentityInput := by
  rintro ⟨realization, hsemantic⟩
  apply infiniteIdentityInput_not_presented
  refine ⟨realization.presentation, ?_⟩
  calc
    infiniteIdentityInput = realization.semantic := hsemantic.symm
    _ = toSemanticCart realization.presentation := realization.realization_eq

/-- The compatible-pair source of the constant map's self-pullback has four cells. -/
theorem finiteConstantCompatibleSource_card :
    Fintype.card
      (CompatibleSource finiteConstantPresentation finiteConstantPresentation) = 4 := by
  decide

/-- The generated self-pullback is represented by a four-source doctrine code. -/
theorem finiteConstantPullback_sourceCard :
    (pullbackDoctrineCode finiteConstantPresentation
      finiteConstantPresentation).sourceCard = 4 := by
  change
    (compatibleSourceValues finiteConstantPresentation
      finiteConstantPresentation).length = 4
  rw [compatibleSourceValues_length_eq_card]
  exact finiteConstantCompatibleSource_card

/-- The generated constant-map self-pullback square satisfies the actual universal property. -/
theorem finiteConstantPullback_isPullback :
    IsPullback
      (toSemanticCart
        (pullbackFstPresentation finiteConstantPresentation
          finiteConstantPresentation).toPresentation).hom
      (toSemanticCart
        (pullbackSndPresentation finiteConstantPresentation
          finiteConstantPresentation).toPresentation).hom
      (toSemanticCart finiteConstantPresentation.toPresentation).hom
      (toSemanticCart finiteConstantPresentation.toPresentation).hom :=
  pullbackPresentation_isPullback finiteConstantPresentation
    finiteConstantPresentation

/-! ## Positive and negative evaluator instances -/

/-- Two concrete Atoms used by the negative finite-support permutation table. -/
def finiteSwapSupport : Finset FiniteModel.FiniteAtom :=
  {FiniteModel.FiniteAtom.componentC, FiniteModel.FiniteAtom.dependsAB}

/-- Swap table on the authored two-Atom support. -/
noncomputable def finiteSwapPermutationCode :
    AtomPermutationCode FiniteModel.carrier where
  support := finiteSwapSupport
  table := Equiv.swap
    ⟨FiniteModel.FiniteAtom.componentC, by simp [finiteSwapSupport]⟩
    ⟨FiniteModel.FiniteAtom.dependsAB, by simp [finiteSwapSupport]⟩

/-- The finite support table moves `componentC`. -/
theorem finiteSwapPermutationCode_componentC :
    finiteSwapPermutationCode.toEquiv FiniteModel.FiniteAtom.componentC =
      FiniteModel.FiniteAtom.dependsAB := by
  rw [AtomPermutationCode.toEquiv_apply_mem]
  · simp [finiteSwapPermutationCode]
  · simp [finiteSwapPermutationCode, finiteSwapSupport]

/-- Validated presentation with a genuinely nonidentity Atom component. -/
noncomputable def finiteSwapPresentation :
    CartPresentationBetween finiteTwoSourceInstance finiteTwoSourceInstance where
  sourceMap := id
  atomEquiv := finiteSwapPermutationCode
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport finiteSwapPermutationCode.toEquiv
    simp [finiteAllAtomPredicate, AtomPredicateCode.transport]
  source_eq := rfl

/-- The identity-Atom finite universal fires on a noninvertible source map. -/
theorem finiteConstant_identityAtom_check :
    evalCartCondition (.allCells .atomMapIdentity)
      finiteConstantPresentation.toPresentation = true := by
  rw [evalCartCondition_atomMapIdentity_eq_true_iff]
  exact AtomPermutationCode.toEquiv_refl

/-- The same finite universal rejects the concrete nonidentity Atom table. -/
theorem finiteSwap_identityAtom_check_false :
    evalCartCondition (.allCells .atomMapIdentity)
      finiteSwapPresentation.toPresentation = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hid :=
    (evalCartCondition_atomMapIdentity_eq_true_iff
      finiteSwapPresentation.toPresentation).mp htrue
  change finiteSwapPermutationCode.toEquiv =
    Equiv.refl FiniteModel.FiniteAtom at hid
  have hcomponent := congrArg
    (fun equiv : Equiv.Perm FiniteModel.FiniteAtom =>
      equiv FiniteModel.FiniteAtom.componentC) hid
  change finiteSwapPermutationCode.toEquiv FiniteModel.FiniteAtom.componentC =
    FiniteModel.FiniteAtom.componentC at hcomponent
  rw [finiteSwapPermutationCode_componentC] at hcomponent
  exact FiniteModel.FiniteAtom.noConfusion hcomponent

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
