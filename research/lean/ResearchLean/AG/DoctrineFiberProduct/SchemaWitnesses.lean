import ResearchLean.AG.DoctrineFiberProduct.Schema
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

/-- All-admitting finite doctrine with a first-order source cardinality. -/
def finiteAllDoctrineCode (sourceCard : ℕ) :
    FiniteDoctrineCode FiniteModel.carrier where
  sourceCard := sourceCard
  normalize := id
  extraction := fun _ => finiteAllAtomPredicate

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

/-- The compatible-pair source of the constant map's self-pullback has four cells. -/
theorem finiteConstantCompatibleSource_card :
    Fintype.card
      (CompatibleSource finiteConstantPresentation finiteConstantPresentation) = 4 := by
  decide

/-- The generated self-pullback is represented by a four-source doctrine code. -/
theorem finiteConstantPullback_sourceCard :
    (pullbackDoctrineCode finiteConstantPresentation
      finiteConstantPresentation).sourceCard = 4 :=
  finiteConstantCompatibleSource_card

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
