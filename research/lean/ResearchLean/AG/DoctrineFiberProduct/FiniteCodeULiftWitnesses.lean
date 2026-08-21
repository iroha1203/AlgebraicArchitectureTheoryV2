import ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULift
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses

/-!
# Finite witnesses for canonical cross-universe code reindexing

The witnesses exercise the F0c2a1 transport on both sides of the finite
boundary.  The accepted constant presentation keeps its noninjective source
table, the nonidentity Atom permutation remains nonidentity, and the malformed
selected-point raw code remains rejected.  The positive and negative Boolean
condition evaluations are transported by the generic evaluator theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

local instance finiteModelULiftWitnessBaseAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Canonical universe lift of the concrete noninvertible constant presentation. -/
def finiteModelLiftConstantPresentation :
    CartPresentation finiteModelLiftCarrier.{u} :=
  finiteModelLiftCartPresentation finiteConstantPresentation.toPresentation

/-- The lifted constant presentation remains accepted by the finite validator. -/
theorem finiteModelLiftConstantPresentation_check_true :
    finiteModelLiftConstantPresentation.{u}.1.checkWellFormed = true :=
  (CartRawCode.checkWellFormed_eq_true_iff _).mpr
    finiteModelLiftConstantPresentation.2

/-- The canonical lift does not turn the constant source table into an injection. -/
theorem finiteModelLiftConstantSourceMap_not_injective :
    ¬ Function.Injective finiteModelLiftConstantPresentation.{u}.1.sourceMap := by
  intro hinjective
  apply finiteConstantSourceMap_not_injective
  intro first second heq
  let sourceEquiv := finiteSourceRebaseEquiv.{0, u}
    finiteTwoSourceInstance.doctrine.sourceCard
  apply sourceEquiv.injective
  apply hinjective
  change (finiteConstantPresentation.toRaw.rebase
      finiteModelLiftCarrierEquiv).sourceMap (sourceEquiv first) =
    (finiteConstantPresentation.toRaw.rebase
      finiteModelLiftCarrierEquiv).sourceMap (sourceEquiv second)
  dsimp [sourceEquiv]
  calc
    _ = finiteSourceRebaseEquiv.{0, u}
        finiteOneSourceInstance.doctrine.sourceCard
        (finiteConstantPresentation.toRaw.sourceMap first) :=
      CartRawCode.rebase_sourceMap finiteModelLiftCarrierEquiv
        finiteConstantPresentation.toRaw first
    _ = finiteSourceRebaseEquiv.{0, u}
        finiteOneSourceInstance.doctrine.sourceCard
        (finiteConstantPresentation.toRaw.sourceMap second) := by
      apply congrArg
      exact heq
    _ = _ := (CartRawCode.rebase_sourceMap finiteModelLiftCarrierEquiv
      finiteConstantPresentation.toRaw second).symm

/-- Canonical universe lift of the presentation with a nonidentity Atom table. -/
noncomputable def finiteModelLiftSwapPresentation :
    CartPresentation finiteModelLiftCarrier.{u} :=
  finiteModelLiftCartPresentation finiteSwapPresentation.toPresentation

/-- The concrete moved Atom is still moved after conjugating the finite table. -/
theorem finiteModelLiftSwapPresentation_moves_componentC :
    finiteModelLiftSwapPresentation.{u}.1.atomEquiv.toEquiv
        (ULift.up FiniteModel.FiniteAtom.componentC) =
      ULift.up FiniteModel.FiniteAtom.dependsAB := by
  change (finiteSwapPresentation.toRaw.rebase
    finiteModelLiftCarrierEquiv).atomEquiv.toEquiv
      (finiteModelLiftCarrierEquiv.atom
        FiniteModel.FiniteAtom.componentC) =
    finiteModelLiftCarrierEquiv.atom FiniteModel.FiniteAtom.dependsAB
  rw [CartRawCode.rebase_atomEquiv_apply]
  change finiteModelLiftCarrierEquiv.atom
      (finiteSwapPermutationCode.toEquiv FiniteModel.FiniteAtom.componentC) =
    finiteModelLiftCarrierEquiv.atom FiniteModel.FiniteAtom.dependsAB
  rw [finiteSwapPermutationCode_componentC]

/-- The positive identity-Atom evaluation is preserved by the universe lift. -/
theorem finiteModelLiftConstant_identityAtom_check :
    evalCartCondition
        (rebaseCartCondition
          (V := finiteModelLiftCarrier.{u})
          ((.allCells .atomMapIdentity) :
            CartConditionSyntax FiniteModel.carrier))
        finiteModelLiftConstantPresentation = true := by
  calc
    _ = evalCartCondition
        ((.allCells .atomMapIdentity) :
          CartConditionSyntax FiniteModel.carrier)
        finiteConstantPresentation.toPresentation :=
      evalCartCondition_finiteModelLift _ _
    _ = true := finiteConstant_identityAtom_check

/-- The negative identity-Atom evaluation is preserved by the universe lift. -/
theorem finiteModelLiftSwap_identityAtom_check_false :
    evalCartCondition
        (rebaseCartCondition
          (V := finiteModelLiftCarrier.{u})
          ((.allCells .atomMapIdentity) :
            CartConditionSyntax FiniteModel.carrier))
        finiteModelLiftSwapPresentation = false := by
  calc
    _ = evalCartCondition
        ((.allCells .atomMapIdentity) :
          CartConditionSyntax FiniteModel.carrier)
        finiteSwapPresentation.toPresentation :=
      evalCartCondition_finiteModelLift _ _
    _ = false := finiteSwap_identityAtom_check_false

/-- Canonical universe lift of the malformed selected-point raw code. -/
def finiteModelLiftBadPointRawCode : CartRawCode finiteModelLiftCarrier.{u} :=
  finiteBadPointRawCode.rebase finiteModelLiftCarrierEquiv

/-- The selected-point defect survives canonical code reindexing. -/
theorem finiteModelLiftBadPointRawCode_not_wellFormed :
    ¬ finiteModelLiftBadPointRawCode.{u}.WellFormed := by
  intro hwellFormed
  have hpoint := hwellFormed.2.2
  change finiteSourceRebaseEquiv.{0, u} 2 finiteTwoSourceOne =
    finiteSourceRebaseEquiv.{0, u} 2 finiteTwoSourceZero at hpoint
  have horiginal := (finiteSourceRebaseEquiv.{0, u} 2).injective hpoint
  have hdown := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val) horiginal
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at hdown

/-- The finite checker rejects the lifted malformed code as well. -/
theorem finiteModelLiftBadPointRawCode_check_false :
    finiteModelLiftBadPointRawCode.{u}.checkWellFormed = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact finiteModelLiftBadPointRawCode_not_wellFormed
    ((CartRawCode.checkWellFormed_eq_true_iff _).mp htrue)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
