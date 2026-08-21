import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses

/-!
# A nondegenerate parametric portfolio of cartesian lifts

This module supplies the branch-independent finite portfolio required by
G-110.  Two constant exact arrows, from selective doctrines with respectively
two and three source cells to one common one-cell target, are pairwise
nonisomorphic and noninvertible.  A concrete package in the common target
fiber is generated from the reviewed `FiniteModel` package, and the arbitrary-
target theorem constructs the actual strong cartesian lift for each member.

No package, lift, isomorphism certificate, or cartesianness proof is an authored
field of the finite presentations or an input to the portfolio.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Selective finite presentations -/

/-- Executable equality for the Atom projection of the concrete finite carrier. -/
local instance finiteCartesianPortfolioAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Identity-normalized doctrine whose every cell omits `componentC`. -/
def finiteSelectiveDoctrineCode (sourceCard : ℕ) :
    FiniteDoctrineCode FiniteModel.carrier where
  sourceCard := sourceCard
  normalize := id
  extraction := fun _ => finiteWithoutComponentCAtomPredicate

/-- The selected cell of the one-source selective doctrine. -/
def finiteSelectiveOnePoint : (finiteSelectiveDoctrineCode 1).Source :=
  ULift.up (0 : Fin 1)

/-- The selected cell of the two-source selective doctrine. -/
def finiteSelectiveTwoPoint : (finiteSelectiveDoctrineCode 2).Source :=
  ULift.up (0 : Fin 2)

/-- The second cell of the two-source selective doctrine. -/
def finiteSelectiveTwoOther : (finiteSelectiveDoctrineCode 2).Source :=
  ULift.up (1 : Fin 2)

/-- The selected cell of the three-source selective doctrine. -/
def finiteSelectiveThreePoint : (finiteSelectiveDoctrineCode 3).Source :=
  ULift.up (0 : Fin 3)

/-- A second cell of the three-source selective doctrine. -/
def finiteSelectiveThreeOther : (finiteSelectiveDoctrineCode 3).Source :=
  ULift.up (1 : Fin 3)

/-- Pointed one-source selective doctrine. -/
def finiteSelectiveOneInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteSelectiveDoctrineCode 1
  point := finiteSelectiveOnePoint

/-- Pointed two-source selective doctrine. -/
def finiteSelectiveTwoInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteSelectiveDoctrineCode 2
  point := finiteSelectiveTwoPoint

/-- Pointed three-source selective doctrine. -/
def finiteSelectiveThreeInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteSelectiveDoctrineCode 3
  point := finiteSelectiveThreePoint

/-- Validated constant presentation from the two-source doctrine to the common target. -/
def finiteSelectiveTwoToOnePresentation :
    CartPresentationBetween finiteSelectiveTwoInstance
      finiteSelectiveOneInstance where
  sourceMap := fun _ => finiteSelectiveOnePoint
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq _ := by
    change finiteWithoutComponentCAtomPredicate =
      finiteWithoutComponentCAtomPredicate.transport
        AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- Validated constant presentation from the three-source doctrine to the common target. -/
def finiteSelectiveThreeToOnePresentation :
    CartPresentationBetween finiteSelectiveThreeInstance
      finiteSelectiveOneInstance where
  sourceMap := fun _ => finiteSelectiveOnePoint
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq _ := by
    change finiteWithoutComponentCAtomPredicate =
      finiteWithoutComponentCAtomPredicate.transport
        AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- Realization provenance for the two-source member. -/
def finiteSelectiveTwoInput : RealizableHom FiniteModel.carrier :=
  realizableHomOf finiteSelectiveTwoToOnePresentation.toPresentation

/-- Realization provenance for the three-source member. -/
def finiteSelectiveThreeInput : RealizableHom FiniteModel.carrier :=
  realizableHomOf finiteSelectiveThreeToOnePresentation.toPresentation

/-! ## A concrete package over the shared target -/

/-- Finite-code endpoint of the reviewed selective `FiniteModel` package. -/
def finitePortfolioSupportInstance : FiniteInstanceCode FiniteModel.carrier where
  doctrine := finiteModelDoctrineCode
  point := ULift.up (1 : Fin 2)

/-- Transport the reviewed core package to its exact finite-code endpoint. -/
noncomputable def finitePortfolioSupportPackage : AATCorePackage FiniteModel.carrier :=
  transportAlong FiniteModel.corePackage finiteModelDoctrineFromFixture

/-- The transported support package lies at the selected finite-code endpoint. -/
theorem finitePortfolioSupportPackage_point :
    (packageProjection FiniteModel.carrier).obj finitePortfolioSupportPackage =
      finitePortfolioSupportInstance.toSemantic := by
  rfl

/-- Exact bridge from the shared one-cell target to the reviewed finite-code endpoint. -/
def finiteSelectiveOneToSupportPresentation :
    CartPresentationBetween finiteSelectiveOneInstance
      finitePortfolioSupportInstance where
  sourceMap := fun _ => ULift.up (1 : Fin 2)
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq _ := by
    change finiteWithoutComponentCAtomPredicate =
      finiteWithoutComponentCAtomPredicate.transport
        AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- Realization provenance for the endpoint bridge. -/
def finiteSelectiveOneToSupportInput : RealizableHom FiniteModel.carrier :=
  realizableHomOf finiteSelectiveOneToSupportPresentation.toPresentation

/-- The reviewed transported package as the exact target of the endpoint bridge. -/
noncomputable def finitePortfolioSupportTarget :
    CoreFiber finiteSelectiveOneToSupportInput.semantic.target :=
  ⟨finitePortfolioSupportPackage, finitePortfolioSupportPackage_point⟩

/-- Cycle 9 generates a strong lift of the bridge to the reviewed support package. -/
noncomputable def finiteSelectiveOneSupportLift :
    StrongCartesianLift finiteSelectiveOneToSupportInput.semantic
      finitePortfolioSupportTarget :=
  strongCartesianLiftOfTarget finiteSelectiveOneToSupportInput.semantic
    finitePortfolioSupportTarget

/-- A concrete package in the shared one-cell target fiber. -/
noncomputable def finiteSelectiveOneTargetPackage :
    CoreFiber finiteSelectiveOneInstance.toSemantic :=
  finiteSelectiveOneSupportLift.domainObject

/-! ## Nondegeneracy -/

/-- The two-source constant table identifies two distinct cells. -/
theorem finiteSelectiveTwoSourceMap_not_injective :
    ¬ Function.Injective finiteSelectiveTwoToOnePresentation.sourceMap := by
  intro hinjective
  have heq : finiteSelectiveTwoPoint = finiteSelectiveTwoOther :=
    hinjective (by rfl)
  have hdown := congrArg
    (fun source : (finiteSelectiveDoctrineCode 2).Source => source.down.val) heq
  norm_num [finiteSelectiveDoctrineCode, finiteSelectiveTwoPoint,
    finiteSelectiveTwoOther] at hdown

/-- The three-source constant table identifies two distinct cells. -/
theorem finiteSelectiveThreeSourceMap_not_injective :
    ¬ Function.Injective finiteSelectiveThreeToOnePresentation.sourceMap := by
  intro hinjective
  have heq : finiteSelectiveThreePoint = finiteSelectiveThreeOther :=
    hinjective (by rfl)
  have hdown := congrArg
    (fun source : (finiteSelectiveDoctrineCode 3).Source => source.down.val) heq
  norm_num [finiteSelectiveDoctrineCode, finiteSelectiveThreePoint,
    finiteSelectiveThreeOther] at hdown

/-- The two-source realized arrow is genuinely noninvertible. -/
theorem finiteSelectiveTwoInput_not_isIso :
    ¬ IsIso finiteSelectiveTwoInput.semantic.hom := by
  intro hiso
  letI : IsIso finiteSelectiveTwoInput.semantic.hom := hiso
  exact finiteSelectiveTwoSourceMap_not_injective
    (extInstHom_sourceMap_injective_of_isIso finiteSelectiveTwoInput.semantic.hom)

/-- The three-source realized arrow is genuinely noninvertible. -/
theorem finiteSelectiveThreeInput_not_isIso :
    ¬ IsIso finiteSelectiveThreeInput.semantic.hom := by
  intro hiso
  letI : IsIso finiteSelectiveThreeInput.semantic.hom := hiso
  exact finiteSelectiveThreeSourceMap_not_injective
    (extInstHom_sourceMap_injective_of_isIso finiteSelectiveThreeInput.semantic.hom)

/-- An isomorphism of pointed extraction instances induces an equivalence of sources. -/
noncomputable def extractionInstanceSourceEquiv
    {X Y : ExtractionInstance FiniteModel.carrier} (iso : X ≅ Y) :
    X.doctrine.Source ≃ Y.doctrine.Source where
  toFun := iso.hom.doctrineHom.sourceMap
  invFun := iso.inv.doctrineHom.sourceMap
  left_inv source := by
    have h := congrArg (fun hom => hom.doctrineHom.sourceMap source)
      iso.hom_inv_id
    exact h
  right_inv target := by
    have h := congrArg (fun hom => hom.doctrineHom.sourceMap target)
      iso.inv_hom_id
    exact h

/-- The two-source endpoint is not isomorphic to the common one-source endpoint. -/
theorem finiteSelectiveTwoEndpoints_not_isomorphic :
    ¬ Nonempty (finiteSelectiveTwoInput.semantic.source ≅
      finiteSelectiveTwoInput.semantic.target) := by
  rintro ⟨iso⟩
  let sourceEquiv := extractionInstanceSourceEquiv iso
  change FiniteSource 2 ≃ FiniteSource 1 at sourceEquiv
  have hcard := Fintype.card_congr sourceEquiv
  norm_num at hcard

/-- The three-source endpoint is not isomorphic to the common one-source endpoint. -/
theorem finiteSelectiveThreeEndpoints_not_isomorphic :
    ¬ Nonempty (finiteSelectiveThreeInput.semantic.source ≅
      finiteSelectiveThreeInput.semantic.target) := by
  rintro ⟨iso⟩
  let sourceEquiv := extractionInstanceSourceEquiv iso
  change FiniteSource 3 ≃ FiniteSource 1 at sourceEquiv
  have hcard := Fintype.card_congr sourceEquiv
  norm_num at hcard

/-- The two- and three-source semantic arrows are not isomorphic. -/
theorem finiteSelectiveTwoThreeInputs_not_isomorphic :
    ¬ Nonempty (CartSemanticInputIso finiteSelectiveTwoInput.semantic
      finiteSelectiveThreeInput.semantic) := by
  rintro ⟨iso⟩
  let sourceEquiv := extractionInstanceSourceEquiv iso.sourceIso
  change FiniteSource 2 ≃ FiniteSource 3 at sourceEquiv
  have hcard := Fintype.card_congr sourceEquiv
  norm_num at hcard

/-- The reverse ordering of the two semantic arrows is also nonisomorphic. -/
theorem finiteSelectiveThreeTwoInputs_not_isomorphic :
    ¬ Nonempty (CartSemanticInputIso finiteSelectiveThreeInput.semantic
      finiteSelectiveTwoInput.semantic) := by
  rintro ⟨iso⟩
  let sourceEquiv := extractionInstanceSourceEquiv iso.sourceIso
  change FiniteSource 3 ≃ FiniteSource 2 at sourceEquiv
  have hcard := Fintype.card_congr sourceEquiv
  norm_num at hcard

/-! ## Actual lifts and the portfolio -/

/-- Actual strong cartesian lift for the two-source member. -/
noncomputable def finiteSelectiveTwoLift :
    StrongCartesianLift finiteSelectiveTwoInput.semantic
      finiteSelectiveOneTargetPackage :=
  strongCartesianLiftOfTarget finiteSelectiveTwoInput.semantic
    finiteSelectiveOneTargetPackage

/-- Actual strong cartesian lift for the three-source member. -/
noncomputable def finiteSelectiveThreeLift :
    StrongCartesianLift finiteSelectiveThreeInput.semantic
      finiteSelectiveOneTargetPackage :=
  strongCartesianLiftOfTarget finiteSelectiveThreeInput.semantic
    finiteSelectiveOneTargetPackage

/--
The finite two-member portfolio of pairwise nonisomorphic, noninvertible arrows
and their generated strong cartesian lifts.
-/
noncomputable def finiteParametricCartLiftFamily :
    ParametricCartLiftFamily FiniteModel.carrier where
  Parameter := Bool
  first := false
  second := true
  first_ne_second := by decide
  input
    | false => finiteSelectiveTwoInput
    | true => finiteSelectiveThreeInput
  pairwise_nonisomorphic := by
    intro first second hne
    cases first <;> cases second
    · exact (hne rfl).elim
    · exact finiteSelectiveTwoThreeInputs_not_isomorphic
    · exact finiteSelectiveThreeTwoInputs_not_isomorphic
    · exact (hne rfl).elim
  endpoints_nonisomorphic := by
    intro parameter
    cases parameter
    · exact finiteSelectiveTwoEndpoints_not_isomorphic
    · exact finiteSelectiveThreeEndpoints_not_isomorphic
  hom_not_isIso := by
    intro parameter
    cases parameter
    · exact finiteSelectiveTwoInput_not_isIso
    · exact finiteSelectiveThreeInput_not_isIso
  targetPackage
    | false => finiteSelectiveOneTargetPackage
    | true => finiteSelectiveOneTargetPackage
  lift
    | false => finiteSelectiveTwoLift
    | true => finiteSelectiveThreeLift

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
