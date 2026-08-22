import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCoherence
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingWitnesses

/-!
# Finite witnesses for constructor-relative reindexing coherence

The selected compositor and unitor are fired on the existing finite selective
chain and the genuine four-axis swap.  Associativity uses a three-step
selective chain `3 → 2 → 1 → support`; the middle leg is already known
noninvertible, and the new first leg is independently noninvertible.  No lift,
comparison, natural isomorphism, or coherence certificate is supplied to the
generic producers.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Executable Atom equality for the concrete finite carrier. -/
local instance finiteCartesianReindexCoherenceAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## The selected two-step compositor and unitor -/

/-- The selected two-step contravariant compositor at the four-axis package. -/
noncomputable def finiteSelectiveReindexCompositorApp :=
  selectedCoreFiberReindexCompositorApp
    finiteSelectiveTwoToOnePresentation
    finiteSelectiveOneToSupportPresentation
    finiteReindexFourAxisTarget

/-- The concrete compositor consumes the actual direct and iterated selected lifts. -/
theorem finiteSelectiveReindexCompositorApp_fac :
    finiteSelectiveReindexCompositorApp.hom.1 ≫
        (selectedTypedCoreFiberCartesianLift
          finiteSelectiveTwoToSupportPresentation
          finiteReindexFourAxisTarget).hom =
      (selectedCoreFiberIteratedCartesianLift
        finiteSelectiveTwoToOnePresentation
        finiteSelectiveOneToSupportPresentation
        finiteReindexFourAxisTarget).hom :=
  selectedCoreFiberReindexCompositorApp_hom_fac
    finiteSelectiveTwoToOnePresentation
    finiteSelectiveOneToSupportPresentation
    finiteReindexFourAxisTarget

/-- Compositor naturality fires on the genuine nonidentity four-axis swap. -/
theorem finiteSelectiveReindexCompositor_naturality :
    (selectedTypedCoreFiberReindexFunctor
        finiteSelectiveOneToSupportPresentation ⋙
      selectedTypedCoreFiberReindexFunctor
        finiteSelectiveTwoToOnePresentation).map finiteReindexAxisSwapHom ≫
        finiteSelectiveReindexCompositorApp.hom =
      finiteSelectiveReindexCompositorApp.hom ≫
        (selectedTypedCoreFiberReindexFunctor
          finiteSelectiveTwoToSupportPresentation).map
            finiteReindexAxisSwapHom :=
  selectedCoreFiberReindexCompositor_naturality
    finiteSelectiveTwoToOnePresentation
    finiteSelectiveOneToSupportPresentation
    finiteReindexAxisSwapHom

/-- The selected typed identity unitor at the finite support package. -/
noncomputable def finiteSupportReindexUnitorApp :=
  selectedCoreFiberReindexUnitorApp finitePortfolioSupportInstance
    finiteReindexFourAxisTarget

/-- The concrete unitor satisfies its actual selected-lift triangle. -/
theorem finiteSupportReindexUnitorApp_fac :
    finiteSupportReindexUnitorApp.hom.1 ≫
        (selectedTypedCoreFiberCartesianLift
          (idTypedPresentation finitePortfolioSupportInstance)
          finiteReindexFourAxisTarget).hom =
      𝟙 finiteReindexFourAxisTarget.1 :=
  selectedCoreFiberReindexUnitorApp_hom_fac
    finitePortfolioSupportInstance finiteReindexFourAxisTarget

/-- Unitor naturality fires on the same nonidentity four-axis swap. -/
theorem finiteSupportReindexUnitor_naturality :
    finiteReindexAxisSwapHom ≫ finiteSupportReindexUnitorApp.hom =
      finiteSupportReindexUnitorApp.hom ≫
        (selectedTypedCoreFiberReindexFunctor
          (idTypedPresentation finitePortfolioSupportInstance)).map
            finiteReindexAxisSwapHom :=
  selectedCoreFiberReindexUnitor_naturality
    finitePortfolioSupportInstance finiteReindexAxisSwapHom

/-! ## A nondegenerate three-step selective chain -/

/-- The third cell of the three-source selective doctrine. -/
def finiteSelectiveThreeLast : (finiteSelectiveDoctrineCode 3).Source :=
  ULift.up (2 : Fin 3)

/-- Collapse the three selective cells to two while preserving the selected point. -/
def finiteSelectiveThreeToTwoCoherenceSourceMap :
    finiteSelectiveThreeInstance.doctrine.Source →
      finiteSelectiveTwoInstance.doctrine.Source :=
  fun source =>
    if source.down.val = 1 then finiteSelectiveTwoOther
    else finiteSelectiveTwoPoint

/-- The new source table preserves the selected point. -/
@[simp]
theorem finiteSelectiveThreeToTwoCoherenceSourceMap_point :
    finiteSelectiveThreeToTwoCoherenceSourceMap finiteSelectiveThreePoint =
      finiteSelectiveTwoPoint := by
  simp [finiteSelectiveThreeToTwoCoherenceSourceMap,
    finiteSelectiveThreePoint]

/-- The third source cell has the same image as the selected source cell. -/
@[simp]
theorem finiteSelectiveThreeToTwoCoherenceSourceMap_last :
    finiteSelectiveThreeToTwoCoherenceSourceMap finiteSelectiveThreeLast =
      finiteSelectiveTwoPoint := by
  simp [finiteSelectiveThreeToTwoCoherenceSourceMap,
    finiteSelectiveThreeLast, finiteSelectiveThreeInstance,
    finiteSelectiveDoctrineCode]

/-- The selected and third source cells are distinct. -/
theorem finiteSelectiveThreePoint_ne_last :
    finiteSelectiveThreePoint ≠ finiteSelectiveThreeLast := by
  intro equality
  have hdown := congrArg
    (fun source : (finiteSelectiveDoctrineCode 3).Source => source.down.val)
    equality
  norm_num [finiteSelectiveDoctrineCode, finiteSelectiveThreePoint,
    finiteSelectiveThreeLast] at hdown

/-- A validated nonidentity first leg for the three-step coherence witness. -/
def finiteSelectiveThreeToTwoCoherencePresentation :
    CartPresentationBetween finiteSelectiveThreeInstance
      finiteSelectiveTwoInstance where
  sourceMap := finiteSelectiveThreeToTwoCoherenceSourceMap
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq _ := by
    change finiteWithoutComponentCAtomPredicate =
      finiteWithoutComponentCAtomPredicate.transport
        AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := finiteSelectiveThreeToTwoCoherenceSourceMap_point

/-- The new three-to-two table is not injective. -/
theorem finiteSelectiveThreeToTwoCoherenceSourceMap_not_injective :
    ¬ Function.Injective
      finiteSelectiveThreeToTwoCoherencePresentation.sourceMap := by
  intro hinjective
  exact finiteSelectiveThreePoint_ne_last
    (hinjective (by
      change finiteSelectiveThreeToTwoCoherenceSourceMap
          finiteSelectiveThreePoint =
        finiteSelectiveThreeToTwoCoherenceSourceMap finiteSelectiveThreeLast
      rw [finiteSelectiveThreeToTwoCoherenceSourceMap_point,
        finiteSelectiveThreeToTwoCoherenceSourceMap_last]))

/-- The first leg of the three-step coherence chain is genuinely noninvertible. -/
theorem finiteSelectiveThreeToTwoCoherenceInput_not_isIso :
    ¬ IsIso
      (typedRealizableHom
        finiteSelectiveThreeToTwoCoherencePresentation).semantic.hom := by
  intro hiso
  letI : IsIso
      (typedRealizableHom
        finiteSelectiveThreeToTwoCoherencePresentation).semantic.hom := hiso
  exact finiteSelectiveThreeToTwoCoherenceSourceMap_not_injective
    (extInstHom_sourceMap_injective_of_isIso
      (typedRealizableHom
        finiteSelectiveThreeToTwoCoherencePresentation).semantic.hom)

/-- The middle leg remains the existing noninvertible two-to-one arrow. -/
theorem finiteSelectiveCoherenceMiddle_not_isIso :
    ¬ IsIso
      (typedRealizableHom finiteSelectiveTwoToOnePresentation).semantic.hom :=
  finiteSelectiveTwoInput_not_isIso

/-! ## Concrete associativity and unit firing -/

/-- Three-step associativity fires on the nondegenerate selective chain. -/
theorem finiteSelectiveReindexCompositor_assoc :
    selectedCoreFiberReindexAssocLeftRoute
        finiteSelectiveThreeToTwoCoherencePresentation
        finiteSelectiveTwoToOnePresentation
        finiteSelectiveOneToSupportPresentation
        finiteReindexFourAxisTarget =
      selectedCoreFiberReindexAssocRightRoute
        finiteSelectiveThreeToTwoCoherencePresentation
        finiteSelectiveTwoToOnePresentation
        finiteSelectiveOneToSupportPresentation
        finiteReindexFourAxisTarget :=
  selectedCoreFiberReindexCompositor_assoc
    finiteSelectiveThreeToTwoCoherencePresentation
    finiteSelectiveTwoToOnePresentation
    finiteSelectiveOneToSupportPresentation
    finiteReindexFourAxisTarget

/-- Left unit coherence fires on the noninvertible selective-two composite. -/
theorem finiteSelectiveReindexCompositor_left_unit :
    selectedCoreFiberReindexLeftUnitRoute
        finiteSelectiveTwoToSupportPresentation finiteReindexFourAxisTarget =
      𝟙 ((selectedTypedCoreFiberReindexFunctor
        finiteSelectiveTwoToSupportPresentation).obj
          finiteReindexFourAxisTarget) :=
  selectedCoreFiberReindexCompositor_left_unit
    finiteSelectiveTwoToSupportPresentation finiteReindexFourAxisTarget

/-- Right unit coherence fires on the same noninvertible selective-two composite. -/
theorem finiteSelectiveReindexCompositor_right_unit :
    selectedCoreFiberReindexRightUnitRoute
        finiteSelectiveTwoToSupportPresentation finiteReindexFourAxisTarget =
      𝟙 ((selectedTypedCoreFiberReindexFunctor
        finiteSelectiveTwoToSupportPresentation).obj
          finiteReindexFourAxisTarget) :=
  selectedCoreFiberReindexCompositor_right_unit
    finiteSelectiveTwoToSupportPresentation finiteReindexFourAxisTarget

/-- The vertical map used by the naturality controls is genuinely nonidentity. -/
theorem finiteSelectiveReindexCoherence_axisSwap_ne_id :
    finiteReindexAxisSwapHom ≠ 𝟙 finiteReindexFourAxisTarget :=
  finiteReindexAxisSwapHom_ne_id

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
