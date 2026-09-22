import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreTransportReindexAdjunction
import ResearchLean.AG.DoctrineFiberProduct.PointedDoctrinePullback
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
The canonical core Beck--Chevalley mate for every commuting square of exact
pointed doctrine morphisms. The square and both adjunctions are semantic:
no finite code or realization witness is required.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open CategoryTheory.Limits

set_option maxHeartbeats 3000000

/-- The semantic square generated from an arbitrary exact pointed cospan. -/
def semanticPointedPullbackSquare
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionInstance U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    ExtInstSquare U where
  northwest := pointedPullback sigmaOne sigmaTwo
  northeast := DTwo
  southwest := DOne
  southeast := Base
  top := pointedPullbackSnd sigmaOne sigmaTwo
  left := pointedPullbackFst sigmaOne sigmaTwo
  right := sigmaTwo
  bottom := sigmaOne
  commutes := pointedPullback_commutes sigmaOne sigmaTwo

/-- The generated semantic square satisfies the pullback universal property. -/
theorem semanticPointedPullbackSquare_isPullback
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionInstance U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    IsPullback
      (semanticPointedPullbackSquare sigmaOne sigmaTwo).left
      (semanticPointedPullbackSquare sigmaOne sigmaTwo).top
      (semanticPointedPullbackSquare sigmaOne sigmaTwo).bottom
      (semanticPointedPullbackSquare sigmaOne sigmaTwo).right :=
  pointedPullback_isPullback sigmaOne sigmaTwo

noncomputable def semanticCoreTransportSquareIso
    {U : AtomCarrier.{u}} (square : ExtInstSquare U) :
    coreFiberTransportFunctor square.top ⋙
        coreFiberTransportFunctor square.right ≅
      coreFiberTransportFunctor square.left ⋙
        coreFiberTransportFunctor square.bottom :=
  (coreFiberCompositor square.top square.right).symm ≪≫
    eqToIso (congrArg coreFiberTransportFunctor square.commutes.symm) ≪≫
    coreFiberCompositor square.left square.bottom

noncomputable def semanticCoreBeckChevalleyMate
    {U : AtomCarrier.{u}} (square : ExtInstSquare U) :
    exact_bottom_semantic_global_reindex_functor square.left ⋙
        coreFiberTransportFunctor square.top ⟶
      coreFiberTransportFunctor square.bottom ⋙
        exact_bottom_semantic_global_reindex_functor square.right :=
  (mateEquiv
    (semanticCoreTransportReindexAdjunction
      ⟨square.northwest, square.southwest, square.left⟩)
    (semanticCoreTransportReindexAdjunction
      ⟨square.northeast, square.southeast, square.right⟩)
    (semanticCoreTransportSquareIso square).hom).natTrans

/-- Equation (5.17): the semantic mate is the right-leg unit, the
reindexed covariant square comparison, and the reindexed left-leg counit. -/
theorem semanticCoreBeckChevalleyMate_app
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (sourcePackage : CoreFiber square.southwest) :
    (semanticCoreBeckChevalleyMate square).app sourcePackage =
      (semanticCoreTransportReindexAdjunction
        ⟨square.northeast, square.southeast, square.right⟩).unit.app
          ((coreFiberTransportFunctor square.top).obj
            ((exact_bottom_semantic_global_reindex_functor square.left).obj
              sourcePackage)) ≫
        (exact_bottom_semantic_global_reindex_functor square.right).map
          ((semanticCoreTransportSquareIso square).hom.app
            ((exact_bottom_semantic_global_reindex_functor square.left).obj
              sourcePackage)) ≫
        (exact_bottom_semantic_global_reindex_functor square.right).map
          ((coreFiberTransportFunctor square.bottom).map
            ((semanticCoreTransportReindexAdjunction
              ⟨square.northwest, square.southwest, square.left⟩).counit.app
                sourcePackage)) := by
  simp [semanticCoreBeckChevalleyMate, mateEquiv_apply]

/-- Every semantic mate is invertible, with no finite presentation premise. -/
theorem semanticCoreBeckChevalleyMate_isIso
    {U : AtomCarrier.{u}} (square : ExtInstSquare U) :
    IsIso (semanticCoreBeckChevalleyMate square) := by
  letI : IsIso (semanticCoreTransportReindexUnit
      ⟨square.northeast, square.southeast, square.right⟩) :=
    semanticCoreTransportReindexUnit_isIso _
  letI : IsIso (semanticCoreTransportReindexCounit
      ⟨square.northwest, square.southwest, square.left⟩) :=
    semanticCoreTransportReindexCounit_isIso _
  rw [NatTrans.isIso_iff_isIso_app]
  intro sourcePackage
  let topSource :=
    (coreFiberTransportFunctor square.top).obj
      ((exact_bottom_semantic_global_reindex_functor square.left).obj
        sourcePackage)
  let unitApp := (semanticCoreTransportReindexAdjunction
    ⟨square.northeast, square.southeast, square.right⟩).unit.app topSource
  let squareApp := (semanticCoreTransportSquareIso square).hom.app
    ((exact_bottom_semantic_global_reindex_functor square.left).obj sourcePackage)
  let counitApp := (semanticCoreTransportReindexAdjunction
    ⟨square.northwest, square.southwest, square.left⟩).counit.app sourcePackage
  letI : IsIso unitApp := by
    change IsIso ((semanticCoreTransportReindexUnit
      ⟨square.northeast, square.southeast, square.right⟩).app topSource)
    exact semanticCoreTransportReindexUnit_app_isIso
      ⟨square.northeast, square.southeast, square.right⟩ topSource
  letI : IsIso squareApp := by
    dsimp [squareApp]
    infer_instance
  letI : IsIso counitApp := by
    change IsIso ((semanticCoreTransportReindexCounit
      ⟨square.northwest, square.southwest, square.left⟩).app sourcePackage)
    exact semanticCoreTransportReindexCounit_app_isIso
      ⟨square.northwest, square.southwest, square.left⟩ sourcePackage
  rw [show (semanticCoreBeckChevalleyMate square).app sourcePackage =
      unitApp ≫
        (exact_bottom_semantic_global_reindex_functor square.right).map squareApp ≫
        (exact_bottom_semantic_global_reindex_functor square.right).map
          ((coreFiberTransportFunctor square.bottom).map counitApp) by
    simp [semanticCoreBeckChevalleyMate, mateEquiv_apply,
      unitApp, squareApp, counitApp]
    rfl]
  infer_instance

noncomputable instance semanticCoreBeckChevalleyMate_app_isIso
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (sourcePackage : CoreFiber square.southwest) :
    IsIso ((semanticCoreBeckChevalleyMate square).app sourcePackage) :=
  (NatTrans.isIso_iff_isIso_app
    (semanticCoreBeckChevalleyMate square)).mp
      (semanticCoreBeckChevalleyMate_isIso square) sourcePackage

/-- Equation (5.19): the discrepancy from the canonical comparison is the
identity exactly when the specified comparison is canonical. -/
theorem semanticCoreBeckChevalley_discrepancy_eq_id_iff
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (sourcePackage : CoreFiber square.southwest)
    (specified :
      (exact_bottom_semantic_global_reindex_functor square.left ⋙
        coreFiberTransportFunctor square.top).obj sourcePackage ⟶
      (coreFiberTransportFunctor square.bottom ⋙
        exact_bottom_semantic_global_reindex_functor square.right).obj
          sourcePackage) :
    specified ≫ inv ((semanticCoreBeckChevalleyMate square).app sourcePackage) =
        𝟙 _ ↔
      specified = (semanticCoreBeckChevalleyMate square).app sourcePackage := by
  constructor
  · intro h
    calc
      specified = specified ≫
          (inv ((semanticCoreBeckChevalleyMate square).app sourcePackage) ≫
            (semanticCoreBeckChevalleyMate square).app sourcePackage) := by
              simp
      _ = (specified ≫
          inv ((semanticCoreBeckChevalleyMate square).app sourcePackage)) ≫
            (semanticCoreBeckChevalleyMate square).app sourcePackage := by
              simp only [Category.assoc]
      _ = (semanticCoreBeckChevalleyMate square).app sourcePackage := by
              rw [h, Category.id_comp]
  · intro h
    rw [h]
    simp

/-- The mate equivalence uniquely identifies the canonical comparison by
its covariant transport square. -/
theorem semanticCoreBeckChevalleyMate_characterization
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (specified :
      exact_bottom_semantic_global_reindex_functor square.left ⋙
          coreFiberTransportFunctor square.top ⟶
        coreFiberTransportFunctor square.bottom ⋙
          exact_bottom_semantic_global_reindex_functor square.right) :
    specified = semanticCoreBeckChevalleyMate square ↔
      (mateEquiv
        (semanticCoreTransportReindexAdjunction
          ⟨square.northwest, square.southwest, square.left⟩)
        (semanticCoreTransportReindexAdjunction
          ⟨square.northeast, square.southeast, square.right⟩)).symm
      (TwoSquare.mk _ _ _ _ specified) =
        (semanticCoreTransportSquareIso square).hom := by
  let E :
      TwoSquare (coreFiberTransportFunctor square.top)
        (coreFiberTransportFunctor square.left)
        (coreFiberTransportFunctor square.right)
        (coreFiberTransportFunctor square.bottom) ≃
      TwoSquare (exact_bottom_semantic_global_reindex_functor square.left)
        (coreFiberTransportFunctor square.bottom)
        (coreFiberTransportFunctor square.top)
        (exact_bottom_semantic_global_reindex_functor square.right) := mateEquiv
    (semanticCoreTransportReindexAdjunction
      ⟨square.northwest, square.southwest, square.left⟩)
    (semanticCoreTransportReindexAdjunction
      ⟨square.northeast, square.southeast, square.right⟩)
  have hm : (TwoSquare.mk _ _ _ _
      (semanticCoreBeckChevalleyMate square)) =
      E (semanticCoreTransportSquareIso square).hom := rfl
  constructor
  · intro h
    subst specified
    rw [hm]
    exact E.left_inv _
  · intro h
    apply congrArg E at h
    rw [E.apply_symm_apply] at h
    rw [← hm] at h
    exact congrArg TwoSquare.natTrans h

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
