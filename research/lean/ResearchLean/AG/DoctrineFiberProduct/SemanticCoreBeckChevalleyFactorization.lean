import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw

/-! Lift factorization of the unrestricted semantic square comparison. -/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

theorem semanticCoreTransportSquareIso_eq_indexed
    {U : AtomCarrier.{u}} (square : ExtInstSquare U) :
    semanticCoreTransportSquareIso square =
      indexedSquareOuterComparison
        (ValidatedIndexedBaseSquare.ofTerm (.leaf square.commutes)) := by
  rfl

/-- The two covariant routes of a semantic commuting square identify their
generated composite lifts, without any finite presentation. -/
theorem semanticCoreTransportSquareIso_hom_fac
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (P : CoreFiber square.northwest) :
    coreFiberIteratedLift square.top square.right P ≫
      ((semanticCoreTransportSquareIso square).hom.app P).1 =
    coreFiberIteratedLift square.left square.bottom P := by
  exact indexedSquareOuterComparison_hom_fac
    (ValidatedIndexedBaseSquare.ofTerm
      (.leaf square.commutes)) P

/-- Equation (5.18): the canonical mate is the unique route comparison
compatible with the cocartesian and cartesian lift factors. -/
theorem semanticCoreBeckChevalleyMate_lift_fac
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (P : CoreFiber square.southwest) :
    coreFiberLift square.top
        ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
      ((semanticCoreBeckChevalleyMate square).app P).1 ≫
      (exact_bottom_semantic_global_selected_lift square.right
        ((coreFiberTransportFunctor square.bottom).obj P)).hom =
    (exact_bottom_semantic_global_selected_lift square.left P).hom ≫
      coreFiberLift square.bottom P := by
  let R := (exact_bottom_semantic_global_reindex_functor square.left).obj P
  let sigmaCmp := (semanticCoreTransportSquareIso square).hom.app R
  let ε := (semanticCoreTransportReindexAdjunction
    ⟨square.northwest, square.southwest, square.left⟩).counit.app P
  let D := (coreFiberTransportFunctor square.top).obj R
  let B := (coreFiberTransportFunctor square.bottom).obj P
  let η := (semanticCoreTransportReindexAdjunction
    ⟨square.northeast, square.southeast, square.right⟩).unit.app D
  change coreFiberLift square.top R ≫
      ((semanticCoreBeckChevalleyMate square).app P).1 ≫
      (exact_bottom_semantic_global_selected_lift square.right B).hom =
    (exact_bottom_semantic_global_selected_lift square.left P).hom ≫
      coreFiberLift square.bottom P
  have fiber_comp {A B C : CoreFiber square.northeast} (f : A ⟶ B) (g : B ⟶ C) :
      (f ≫ g).1 = f.1 ≫ g.1 := rfl
  rw [semanticCoreBeckChevalleyMate_app]
  simp only [fiber_comp, Category.assoc]
  dsimp only [B, Functor.id_obj]
  have hmap₂ := exact_bottom_semantic_global_reindex_map_fac square.right
    ((coreFiberTransportFunctor square.bottom).map ε)
  simp only [Functor.id_obj] at hmap₂
  rw [hmap₂]
  have hmap₁ := exact_bottom_semantic_global_reindex_map_fac square.right sigmaCmp
  dsimp only [R, Functor.comp_obj] at hmap₁
  dsimp only [Functor.comp_obj]
  simp only [← Category.assoc]
  rw [Category.assoc (coreFiberLift square.top R ≫ η.1)]
  rw [hmap₁]
  have hunit := semanticCoreTransportReindexUnit_app_fac
    (⟨square.northeast, square.southeast, square.right⟩ : CartSemanticInput U) D
  change η.1 ≫
      (exact_bottom_semantic_global_selected_lift square.right
        ((coreFiberTransportFunctor square.right).obj D)).hom =
    coreFiberLift square.right D at hunit
  dsimp only [D, R] at hunit ⊢
  rw [← Category.assoc]
  rw [Category.assoc (coreFiberLift square.top
    ((exact_bottom_semantic_global_reindex_functor square.left).obj P)) η.1
    (exact_bottom_semantic_global_selected_lift square.right
      ((coreFiberTransportFunctor square.right).obj
        ((coreFiberTransportFunctor square.top).obj
          ((exact_bottom_semantic_global_reindex_functor square.left).obj P)))).hom]
  rw [hunit]
  have hsquare := semanticCoreTransportSquareIso_hom_fac square R
  dsimp only [R, coreFiberIteratedLift] at hsquare
  rw [hsquare]
  have htransport := coreFiberTransportMap_fac square.bottom ε
  change coreFiberLift square.bottom
      ((coreFiberTransportFunctor square.left).obj
        ((exact_bottom_semantic_global_reindex_functor square.left).obj P)) ≫
      ((coreFiberTransportFunctor square.bottom).map ε).1 =
    ε.1 ≫ coreFiberLift square.bottom P at htransport
  rw [Category.assoc (coreFiberLift square.left
    ((exact_bottom_semantic_global_reindex_functor square.left).obj P))]
  rw [htransport]
  have hcounit := semanticCoreTransportReindexCounit_app_fac
    (⟨square.northwest, square.southwest, square.left⟩ : CartSemanticInput U) P
  change coreFiberLift square.left
      ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫ ε.1 =
    (exact_bottom_semantic_global_selected_lift square.left P).hom at hcounit
  rw [← Category.assoc]
  rw [hcounit]

/-- Proposition 5.12: the two lift triangles of (5.18) characterize the
canonical component among all specified comparisons, without assuming that
the specified comparison is invertible. -/
theorem semanticCoreBeckChevalleyMate_lift_fac_iff
    {U : AtomCarrier.{u}} (square : ExtInstSquare U)
    (P : CoreFiber square.southwest)
    (specified :
      (exact_bottom_semantic_global_reindex_functor square.left ⋙
        coreFiberTransportFunctor square.top).obj P ⟶
      (coreFiberTransportFunctor square.bottom ⋙
        exact_bottom_semantic_global_reindex_functor square.right).obj P) :
    coreFiberLift square.top
        ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
      specified.1 ≫
      (exact_bottom_semantic_global_selected_lift square.right
        ((coreFiberTransportFunctor square.bottom).obj P)).hom =
      (exact_bottom_semantic_global_selected_lift square.left P).hom ≫
        coreFiberLift square.bottom P ↔
    specified = (semanticCoreBeckChevalleyMate square).app P := by
  constructor
  · intro h
    apply CategoryTheory.Functor.Fiber.hom_ext
    let rightLift := exact_bottom_semantic_global_selected_lift square.right
      ((coreFiberTransportFunctor square.bottom).obj P)
    letI : (packageProjection U).IsStronglyCartesian square.right rightLift.hom := by
      simpa only [rightLift, cartSemanticInputOfHom] using rightLift.isStronglyCartesian
    letI : (packageProjection U).IsStronglyCocartesian square.top
        (coreFiberLift square.top
          ((exact_bottom_semantic_global_reindex_functor square.left).obj P)) :=
      coreFiberLift_isStronglyCocartesian square.top _
    letI : (packageProjection U).IsHomLift (𝟙 square.northeast) specified.1 :=
      specified.2
    letI : (packageProjection U).IsHomLift (𝟙 square.northeast)
        ((semanticCoreBeckChevalleyMate square).app P).1 :=
      ((semanticCoreBeckChevalleyMate square).app P).2
    letI : (packageProjection U).IsHomLift square.top
        (coreFiberLift square.top
          ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
          specified.1) := by
      infer_instance
    letI : (packageProjection U).IsHomLift square.top
        (coreFiberLift square.top
          ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
          ((semanticCoreBeckChevalleyMate square).app P).1) := by
      infer_instance
    have hcart :
        coreFiberLift square.top
            ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
          specified.1 =
        coreFiberLift square.top
            ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
          ((semanticCoreBeckChevalleyMate square).app P).1 := by
      apply CategoryTheory.Functor.IsStronglyCartesian.ext
        (packageProjection U) square.right rightLift.hom square.top
      change coreFiberLift square.top
          ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
          specified.1 ≫ rightLift.hom =
        coreFiberLift square.top
          ((exact_bottom_semantic_global_reindex_functor square.left).obj P) ≫
          ((semanticCoreBeckChevalleyMate square).app P).1 ≫ rightLift.hom
      rw [h, semanticCoreBeckChevalleyMate_lift_fac square P]
    apply CategoryTheory.Functor.IsStronglyCocartesian.ext
      (packageProjection U) square.top
      (coreFiberLift square.top
        ((exact_bottom_semantic_global_reindex_functor square.left).obj P))
      (𝟙 square.northeast)
    exact hcart
  · intro h
    subst specified
    exact semanticCoreBeckChevalleyMate_lift_fac square P

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
