import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement

/-! Comparison of semantic-global Beck--Chevalley data with decoded finite presentations. -/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-- The unrestricted reindexing agrees with the finite selected reindexing
after the canonical comparison of their cartesian lifts. -/
noncomputable def semanticFiniteReindexComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    exact_bottom_semantic_global_reindex_functor input.semantic.hom ≅
      selectedCoreFiberReindexFunctor input := by
  exact coreFiberCleavageSelectedComparison input
    (exact_bottom_semantic_global_cartesian_cleavage input.semantic.hom)

/-- The bridge to the finite selected functor preserves the actual cartesian
lift, so it records a map law as well as an objectwise isomorphism. -/
theorem semanticFiniteReindexComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    ((semanticFiniteReindexComparison input).hom.app targetPackage).1 ≫
      (selectedCoreFiberCartesianLift input targetPackage).hom =
    (exact_bottom_semantic_global_selected_lift input.semantic.hom
      targetPackage).hom := by
  exact coreFiberCleavageSelectedComparisonApp_hom_fac input
    (exact_bottom_semantic_global_cartesian_cleavage input.semantic.hom)
    targetPackage

/-- The finite reindex comparison is exactly the adjoint conjugate of the
identity covariant transport map. This aligns the two adjunctions, not only
their right functors. -/
theorem semanticFiniteReindexComparison_eq_conjugate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    (semanticFiniteReindexComparison input).hom =
      conjugateEquiv
        (semanticCoreTransportReindexAdjunction input.semantic)
        (coreTransportReindexAdjunction input)
        (𝟙 (coreFiberTransportFunctor input.semantic.hom)) := by
  apply NatTrans.ext
  funext P
  apply CategoryTheory.Functor.Fiber.hom_ext
  let genericLift := exact_bottom_semantic_global_selected_lift
    input.semantic.hom P
  let finiteLift := selectedCoreFiberCartesianLift input P
  let conjugate := (conjugateEquiv
    (semanticCoreTransportReindexAdjunction input.semantic)
    (coreTransportReindexAdjunction input)
    (𝟙 (coreFiberTransportFunctor input.semantic.hom))).app P
  letI : (packageProjection U).IsStronglyCartesian input.semantic.hom
      finiteLift.hom := finiteLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom finiteLift.hom
    (𝟙 input.semantic.source)
  change ((semanticFiniteReindexComparison input).hom.app P).1 ≫
      finiteLift.hom = conjugate.1 ≫ finiteLift.hom
  rw [semanticFiniteReindexComparison_hom_fac]
  have hmap := coreFiberTransportMap_fac input.semantic.hom conjugate
  change coreFiberLift input.semantic.hom
      ((exact_bottom_semantic_global_reindex_functor input.semantic.hom).obj P) ≫
      ((coreFiberTransportFunctor input.semantic.hom).map conjugate).1 =
    conjugate.1 ≫ coreFiberLift input.semantic.hom
      ((selectedCoreFiberReindexFunctor input).obj P) at hmap
  have hcounit := conjugateEquiv_counit
    (semanticCoreTransportReindexAdjunction input.semantic)
    (coreTransportReindexAdjunction input)
    (𝟙 (coreFiberTransportFunctor input.semantic.hom)) P
  simp only [NatTrans.id_app, Category.id_comp] at hcounit
  have fiber_comp {A B C : CoreFiber input.semantic.target}
      (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).1 = f.1 ≫ g.1 := rfl
  have hcounit' := congrArg Subtype.val hcounit.symm
  simp only [fiber_comp] at hcounit'
  calc
    genericLift.hom =
        coreFiberLift input.semantic.hom
          ((exact_bottom_semantic_global_reindex_functor input.semantic.hom).obj P) ≫
          ((semanticCoreTransportReindexCounit input.semantic).app P).1 := by
            exact (semanticCoreTransportReindexCounit_app_fac input.semantic P).symm
    _ = coreFiberLift input.semantic.hom
          ((exact_bottom_semantic_global_reindex_functor input.semantic.hom).obj P) ≫
          ((coreFiberTransportFunctor input.semantic.hom).map conjugate).1 ≫
          ((coreTransportReindexCounit input).app P).1 := by
            exact congrArg
              (coreFiberLift input.semantic.hom
                ((exact_bottom_semantic_global_reindex_functor
                  input.semantic.hom).obj P) ≫ ·) hcounit'
    _ = conjugate.1 ≫
          coreFiberLift input.semantic.hom
            ((selectedCoreFiberReindexFunctor input).obj P) ≫
          ((coreTransportReindexCounit input).app P).1 := by
            rw [← Category.assoc, hmap, Category.assoc]
    _ = conjugate.1 ≫ finiteLift.hom := by
          rw [coreTransportReindexCounit_app_fac input P]

/-- The semantic covariant comparison specializes to the finite square
comparison after decoding, including all four mapped base arrows. -/
theorem semanticCoreTransportSquareIso_decode
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    semanticCoreTransportSquareIso (decodeBCSquare presentation) =
      bcCoreTransportSquareIso presentation := by
  have h := bcProvenanceCoreTransportSquareIso_eq_semantic
    (BCRealizationProvenance.mk presentation rfl :
      BCRealizationProvenance (toSemanticBC presentation))
  change bcCoreTransportSquareIso presentation =
    semanticCoreTransportSquareIso (decodeBCSquare presentation) at h
  exact h.symm

/-- The unrestricted mate specializes to the existing finite mate after the
canonical comparisons on both reindexing legs. This is the map-level
conservation law for decoded presentations. -/
theorem semanticCoreBeckChevalleyMate_decode
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    Functor.whiskerRight
        (semanticFiniteReindexComparison
          (bcLeftInput presentation)).hom
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))) ≫
      coreBeckChevalleyMate presentation =
    semanticCoreBeckChevalleyMate (decodeBCSquare presentation) ≫
      Functor.whiskerLeft
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation)))
        (semanticFiniteReindexComparison
          (bcRightInput presentation)).hom := by
  let square := decodeBCSquare presentation
  let leftGeneric := semanticCoreTransportReindexAdjunction
    (bcLeftInput presentation).semantic
  let leftFinite := bcLeftAdjunction presentation
  let rightGeneric := semanticCoreTransportReindexAdjunction
    (bcRightInput presentation).semantic
  let rightFinite := bcRightAdjunction presentation
  let alpha := (semanticCoreTransportSquareIso square).hom
  have rightChange := mateEquiv_conjugateEquiv_vcomp
    leftGeneric rightGeneric rightFinite alpha
      (𝟙 (coreFiberTransportFunctor square.right))
  have leftChange := conjugateEquiv_mateEquiv_vcomp
    leftGeneric leftFinite rightFinite
      (𝟙 (coreFiberTransportFunctor square.left)) alpha
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft] at rightChange leftChange
  have rightComp :
      (conjugateEquiv rightGeneric rightFinite)
        (𝟙 (coreFiberTransportFunctor square.right)) =
      (semanticFiniteReindexComparison (bcRightInput presentation)).hom := by
    simpa only [rightGeneric, rightFinite, bcRightAdjunction, bcRightInput,
      square, decodeBCSquare, typedRealizableHom, typedCartSemanticInput] using
      (semanticFiniteReindexComparison_eq_conjugate
        (bcRightInput presentation)).symm
  have leftComp :
      (conjugateEquiv leftGeneric leftFinite)
        (𝟙 (coreFiberTransportFunctor square.left)) =
      (semanticFiniteReindexComparison (bcLeftInput presentation)).hom := by
    simpa only [leftGeneric, leftFinite, bcLeftAdjunction, bcLeftInput,
      square, decodeBCSquare, typedRealizableHom, typedCartSemanticInput] using
      (semanticFiniteReindexComparison_eq_conjugate
        (bcLeftInput presentation)).symm
  rw [rightComp] at rightChange
  rw [leftComp] at leftChange
  let alphaSq : TwoSquare
      (coreFiberTransportFunctor square.top)
      (coreFiberTransportFunctor square.left)
      (coreFiberTransportFunctor square.right)
      (coreFiberTransportFunctor square.bottom) := alpha
  have middleEq :
      alphaSq.whiskerRight (𝟙 (coreFiberTransportFunctor square.right)) =
        alphaSq.whiskerLeft (𝟙 (coreFiberTransportFunctor square.left)) := by
    ext P
    simp [TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
  dsimp only [alphaSq, TwoSquare.whiskerRight, TwoSquare.whiskerLeft] at middleEq
  rw [middleEq] at rightChange
  have combined := leftChange.symm.trans rightChange
  change
    ((mateEquiv leftFinite rightFinite
      (bcCoreTransportSquareIso presentation).hom).whiskerTop
        (semanticFiniteReindexComparison (bcLeftInput presentation)).hom).natTrans =
    ((mateEquiv leftGeneric rightGeneric
      (semanticCoreTransportSquareIso square).hom).whiskerBottom
        (semanticFiniteReindexComparison (bcRightInput presentation)).hom).natTrans
  rw [← semanticCoreTransportSquareIso_decode presentation]
  exact congrArg TwoSquare.natTrans combined

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
