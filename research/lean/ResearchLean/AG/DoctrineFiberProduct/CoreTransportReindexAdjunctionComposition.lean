import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCoherence

/-!
# Generated transport--reindex adjunction under finite composition

This module transports the composite of the two generated component
adjunctions across the covariant and contravariant finite-presentation
compositors.  The resulting adjunction has exactly the functors of the direct
composite presentation.  Its unit and counit are expanded through both
component adjunctions and both generated compositors, fixing the coherence
route that a later theorem must compare with the independently generated
direct adjunction.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- G-110(E) pullback-side composition predecessor: transport the composite
of the two generated component adjunctions onto the direct finite-composite
transport and selected-reindex functors.  Both route isomorphisms are the
producer-derived compositors; no adjunction or coherence equality is supplied
by the caller. -/
noncomputable def coreTransportReindexCompositorAdjunction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    coreFiberTransportFunctor
        (typedPresentationToSemantic (compPresentation first second)) ⊣
      selectedTypedCoreFiberReindexFunctor
        (compPresentation first second) :=
  ((((coreTransportReindexAdjunction (typedRealizableHom first)).comp
      (coreTransportReindexAdjunction (typedRealizableHom second))).ofNatIsoLeft
        (typedCoreFiberTransportCompositor first second).symm).ofNatIsoRight
          (selectedCoreFiberReindexCompositor first second))

private theorem coreTransportReindexCompositorAdjunction_unit_app_homEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (sourcePackage : CoreFiber source.toSemantic) :
    (coreTransportReindexCompositorAdjunction first second).unit.app sourcePackage =
      (((coreTransportReindexAdjunction (typedRealizableHom first)).comp
        (coreTransportReindexAdjunction (typedRealizableHom second))).homEquiv
          sourcePackage _
          ((typedCoreFiberTransportCompositor first second).inv.app
            sourcePackage)) ≫
        (selectedCoreFiberReindexCompositor first second).hom.app _ := by
  simp [coreTransportReindexCompositorAdjunction, Adjunction.ofNatIsoLeft,
    Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.equivHomsetLeftOfNatIso,
    Adjunction.equivHomsetRightOfNatIso]

private theorem coreTransportReindexCompositorAdjunction_counit_app_homEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (coreTransportReindexCompositorAdjunction first second).counit.app targetPackage =
      (typedCoreFiberTransportCompositor first second).hom.app _ ≫
        (((coreTransportReindexAdjunction (typedRealizableHom first)).comp
          (coreTransportReindexAdjunction (typedRealizableHom second))).homEquiv
            _ _).symm
          ((selectedCoreFiberReindexCompositor first second).inv.app
            targetPackage) := by
  simp [coreTransportReindexCompositorAdjunction, Adjunction.ofNatIsoLeft,
    Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.equivHomsetLeftOfNatIso,
    Adjunction.equivHomsetRightOfNatIso]

private theorem coreTransportReindexCompositorAdjunction_unit_app_expanded
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (sourcePackage : CoreFiber source.toSemantic) :
    (coreTransportReindexCompositorAdjunction first second).unit.app sourcePackage =
      ((coreTransportReindexAdjunction (typedRealizableHom first)).comp
        (coreTransportReindexAdjunction (typedRealizableHom second))).unit.app
          sourcePackage ≫
        (selectedTypedCoreFiberReindexFunctor second ⋙
          selectedTypedCoreFiberReindexFunctor first).map
            ((typedCoreFiberTransportCompositor first second).inv.app
              sourcePackage) ≫
        (selectedCoreFiberReindexCompositor first second).hom.app _ := by
  rw [coreTransportReindexCompositorAdjunction_unit_app_homEquiv,
    Adjunction.homEquiv_unit]
  simp only [typedRealizableHom, typedCartSemanticInput,
    selectedTypedCoreFiberReindexFunctor, Category.assoc]

private theorem coreTransportReindexCompositorAdjunction_counit_app_expanded
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (coreTransportReindexCompositorAdjunction first second).counit.app targetPackage =
      (typedCoreFiberTransportCompositor first second).hom.app _ ≫
        (coreFiberTransportFunctor
          (typedPresentationToSemantic first) ⋙
          coreFiberTransportFunctor
            (typedPresentationToSemantic second)).map
          ((selectedCoreFiberReindexCompositor first second).inv.app
            targetPackage) ≫
        ((coreTransportReindexAdjunction (typedRealizableHom first)).comp
          (coreTransportReindexAdjunction (typedRealizableHom second))).counit.app
            targetPackage := by
  rw [coreTransportReindexCompositorAdjunction_counit_app_homEquiv,
    Adjunction.homEquiv_counit]
  simp only [typedRealizableHom, typedCartSemanticInput,
    selectedTypedCoreFiberReindexFunctor]

/-- The transported composite-adjunction unit is the first generated unit,
the reindexed second generated unit, transport by the inverse covariant
compositor, and the forward selected-reindex compositor.  This fixes every
constituent and its order before comparison with the direct generated unit. -/
theorem coreTransportReindexCompositorAdjunction_unit_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (sourcePackage : CoreFiber source.toSemantic) :
    (coreTransportReindexCompositorAdjunction first second).unit.app sourcePackage =
      (coreTransportReindexAdjunction
          (typedRealizableHom first)).unit.app sourcePackage ≫
        (selectedTypedCoreFiberReindexFunctor first).map
          ((coreTransportReindexAdjunction
            (typedRealizableHom second)).unit.app
              ((coreFiberTransportFunctor
                (typedPresentationToSemantic first)).obj sourcePackage)) ≫
        (selectedTypedCoreFiberReindexFunctor second ⋙
          selectedTypedCoreFiberReindexFunctor first).map
            ((typedCoreFiberTransportCompositor first second).inv.app
              sourcePackage) ≫
        (selectedCoreFiberReindexCompositor first second).hom.app _ := by
  rw [coreTransportReindexCompositorAdjunction_unit_app_expanded,
    Adjunction.comp_unit_app]
  simp only [typedRealizableHom, typedCartSemanticInput,
    selectedTypedCoreFiberReindexFunctor, Category.assoc]

/-- The transported composite-adjunction counit is the inverse selected
reindex compositor mapped through both transports, followed by the first and
second generated counits, with the forward covariant compositor at the
source.  Equality with the direct generated counit remains the next coherence
obligation. -/
theorem coreTransportReindexCompositorAdjunction_counit_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (targetPackage : CoreFiber target.toSemantic) :
    (coreTransportReindexCompositorAdjunction first second).counit.app targetPackage =
      (typedCoreFiberTransportCompositor first second).hom.app _ ≫
        (coreFiberTransportFunctor
          (typedPresentationToSemantic first) ⋙
          coreFiberTransportFunctor
            (typedPresentationToSemantic second)).map
          ((selectedCoreFiberReindexCompositor first second).inv.app
            targetPackage) ≫
        (coreFiberTransportFunctor
          (typedPresentationToSemantic second)).map
          ((coreTransportReindexAdjunction
            (typedRealizableHom first)).counit.app
              ((selectedTypedCoreFiberReindexFunctor second).obj
                targetPackage)) ≫
        (coreTransportReindexAdjunction
          (typedRealizableHom second)).counit.app targetPackage := by
  rw [coreTransportReindexCompositorAdjunction_counit_app_expanded,
    Adjunction.comp_counit_app]
  simp only [typedRealizableHom, typedCartSemanticInput,
    selectedTypedCoreFiberReindexFunctor]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
