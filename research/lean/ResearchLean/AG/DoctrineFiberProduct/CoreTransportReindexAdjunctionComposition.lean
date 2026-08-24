import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema
import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement

/-!
# Generated transport--reindex adjunction under finite composition

This module transports the composite of the two generated component
adjunctions across the covariant and contravariant finite-presentation
compositors.  The resulting adjunction has exactly the functors of the direct
composite presentation.  Its unit and counit are expanded through both
component adjunctions and both generated compositors, fixing the coherence
route.  Strong-cartesian uniqueness then identifies it with the independently
generated direct adjunction.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

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

/-- The typed covariant compositor factors the direct generated lift through
the literal two-step generated lift.  This exposes the equality cast hidden in
the typed compositor wrapper and is the covariant triangle used by the
adjunction-composition comparison. -/
theorem typedCoreFiberTransportCompositor_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (sourcePackage : CoreFiber source.toSemantic) :
    coreFiberLift (typedPresentationToSemantic (compPresentation first second))
        sourcePackage ≫
        ((typedCoreFiberTransportCompositor first second).hom.app sourcePackage).1 =
      coreFiberIteratedLift (typedPresentationToSemantic first)
        (typedPresentationToSemantic second) sourcePackage := by
  rw [typedCoreFiberTransportCompositor_eq]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change coreFiberLift
      (typedPresentationToSemantic (compPresentation first second))
      sourcePackage ≫
        (((eqToIso (congrArg coreFiberTransportFunctor
          (typedPresentationToSemantic_comp first second))).hom.app
            sourcePackage).1 ≫
          (coreFiberCompositorApp (typedPresentationToSemantic first)
            (typedPresentationToSemantic second) sourcePackage).hom.1) = _
  rw [← Category.assoc]
  rw [coreFiberLift_eqToIso_fac _ _
    (typedPresentationToSemantic_comp first second)]
  exact coreFiberCompositorApp_hom_fac _ _ sourcePackage

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
source.  The final adjunction equality establishes its comparison with the
direct generated counit. -/
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

/-- G-110(E) finite-composition adjunction coherence: after transporting the
component adjunction composite across the generated covariant and
contravariant compositors, it is exactly the independently generated
transport--reindex adjunction of the direct composite presentation.  The proof
uses both component transpose factor laws, both compositor triangles, and
strong-cartesian uniqueness; no equality of adjunctions is caller-supplied. -/
theorem coreTransportReindexCompositorAdjunction_eq_direct
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    coreTransportReindexCompositorAdjunction first second =
      coreTransportReindexAdjunction
        (typedRealizableHom (compPresentation first second)) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext sourcePackage
  simp only [coreTransportReindexCompositorAdjunction,
    Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft,
    Adjunction.mkOfHomEquiv_unit_app, Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.equivHomsetLeftOfNatIso_apply,
    Adjunction.equivHomsetRightOfNatIso_apply, Adjunction.comp_homEquiv,
    Equiv.trans_apply, coreTransportReindexAdjunction,
    coreTransportReindexCoreHomEquiv, coreTransportReindexHomEquiv,
    Category.comp_id]
  let directPackage := (coreFiberTransportFunctor
    (typedPresentationToSemantic (compPresentation first second))).obj
      sourcePackage
  let middlePackage :=
    (coreFiberTransportFunctor
      (typedPresentationToSemantic first)).obj sourcePackage
  let secondTranspose := coreTransportToReindexHom
    (typedRealizableHom second) middlePackage directPackage
    ((typedCoreFiberTransportCompositor first second).inv.app sourcePackage)
  let firstTranspose := coreTransportToReindexHom
    (typedRealizableHom first) sourcePackage
    ((selectedCoreFiberReindexFunctor
      (typedRealizableHom second)).obj directPackage) secondTranspose
  change firstTranspose ≫
      (selectedCoreFiberReindexCompositor first second).hom.app directPackage =
    coreTransportToReindexHom
      (typedRealizableHom (compPresentation first second)) sourcePackage
      directPackage (𝟙 directPackage)
  apply CategoryTheory.Functor.Fiber.hom_ext
  let directLift := selectedTypedCoreFiberCartesianLift
    (compPresentation first second) directPackage
  letI : (packageProjection U).IsStronglyCartesian
      (typedPresentationToSemantic (compPresentation first second))
      directLift.hom := directLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U)
    (typedPresentationToSemantic (compPresentation first second))
    directLift.hom (𝟙 source.toSemantic)
  change (firstTranspose.1 ≫
      (selectedCoreFiberReindexCompositorApp first second directPackage).hom.1) ≫
        directLift.hom =
    (coreTransportToReindexHom
      (typedRealizableHom (compPresentation first second)) sourcePackage
      directPackage (𝟙 directPackage)).1 ≫ directLift.hom
  rw [Category.assoc, selectedCoreFiberReindexCompositorApp_hom_fac]
  change firstTranspose.1 ≫
      ((selectedTypedCoreFiberCartesianLift first
          ((selectedTypedCoreFiberReindexFunctor second).obj
            directPackage)).hom ≫
        (selectedTypedCoreFiberCartesianLift second directPackage).hom) =
    (coreTransportToReindexHom
      (typedRealizableHom (compPresentation first second)) sourcePackage
      directPackage (𝟙 directPackage)).1 ≫
      (selectedTypedCoreFiberCartesianLift
        (compPresentation first second) directPackage).hom
  have firstFactorization :
      firstTranspose.1 ≫
          (selectedCoreFiberCartesianLift (typedRealizableHom first) _).hom =
        coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
          secondTranspose.1 := by
    simpa only [typedRealizableHom, typedCartSemanticInput] using
      coreTransportToReindexHom_fac
        (typedRealizableHom first) sourcePackage _ secondTranspose
  have secondFactorization :
      secondTranspose.1 ≫
          (selectedCoreFiberCartesianLift
            (typedRealizableHom second) directPackage).hom =
        coreFiberLift (typedPresentationToSemantic second) middlePackage ≫
          ((typedCoreFiberTransportCompositor first second).inv.app
            sourcePackage).1 := by
    simpa only [typedRealizableHom, typedCartSemanticInput] using
      coreTransportToReindexHom_fac
        (typedRealizableHom second) middlePackage directPackage
        ((typedCoreFiberTransportCompositor first second).inv.app sourcePackage)
  have directFactorization :
      (coreTransportToReindexHom
          (typedRealizableHom (compPresentation first second)) sourcePackage
          directPackage (𝟙 directPackage)).1 ≫
          (selectedTypedCoreFiberCartesianLift
            (compPresentation first second) directPackage).hom =
        coreFiberLift
          (typedPresentationToSemantic (compPresentation first second))
          sourcePackage := by
    simpa only [typedRealizableHom, typedCartSemanticInput,
      Category.comp_id] using
      coreTransportToReindexHom_fac
        (typedRealizableHom (compPresentation first second)) sourcePackage
        directPackage (𝟙 directPackage)
  calc
    firstTranspose.1 ≫
        ((selectedTypedCoreFiberCartesianLift first
            ((selectedTypedCoreFiberReindexFunctor second).obj
              directPackage)).hom ≫
          (selectedTypedCoreFiberCartesianLift second directPackage).hom) =
      (firstTranspose.1 ≫
        (selectedCoreFiberCartesianLift (typedRealizableHom first) _).hom) ≫
        (selectedCoreFiberCartesianLift
          (typedRealizableHom second) directPackage).hom :=
      (Category.assoc _ _ _).symm
    _ = (coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
          secondTranspose.1) ≫
        (selectedCoreFiberCartesianLift
          (typedRealizableHom second) directPackage).hom := by
      rw [firstFactorization]
    _ = coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
        (secondTranspose.1 ≫
          (selectedCoreFiberCartesianLift
            (typedRealizableHom second) directPackage).hom) :=
      Category.assoc _ _ _
    _ = coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
        (coreFiberLift (typedPresentationToSemantic second) middlePackage ≫
          ((typedCoreFiberTransportCompositor first second).inv.app
            sourcePackage).1) := by
      rw [secondFactorization]
    _ = coreFiberIteratedLift (typedPresentationToSemantic first)
          (typedPresentationToSemantic second) sourcePackage ≫
        ((typedCoreFiberTransportCompositor first second).inv.app
          sourcePackage).1 :=
      (Category.assoc _ _ _).symm
    _ = coreFiberLift
        (typedPresentationToSemantic (compPresentation first second))
        sourcePackage := by
      rw [← typedCoreFiberTransportCompositor_hom_fac first second
        sourcePackage, Category.assoc]
      have hcancel :=
        congrArg (fun f => f.1)
          (Iso.hom_inv_id
            ((typedCoreFiberTransportCompositor first second).app sourcePackage))
      change ((typedCoreFiberTransportCompositor first second).hom.app
          sourcePackage).1 ≫
          ((typedCoreFiberTransportCompositor first second).inv.app
            sourcePackage).1 = 𝟙 _ at hcancel
      rw [hcancel]
      exact Category.comp_id _
    _ = (coreTransportToReindexHom
          (typedRealizableHom (compPresentation first second)) sourcePackage
          directPackage (𝟙 directPackage)).1 ≫
        (selectedTypedCoreFiberCartesianLift
          (compPresentation first second) directPackage).hom := by
      simpa using directFactorization.symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
