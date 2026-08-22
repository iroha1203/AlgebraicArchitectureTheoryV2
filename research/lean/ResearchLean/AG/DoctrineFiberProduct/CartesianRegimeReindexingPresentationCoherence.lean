import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationReplacement

/-!
# Presentation-relative coherence for selected cartesian reindexing

This module descends the selected contravariant compositor and unitor across
finite-presentation replacement.  An arbitrary direct presentation is compared
with the generated composite presentation using equality of their decoded
semantic arrows.  Likewise, an arbitrary identity-decoding presentation is
compared with the generated identity presentation.

## Implementation notes

The public constructions accept only typed presentations and decoded-arrow
equalities.  They compose the Cycle 32 selected compositor or unitor with the
producer-generated presentation comparison from the preceding module.  The
simultaneous-replacement proofs normalize the relevant selected lifts to one
literal semantic input and consume the Cycle 33 cleavage compatibility
theorems.  Semantic equality retags only strong-cartesianness propositions; no
complete functor is transported and no comparison or coherence datum is
accepted from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Semantic equalities generated from typed presentation data -/

/--
The generated composite presentation has the decoded arrow prescribed by an
arbitrary direct presentation satisfying the semantic composition equation.
This API lemma supports the relative compositor without exposing a composite
comparison as caller data.
-/
theorem typedPresentationComposite_eq_direct
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (composition_eq : typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second) :
    typedPresentationToSemantic (compPresentation first second) =
      typedPresentationToSemantic direct := by
  calc
    _ = typedPresentationToSemantic first ≫
        typedPresentationToSemantic second := by
      simpa only [typedCartSemanticInput, typedRealizableHom_hom] using
        typedRealizableHom_comp_hom first second
    _ = _ := composition_eq.symm

/--
Semantic replacement of both composable legs generates semantic replacement
of their authored composite presentations.  This is an API lemma for the
simultaneous compositor square.
-/
theorem typedPresentationComposite_congr
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first₀ first₁ : CartPresentationBetween source middle)
    (second₀ second₁ : CartPresentationBetween middle target)
    (first_eq : typedPresentationToSemantic first₀ =
      typedPresentationToSemantic first₁)
    (second_eq : typedPresentationToSemantic second₀ =
      typedPresentationToSemantic second₁) :
    typedPresentationToSemantic (compPresentation first₀ second₀) =
      typedPresentationToSemantic (compPresentation first₁ second₁) := by
  calc
    _ = typedPresentationToSemantic first₀ ≫
        typedPresentationToSemantic second₀ := by
      simpa only [typedCartSemanticInput, typedRealizableHom_hom] using
        typedRealizableHom_comp_hom first₀ second₀
    _ = typedPresentationToSemantic first₁ ≫
        typedPresentationToSemantic second₁ := by
      rw [first_eq, second_eq]
    _ = _ := by
      simpa only [typedCartSemanticInput, typedRealizableHom_hom] using
        (typedRealizableHom_comp_hom first₁ second₁).symm

/--
Two arbitrary direct presentations have equal decoded arrows when their two
leg presentations are replaced semantically and both direct arrows satisfy the
corresponding composition equations.  The simultaneous compositor theorem
uses this generated equality for its direct comparison.
-/
theorem typedPresentationDirect_congr
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct₀ direct₁ : CartPresentationBetween source target)
    (first₀ first₁ : CartPresentationBetween source middle)
    (second₀ second₁ : CartPresentationBetween middle target)
    (composition₀ : typedPresentationToSemantic direct₀ =
      typedPresentationToSemantic first₀ ≫
        typedPresentationToSemantic second₀)
    (composition₁ : typedPresentationToSemantic direct₁ =
      typedPresentationToSemantic first₁ ≫
        typedPresentationToSemantic second₁)
    (first_eq : typedPresentationToSemantic first₀ =
      typedPresentationToSemantic first₁)
    (second_eq : typedPresentationToSemantic second₀ =
      typedPresentationToSemantic second₁) :
    typedPresentationToSemantic direct₀ =
      typedPresentationToSemantic direct₁ := by
  calc
    _ = typedPresentationToSemantic first₀ ≫
        typedPresentationToSemantic second₀ := composition₀
    _ = typedPresentationToSemantic first₁ ≫
        typedPresentationToSemantic second₁ := by
      rw [first_eq, second_eq]
    _ = _ := composition₁.symm

/--
The generated identity presentation and any identity-decoding presentation
have equal decoded arrows.  This API lemma supplies the comparison used by the
relative unitor.
-/
theorem typedPresentationIdentity_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation : CartPresentationBetween instanceCode instanceCode)
    (identity_eq : typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic) :
    typedPresentationToSemantic (idTypedPresentation instanceCode) =
      typedPresentationToSemantic identityPresentation := by
  calc
    _ = 𝟙 instanceCode.toSemantic := by
      simpa only [typedCartSemanticInput, typedRealizableHom_hom] using
        typedRealizableHom_id_hom instanceCode
    _ = _ := identity_eq.symm

/-! ## Relative compositor -/

/--
The relative compositor component for an arbitrary direct presentation.  Its
second factor is generated by presentation replacement from the authored
composite to `direct`.
-/
noncomputable def selectedTypedCoreFiberPresentationCompositorApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (composition_eq : typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first).obj targetPackage ≅
      (selectedTypedCoreFiberReindexFunctor direct).obj targetPackage :=
  (selectedCoreFiberReindexCompositorApp first second targetPackage).trans
    (selectedTypedCoreFiberPresentationComparisonApp
      (compPresentation first second) direct
      (typedPresentationComposite_eq_direct direct first second composition_eq)
      targetPackage)

/--
The forward relative compositor component followed by the direct selected lift
is the literal two-step selected lift.  This is the component triangle used by
the presentation-replacement compatibility proof.
-/
theorem selectedTypedCoreFiberPresentationCompositorApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (composition_eq : typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberPresentationCompositorApp direct first second
      composition_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberCartesianLift direct targetPackage).hom =
      (selectedCoreFiberIteratedCartesianLift first second targetPackage).hom := by
  change
    ((selectedCoreFiberReindexCompositorApp first second targetPackage).hom.1 ≫
      (selectedTypedCoreFiberPresentationComparisonApp
        (compPresentation first second) direct
        (typedPresentationComposite_eq_direct direct first second composition_eq)
        targetPackage).hom.1) ≫
      (selectedTypedCoreFiberCartesianLift direct targetPackage).hom =
        (selectedCoreFiberIteratedCartesianLift first second targetPackage).hom
  rw [Category.assoc,
    selectedTypedCoreFiberPresentationComparisonApp_hom_fac,
    selectedCoreFiberReindexCompositorApp_hom_fac]

/--
The inverse relative compositor component followed by the literal two-step
lift is the direct selected lift.  Together with the forward triangle this
records both orientations of the generated comparison.
-/
theorem selectedTypedCoreFiberPresentationCompositorApp_inv_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (composition_eq : typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberPresentationCompositorApp direct first second
      composition_eq targetPackage).inv.1 ≫
        (selectedCoreFiberIteratedCartesianLift first second targetPackage).hom =
      (selectedTypedCoreFiberCartesianLift direct targetPackage).hom := by
  rw [← selectedTypedCoreFiberPresentationCompositorApp_hom_fac
    direct first second composition_eq targetPackage]
  have canceled := congrArg
    (fun hom => hom.1 ≫
      (selectedTypedCoreFiberCartesianLift direct targetPackage).hom)
    (selectedTypedCoreFiberPresentationCompositorApp direct first second
      composition_eq targetPackage).inv_hom_id
  simpa only [Category.assoc, Category.id_comp] using canceled

/--
The relative compositor component is natural on every vertical target map.
Naturality is generated from the Cycle 32 compositor and
`selectedTypedCoreFiberPresentationComparison`.
-/
theorem selectedTypedCoreFiberPresentationCompositor_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (composition_eq : typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second)
    {sourcePackage targetPackage : CoreFiber target.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first).map hom ≫
      (selectedTypedCoreFiberPresentationCompositorApp direct first second
        composition_eq targetPackage).hom =
      (selectedTypedCoreFiberPresentationCompositorApp direct first second
        composition_eq sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor direct).map hom := by
  change
    (selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first).map hom ≫
      ((selectedCoreFiberReindexCompositorApp first second targetPackage).hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp
          (compPresentation first second) direct
          (typedPresentationComposite_eq_direct direct first second composition_eq)
          targetPackage).hom) =
      ((selectedCoreFiberReindexCompositorApp first second sourcePackage).hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp
          (compPresentation first second) direct
          (typedPresentationComposite_eq_direct direct first second composition_eq)
          sourcePackage).hom) ≫
        (selectedTypedCoreFiberReindexFunctor direct).map hom
  calc
    _ = ((selectedTypedCoreFiberReindexFunctor second ⋙
          selectedTypedCoreFiberReindexFunctor first).map hom ≫
        (selectedCoreFiberReindexCompositorApp first second
          targetPackage).hom) ≫
        (selectedTypedCoreFiberPresentationComparisonApp
          (compPresentation first second) direct
          (typedPresentationComposite_eq_direct direct first second composition_eq)
          targetPackage).hom := (Category.assoc _ _ _).symm
    _ = ((selectedCoreFiberReindexCompositorApp first second
          sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor
          (compPresentation first second)).map hom) ≫
        (selectedTypedCoreFiberPresentationComparisonApp
          (compPresentation first second) direct
          (typedPresentationComposite_eq_direct direct first second composition_eq)
          targetPackage).hom := by
      rw [selectedCoreFiberReindexCompositor_naturality]
    _ = (selectedCoreFiberReindexCompositorApp first second
          sourcePackage).hom ≫
        ((selectedTypedCoreFiberReindexFunctor
          (compPresentation first second)).map hom ≫
          (selectedTypedCoreFiberPresentationComparisonApp
            (compPresentation first second) direct
            (typedPresentationComposite_eq_direct direct first second composition_eq)
            targetPackage).hom) := Category.assoc _ _ _
    _ = (selectedCoreFiberReindexCompositorApp first second
          sourcePackage).hom ≫
        ((selectedTypedCoreFiberPresentationComparisonApp
          (compPresentation first second) direct
          (typedPresentationComposite_eq_direct direct first second composition_eq)
          sourcePackage).hom ≫
          (selectedTypedCoreFiberReindexFunctor direct).map hom) := by
      rw [selectedTypedCoreFiberPresentationComparison_naturality]
    _ = _ := (Category.assoc _ _ _).symm

/--
The natural relative contravariant compositor for any direct presentation with
the prescribed decoded composite arrow.
-/
noncomputable def selectedTypedCoreFiberPresentationCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct : CartPresentationBetween source target)
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (composition_eq : typedPresentationToSemantic direct =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second) :
    selectedTypedCoreFiberReindexFunctor second ⋙
        selectedTypedCoreFiberReindexFunctor first ≅
      selectedTypedCoreFiberReindexFunctor direct :=
  NatIso.ofComponents
    (selectedTypedCoreFiberPresentationCompositorApp direct first second
      composition_eq)
    (fun hom => selectedTypedCoreFiberPresentationCompositor_naturality
      direct first second composition_eq hom)

/-! ## Simultaneous presentation replacement for the compositor -/

/--
Retag the selected lift family of `replacement` to the equal literal semantic
input of `reference`.  This private normalization changes only the
strong-cartesianness proposition and supplies the actual choices consumed by
the Cycle 33 compatibility theorem.
-/
private noncomputable def selectedTypedCoreFiberPresentationRetaggedCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (reference replacement : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic reference =
      typedPresentationToSemantic replacement) :
    CoreFiberCartesianCleavage (typedCartSemanticInput reference) where
  lift targetPackage := by
    let lift := selectedTypedCoreFiberCartesianLift replacement targetPackage
    exact
      { domain := lift.domain
        hom := lift.hom
        isStronglyCartesian := by
          change (packageProjection U).IsStronglyCartesian
            (typedPresentationToSemantic reference) lift.hom
          rw [semantic_eq]
          exact lift.isStronglyCartesian }

/--
The two `selectedTypedCoreFiberPresentationComparison` values whiskered across
a contravariant composable pair.  Its component is the second-leg comparison
mapped by the first functor, followed by the first-leg comparison at the
replaced object.
-/
noncomputable def selectedTypedCoreFiberPresentationHorizontalComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first₀ first₁ : CartPresentationBetween source middle)
    (second₀ second₁ : CartPresentationBetween middle target)
    (first_eq : typedPresentationToSemantic first₀ =
      typedPresentationToSemantic first₁)
    (second_eq : typedPresentationToSemantic second₀ =
      typedPresentationToSemantic second₁) :
    selectedTypedCoreFiberReindexFunctor second₀ ⋙
        selectedTypedCoreFiberReindexFunctor first₀ ≅
      selectedTypedCoreFiberReindexFunctor second₁ ⋙
        selectedTypedCoreFiberReindexFunctor first₁ :=
  (Functor.isoWhiskerRight
    (selectedTypedCoreFiberPresentationComparison second₀ second₁
      second_eq)
    (selectedTypedCoreFiberReindexFunctor first₀)).trans
  (Functor.isoWhiskerLeft
    (selectedTypedCoreFiberReindexFunctor second₁)
    (selectedTypedCoreFiberPresentationComparison first₀ first₁
      first_eq))

/--
Componentwise compatibility of relative compositors under simultaneous
replacement of the two legs and the direct presentation.  The proof
normalizes all six selected lift families to the first literal composite input
and applies Cycle 33 choice compatibility before returning through the
generated typed presentation comparisons.
-/
theorem selectedTypedCoreFiberPresentationCompositor_compatibility_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct₀ direct₁ : CartPresentationBetween source target)
    (first₀ first₁ : CartPresentationBetween source middle)
    (second₀ second₁ : CartPresentationBetween middle target)
    (composition₀ : typedPresentationToSemantic direct₀ =
      typedPresentationToSemantic first₀ ≫
        typedPresentationToSemantic second₀)
    (composition₁ : typedPresentationToSemantic direct₁ =
      typedPresentationToSemantic first₁ ≫
        typedPresentationToSemantic second₁)
    (first_eq : typedPresentationToSemantic first₀ =
      typedPresentationToSemantic first₁)
    (second_eq : typedPresentationToSemantic second₀ =
      typedPresentationToSemantic second₁)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberPresentationCompositorApp direct₀ first₀ second₀
      composition₀ targetPackage).hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp direct₀ direct₁
          (typedPresentationDirect_congr direct₀ direct₁ first₀ first₁
            second₀ second₁ composition₀ composition₁ first_eq second_eq)
          targetPackage).hom =
      (selectedTypedCoreFiberReindexFunctor first₀).map
          (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
            second_eq targetPackage).hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
          first_eq
          ((selectedTypedCoreFiberReindexFunctor second₁).obj
            targetPackage)).hom ≫
        (selectedTypedCoreFiberPresentationCompositorApp direct₁ first₁
          second₁ composition₁ targetPackage).hom := by
  let composite₀ := compPresentation first₀ second₀
  let composite₁ := compPresentation first₁ second₁
  let composite_eq : typedPresentationToSemantic composite₀ =
      typedPresentationToSemantic composite₁ :=
    typedPresentationComposite_congr first₀ first₁ second₀ second₁
      first_eq second_eq
  let composite_direct₀_eq : typedPresentationToSemantic composite₀ =
      typedPresentationToSemantic direct₀ :=
    typedPresentationComposite_eq_direct direct₀ first₀ second₀ composition₀
  let composite_direct₁_eq : typedPresentationToSemantic composite₀ =
      typedPresentationToSemantic direct₁ :=
    composite_eq.trans
      (typedPresentationComposite_eq_direct direct₁ first₁ second₁
        composition₁)
  let firstChoice₀ := selectedTypedCoreFiberCartesianCleavage first₀
  let firstChoice₁ := selectedTypedCoreFiberPresentationRetaggedCleavage
    first₀ first₁ first_eq
  let secondChoice₀ := selectedTypedCoreFiberCartesianCleavage second₀
  let secondChoice₁ := selectedTypedCoreFiberPresentationRetaggedCleavage
    second₀ second₁ second_eq
  let compositeChoice₀ :=
    selectedTypedCoreFiberPresentationRetaggedCleavage
      composite₀ direct₀ composite_direct₀_eq
  let compositeChoice₁ :=
    selectedTypedCoreFiberPresentationRetaggedCleavage
      composite₀ direct₁ composite_direct₁_eq
  have choiceCompatibility :=
    coreFiberCleavageReindexCompositor_compatibility_app
      first₀ second₀ firstChoice₀ firstChoice₁ secondChoice₀
      secondChoice₁ compositeChoice₀ compositeChoice₁ targetPackage
  have choiceCompatibility_fac := congrArg
    (fun route => route.1 ≫
      (selectedTypedCoreFiberCartesianLift direct₁ targetPackage).hom)
    choiceCompatibility
  apply CategoryTheory.Functor.Fiber.hom_ext
  let finalLift := selectedTypedCoreFiberCartesianLift direct₁ targetPackage
  letI := finalLift.isStronglyCartesian
  have compositeComparison_fac :
      (CoreFiberCartesianCleavage.comparisonApp compositeChoice₀
        compositeChoice₁ targetPackage).hom.1 ≫ finalLift.hom =
        (compositeChoice₀.lift targetPackage).hom := by
    change
      (CoreFiberCartesianCleavage.comparisonApp compositeChoice₀
        compositeChoice₁ targetPackage).hom.1 ≫
          (compositeChoice₁.lift targetPackage).hom =
        (compositeChoice₀.lift targetPackage).hom
    exact CoreFiberCartesianCleavage.comparisonApp_hom_fac
      compositeChoice₀ compositeChoice₁ targetPackage
  have secondCompositor_fac :
      (coreFiberCleavageReindexCompositorApp first₀ second₀
        firstChoice₁ secondChoice₁ compositeChoice₁
        targetPackage).hom.1 ≫ finalLift.hom =
      (coreFiberCleavageIteratedCartesianLift first₀ second₀
        firstChoice₁ secondChoice₁ targetPackage).hom := by
    change
      (coreFiberCleavageReindexCompositorApp first₀ second₀
        firstChoice₁ secondChoice₁ compositeChoice₁
        targetPackage).hom.1 ≫
          (compositeChoice₁.lift targetPackage).hom =
      (coreFiberCleavageIteratedCartesianLift first₀ second₀
        firstChoice₁ secondChoice₁ targetPackage).hom
    exact coreFiberCleavageReindexCompositorApp_hom_fac first₀ second₀
      firstChoice₁ secondChoice₁ compositeChoice₁ targetPackage
  have firstChoiceComparison_fac :
      (CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
        (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1 ≫
          (firstChoice₁.lift
            (secondChoice₁.reindexFunctor.obj targetPackage)).hom =
        (firstChoice₀.lift
          (secondChoice₁.reindexFunctor.obj targetPackage)).hom :=
    CoreFiberCartesianCleavage.comparisonApp_hom_fac firstChoice₀ firstChoice₁
      (secondChoice₁.reindexFunctor.obj targetPackage)
  have firstPresentationComparison_fac :
      (selectedTypedCoreFiberPresentationComparisonApp first₀ first₁ first_eq
        ((selectedTypedCoreFiberReindexFunctor second₁).obj
          targetPackage)).hom.1 ≫
          (selectedTypedCoreFiberCartesianLift first₁
            ((selectedTypedCoreFiberReindexFunctor second₁).obj
              targetPackage)).hom =
        (selectedTypedCoreFiberCartesianLift first₀
          ((selectedTypedCoreFiberReindexFunctor second₁).obj
            targetPackage)).hom :=
    selectedTypedCoreFiberPresentationComparisonApp_hom_fac first₀ first₁
      first_eq ((selectedTypedCoreFiberReindexFunctor second₁).obj targetPackage)
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (typedCartSemanticInput direct₁).hom
    finalLift.hom (𝟙 source.toSemantic)
  change
    (((selectedTypedCoreFiberPresentationCompositorApp direct₀ first₀ second₀
      composition₀ targetPackage).hom.1 ≫
        (selectedTypedCoreFiberPresentationComparisonApp direct₀ direct₁
          (typedPresentationDirect_congr direct₀ direct₁ first₀ first₁
            second₀ second₁ composition₀ composition₁ first_eq second_eq)
          targetPackage).hom.1) ≫ finalLift.hom) =
      ((((selectedTypedCoreFiberReindexFunctor first₀).map
          (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
            second_eq targetPackage).hom).1 ≫
        (selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
          first_eq
          ((selectedTypedCoreFiberReindexFunctor second₁).obj
            targetPackage)).hom.1) ≫
        (selectedTypedCoreFiberPresentationCompositorApp direct₁ first₁
          second₁ composition₁ targetPackage).hom.1) ≫ finalLift.hom
  change
    (((coreFiberCleavageReindexCompositorApp first₀ second₀
      firstChoice₀ secondChoice₀ compositeChoice₀
      targetPackage).hom.1 ≫
        (CoreFiberCartesianCleavage.comparisonApp compositeChoice₀
          compositeChoice₁ targetPackage).hom.1) ≫ finalLift.hom) =
      ((((firstChoice₀.reindexFunctor.map
          (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
            secondChoice₁ targetPackage).hom).1 ≫
        (CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
          (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1) ≫
        (coreFiberCleavageReindexCompositorApp first₀ second₀
          firstChoice₁ secondChoice₁ compositeChoice₁
          targetPackage).hom.1) ≫ finalLift.hom) at choiceCompatibility_fac
  calc
    _ = (selectedCoreFiberIteratedCartesianLift first₀ second₀
        targetPackage).hom := by
      rw [Category.assoc,
        selectedTypedCoreFiberPresentationComparisonApp_hom_fac,
        selectedTypedCoreFiberPresentationCompositorApp_hom_fac]
    _ = (((coreFiberCleavageReindexCompositorApp first₀ second₀
          firstChoice₀ secondChoice₀ compositeChoice₀
          targetPackage).hom.1 ≫
        (CoreFiberCartesianCleavage.comparisonApp compositeChoice₀
          compositeChoice₁ targetPackage).hom.1) ≫ finalLift.hom) := by
      symm
      calc
        _ = (coreFiberCleavageReindexCompositorApp first₀ second₀
              firstChoice₀ secondChoice₀ compositeChoice₀
              targetPackage).hom.1 ≫
            ((CoreFiberCartesianCleavage.comparisonApp compositeChoice₀
              compositeChoice₁ targetPackage).hom.1 ≫ finalLift.hom) :=
          Category.assoc _ _ _
        _ = (coreFiberCleavageReindexCompositorApp first₀ second₀
              firstChoice₀ secondChoice₀ compositeChoice₀
              targetPackage).hom.1 ≫
            (compositeChoice₀.lift targetPackage).hom := by
          rw [compositeComparison_fac]
        _ = (coreFiberCleavageIteratedCartesianLift first₀ second₀
              firstChoice₀ secondChoice₀ targetPackage).hom :=
          coreFiberCleavageReindexCompositorApp_hom_fac first₀ second₀
            firstChoice₀ secondChoice₀ compositeChoice₀ targetPackage
        _ = (selectedCoreFiberIteratedCartesianLift first₀ second₀
              targetPackage).hom := rfl
    _ = (((firstChoice₀.reindexFunctor.map
          (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
            secondChoice₁ targetPackage).hom).1 ≫
        (CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
          (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1) ≫
        (coreFiberCleavageReindexCompositorApp first₀ second₀
          firstChoice₁ secondChoice₁ compositeChoice₁
          targetPackage).hom.1) ≫ finalLift.hom := by
      exact choiceCompatibility_fac
    _ = (selectedCoreFiberIteratedCartesianLift first₀ second₀
        targetPackage).hom := by
      calc
        _ = ((firstChoice₀.reindexFunctor.map
              (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                secondChoice₁ targetPackage).hom).1 ≫
            (CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
              (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1) ≫
            ((coreFiberCleavageReindexCompositorApp first₀ second₀
              firstChoice₁ secondChoice₁ compositeChoice₁
              targetPackage).hom.1 ≫ finalLift.hom) := Category.assoc _ _ _
        _ = ((firstChoice₀.reindexFunctor.map
              (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                secondChoice₁ targetPackage).hom).1 ≫
            (CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
              (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1) ≫
            (coreFiberCleavageIteratedCartesianLift first₀ second₀
              firstChoice₁ secondChoice₁ targetPackage).hom := by
          rw [secondCompositor_fac]
        _ = (firstChoice₀.reindexFunctor.map
              (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                secondChoice₁ targetPackage).hom).1 ≫
            ((CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
              (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1 ≫
              ((firstChoice₁.lift
                (secondChoice₁.reindexFunctor.obj targetPackage)).hom ≫
                (secondChoice₁.lift targetPackage).hom)) := by
          simp only [coreFiberCleavageIteratedCartesianLift, Category.assoc]
        _ = (firstChoice₀.reindexFunctor.map
              (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                secondChoice₁ targetPackage).hom).1 ≫
            (((CoreFiberCartesianCleavage.comparisonApp firstChoice₀ firstChoice₁
              (secondChoice₁.reindexFunctor.obj targetPackage)).hom.1 ≫
              (firstChoice₁.lift
                (secondChoice₁.reindexFunctor.obj targetPackage)).hom) ≫
              (secondChoice₁.lift targetPackage).hom) := by
          exact congrArg
            (fun tail =>
              (firstChoice₀.reindexFunctor.map
                (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                  secondChoice₁ targetPackage).hom).1 ≫ tail)
            (Category.assoc _ _ _).symm
        _ = (firstChoice₀.reindexFunctor.map
              (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                secondChoice₁ targetPackage).hom).1 ≫
            ((firstChoice₀.lift
              (secondChoice₁.reindexFunctor.obj targetPackage)).hom ≫
              (secondChoice₁.lift targetPackage).hom) := by
          rw [firstChoiceComparison_fac]
        _ = ((firstChoice₀.reindexFunctor.map
              (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
                secondChoice₁ targetPackage).hom).1 ≫
            (firstChoice₀.lift
              (secondChoice₁.reindexFunctor.obj targetPackage)).hom) ≫
              (secondChoice₁.lift targetPackage).hom :=
          (Category.assoc _ _ _).symm
        _ = ((firstChoice₀.lift
              (secondChoice₀.reindexFunctor.obj targetPackage)).hom ≫
            (CoreFiberCartesianCleavage.comparisonApp secondChoice₀
              secondChoice₁ targetPackage).hom.1) ≫
              (secondChoice₁.lift targetPackage).hom := by
          rw [firstChoice₀.reindexFunctor_map_fac]
        _ = (firstChoice₀.lift
              (secondChoice₀.reindexFunctor.obj targetPackage)).hom ≫
            ((CoreFiberCartesianCleavage.comparisonApp secondChoice₀
              secondChoice₁ targetPackage).hom.1 ≫
              (secondChoice₁.lift targetPackage).hom) :=
          Category.assoc _ _ _
        _ = (firstChoice₀.lift
              (secondChoice₀.reindexFunctor.obj targetPackage)).hom ≫
            (secondChoice₀.lift targetPackage).hom := by
          rw [CoreFiberCartesianCleavage.comparisonApp_hom_fac]
        _ = (selectedCoreFiberIteratedCartesianLift first₀ second₀
              targetPackage).hom := rfl
    _ = ((((selectedTypedCoreFiberReindexFunctor first₀).map
          (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
            second_eq targetPackage).hom).1 ≫
        (selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
          first_eq
          ((selectedTypedCoreFiberReindexFunctor second₁).obj
            targetPackage)).hom.1) ≫
        (selectedTypedCoreFiberPresentationCompositorApp direct₁ first₁
          second₁ composition₁ targetPackage).hom.1) ≫ finalLift.hom := by
      symm
      calc
        _ = (((selectedTypedCoreFiberReindexFunctor first₀).map
              (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                second_eq targetPackage).hom).1 ≫
            (selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
              first_eq
              ((selectedTypedCoreFiberReindexFunctor second₁).obj
                targetPackage)).hom.1) ≫
            ((selectedTypedCoreFiberPresentationCompositorApp direct₁ first₁
              second₁ composition₁ targetPackage).hom.1 ≫
              finalLift.hom) := Category.assoc _ _ _
        _ = (((selectedTypedCoreFiberReindexFunctor first₀).map
              (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                second_eq targetPackage).hom).1 ≫
            (selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
              first_eq
              ((selectedTypedCoreFiberReindexFunctor second₁).obj
                targetPackage)).hom.1) ≫
            (selectedCoreFiberIteratedCartesianLift first₁ second₁
              targetPackage).hom := by
          rw [selectedTypedCoreFiberPresentationCompositorApp_hom_fac]
        _ = ((selectedTypedCoreFiberReindexFunctor first₀).map
              (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                second_eq targetPackage).hom).1 ≫
            ((selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
              first_eq
              ((selectedTypedCoreFiberReindexFunctor second₁).obj
                targetPackage)).hom.1 ≫
              ((selectedTypedCoreFiberCartesianLift first₁
                ((selectedTypedCoreFiberReindexFunctor second₁).obj
                  targetPackage)).hom ≫
                (selectedTypedCoreFiberCartesianLift second₁
                  targetPackage).hom)) := by
          simp only [selectedCoreFiberIteratedCartesianLift, Category.assoc]
        _ = ((selectedTypedCoreFiberReindexFunctor first₀).map
              (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                second_eq targetPackage).hom).1 ≫
            (((selectedTypedCoreFiberPresentationComparisonApp first₀ first₁
              first_eq
              ((selectedTypedCoreFiberReindexFunctor second₁).obj
                targetPackage)).hom.1 ≫
              (selectedTypedCoreFiberCartesianLift first₁
                ((selectedTypedCoreFiberReindexFunctor second₁).obj
                  targetPackage)).hom) ≫
              (selectedTypedCoreFiberCartesianLift second₁
                targetPackage).hom) := by
          exact congrArg
            (fun tail =>
              ((selectedTypedCoreFiberReindexFunctor first₀).map
                (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                  second_eq targetPackage).hom).1 ≫ tail)
            (Category.assoc _ _ _).symm
        _ = ((selectedTypedCoreFiberReindexFunctor first₀).map
              (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                second_eq targetPackage).hom).1 ≫
            ((selectedTypedCoreFiberCartesianLift first₀
              ((selectedTypedCoreFiberReindexFunctor second₁).obj
                targetPackage)).hom ≫
              (selectedTypedCoreFiberCartesianLift second₁
                targetPackage).hom) := by
          rw [firstPresentationComparison_fac]
        _ = (((selectedTypedCoreFiberReindexFunctor first₀).map
              (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
                second_eq targetPackage).hom).1 ≫
            (selectedTypedCoreFiberCartesianLift first₀
              ((selectedTypedCoreFiberReindexFunctor second₁).obj
                targetPackage)).hom) ≫
              (selectedTypedCoreFiberCartesianLift second₁
                targetPackage).hom := (Category.assoc _ _ _).symm
        _ = ((selectedTypedCoreFiberCartesianLift first₀
              ((selectedTypedCoreFiberReindexFunctor second₀).obj
                targetPackage)).hom ≫
            (selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
              second_eq targetPackage).hom.1) ≫
              (selectedTypedCoreFiberCartesianLift second₁
                targetPackage).hom := by
          rw [selectedTypedCoreFiberReindexFunctor_map_fac]
        _ = (selectedTypedCoreFiberCartesianLift first₀
              ((selectedTypedCoreFiberReindexFunctor second₀).obj
                targetPackage)).hom ≫
            ((selectedTypedCoreFiberPresentationComparisonApp second₀ second₁
              second_eq targetPackage).hom.1 ≫
              (selectedTypedCoreFiberCartesianLift second₁
                targetPackage).hom) := Category.assoc _ _ _
        _ = (selectedTypedCoreFiberCartesianLift first₀
              ((selectedTypedCoreFiberReindexFunctor second₀).obj
                targetPackage)).hom ≫
            (selectedTypedCoreFiberCartesianLift second₀ targetPackage).hom := by
          rw [selectedTypedCoreFiberPresentationComparisonApp_hom_fac]
        _ = (selectedCoreFiberIteratedCartesianLift first₀ second₀
              targetPackage).hom := rfl

/--
Whole relative compositor compatibility under simultaneous replacement of the
direct presentation and both composable legs.
-/
theorem selectedTypedCoreFiberPresentationCompositor_compatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (direct₀ direct₁ : CartPresentationBetween source target)
    (first₀ first₁ : CartPresentationBetween source middle)
    (second₀ second₁ : CartPresentationBetween middle target)
    (composition₀ : typedPresentationToSemantic direct₀ =
      typedPresentationToSemantic first₀ ≫
        typedPresentationToSemantic second₀)
    (composition₁ : typedPresentationToSemantic direct₁ =
      typedPresentationToSemantic first₁ ≫
        typedPresentationToSemantic second₁)
    (first_eq : typedPresentationToSemantic first₀ =
      typedPresentationToSemantic first₁)
    (second_eq : typedPresentationToSemantic second₀ =
      typedPresentationToSemantic second₁) :
    (selectedTypedCoreFiberPresentationCompositor direct₀ first₀ second₀
      composition₀).trans
        (selectedTypedCoreFiberPresentationComparison direct₀ direct₁
          (typedPresentationDirect_congr direct₀ direct₁ first₀ first₁
            second₀ second₁ composition₀ composition₁ first_eq second_eq)) =
      (selectedTypedCoreFiberPresentationHorizontalComparison first₀ first₁
        second₀ second₁ first_eq second_eq).trans
        (selectedTypedCoreFiberPresentationCompositor direct₁ first₁ second₁
          composition₁) := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  exact selectedTypedCoreFiberPresentationCompositor_compatibility_app
    direct₀ direct₁ first₀ first₁ second₀ second₁ composition₀
    composition₁ first_eq second_eq targetPackage

/-! ## Relative unitor -/

/--
The relative unitor component for an arbitrary identity-decoding
presentation.  Its second factor is the generated comparison from the authored
identity constructor to the supplied presentation.
-/
noncomputable def selectedTypedCoreFiberPresentationUnitorApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation : CartPresentationBetween instanceCode instanceCode)
    (identity_eq : typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    targetPackage ≅
      (selectedTypedCoreFiberReindexFunctor identityPresentation).obj
        targetPackage :=
  (selectedCoreFiberReindexUnitorApp instanceCode targetPackage).trans
    (selectedTypedCoreFiberPresentationComparisonApp
      (idTypedPresentation instanceCode) identityPresentation
      (typedPresentationIdentity_eq instanceCode identityPresentation
        identity_eq) targetPackage)

/--
The forward relative unitor component followed by the selected identity lift
is the literal identity package morphism.
-/
theorem selectedTypedCoreFiberPresentationUnitorApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation : CartPresentationBetween instanceCode instanceCode)
    (identity_eq : typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (selectedTypedCoreFiberPresentationUnitorApp instanceCode
      identityPresentation identity_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberCartesianLift identityPresentation
          targetPackage).hom =
      𝟙 targetPackage.1 := by
  change
    ((selectedCoreFiberReindexUnitorApp instanceCode targetPackage).hom.1 ≫
      (selectedTypedCoreFiberPresentationComparisonApp
        (idTypedPresentation instanceCode) identityPresentation
        (typedPresentationIdentity_eq instanceCode identityPresentation
          identity_eq) targetPackage).hom.1) ≫
      (selectedTypedCoreFiberCartesianLift identityPresentation
        targetPackage).hom = 𝟙 targetPackage.1
  rw [Category.assoc,
    selectedTypedCoreFiberPresentationComparisonApp_hom_fac,
    selectedCoreFiberReindexUnitorApp_hom_fac]

/--
The inverse relative unitor component is the selected identity lift itself.
This supplies the reverse component triangle.
-/
theorem selectedTypedCoreFiberPresentationUnitorApp_inv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation : CartPresentationBetween instanceCode instanceCode)
    (identity_eq : typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (selectedTypedCoreFiberPresentationUnitorApp instanceCode
      identityPresentation identity_eq targetPackage).inv.1 =
      (selectedTypedCoreFiberCartesianLift identityPresentation
        targetPackage).hom := by
  let comparison := selectedTypedCoreFiberPresentationUnitorApp instanceCode
    identityPresentation identity_eq targetPackage
  have inv_hom_id_underlying := congrArg (fun hom => hom.1)
    comparison.inv_hom_id
  change comparison.inv.1 ≫ comparison.hom.1 =
    𝟙 (selectedTypedCoreFiberCartesianLift identityPresentation
      targetPackage).domain at inv_hom_id_underlying
  have lift_eq_inv :
      (selectedTypedCoreFiberCartesianLift identityPresentation
        targetPackage).hom =
      comparison.inv.1 := by
    calc
      _ = 𝟙 (selectedTypedCoreFiberCartesianLift identityPresentation
            targetPackage).domain ≫
          (selectedTypedCoreFiberCartesianLift identityPresentation
            targetPackage).hom := (Category.id_comp _).symm
      _ = (comparison.inv.1 ≫ comparison.hom.1) ≫
          (selectedTypedCoreFiberCartesianLift identityPresentation
            targetPackage).hom := by
        exact (congrArg
          (fun hom => hom ≫
            (selectedTypedCoreFiberCartesianLift identityPresentation
              targetPackage).hom)
          inv_hom_id_underlying).symm
      _ = comparison.inv.1 ≫
          (comparison.hom.1 ≫
            (selectedTypedCoreFiberCartesianLift identityPresentation
              targetPackage).hom) := Category.assoc _ _ _
      _ = comparison.inv.1 ≫ 𝟙 targetPackage.1 := by
        rw [selectedTypedCoreFiberPresentationUnitorApp_hom_fac]
      _ = comparison.inv.1 := Category.comp_id _
  exact lift_eq_inv.symm

/--
The relative unitor component is natural on every vertical map in the fixed
core fiber.
-/
theorem selectedTypedCoreFiberPresentationUnitor_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation : CartPresentationBetween instanceCode instanceCode)
    (identity_eq : typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic)
    {sourcePackage targetPackage : CoreFiber instanceCode.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    hom ≫ (selectedTypedCoreFiberPresentationUnitorApp instanceCode
        identityPresentation identity_eq targetPackage).hom =
      (selectedTypedCoreFiberPresentationUnitorApp instanceCode
        identityPresentation identity_eq sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor identityPresentation).map hom := by
  change
    hom ≫ ((selectedCoreFiberReindexUnitorApp instanceCode
        targetPackage).hom ≫
      (selectedTypedCoreFiberPresentationComparisonApp
        (idTypedPresentation instanceCode) identityPresentation
        (typedPresentationIdentity_eq instanceCode identityPresentation
          identity_eq) targetPackage).hom) =
      ((selectedCoreFiberReindexUnitorApp instanceCode sourcePackage).hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp
          (idTypedPresentation instanceCode) identityPresentation
          (typedPresentationIdentity_eq instanceCode identityPresentation
            identity_eq) sourcePackage).hom) ≫
        (selectedTypedCoreFiberReindexFunctor identityPresentation).map hom
  calc
    _ = (hom ≫ (selectedCoreFiberReindexUnitorApp instanceCode
        targetPackage).hom) ≫
      (selectedTypedCoreFiberPresentationComparisonApp
        (idTypedPresentation instanceCode) identityPresentation
        (typedPresentationIdentity_eq instanceCode identityPresentation
          identity_eq) targetPackage).hom := (Category.assoc _ _ _).symm
    _ = ((selectedCoreFiberReindexUnitorApp instanceCode sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor
          (idTypedPresentation instanceCode)).map hom) ≫
      (selectedTypedCoreFiberPresentationComparisonApp
        (idTypedPresentation instanceCode) identityPresentation
        (typedPresentationIdentity_eq instanceCode identityPresentation
          identity_eq) targetPackage).hom := by
      rw [selectedCoreFiberReindexUnitor_naturality]
    _ = (selectedCoreFiberReindexUnitorApp instanceCode sourcePackage).hom ≫
      ((selectedTypedCoreFiberReindexFunctor
        (idTypedPresentation instanceCode)).map hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp
          (idTypedPresentation instanceCode) identityPresentation
          (typedPresentationIdentity_eq instanceCode identityPresentation
            identity_eq) targetPackage).hom) := Category.assoc _ _ _
    _ = (selectedCoreFiberReindexUnitorApp instanceCode sourcePackage).hom ≫
      ((selectedTypedCoreFiberPresentationComparisonApp
        (idTypedPresentation instanceCode) identityPresentation
        (typedPresentationIdentity_eq instanceCode identityPresentation
          identity_eq) sourcePackage).hom ≫
        (selectedTypedCoreFiberReindexFunctor identityPresentation).map hom) := by
      rw [selectedTypedCoreFiberPresentationComparison_naturality]
    _ = _ := (Category.assoc _ _ _).symm

/--
The natural relative contravariant unitor for any identity-decoding finite
presentation.
-/
noncomputable def selectedTypedCoreFiberPresentationUnitor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identityPresentation : CartPresentationBetween instanceCode instanceCode)
    (identity_eq : typedPresentationToSemantic identityPresentation =
      𝟙 instanceCode.toSemantic) :
    Functor.id (CoreFiber instanceCode.toSemantic) ≅
      selectedTypedCoreFiberReindexFunctor identityPresentation :=
  NatIso.ofComponents
    (selectedTypedCoreFiberPresentationUnitorApp instanceCode
      identityPresentation identity_eq)
    (fun hom => selectedTypedCoreFiberPresentationUnitor_naturality
      instanceCode identityPresentation identity_eq hom)

/-! ## Presentation replacement for the unitor -/

/--
Componentwise compatibility of the relative unitor for two independently
authored identity-decoding presentations.  The semantic equality between the
two presentations is derived from their identity equations.  Cycle 33 unitor
compatibility is applied to the canonical selected identity cleavage and the
second selected lift family retagged to that same literal input.
-/
theorem selectedTypedCoreFiberPresentationUnitor_compatibility_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identity₀ identity₁ :
      CartPresentationBetween instanceCode instanceCode)
    (identity₀_eq : typedPresentationToSemantic identity₀ =
      𝟙 instanceCode.toSemantic)
    (identity₁_eq : typedPresentationToSemantic identity₁ =
      𝟙 instanceCode.toSemantic)
    (targetPackage : CoreFiber instanceCode.toSemantic) :
    (selectedTypedCoreFiberPresentationUnitorApp instanceCode identity₀
      identity₀_eq targetPackage).hom ≫
        (selectedTypedCoreFiberPresentationComparisonApp identity₀ identity₁
          (identity₀_eq.trans identity₁_eq.symm) targetPackage).hom =
      (selectedTypedCoreFiberPresentationUnitorApp instanceCode identity₁
        identity₁_eq targetPackage).hom := by
  let canonicalIdentity := idTypedPresentation instanceCode
  let canonical_identity₁_eq :
      typedPresentationToSemantic canonicalIdentity =
        typedPresentationToSemantic identity₁ :=
    typedPresentationIdentity_eq instanceCode identity₁ identity₁_eq
  let firstChoice := selectedTypedCoreFiberCartesianCleavage canonicalIdentity
  let secondChoice := selectedTypedCoreFiberPresentationRetaggedCleavage
    canonicalIdentity identity₁ canonical_identity₁_eq
  have choiceCompatibility :=
    coreFiberCleavageReindexUnitor_compatibility_app instanceCode
      firstChoice secondChoice targetPackage
  have choiceCompatibility_fac := congrArg
    (fun route => route.1 ≫
      (selectedTypedCoreFiberCartesianLift identity₁ targetPackage).hom)
    choiceCompatibility
  apply CategoryTheory.Functor.Fiber.hom_ext
  let finalLift := selectedTypedCoreFiberCartesianLift identity₁ targetPackage
  letI := finalLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (typedCartSemanticInput identity₁).hom
    finalLift.hom (𝟙 instanceCode.toSemantic)
  change
    (((selectedTypedCoreFiberPresentationUnitorApp instanceCode identity₀
      identity₀_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberPresentationComparisonApp identity₀ identity₁
          (identity₀_eq.trans identity₁_eq.symm) targetPackage).hom.1) ≫
      finalLift.hom) =
      (selectedTypedCoreFiberPresentationUnitorApp instanceCode identity₁
        identity₁_eq targetPackage).hom.1 ≫ finalLift.hom
  calc
    _ = 𝟙 targetPackage.1 := by
      rw [Category.assoc,
        selectedTypedCoreFiberPresentationComparisonApp_hom_fac,
        selectedTypedCoreFiberPresentationUnitorApp_hom_fac]
    _ = ((coreFiberCleavageReindexUnitorApp instanceCode firstChoice
          targetPackage).hom.1 ≫
        (CoreFiberCartesianCleavage.comparisonApp firstChoice secondChoice
          targetPackage).hom.1) ≫ finalLift.hom := by
      symm
      calc
        _ = (coreFiberCleavageReindexUnitorApp instanceCode firstChoice
              targetPackage).hom.1 ≫
            ((CoreFiberCartesianCleavage.comparisonApp firstChoice secondChoice
              targetPackage).hom.1 ≫ finalLift.hom) := Category.assoc _ _ _
        _ = (coreFiberCleavageReindexUnitorApp instanceCode firstChoice
              targetPackage).hom.1 ≫
            (firstChoice.lift targetPackage).hom := by
          change
            (coreFiberCleavageReindexUnitorApp instanceCode firstChoice
              targetPackage).hom.1 ≫
                ((CoreFiberCartesianCleavage.comparisonApp firstChoice
                  secondChoice targetPackage).hom.1 ≫
                  (secondChoice.lift targetPackage).hom) =
              (coreFiberCleavageReindexUnitorApp instanceCode firstChoice
                targetPackage).hom.1 ≫
                (firstChoice.lift targetPackage).hom
          rw [CoreFiberCartesianCleavage.comparisonApp_hom_fac]
        _ = 𝟙 targetPackage.1 :=
          coreFiberCleavageReindexUnitorApp_hom_fac instanceCode firstChoice
            targetPackage
    _ = (coreFiberCleavageReindexUnitorApp instanceCode secondChoice
          targetPackage).hom.1 ≫ finalLift.hom := by
      simpa only [Category.assoc] using choiceCompatibility_fac
    _ = 𝟙 targetPackage.1 :=
      coreFiberCleavageReindexUnitorApp_hom_fac instanceCode secondChoice
        targetPackage
    _ = (selectedTypedCoreFiberPresentationUnitorApp instanceCode identity₁
          identity₁_eq targetPackage).hom.1 ≫ finalLift.hom :=
      (selectedTypedCoreFiberPresentationUnitorApp_hom_fac instanceCode identity₁
        identity₁_eq targetPackage).symm

/--
Whole relative unitor compatibility for any two identity-decoding
presentations.  The comparison between their selected functors is generated
solely from their decoded identity equations.
-/
theorem selectedTypedCoreFiberPresentationUnitor_compatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (instanceCode : FiniteInstanceCode U)
    (identity₀ identity₁ :
      CartPresentationBetween instanceCode instanceCode)
    (identity₀_eq : typedPresentationToSemantic identity₀ =
      𝟙 instanceCode.toSemantic)
    (identity₁_eq : typedPresentationToSemantic identity₁ =
      𝟙 instanceCode.toSemantic) :
    (selectedTypedCoreFiberPresentationUnitor instanceCode identity₀
      identity₀_eq).trans
        (selectedTypedCoreFiberPresentationComparison identity₀ identity₁
          (identity₀_eq.trans identity₁_eq.symm)) =
      selectedTypedCoreFiberPresentationUnitor instanceCode identity₁
        identity₁_eq := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  exact selectedTypedCoreFiberPresentationUnitor_compatibility_app
    instanceCode identity₀ identity₁ identity₀_eq identity₁_eq
      targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
