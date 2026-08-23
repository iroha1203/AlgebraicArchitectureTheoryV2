import Mathlib.CategoryTheory.Adjunction.Mates
import ResearchLean.AG.DoctrineFiberProduct.BCSchema
import ResearchLean.AG.DoctrineFiberProduct.DoctrinePullbackFiniteCode
import ResearchLean.AG.DoctrineFiberProduct.PointedDoctrinePullback
import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexAdjunction

/-!
# The canonical core Beck--Chevalley mate

For every validated finite Beck--Chevalley presentation, this module first
connects its decoded finite-code pullback to the generic pointed pullback of
Cycle 30.  It then compares the two covariant routes around the generated
square and applies the Cycle 35 adjunctions to obtain the canonical mate

`(π₁)^* ⋙ (π₂)_! ⟶ (σ₁)_! ⋙ (σ₂)^*`.

The displayed notation follows application order: the left side first
reindexes along `π₁` and then transports along `π₂`; the right side first
transports along `σ₁` and then reindexes along `σ₂`.  No pullback certificate,
comparison transformation, adjunction, unit, or counit is supplied by a caller.
The reindexing functors and adjunctions here use the fixed selected cleavage;
comparison with mates generated from arbitrary cleavages is a downstream
obligation, not a conclusion of this module.

## Implementation notes

The finite-code northwest object is not definitionally the generic Cycle 30
pullback.  We therefore use the producer-generated doctrine isomorphism and
prove its selected-point equation, rather than casting either endpoint or
assuming an endpoint isomorphism.  The covariant square comparison is the
inverse G-109 compositor on the top/right route, the decoded square equality,
and the compositor on the left/bottom route.  `mateEquiv` is then used directly
with the generated Cycle 35 adjunctions.  This keeps the unit/counit provenance
visible and rejects a hand-authored mate or a target-fitted component formula.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory CategoryTheory.Limits
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## The Cycle 30 pointed-pullback bridge -/

/--
The decoded finite-code pullback is canonically isomorphic, as a pointed
extraction instance, to the generic pointed pullback of its decoded cospan.
-/
noncomputable def finiteCodePointedPullbackIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    (pullbackInstanceCode first second).toSemantic ≅
      pointedPullback (typedPresentationToSemantic first)
        (typedPresentationToSemantic second) where
  hom :=
    { doctrineHom := (doctrinePullbackFiniteCodeIso first second).hom
      source_eq := by
        apply Subtype.ext
        apply Prod.ext
        · exact pullbackInstanceCode_point_fst first second
        · exact pullbackInstanceCode_point_snd first second }
  inv :=
    { doctrineHom := (doctrinePullbackFiniteCodeIso first second).inv
      source_eq := by
        change (compatibleSourceEquiv first second).symm
            (pointedPullbackSource (typedPresentationToSemantic first)
              (typedPresentationToSemantic second)) =
          (pullbackInstanceCode first second).point
        apply (compatibleSourceEquiv first second).injective
        rw [(compatibleSourceEquiv first second).apply_symm_apply]
        apply Subtype.ext
        apply Prod.ext
        · exact (pullbackInstanceCode_point_fst first second).symm
        · exact (pullbackInstanceCode_point_snd first second).symm }
  hom_inv_id := by
    apply ExtInstHom.ext
    exact (doctrinePullbackFiniteCodeIso first second).hom_inv_id
  inv_hom_id := by
    apply ExtInstHom.ext
    exact (doctrinePullbackFiniteCodeIso first second).inv_hom_id

/-- The pointed bridge preserves the first generated projection. -/
theorem finiteCodePointedPullbackIso_hom_fst
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    (finiteCodePointedPullbackIso first second).hom ≫
        pointedPullbackFst (typedPresentationToSemantic first)
          (typedPresentationToSemantic second) =
      typedPresentationToSemantic (pullbackFstPresentation first second) := by
  apply ExtInstHom.ext
  exact doctrinePullbackFiniteCodeIso_hom_fst first second

/-- The pointed bridge preserves the second generated projection. -/
theorem finiteCodePointedPullbackIso_hom_snd
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    (finiteCodePointedPullbackIso first second).hom ≫
        pointedPullbackSnd (typedPresentationToSemantic first)
          (typedPresentationToSemantic second) =
      typedPresentationToSemantic (pullbackSndPresentation first second) := by
  apply ExtInstHom.ext
  exact doctrinePullbackFiniteCodeIso_hom_snd first second

/--
The exact decoded square is a pullback by transport of the Cycle 30 producer,
not by accepting an `IsPullback` field from the finite presentation.
-/
theorem finiteCodePointedPullback_isPullback_from_producer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base) :
    IsPullback
      (typedPresentationToSemantic (pullbackFstPresentation first second))
      (typedPresentationToSemantic (pullbackSndPresentation first second))
      (typedPresentationToSemantic first)
      (typedPresentationToSemantic second) := by
  have genericPullback := pointedPullback_isPullback
    (typedPresentationToSemantic first) (typedPresentationToSemantic second)
  refine IsPullback.of_iso'
    (P' := (pullbackInstanceCode first second).toSemantic)
    (X' := left.toSemantic) (Y' := right.toSemantic) (Z' := base.toSemantic)
    (fst' := typedPresentationToSemantic
      (pullbackFstPresentation first second))
    (snd' := typedPresentationToSemantic
      (pullbackSndPresentation first second))
    (f' := typedPresentationToSemantic first)
    (g' := typedPresentationToSemantic second)
    genericPullback (finiteCodePointedPullbackIso first second)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa using finiteCodePointedPullbackIso_hom_fst first second
  · simpa using finiteCodePointedPullbackIso_hom_snd first second
  · simp
  · simp

/-! ## Exact typed square functors -/

/-- The generated first projection `π₁`. -/
def bcLeftPresentation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  pullbackFstPresentation presentation.1.cospan.first
    presentation.1.cospan.second

/-- The generated second projection `π₂`. -/
def bcTopPresentation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  pullbackSndPresentation presentation.1.cospan.first
    presentation.1.cospan.second

/-- The first cospan leg `σ₁`. -/
def bcBottomPresentation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) := presentation.1.cospan.first

/-- The second cospan leg `σ₂`. -/
def bcRightPresentation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) := presentation.1.cospan.second

/-- The decoded four-leg square is the Cycle 30 producer-derived pullback. -/
theorem bcPresentation_isPullback_from_producer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    IsPullback
      (typedPresentationToSemantic (bcLeftPresentation presentation))
      (typedPresentationToSemantic (bcTopPresentation presentation))
      (typedPresentationToSemantic (bcBottomPresentation presentation))
      (typedPresentationToSemantic (bcRightPresentation presentation)) := by
  exact finiteCodePointedPullback_isPullback_from_producer
    presentation.1.cospan.first presentation.1.cospan.second

/-- The decoded semantic arrows commute in the orientation used by the mate. -/
theorem bcPresentation_commutes
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    typedPresentationToSemantic (bcTopPresentation presentation) ≫
        typedPresentationToSemantic (bcRightPresentation presentation) =
      typedPresentationToSemantic (bcLeftPresentation presentation) ≫
        typedPresentationToSemantic (bcBottomPresentation presentation) := by
  exact (pullbackPresentation_commutes presentation.1.cospan.first
    presentation.1.cospan.second).symm

/-- Typed presentation composition decodes to semantic composition. -/
theorem typedPresentationToSemantic_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    typedPresentationToSemantic (compPresentation first second) =
      typedPresentationToSemantic first ≫ typedPresentationToSemantic second := by
  simpa only [typedRealizableHom_hom] using
    typedRealizableHom_comp_hom first second

/-- The G-109 compositor with the typed composite presentation exposed. -/
noncomputable def typedCoreFiberTransportCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    coreFiberTransportFunctor
        (typedPresentationToSemantic (compPresentation first second)) ≅
      coreFiberTransportFunctor (typedPresentationToSemantic first) ⋙
        coreFiberTransportFunctor (typedPresentationToSemantic second) :=
  eqToIso (congrArg coreFiberTransportFunctor
      (typedPresentationToSemantic_comp first second)) ≪≫
    coreFiberCompositor (typedPresentationToSemantic first)
      (typedPresentationToSemantic second)

/-- The top/right composite presentation. -/
def bcTopRightPresentation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  compPresentation (bcTopPresentation presentation)
    (bcRightPresentation presentation)

/-- The left/bottom composite presentation. -/
def bcLeftBottomPresentation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  compPresentation (bcLeftPresentation presentation)
    (bcBottomPresentation presentation)

/-- The two generated composite presentations decode to the same base arrow. -/
theorem bcCompositePresentations_semantic_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    typedPresentationToSemantic (bcTopRightPresentation presentation) =
      typedPresentationToSemantic (bcLeftBottomPresentation presentation) := by
  rw [show typedPresentationToSemantic (bcTopRightPresentation presentation) =
      typedPresentationToSemantic (bcTopPresentation presentation) ≫
        typedPresentationToSemantic (bcRightPresentation presentation) by
    exact typedPresentationToSemantic_comp _ _]
  rw [show typedPresentationToSemantic (bcLeftBottomPresentation presentation) =
      typedPresentationToSemantic (bcLeftPresentation presentation) ≫
        typedPresentationToSemantic (bcBottomPresentation presentation) by
    exact typedPresentationToSemantic_comp _ _]
  exact bcPresentation_commutes presentation

/--
The covariant square comparison generated from the two G-109 compositors and
the decoded square equality.
-/
noncomputable def bcCoreTransportSquareIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic (bcRightPresentation presentation)) ≅
      coreFiberTransportFunctor
          (typedPresentationToSemantic (bcLeftPresentation presentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)) :=
  (typedCoreFiberTransportCompositor
      (bcTopPresentation presentation)
      (bcRightPresentation presentation)).symm ≪≫
    typedCoreFiberTransportPresentationComparison
      (bcTopRightPresentation presentation)
      (bcLeftBottomPresentation presentation)
      (bcCompositePresentations_semantic_eq presentation) ≪≫
    typedCoreFiberTransportCompositor
      (bcLeftPresentation presentation)
      (bcBottomPresentation presentation)

/-! ## The canonical mate -/

/-- Cycle 35 adjunction on the first projection. -/
noncomputable def bcLeftAdjunction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  coreTransportReindexAdjunction
    (typedRealizableHom (bcLeftPresentation presentation))

/-- Cycle 35 adjunction on the second cospan leg. -/
noncomputable def bcRightAdjunction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  coreTransportReindexAdjunction
    (typedRealizableHom (bcRightPresentation presentation))

/--
The canonical Beck--Chevalley mate in the fixed orientation
`(π₂)_! (π₁)^* ⟶ (σ₂)^* (σ₁)_!`.
-/
noncomputable def coreBeckChevalleyMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcLeftPresentation presentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)) ⟶
      coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)) ⋙
        selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation)) :=
  (mateEquiv (bcLeftAdjunction presentation)
    (bcRightAdjunction presentation)
    (bcCoreTransportSquareIso presentation).hom).natTrans

/--
The mate component is the generated right-leg unit, the transported covariant
square comparison, and the generated left-projection counit.
-/
theorem coreBeckChevalleyMate_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (sourcePackage : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    (coreBeckChevalleyMate presentation).app sourcePackage =
      (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
              (typedPresentationToSemantic (bcTopPresentation presentation))).obj
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom (bcLeftPresentation presentation))).obj
                sourcePackage)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
            ((bcCoreTransportSquareIso presentation).hom.app
              ((selectedCoreFiberReindexFunctor
                (typedRealizableHom (bcLeftPresentation presentation))).obj
                  sourcePackage)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              ((bcLeftAdjunction presentation).counit.app sourcePackage)) := by
  simp [coreBeckChevalleyMate, mateEquiv_apply]

/-- Naturality of the generated mate on every vertical source-fiber map. -/
theorem coreBeckChevalleyMate_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage targetPackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcLeftPresentation presentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).map hom ≫
        (coreBeckChevalleyMate presentation).app targetPackage =
      (coreBeckChevalleyMate presentation).app sourcePackage ≫
        (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation)) ⋙
            selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcRightPresentation presentation))).map hom :=
  (coreBeckChevalleyMate presentation).naturality hom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
