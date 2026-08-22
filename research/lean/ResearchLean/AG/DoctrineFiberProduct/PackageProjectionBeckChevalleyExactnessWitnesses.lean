import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness
import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.PointedDoctrinePullbackWitnesses

/-!
# Nondegenerate finite firing of package Beck--Chevalley exactness

The positive control is the symmetric three-to-two cospan.  Both cospan legs
and both generated pullback projections are noninvertible, while the pointed
square is generated as an actual pullback.  The package-specific theorem still
makes the canonical mate, and every arbitrary-cleavage mate, invertible.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory CategoryTheory.Limits
open AtomFoundation CrossStageCoherence

local instance finiteBCExactnessAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Symmetric noninvertible cospan used for the exactness firing. -/
def finiteBCExactnessCospan :
    CartCospanPresentation FiniteModel.carrier where
  firstSource := finiteThreeSourceInstance
  secondSource := finiteThreeSourceInstance
  base := finiteTwoSourceInstance
  first := finiteThreeToTwoPresentation
  second := finiteThreeToTwoPresentation

/-- Validated finite presentation generated from the symmetric cospan. -/
def finiteBCExactnessPresentation : BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finiteBCExactnessCospan
    finiteBCDiagnosticPresentation

/-- The exact decoded finite square is a producer-derived pointed pullback. -/
theorem finiteBCExactness_isPullback :
    IsPullback
      (typedPresentationToSemantic
        (bcLeftPresentation finiteBCExactnessPresentation))
      (typedPresentationToSemantic
        (bcTopPresentation finiteBCExactnessPresentation))
      (typedPresentationToSemantic
        (bcBottomPresentation finiteBCExactnessPresentation))
      (typedPresentationToSemantic
        (bcRightPresentation finiteBCExactnessPresentation)) :=
  bcPresentation_isPullback_from_producer finiteBCExactnessPresentation

/-- The symmetric three-to-two pointed leg is noninvertible. -/
theorem finiteBCExactness_leg_not_isIso :
    ¬ IsIso (typedPresentationToSemantic finiteThreeToTwoPresentation) := by
  intro hIso
  letI : IsIso
      (typedPresentationToSemantic finiteThreeToTwoPresentation) := hIso
  have injective := extInstHom_sourceMap_injective_of_isIso
    (typedPresentationToSemantic finiteThreeToTwoPresentation)
  exact finiteThreeSourceZero_ne_one
    (injective (by
      simpa only [finiteProperPointedLeg_doctrineHom] using
        finiteThreeToTwoDoctrineHom_zero.trans
          finiteThreeToTwoDoctrineHom_one.symm))

/-- The bottom cospan leg is noninvertible. -/
theorem finiteBCExactness_bottom_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcBottomPresentation finiteBCExactnessPresentation)) := by
  simpa [finiteBCExactnessPresentation, finiteBCExactnessCospan,
    bcBottomPresentation, bcPresentationOfCospan] using
    finiteBCExactness_leg_not_isIso

/-- The right cospan leg is noninvertible. -/
theorem finiteBCExactness_right_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcRightPresentation finiteBCExactnessPresentation)) := by
  simpa [finiteBCExactnessPresentation, finiteBCExactnessCospan,
    bcRightPresentation, bcPresentationOfCospan] using
    finiteBCExactness_leg_not_isIso

/-- The generated left pullback projection is noninvertible. -/
theorem finiteBCExactness_left_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteBCExactnessPresentation)) := by
  intro hIso
  letI : IsIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteBCExactnessPresentation)) := hIso
  let bridge := finiteCodePointedPullbackIso
    finiteThreeToTwoPresentation finiteThreeToTwoPresentation
  let genericProjection := pointedPullbackFst
    finiteProperPointedLeg finiteProperPointedLeg
  letI : IsIso bridge.hom := by infer_instance
  have composed_eq : bridge.hom ≫ genericProjection =
      typedPresentationToSemantic
        (pullbackFstPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation) := by
    simpa [bridge, genericProjection] using
      finiteCodePointedPullbackIso_hom_fst
        finiteThreeToTwoPresentation finiteThreeToTwoPresentation
  have composed : IsIso (bridge.hom ≫ genericProjection) := by
    rw [composed_eq]
    change IsIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteBCExactnessPresentation))
    infer_instance
  letI : IsIso (bridge.hom ≫ genericProjection) := composed
  have genericIso : IsIso genericProjection :=
    IsIso.of_isIso_comp_left bridge.hom genericProjection
  exact finiteProperPointedPullback_fst_not_isIso genericIso

/-- The generated top pullback projection is noninvertible. -/
theorem finiteBCExactness_top_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcTopPresentation finiteBCExactnessPresentation)) := by
  intro hIso
  letI : IsIso
      (typedPresentationToSemantic
        (bcTopPresentation finiteBCExactnessPresentation)) := hIso
  let bridge := finiteCodePointedPullbackIso
    finiteThreeToTwoPresentation finiteThreeToTwoPresentation
  let genericProjection := pointedPullbackSnd
    finiteProperPointedLeg finiteProperPointedLeg
  letI : IsIso bridge.hom := by infer_instance
  have composed_eq : bridge.hom ≫ genericProjection =
      typedPresentationToSemantic
        (pullbackSndPresentation finiteThreeToTwoPresentation
          finiteThreeToTwoPresentation) := by
    simpa [bridge, genericProjection] using
      finiteCodePointedPullbackIso_hom_snd
        finiteThreeToTwoPresentation finiteThreeToTwoPresentation
  have composed : IsIso (bridge.hom ≫ genericProjection) := by
    rw [composed_eq]
    change IsIso
      (typedPresentationToSemantic
        (bcTopPresentation finiteBCExactnessPresentation))
    infer_instance
  letI : IsIso (bridge.hom ≫ genericProjection) := composed
  have genericIso : IsIso genericProjection :=
    IsIso.of_isIso_comp_left bridge.hom genericProjection
  exact finiteProperPointedPullback_snd_not_isIso genericIso

/-- The canonical mate is invertible on the four-noninvertible-leg pullback. -/
theorem finiteBCExactnessMate_isIso :
    IsIso (coreBeckChevalleyMate finiteBCExactnessPresentation) :=
  coreBeckChevalleyMate_isIso finiteBCExactnessPresentation

/-- Every arbitrary-cleavage mate remains invertible on the same control. -/
theorem finiteBCExactnessCleavageMate_isIso
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput finiteBCExactnessPresentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput finiteBCExactnessPresentation).semantic) :
    IsIso (coreBeckChevalleyCleavageMate finiteBCExactnessPresentation
      leftCleavage rightCleavage) :=
  coreBeckChevalleyCleavageMate_isIso finiteBCExactnessPresentation
    leftCleavage rightCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
