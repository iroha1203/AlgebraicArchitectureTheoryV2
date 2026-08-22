import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMateCleavageIndependence
import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMateWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCleavageWitnesses

/-!
# Finite witnesses for mate-level cleavage independence

Two controls are kept separate.  The support-identity square carries the
reviewed literal and visibly twisted right cleavages, so the mate comparison
and its naturality fire with a genuine choice difference and a nonidentity
vertical map.  The asymmetric Cycle 37 square separately retains the two
noninvertible reindexing legs and specializes the arbitrary-cleavage theorem to
the selected normalization anchor.  Neither control is presented as combining
both properties in one fixture.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence

local instance finiteMateCleavageAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Identity-square control with a visible cleavage change -/

/-- The generated left projection uses its selected cleavage. -/
noncomputable def finiteIdentityMateLeftCleavage :
    CoreFiberCartesianCleavage
      (bcLeftInput finiteAuthoredSupportBCPresentation).semantic :=
  selectedCoreFiberCartesianCleavage
    (bcLeftInput finiteAuthoredSupportBCPresentation)

/-- Mate generated with the literal right identity cleavage. -/
noncomputable def finiteIdentityLiteralCoreBeckChevalleyMate :=
  coreBeckChevalleyCleavageMate finiteAuthoredSupportBCPresentation
    finiteIdentityMateLeftCleavage finiteCleavageLiteralIdentityChoice

/-- Mate generated with the visibly twisted right identity cleavage. -/
noncomputable def finiteIdentityTwistedCoreBeckChevalleyMate :=
  coreBeckChevalleyCleavageMate finiteAuthoredSupportBCPresentation
    finiteIdentityMateLeftCleavage finiteCleavageTwistedIdentityChoice

/-- The two concrete mates commute with the generated cleavage comparisons. -/
theorem finiteIdentityCoreBeckChevalleyMate_comparison :
    Functor.whiskerRight
          (CoreFiberCartesianCleavage.comparison
            finiteIdentityMateLeftCleavage
            finiteIdentityMateLeftCleavage).hom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation finiteAuthoredSupportBCPresentation))) ≫
        finiteIdentityTwistedCoreBeckChevalleyMate =
      finiteIdentityLiteralCoreBeckChevalleyMate ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation finiteAuthoredSupportBCPresentation)))
          (CoreFiberCartesianCleavage.comparison
            finiteCleavageLiteralIdentityChoice
            finiteCleavageTwistedIdentityChoice).hom :=
  coreBeckChevalleyCleavageMate_comparison
    finiteAuthoredSupportBCPresentation
    finiteIdentityMateLeftCleavage finiteIdentityMateLeftCleavage
    finiteCleavageLiteralIdentityChoice finiteCleavageTwistedIdentityChoice

/-- The right comparison used above visibly moves axis zero to axis one. -/
theorem finiteIdentityMateRightComparison_axis_zero :
    finiteCleavageTwistedAxisReflect
        (((CoreFiberCartesianCleavage.comparison
            finiteCleavageLiteralIdentityChoice
            finiteCleavageTwistedIdentityChoice).hom.app
              finiteCleavageFourAxisTarget).1.upper.axisMap
                finiteReindexAxisZero) = finiteReindexAxisOne :=
  finiteCleavageComparisonApp_axis_zero

/-- The literal mate's naturality fires on the genuine axis-swap map. -/
theorem finiteIdentityLiteralCoreBeckChevalleyMate_axisSwap_naturality :
    (finiteIdentityMateLeftCleavage.reindexFunctor ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation finiteAuthoredSupportBCPresentation))).map
          finiteCleavageAxisSwapHom ≫
        finiteIdentityLiteralCoreBeckChevalleyMate.app
          finiteCleavageFourAxisTarget =
      finiteIdentityLiteralCoreBeckChevalleyMate.app
          finiteCleavageFourAxisTarget ≫
        (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation finiteAuthoredSupportBCPresentation)) ⋙
          finiteCleavageLiteralIdentityChoice.reindexFunctor).map
            finiteCleavageAxisSwapHom :=
  coreBeckChevalleyCleavageMate_naturality
    finiteAuthoredSupportBCPresentation finiteIdentityMateLeftCleavage
    finiteCleavageLiteralIdentityChoice finiteCleavageAxisSwapHom

/-- The vertical map in the identity-square naturality control is nonidentity. -/
theorem finiteIdentityMate_axisSwap_ne_id :
    finiteCleavageAxisSwapHom ≠ 𝟙 finiteCleavageFourAxisTarget :=
  finiteCleavageAxisSwapHom_ne_id

/-! ## Noninvertible-square selected-normalization control -/

/-- Selected cleavage on the generated noninvertible first projection. -/
noncomputable def finiteCanonicalMateSelectedLeftCleavage :
    CoreFiberCartesianCleavage
      (bcLeftInput finiteCanonicalMatePresentation).semantic :=
  selectedCoreFiberCartesianCleavage
    (bcLeftInput finiteCanonicalMatePresentation)

/-- Selected cleavage on the noninvertible second cospan leg. -/
noncomputable def finiteCanonicalMateSelectedRightCleavage :
    CoreFiberCartesianCleavage
      (bcRightInput finiteCanonicalMatePresentation).semantic :=
  selectedCoreFiberCartesianCleavage
    (bcRightInput finiteCanonicalMatePresentation)

/-- The arbitrary-cleavage producer specialized to both selected choices. -/
noncomputable def finiteCanonicalSelectedCleavageMate :=
  coreBeckChevalleyCleavageMate finiteCanonicalMatePresentation
    finiteCanonicalMateSelectedLeftCleavage
    finiteCanonicalMateSelectedRightCleavage

/-- The selected specialization compares canonically with the Cycle 37 mate. -/
theorem finiteCanonicalSelectedCleavageMate_comparison :
    Functor.whiskerRight
          (coreFiberCleavageSelectedComparison
            (bcLeftInput finiteCanonicalMatePresentation)
            finiteCanonicalMateSelectedLeftCleavage).hom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation finiteCanonicalMatePresentation))) ≫
        coreBeckChevalleyMate finiteCanonicalMatePresentation =
      finiteCanonicalSelectedCleavageMate ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation finiteCanonicalMatePresentation)))
          (coreFiberCleavageSelectedComparison
            (bcRightInput finiteCanonicalMatePresentation)
            finiteCanonicalMateSelectedRightCleavage).hom :=
  coreBeckChevalleyCleavageMate_selectedComparison
    finiteCanonicalMatePresentation finiteCanonicalMateSelectedLeftCleavage
    finiteCanonicalMateSelectedRightCleavage

/-- The first reindexing leg in this separate control remains noninvertible. -/
theorem finiteCanonicalSelectedCleavageMate_left_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteCanonicalMatePresentation)) :=
  finiteCanonicalMate_left_not_isIso

/-- The second reindexing leg in this separate control remains noninvertible. -/
theorem finiteCanonicalSelectedCleavageMate_right_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcRightPresentation finiteCanonicalMatePresentation)) :=
  finiteCanonicalMate_right_not_isIso

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
