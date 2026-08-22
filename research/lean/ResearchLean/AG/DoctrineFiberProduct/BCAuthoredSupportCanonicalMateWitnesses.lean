import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactnessWitnesses

/-!
# Finite firing of the canonical mate on authored support

The existing finite authored-support fixture contains a genuine diagnostic
2-cell.  Restricting the exact canonical mate to that nonempty discrete support
therefore produces an invertible component rather than an empty-family result.

The symmetric Cycle 39 pullback remains the separate nondegeneracy control for
four noninvertible square legs.  This file does not claim that the identity
authored-support fixture itself has those legs.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence

local instance finiteAuthoredCanonicalAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The generated direct route on the concrete nonempty authored support. -/
noncomputable def finiteAuthoredSupportDirectRoute :
    AuthoredSupportRoute finiteAuthoredBCDatumSquare.context :=
  authoredSupportDirectRoute finiteAuthoredBCDatumSquare.context

/-- The generated via-base route on the same support. -/
noncomputable def finiteAuthoredSupportViaBaseRoute :
    AuthoredSupportRoute finiteAuthoredBCDatumSquare.context :=
  authoredSupportViaBaseRoute finiteAuthoredBCDatumSquare.context

/-- The canonical exact mate restricted to the concrete authored support. -/
noncomputable def finiteAuthoredSupportCanonicalMate :
    finiteAuthoredSupportDirectRoute ⟶
      finiteAuthoredSupportViaBaseRoute :=
  authoredSupportCanonicalMate finiteAuthoredBCDatumSquare.context

/-- The unique authored cell reads the exact producer mate component. -/
theorem finiteAuthoredSupportCanonicalMate_component_heq :
    HEq
      (finiteAuthoredSupportCanonicalMate.app
        (Discrete.mk FiniteBCDiagnosticCell.cell))
      ((coreBeckChevalleyMate
          finiteAuthoredBCDatumSquare.context.square.presentation).app
        (authoredSupportDecodedObject finiteAuthoredBCDatumSquare.context
          (Discrete.mk FiniteBCDiagnosticCell.cell))) := by
  exact authoredSupportCanonicalMate_app_heq
    finiteAuthoredBCDatumSquare.context
    (Discrete.mk FiniteBCDiagnosticCell.cell)

/-- The canonical restriction is an isomorphism on the nonempty support. -/
noncomputable instance finiteAuthoredSupportCanonicalMate_isIso :
    IsIso finiteAuthoredSupportCanonicalMate := by
  dsimp [finiteAuthoredSupportCanonicalMate]
  infer_instance

/-- The actual unique authored component is invertible. -/
noncomputable instance finiteAuthoredSupportCanonicalMate_component_isIso :
    IsIso (finiteAuthoredSupportCanonicalMate.app
      (Discrete.mk FiniteBCDiagnosticCell.cell)) := by
  infer_instance

/--
The separate symmetric positive control still has a producer-derived pullback,
four noninvertible legs, and an invertible canonical mate.
-/
theorem finiteAuthoredSupport_separate_four_leg_exactness_control :
    IsPullback
        (typedPresentationToSemantic
          (bcLeftPresentation finiteBCExactnessPresentation))
        (typedPresentationToSemantic
          (bcTopPresentation finiteBCExactnessPresentation))
        (typedPresentationToSemantic
          (bcBottomPresentation finiteBCExactnessPresentation))
        (typedPresentationToSemantic
          (bcRightPresentation finiteBCExactnessPresentation)) ∧
      (¬ IsIso (typedPresentationToSemantic
        (bcBottomPresentation finiteBCExactnessPresentation))) ∧
      (¬ IsIso (typedPresentationToSemantic
        (bcRightPresentation finiteBCExactnessPresentation))) ∧
      (¬ IsIso (typedPresentationToSemantic
        (bcLeftPresentation finiteBCExactnessPresentation))) ∧
      (¬ IsIso (typedPresentationToSemantic
        (bcTopPresentation finiteBCExactnessPresentation))) ∧
      IsIso (coreBeckChevalleyMate finiteBCExactnessPresentation) := by
  exact ⟨finiteBCExactness_isPullback,
    finiteBCExactness_bottom_not_isIso,
    finiteBCExactness_right_not_isIso,
    finiteBCExactness_left_not_isIso,
    finiteBCExactness_top_not_isIso,
    finiteBCExactnessMate_isIso⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
