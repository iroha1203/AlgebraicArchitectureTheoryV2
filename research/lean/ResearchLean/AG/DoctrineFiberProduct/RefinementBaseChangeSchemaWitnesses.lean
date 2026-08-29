import ResearchLean.AG.AtomFoundation.RefinementObstruction
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChangeSchema

/-!
# Structural controls for the refinement base-change schema

This module supplies the F0 positive and negative controls for the unique
closed condition.  The positive control is an identity refinement.  The
negative control is the reviewed finite G-101 refinement placed over an
identity cospan, so its known failure of extraction reflection occurs in the
compatible locus.  These controls construct no reverse transport, regime, or
branch; those remain K2 obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## K0 strictness of the exact-to-refinement comparison -/

/-- The finite strict refinement is not in the image of the comparison functor. -/
theorem finiteExtractionRefinement_not_in_comparison_image :
    ¬ ∃ exact : ExactDoctrineHom FiniteModel.extractionDoctrine
        refinementTargetDoctrine,
      (doctrineToRefinement FiniteModel.carrier).map exact =
        finiteExtractionRefinement := by
  rintro ⟨exact, heq⟩
  have hsourceMap := congrArg RefinementDoctrineHom.sourceMap heq
  have hatomMap := congrArg RefinementDoctrineHom.atomMap heq
  have obstruction := finiteExtractionRefinement_not_reflecting
  have htarget : refinementTargetDoctrine.extracts
      (exact.sourceMap FiniteModel.ExtractionSource.withoutComponentC)
      (exact.atomEquiv FiniteModel.FiniteAtom.componentC) := by
    simpa [doctrineToRefinement, exactToRefinement] using obstruction.1
  have hsource := (exact.extraction_iff
    FiniteModel.ExtractionSource.withoutComponentC
    FiniteModel.FiniteAtom.componentC).mpr htarget
  exact obstruction.2 hsource

/-! ## Identity positive control -/

/-- Identity-cospan raw data used by the positive evaluator control. -/
noncomputable def finiteRefinementIdentityData :
    RefinementBCIdentityData FiniteModel.carrier where
  DOne := refinementTargetPoint
  DTwo := refinementTargetPoint
  Base := refinementTargetPoint
  sigmaOne := 𝟙 refinementTargetPoint
  sigmaTwo := 𝟙 refinementTargetPoint

/-- The unique condition fires on the identity-refinement control. -/
theorem finiteRefinementIdentity_eval :
    evalRefinementBCCondition pulledLocusExtractionReflectingTerm
      finiteRefinementIdentityData.configuration := by
  intro source _locus atom extracted
  exact extracted

/-! ## Strict finite negative control -/

/-- The reviewed strict finite refinement, equipped with its selected sources. -/
noncomputable def finitePointedExtractionRefinement :
    PointedRefinementHom (packagePoint refinementSourcePackage)
      refinementTargetPoint where
  doctrineHom := finiteExtractionRefinement
  source_eq := rfl

/-- The pointed finite refinement is likewise outside the exact comparison image. -/
theorem finitePointedExtractionRefinement_not_strict_image :
    ¬ ∃ exact : packagePoint refinementSourcePackage ⟶ refinementTargetPoint,
      PointedRefinementHom.ofExact exact = finitePointedExtractionRefinement := by
  rintro ⟨exact, heq⟩
  apply finiteExtractionRefinement_not_in_comparison_image
  refine ⟨exact.doctrineHom, ?_⟩
  simpa [PointedRefinementHom.ofExact, finitePointedExtractionRefinement,
    doctrineToRefinement] using congrArg PointedRefinementHom.doctrineHom heq

/-! ## K2 signature-vacuity witness -/

/--
The accepted F0 regime signature is automatically inhabited when its two target
package fibers are empty.  This exposes the exact vacuity mechanism relevant to
the K2 necessity direction; it is evidence for a GOAL defect, not a branch
producer.
-/
theorem regimeAvailable_of_empty_target_fibers
    (C : RefinementBCConfiguration U)
    (baseEmpty : IsEmpty (CoreFiber C.DOne))
    (pullbackEmpty : IsEmpty (CoreFiber C.pullback)) :
    RegimeAvailable C := by
  letI : IsEmpty (CoreFiber C.DOne) := baseEmpty
  letI : IsEmpty (CoreFiber C.pullback) := pullbackEmpty
  exact ⟨{
    baseCleavage := ⟨fun target => isEmptyElim target⟩
    pulledCleavage := ⟨fun target => isEmptyElim target⟩
  }⟩

/--
The strict finite refinement over the identity cospan.  Every refined source is
in the compatible locus because the second endpoint is the target itself.
-/
noncomputable def finiteRefinementConfiguration :
    RefinementBCConfiguration FiniteModel.carrier where
  DOnePrime := packagePoint refinementSourcePackage
  DOne := refinementTargetPoint
  DTwo := refinementTargetPoint
  Base := refinementTargetPoint
  sigmaOne := 𝟙 refinementTargetPoint
  sigmaTwo := 𝟙 refinementTargetPoint
  refinement := finitePointedExtractionRefinement

/-- The G-101 source package inhabits the refined-endpoint package fiber. -/
noncomputable def finiteRefinementSourceFiberPackage :
    CoreFiber finiteRefinementConfiguration.DOnePrime :=
  ⟨refinementSourcePackage, rfl⟩

/-- The G-101 target package inhabits the original-endpoint package fiber. -/
noncomputable def finiteRefinementTargetFiberPackage :
    CoreFiber finiteRefinementConfiguration.DOne :=
  ⟨refinementTargetPackage, refinementTargetPackage_point⟩

/-- The selected nonreflection source belongs to the compatible pulled locus. -/
theorem finiteRefinementConfiguration_source_in_locus :
    InPulledLocus finiteRefinementConfiguration
      FiniteModel.ExtractionSource.withoutComponentC := by
  refine ⟨FiniteModel.ExtractionSource.withoutComponentC, ?_⟩
  rfl

/-- The closed condition rejects the strict finite configuration. -/
theorem finiteRefinementConfiguration_not_eval :
    ¬ evalRefinementBCCondition pulledLocusExtractionReflectingTerm
      finiteRefinementConfiguration := by
  intro reflects
  have obstruction := finiteExtractionRefinement_not_reflecting
  exact obstruction.2 <| reflects
    FiniteModel.ExtractionSource.withoutComponentC
    finiteRefinementConfiguration_source_in_locus
    FiniteModel.FiniteAtom.componentC obstruction.1

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
