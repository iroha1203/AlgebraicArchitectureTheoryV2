import ResearchLean.AG.RealizationReconstruction.GeneralRelativeLensAAT
import ResearchLean.AG.RealizationReconstruction.CSAATFullyFaithfulComparisonTransport
import Formal.Util.AssertStandardAxioms

/-!
The comparison group of a relative lens arrow is transported to the actual
AAT typed construction, using its proved full and faithful readback.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace GeneralLens

/-- Theorem 4.41 applied to the view-changing lens category and the AAT typed
construction of 1.39, with independently selected reference views. -/
noncomputable def aatComparisonMulEquiv
    {X Y : Pointed.{u}} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup (aatTypedFunctor.map c) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    aatTypedFunctor aatTypedFunctorFullyFaithful c

/-- The comparison isomorphism respects the source automorphism projection. -/
theorem aatComparison_source_compatibility
    {X Y : Pointed.{u}} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    generatedArrowComparisonSourceHom (aatTypedFunctor.map c)
        (aatComparisonMulEquiv c pair) =
      fullyFaithfulEndpointAutMulEquiv
        aatTypedFunctor aatTypedFunctorFullyFaithful X
        (generatedArrowComparisonSourceHom c pair) :=
  generatedArrowComparison_source_compatibility
    aatTypedFunctor aatTypedFunctorFullyFaithful c pair

end GeneralLens

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
