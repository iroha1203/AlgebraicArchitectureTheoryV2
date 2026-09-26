import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionBottomNormalization
import ResearchLean.AG.RealizationReconstruction.CSAATFullyFaithfulComparisonTransport
import Formal.Util.AssertStandardAxioms

/-! The full comparison group of an arbitrary arrow under the one G-124 reader. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ComparisonTransport

open CategoryTheory IndependentAATPrimitiveReconstruction RealizationReconstruction

universe u v

/-- Every comparison-preserving endpoint pair, including the pairs of a
noninvertible arrow, is transported by the accepted common equivalence. -/
noncomputable def comparisonMulEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup ((reading parameter).map c) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor c

/-- Both endpoints of the whole comparison pair are read by the main functor. -/
@[simp] theorem comparisonMulEquiv_source_hom (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (comparisonMulEquiv parameter c pair).1.1.hom =
      (reading parameter).map pair.1.1.hom := rfl

@[simp] theorem comparisonMulEquiv_target_hom (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (comparisonMulEquiv parameter c pair).1.2.hom =
      (reading parameter).map pair.1.2.hom := rfl

/-- The first endpoint of the transported pair is exactly the primitive
reading of the original endpoint automorphism. -/
theorem source_compatibility (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    generatedArrowComparisonSourceHom ((reading parameter).map c)
        (comparisonMulEquiv parameter c pair) =
      fullyFaithfulEndpointAutMulEquiv
        (reading parameter) (equivalence parameter).fullyFaithfulFunctor X
        (generatedArrowComparisonSourceHom c pair) :=
  generatedArrowComparison_source_compatibility
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor c pair

/-- For an isomorphism comparison, the canonical conjugation section is
preserved; no section is asserted for a general comparison arrow. -/
theorem section_compatibility (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ≅ Y) (a : Aut X) :
    comparisonMulEquiv parameter c.hom (generatedArrowComparisonSectionHom c a) =
      generatedArrowComparisonSectionHom ((reading parameter).mapIso c)
        (fullyFaithfulEndpointAutMulEquiv
          (reading parameter) (equivalence parameter).fullyFaithfulFunctor X a) :=
  generatedArrowComparison_section_compatibility
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor c a

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ComparisonTransport

end AAT.AG.LocalSemanticReconstruction.G124ComparisonTransport
