import ResearchLean.AG.LocalSemanticReconstruction.G124ComparisonObservationTransport
import ResearchLean.AG.LocalSemanticReconstruction.G124KaroubiProjection
import ResearchLean.AG.LocalSemanticReconstruction.G124PrimitiveKernel
import Formal.Util.AssertStandardAxioms

/-! Design IV-4/C: all comparison pairs, restrictions and Arrow squares use
the same main primitive reader; the fixed G-122 section retains its bottom
and coefficient evaluations in the resulting local comparison group. -/
namespace AAT.AG.LocalSemanticReconstruction.G124MainTheorem
open CategoryTheory CategoryTheory.Idempotents
open RealizationReconstruction IndependentAATPrimitiveReconstruction
universe u v

/-- The full comparison group of every arrow, including noninvertible ones,
is transported bijectively. The exact bottom-fixed subgroup is preserved and
reflected by that same group map. -/
theorem comparison_full_and_bottom
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    Function.Bijective (G124ComparisonTransport.comparisonMulEquiv parameter c) ∧
    (∀ pair : GeneratedArrowComparisonSubgroup c,
      pair ∈ G124ProjectionGroupSquare.nativeBottomFixedComparison parameter c ↔
      G124ComparisonTransport.comparisonMulEquiv parameter c pair ∈
        G124ProjectionGroupSquare.localBottomFixedComparison parameter
          ((reading parameter).map c)) := by
  exact ⟨(G124ComparisonTransport.comparisonMulEquiv parameter c).bijective,
    G124ProjectionGroupSquare.bottom_comparison_mem_iff parameter c⟩

/-- Arbitrary qualified endpoint subgroups transport through all three
primitive projections via the one full comparison-group equivalence. -/
theorem comparison_all_qualifications
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (bottomSource : Subgroup (Aut ((G124ProjectionGlobal.nativeBottom parameter).obj X)))
    (bottomTarget : Subgroup (Aut ((G124ProjectionGlobal.nativeBottom parameter).obj Y)))
    (observationSource : Subgroup
      (Aut ((G124ProjectionGlobal.nativeObservation parameter).obj X)))
    (observationTarget : Subgroup
      (Aut ((G124ProjectionGlobal.nativeObservation parameter).obj Y)))
    (coefficientSource : Subgroup
      (Aut ((G124ProjectionGlobal.nativeCoefficient parameter).obj X)))
    (coefficientTarget : Subgroup
      (Aut ((G124ProjectionGlobal.nativeCoefficient parameter).obj Y))) :
    (G124ProjectionGroupSquare.nativeQualifiedComparison
      (G124ProjectionGlobal.nativeBottom parameter) c bottomSource bottomTarget).map
        (G124ComparisonTransport.comparisonMulEquiv parameter c).toMonoidHom =
      G124ProjectionGroupSquare.localQualifiedComparison
        (reading parameter) (G124ProjectionGlobal.localBottom parameter)
        (G124ProjectionGlobal.nativeBottom parameter)
        (G124ProjectionGlobal.bottomReadingIso parameter) c
        bottomSource bottomTarget ∧
    (G124ProjectionGroupSquare.nativeQualifiedComparison
      (G124ProjectionGlobal.nativeObservation parameter) c
      observationSource observationTarget).map
        (G124ComparisonTransport.comparisonMulEquiv parameter c).toMonoidHom =
      G124ProjectionGroupSquare.localQualifiedComparison
        (reading parameter) (G124ProjectionGlobal.localObservation parameter)
        (G124ProjectionGlobal.nativeObservation parameter)
        (G124ProjectionGlobal.observationReadingIso parameter) c
        observationSource observationTarget ∧
    (G124ProjectionGroupSquare.nativeQualifiedComparison
      (G124ProjectionGlobal.nativeCoefficient parameter) c
      coefficientSource coefficientTarget).map
        (G124ComparisonTransport.comparisonMulEquiv parameter c).toMonoidHom =
      G124ProjectionGroupSquare.localQualifiedComparison
        (reading parameter) (G124ProjectionGlobal.localCoefficient parameter)
        (G124ProjectionGlobal.nativeCoefficient parameter)
        (G124ProjectionGlobal.coefficientReadingIso parameter) c
        coefficientSource coefficientTarget := by
  exact ⟨G124ProjectionGroupSquare.bottom_qualified_map_eq parameter c
      bottomSource bottomTarget,
    G124ProjectionGroupSquare.observation_qualified_map_eq parameter c
      observationSource observationTarget,
    G124ProjectionGroupSquare.coefficient_qualified_map_eq parameter c
      coefficientSource coefficientTarget⟩

/-- Every square between arbitrary normalized Arrow objects is read
componentwise by the same N; this is the Arrow-category morphism, not only
an Arrow object's internal hom. -/
theorem arbitrary_karoubi_arrow_square
    (parameter : Parameter.{u, v})
    {P Q : Karoubi (Arrow (NativeCategory parameter))} (square : P ⟶ Q) :
    ((G124KaroubiProjection.karoubiArrowReading parameter).map square).f.left =
      (reading parameter).map square.f.left ∧
    ((G124KaroubiProjection.karoubiArrowReading parameter).map square).f.right =
      (reading parameter).map square.f.right := by
  exact ⟨rfl, rfl⟩

/-- The same unrestricted comparison group carries the G-120 observation
classification through its actual bottom-fixed source restriction: kernels
and every lift fiber are transported, for an arbitrary comparison c. -/
theorem comparison_g120_kernel_and_fibers
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    Function.Bijective
      (G124ComparisonObservationTransport.bottomObservationKernelEquiv
        parameter c) ∧
    (∀ pair : GeneratedArrowComparisonSubgroup c,
      Function.Bijective
        (G124ComparisonObservationTransport.bottomObservationFiberEquiv
          parameter c pair)) ∧
    Function.Bijective
      (G124ComparisonObservationTransport.sourceRestrictionKernelEquiv
        parameter c) ∧
    (∀ a : Aut X,
      Function.Bijective
        (G124ComparisonObservationTransport.sourceRestrictionFiberEquiv
          parameter c a)) := by
  exact ⟨(G124ComparisonObservationTransport.bottomObservationKernelEquiv
      parameter c).bijective,
    fun pair => (G124ComparisonObservationTransport.bottomObservationFiberEquiv
      parameter c pair).bijective,
    (G124ComparisonObservationTransport.sourceRestrictionKernelEquiv
      parameter c).bijective,
    fun a => (G124ComparisonObservationTransport.sourceRestrictionFiberEquiv
      parameter c a).bijective⟩

/-- In the fixed three-case G-122 classification, the entire canonical
section has the original bottom and coefficient values on both endpoints
after passage through the main reader. -/
theorem fixed_g122_section_bottom_and_coefficient
    (normalized : FiniteAxisFoldComparisonRestrictionKernel.NormalizedComparison)
    (q : IndependentCarrierGraph.Query) :
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        (G124PrimitiveKernel.fixedG122LocalSectionHom
          (G124PrimitiveKernel.fixedG122NormalizedComparisonEquiv normalized)).1.1.hom.hom.val
        (.source q) =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        normalized.1.1.hom.f.hom (.source q) ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        (G124PrimitiveKernel.fixedG122LocalSectionHom
          (G124PrimitiveKernel.fixedG122NormalizedComparisonEquiv normalized)).1.1.hom.hom.val
        (.coefficient q) =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        normalized.1.1.hom.f.hom (.coefficient q) ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        (G124PrimitiveKernel.fixedG122LocalSectionHom
          (G124PrimitiveKernel.fixedG122NormalizedComparisonEquiv normalized)).1.2.hom.hom.val
        (.source q) =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        normalized.1.2.hom.f.hom (.source q) ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        (G124PrimitiveKernel.fixedG122LocalSectionHom
          (G124PrimitiveKernel.fixedG122NormalizedComparisonEquiv normalized)).1.2.hom.hom.val
        (.coefficient q) =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        normalized.1.2.hom.f.hom (.coefficient q) := by
  exact ⟨G124PrimitiveKernel.fixedG122LocalSection_sourcePoint normalized q,
    G124PrimitiveKernel.fixedG122LocalSection_sourceCoefficientPoint normalized q,
    G124PrimitiveKernel.fixedG122LocalSection_targetSourcePoint normalized q,
    G124PrimitiveKernel.fixedG122LocalSection_targetCoefficientPoint normalized q⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end AAT.AG.LocalSemanticReconstruction.G124MainTheorem
