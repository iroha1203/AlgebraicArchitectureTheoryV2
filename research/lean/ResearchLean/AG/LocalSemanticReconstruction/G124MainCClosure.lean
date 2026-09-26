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
open ComparisonInformationLoss G124ProjectionGlobal G124ProjectionGroupSquare
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

/-- The G-120 qualified source restriction itself commutes with main N.
Its short exact criterion and the kernel action on every fiber transport
without asserting surjectivity for an arbitrary comparison. -/
theorem comparison_g120_restriction_classification
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    (∀ pair : nativeBottomFixedComparison parameter c,
      G124ComparisonObservationTransport.localBottomSourceRestriction parameter
          ((reading parameter).map c)
          (G124ComparisonObservationTransport.bottomFixedComparisonEquiv parameter c pair) =
        G124ComparisonObservationTransport.bottomFixedEndpointEquiv parameter X
          (G124ComparisonObservationTransport.nativeBottomSourceRestriction parameter c pair)) ∧
    (IsGroupShortExact
        (restrictedKernelInclusion (generatedArrowComparisonSourceHom c)
          (nativeBottomFixedComparison parameter c)
          (nativeBottomFixed parameter X)
          (G124ComparisonObservationTransport.nativeBottomSource_preserves parameter c))
        (G124ComparisonObservationTransport.nativeBottomSourceRestriction parameter c) ↔
      IsGroupShortExact
        (restrictedKernelInclusion
          (generatedArrowComparisonSourceHom ((reading parameter).map c))
          (localBottomFixedComparison parameter ((reading parameter).map c))
          (localBottomFixed parameter ((reading parameter).obj X))
          (G124ComparisonObservationTransport.localBottomSource_preserves parameter
            ((reading parameter).map c)))
        (G124ComparisonObservationTransport.localBottomSourceRestriction parameter
          ((reading parameter).map c))) ∧
    (∀ (a : nativeBottomFixed parameter X)
      (kernelElement : ((G124ComparisonObservationTransport.nativeBottomSourceRestriction
        parameter c).ker)ᵐᵒᵖ)
      (point : RestrictionKernelFiberTransport.Fiber
        (G124ComparisonObservationTransport.nativeBottomSourceRestriction parameter c) a),
      G124ComparisonObservationTransport.bottomRestrictedFiberEquiv parameter c a
          (RestrictionKernelFiberTransport.rightKernelAction
            (G124ComparisonObservationTransport.nativeBottomSourceRestriction parameter c)
            a kernelElement point) =
        RestrictionKernelFiberTransport.rightKernelAction
          (G124ComparisonObservationTransport.localBottomSourceRestriction parameter
            ((reading parameter).map c))
          (G124ComparisonObservationTransport.bottomFixedEndpointEquiv parameter X a)
          (MulOpposite.op
            (G124ComparisonObservationTransport.bottomRestrictedKernelEquiv parameter c
              (MulOpposite.unop kernelElement)))
          (G124ComparisonObservationTransport.bottomRestrictedFiberEquiv parameter c a point)) := by
  exact ⟨G124ComparisonObservationTransport.bottomSourceRestriction_square parameter c,
    G124ComparisonObservationTransport.bottomRestricted_shortExact_iff parameter c,
    G124ComparisonObservationTransport.bottomRestrictedFiberEquiv_smul parameter c⟩

/-- Every qualified source element has a native lift exactly when its
transported main-local element has a lift. -/
theorem comparison_g120_lift_exists_iff
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (a : nativeBottomFixed parameter X) :
    Nonempty (RestrictionKernelFiberTransport.Fiber
      (G124ComparisonObservationTransport.nativeBottomSourceRestriction parameter c) a) ↔
    Nonempty (RestrictionKernelFiberTransport.Fiber
      (G124ComparisonObservationTransport.localBottomSourceRestriction parameter
        ((reading parameter).map c))
      (G124ComparisonObservationTransport.bottomFixedEndpointEquiv parameter X a)) :=
  Equiv.nonempty_congr
    (G124ComparisonObservationTransport.bottomRestrictedFiberEquiv parameter c a)

/-- G-120's exact reflection classification is transported by the whole
comparison equivalence and the endpoint square of the same main N. Each
side retains its kernel-and-image criterion; reflection is not postulated
for an arbitrary comparison. -/
theorem comparison_g120_reflection_transport
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    ((nativeBottomFixed parameter X).comap
        (generatedArrowComparisonSourceHom c) =
      nativeBottomFixedComparison parameter c ↔
      (localBottomFixed parameter ((reading parameter).obj X)).comap
        (generatedArrowComparisonSourceHom ((reading parameter).map c)) =
      localBottomFixedComparison parameter ((reading parameter).map c)) ∧
    ((nativeBottomFixed parameter X).comap
        (generatedArrowComparisonSourceHom c) =
      nativeBottomFixedComparison parameter c ↔
      (generatedArrowComparisonSourceHom c).ker ≤
        nativeBottomFixedComparison parameter c ∧
      (nativeBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) =
        nativeBottomFixed parameter X ⊓
          (generatedArrowComparisonSourceHom c).range) ∧
    ((localBottomFixed parameter ((reading parameter).obj X)).comap
        (generatedArrowComparisonSourceHom ((reading parameter).map c)) =
      localBottomFixedComparison parameter ((reading parameter).map c) ↔
      (generatedArrowComparisonSourceHom ((reading parameter).map c)).ker ≤
        localBottomFixedComparison parameter ((reading parameter).map c) ∧
      (localBottomFixedComparison parameter ((reading parameter).map c)).map
          (generatedArrowComparisonSourceHom ((reading parameter).map c)) =
        localBottomFixed parameter ((reading parameter).obj X) ⊓
          (generatedArrowComparisonSourceHom ((reading parameter).map c)).range) := by
  let E := G124ComparisonTransport.comparisonMulEquiv parameter c
  have hSource (pair : GeneratedArrowComparisonSubgroup c) :
      pair ∈ (nativeBottomFixed parameter X).comap
          (generatedArrowComparisonSourceHom c) ↔
        E pair ∈ (localBottomFixed parameter ((reading parameter).obj X)).comap
          (generatedArrowComparisonSourceHom ((reading parameter).map c)) := by
    change generatedArrowComparisonSourceHom c pair ∈ nativeBottomFixed parameter X ↔
      generatedArrowComparisonSourceHom ((reading parameter).map c) (E pair) ∈
        localBottomFixed parameter ((reading parameter).obj X)
    rw [G124ComparisonTransport.source_compatibility]
    exact bottom_fixed_iff parameter X _
  have hBottom (pair : GeneratedArrowComparisonSubgroup c) :
      pair ∈ nativeBottomFixedComparison parameter c ↔
        E pair ∈ localBottomFixedComparison parameter ((reading parameter).map c) :=
    bottom_comparison_mem_iff parameter c pair
  refine ⟨?_,
    G124ComparisonObservationTransport.nativeBottomSource_reflection_iff parameter c,
    G124ComparisonObservationTransport.localBottomSource_reflection_iff parameter
      ((reading parameter).map c)⟩
  constructor
  · intro hn
    apply Subgroup.ext
    intro localPair
    obtain ⟨pair, rfl⟩ := E.surjective localPair
    constructor
    · intro hp
      exact (hBottom pair).mp (by simpa only [hn] using (hSource pair).mpr hp)
    · intro hp
      exact (hSource pair).mp (by simpa only [hn] using (hBottom pair).mpr hp)
  · intro hl
    apply Subgroup.ext
    intro pair
    constructor
    · intro hp
      exact (hBottom pair).mpr (by simpa only [hl] using (hSource pair).mp hp)
    · intro hp
      exact (hSource pair).mpr (by simpa only [hl] using (hBottom pair).mp hp)

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

/-- In the fixed G-122 three-case input, the same local normalization has a
genuine right-inverse section on every normalized group element. The entire
restricted kernel and each lift fiber, rather than a selected witness, are
recovered alongside the generated and constant-one readings. -/
theorem fixed_g122_three_case_section_classification :
    (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldIdentityCochainBarBetaNativeHom =
      (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldBarAlphaNativeHom ∧
    (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldBarBetaNativeHom ≠
      (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldBarAlphaNativeHom ∧
    ¬ IsIso ((reading finiteAxisFoldGeometryParameter).map
      finiteAxisFoldBarBetaNativeHom) ∧
    (∀ normalized : GeneratedArrowComparisonSubgroup
      ((G124PrimitiveNormalization.localNormalizationFunctor
        G124PrimitiveKernel.fixedG122Carrier).map
          G124PrimitiveKernel.fixedG122LocalArrow),
      G124PrimitiveKernel.localComparisonNormalization
          G124PrimitiveKernel.fixedG122LocalArrow
          (G124PrimitiveKernel.fixedG122LocalSectionHom normalized) = normalized) ∧
    IsGroupShortExact
      (G124PrimitiveKernel.localComparisonNormalization
        G124PrimitiveKernel.fixedG122LocalArrow).ker.subtype
      (G124PrimitiveKernel.localComparisonNormalization
        G124PrimitiveKernel.fixedG122LocalArrow) ∧
    Function.Bijective G124PrimitiveKernel.fixedG122RestrictedKernelMulEquiv ∧
    Function.Bijective G124PrimitiveKernel.fixedG122PrimitiveKernelMulEquiv ∧
    (∀ (normalized : GeneratedArrowComparisonSubgroup
      ((G124PrimitiveNormalization.localNormalizationFunctor
        G124PrimitiveKernel.fixedG122Carrier).map
          G124PrimitiveKernel.fixedG122LocalArrow))
      (first second : RestrictionKernelFiberTransport.Fiber
        (G124PrimitiveKernel.localComparisonNormalization
          G124PrimitiveKernel.fixedG122LocalArrow) normalized),
      ∃! kernel : ((G124PrimitiveKernel.localComparisonNormalization
        G124PrimitiveKernel.fixedG122LocalArrow).ker)ᵐᵒᵖ,
        RestrictionKernelFiberTransport.rightKernelAction
          (G124PrimitiveKernel.localComparisonNormalization
            G124PrimitiveKernel.fixedG122LocalArrow) normalized
          kernel first = second) := by
  exact ⟨G124PrimitiveKernel.fixedG122MainReading_identityBarBeta,
    G124PrimitiveKernel.fixedG122MainReading_generatedBarBeta_ne_barAlpha,
    G124PrimitiveKernel.fixedG122MainReading_generatedBarBeta_not_isIso,
    G124PrimitiveKernel.fixedG122LocalSection_rightInverse,
    G124PrimitiveKernel.fixedG122Local_shortExact,
    G124PrimitiveKernel.fixedG122RestrictedKernelMulEquiv.bijective,
    G124PrimitiveKernel.fixedG122PrimitiveKernelMulEquiv.bijective,
    G124PrimitiveKernel.fixedG122LocalFiber_existsUnique_kernel⟩

/-- The concrete ambient-kernel obstruction used in the fixed three-case
classification has all four bottom/coefficient primitive point evaluations,
while remaining outside the range of the restricted kernel. -/
theorem fixed_g122_ambient_obstruction_points
    (q : IndependentCarrierGraph.Query) :
    G124PrimitiveKernel.fixedG122PrimitiveAmbientElement ∉
      (G124PrimitiveKernel.primitiveRestrictedToAmbient
        G124PrimitiveKernel.fixedG122LocalArrow).range ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        G124PrimitiveKernel.fixedG122PrimitiveAmbientElement.1.forward.hom.val
        (.source q) =
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        ((G124PrimitiveNormalization.representativeAdmissibleReading
          G124PrimitiveKernel.fixedG122Carrier).map
            (𝟙 G124PrimitiveKernel.fixedG122Source)).hom.val (.source q) ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        G124PrimitiveKernel.fixedG122PrimitiveAmbientElement.1.forward.hom.val
        (.coefficient q) =
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        ((G124PrimitiveNormalization.representativeAdmissibleReading
          G124PrimitiveKernel.fixedG122Carrier).map
            (𝟙 G124PrimitiveKernel.fixedG122Source)).hom.val (.coefficient q) ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        G124PrimitiveKernel.fixedG122PrimitiveAmbientElement.2.forward.hom.val
        (.source q) =
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        ((G124PrimitiveNormalization.representativeAdmissibleReading
          G124PrimitiveKernel.fixedG122Carrier).map
            (𝟙 G124PrimitiveKernel.fixedG122Target)).hom.val (.source q) ∧
    IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        G124PrimitiveKernel.fixedG122PrimitiveAmbientElement.2.forward.hom.val
        (.coefficient q) =
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
        ((G124PrimitiveNormalization.representativeAdmissibleReading
          G124PrimitiveKernel.fixedG122Carrier).map
            (𝟙 G124PrimitiveKernel.fixedG122Target)).hom.val (.coefficient q) := by
  exact ⟨G124PrimitiveKernel.fixedG122PrimitiveAmbientElement_not_restricted_range,
    G124PrimitiveKernel.fixedG122PrimitiveAmbient_sourcePoint q,
    G124PrimitiveKernel.fixedG122PrimitiveAmbient_source_coefficientPoint q,
    G124PrimitiveKernel.fixedG122PrimitiveAmbient_target_sourcePoint q,
    G124PrimitiveKernel.fixedG122PrimitiveAmbient_target_coefficientPoint q⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end AAT.AG.LocalSemanticReconstruction.G124MainTheorem
