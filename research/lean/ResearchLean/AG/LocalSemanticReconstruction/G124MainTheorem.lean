import ResearchLean.AG.LocalSemanticReconstruction.G124PrimitiveKernel
import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionGroupSquare
import ResearchLean.AG.LocalSemanticReconstruction.G124KaroubiProjection
import ResearchLean.AG.LocalSemanticReconstruction.CSProtocolAdapterLocal
import ResearchLean.AG.LocalSemanticReconstruction.CSFixedFFiberD
import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteValueQueryBridge
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeMainFlip
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeEdgelessCriterion
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeInverseLimitUniversal
import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingEffectiveness
import ResearchLean.AG.LocalSemanticReconstruction.G124MainCClosure
import ResearchLean.AG.LocalSemanticReconstruction.G124MainE1Closure
import ResearchLean.AG.LocalSemanticReconstruction.G124MainE2Finite
import ResearchLean.AG.LocalSemanticReconstruction.G124MainE2Route
import Formal.Util.AssertStandardAxioms

/-! Design IV-4: one quantified theorem family over the same primitive reader.
The clauses below expose the original inputs and equations of A--E; they do
not take projection squares, kernel equivalences, or point equations as data. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
open CategoryTheory.Idempotents
universe u v

namespace G124MainTheorem

/-- For each original parameter, the same primitive reader has unique Hom
assembly and object realization; every arbitrary comparison is transported
through all three component projections at both endpoints. -/
theorem aatLocalSemanticReconstruction_abc
    (parameter : Parameter.{u, v}) :
    (∀ {X Y : NativeCategory parameter}
      (localMorphism : (reading parameter).obj X ⟶ (reading parameter).obj Y),
      ∃! f : X ⟶ Y, (reading parameter).map f = localMorphism) ∧
    (∀ localObject : LocalCategory parameter,
      ∃ X : NativeCategory parameter,
        Nonempty ((reading parameter).obj X ≅ localObject)) ∧
    (∀ {X Y : NativeCategory parameter} (c : X ⟶ Y)
      (pair : GeneratedArrowComparisonSubgroup c),
      (((G124ProjectionGlobal.bottomReadingIso parameter).app X).conjAut
          ((G124ProjectionGlobal.localBottom parameter).mapIso
            (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.1),
        ((G124ProjectionGlobal.bottomReadingIso parameter).app Y).conjAut
          ((G124ProjectionGlobal.localBottom parameter).mapIso
            (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.2)) =
        ((G124ProjectionGlobal.nativeBottom parameter).mapIso pair.1.1,
          (G124ProjectionGlobal.nativeBottom parameter).mapIso pair.1.2) ∧
      (((G124ProjectionGlobal.observationReadingIso parameter).app X).conjAut
          ((G124ProjectionGlobal.localObservation parameter).mapIso
            (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.1),
        ((G124ProjectionGlobal.observationReadingIso parameter).app Y).conjAut
          ((G124ProjectionGlobal.localObservation parameter).mapIso
            (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.2)) =
        ((G124ProjectionGlobal.nativeObservation parameter).mapIso pair.1.1,
          (G124ProjectionGlobal.nativeObservation parameter).mapIso pair.1.2) ∧
      (((G124ProjectionGlobal.coefficientReadingIso parameter).app X).conjAut
          ((G124ProjectionGlobal.localCoefficient parameter).mapIso
            (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.1),
        ((G124ProjectionGlobal.coefficientReadingIso parameter).app Y).conjAut
          ((G124ProjectionGlobal.localCoefficient parameter).mapIso
            (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.2)) =
        ((G124ProjectionGlobal.nativeCoefficient parameter).mapIso pair.1.1,
          (G124ProjectionGlobal.nativeCoefficient parameter).mapIso pair.1.2)) ∧
    (∀ (P Q : Karoubi (NativeCategory parameter)) (f : P.X ⟶ Q.X),
      P.p ≫ f ≫ Q.p = f ↔
        ((G124KaroubiProjection.karoubiReading parameter).obj P).p ≫
          (reading parameter).map f ≫
          ((G124KaroubiProjection.karoubiReading parameter).obj Q).p =
            (reading parameter).map f) ∧
    (∀ (P Q : Karoubi (NativeCategory parameter)),
      Function.Bijective
        (G124KaroubiProjection.karoubiComparisonHomEquiv parameter P Q)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y localMorphism
    exact existsUnique_preimage parameter localMorphism
  · intro localObject
    exact ⟨(reconstructionData parameter).objectAssembly.assembleObject localObject,
      ⟨(reconstructionData parameter).objectAssembly.readAssembledIso localObject⟩⟩
  · intro X Y c pair
    exact ⟨G124ProjectionGroupSquare.bottom_comparison_pair_square parameter c pair,
      G124ProjectionGroupSquare.observation_comparison_pair_square parameter c pair,
      G124ProjectionGroupSquare.coefficient_comparison_pair_square parameter c pair⟩
  · exact G124KaroubiProjection.karoubi_comparison_iff parameter
  · intro P Q
    exact (G124KaroubiProjection.karoubiComparisonHomEquiv parameter P Q).bijective

/-- The three fixed G-122 comparisons share the one primitive reader: the
constant-one comparison is the five-factor comparison, the defect comparison
is distinct and noninvertible, and the fixed local normalization has its
entire restricted kernel, principal lift fibers and a distinct ambient
kernel element. -/
theorem aatLocalSemanticReconstruction_c_g122 :
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
    AAT.AG.ComparisonInformationLoss.IsGroupShortExact
      (G124PrimitiveKernel.localComparisonNormalization
        G124PrimitiveKernel.fixedG122LocalArrow).ker.subtype
      (G124PrimitiveKernel.localComparisonNormalization
        G124PrimitiveKernel.fixedG122LocalArrow) ∧
    G124PrimitiveKernel.fixedG122PrimitiveAmbientElement ∉
      (G124PrimitiveKernel.primitiveRestrictedToAmbient
        G124PrimitiveKernel.fixedG122LocalArrow).range ∧
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
    G124PrimitiveKernel.fixedG122Local_shortExact,
    G124PrimitiveKernel.fixedG122PrimitiveAmbientElement_not_restricted_range,
    G124PrimitiveKernel.fixedG122LocalFiber_existsUnique_kernel⟩

/-- The finite reading criteria are independent of the A--C parameter and
hold for every operation graph, hidden carrier, visible subgroup and element.
Effectiveness uses the original enumerable finite-input algorithm. -/
theorem aatLocalSemanticReconstruction_d
    (F : FixedFDirectedMultigraph.{u, v}) (K : Type*) [Nontrivial K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    (∀ S : Finset F.Vertex,
      (FiniteReading.Separates
        (FinitePermutationReadingCriteria.readAt F K visible.1) S ↔
        InducedComponent.MeetsEveryFullComponent F
          (fun vertex => vertex ∈ S)) ∧
      (FiniteReading.Extends
        (FinitePermutationReadingCriteria.readAt F K visible.1) S
        (FinitePermutationReadingCriteria.EdgeCoherent F K S) ↔
        InducedComponent.RetainsFullConnectivity F
          (fun vertex => vertex ∈ S))) ∧
    ((∃ S : Finset F.Vertex,
      FiniteReading.Determining
        (FinitePermutationReadingCriteria.readAt F K visible.1) S
        (FinitePermutationReadingCriteria.EdgeCoherent F K S)) ↔
      Finite (FixedFComponent F)) ∧
    (([Fintype F.Vertex] → [DecidableEq F.Vertex] →
      [Fintype F.Edge] → [Fintype K] → [DecidableEq K] →
      ∃ S : Finset F.Vertex,
        FiniteReading.Determining
          (FinitePermutationReadingCriteria.readAt F K visible.1) S
          (FinitePermutationReadingCriteria.EdgeCoherent F K S) ∧
        FiniteReading.Effective
          (FinitePermutationReadingCriteria.readAt F K visible.1) S
          (FinitePermutationReadingCriteria.EdgeCoherent F K S))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    exact ⟨FinitePermutationReadingCriteria.separates_iff F K visible.1 S,
      FinitePermutationReadingCriteria.extends_iff F K visible.1 S⟩
  · exact FinitePermutationReadingCriteria.exists_finite_determining_iff F K visible.1
  · intro _ _ _ _ _
    exact FinitePermutationReadingEffectiveness.exists_effective_determining
      F K visible.1

/-- The inverse-limit lift of arbitrary compatible finite tag projections is
unique in the actual source-choice subgroup. -/
theorem aatLocalSemanticReconstruction_e1_universal
    {G : Type*} [Group G]
    (projections : TagChangeInverseLimitUniversal.Projections G)
    (other : G →* taggedSourceChoiceAutSubgroup)
    (hmatch : ∀ g S,
      (taggedSourceChoiceSubgroupMulEquivCoherentFamily (other g)).toAdd.value S =
        (projections.map S g).toAdd) :
    other = TagChangeInverseLimitUniversal.lift projections :=
  TagChangeInverseLimitUniversal.lift_unique projections other hmatch

/-- The same raw coherent family is assembled by the main B inverse; its
finite nonseparation and the uniform flip equations hold in that Hom. The
edgeless D criterion gives the corresponding actual nonexistence result. -/
theorem aatLocalSemanticReconstruction_e1 :
    (∀ family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex,
      assembleHom
        (.geometry FiniteModel.carrier IndependentGeometryHomPrimitive.Mode.explicit)
        (TagChangeMainRecovery.J family) =
        taggedSourceChoiceNativeHom (TagChange.assemble family)) ∧
    (∀ S : Finset TagChange.TaggedArchitectureIndex,
      ∃ family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex,
        TagChangeMainRecovery.J family ≠
          TagChangeMainRecovery.J (TagChange.read (fun _ => false)) ∧
        ∀ source ∈ S, TagChange.assemble family source = false) ∧
    (TagChangeMainFlip.t ≫ TagChangeMainFlip.t =
      𝟙 ((reading
        (.geometry FiniteModel.carrier IndependentGeometryHomPrimitive.Mode.explicit)).obj
          taggedNativeObject)) ∧
    (TagChangeMainFlip.e ≫ TagChangeMainFlip.t =
      TagChangeMainFlip.t ≫ TagChangeMainFlip.e) ∧
    (TagChangeMainFlip.e ≫ TagChangeMainFlip.t ≠ TagChangeMainFlip.e) ∧
    (¬ ∃ S : Finset TagChangeEdgelessCriterion.graph.Vertex,
      FiniteReading.Determining
        (FinitePermutationReadingCriteria.readAt
          TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity) S
        (FinitePermutationReadingCriteria.EdgeCoherent
          TagChangeEdgelessCriterion.graph Bool S)) := by
  exact ⟨TagChangeMainRecovery.assembleHom_J,
    TagChangeMainRecovery.finite_J_not_separating,
    TagChangeMainFlip.t_square,
    TagChangeMainFlip.e_commutes_t,
    TagChangeMainFlip.e_comp_t_ne_e,
    TagChangeEdgelessCriterion.no_finite_determining⟩

/-- The lens family retains every general semantic Hom under the finite
reference-fiber assembly in the same main reader, while the original fixed-u
change fiber is determined by that reference view for every visible H. -/
theorem aatLocalSemanticReconstruction_e2_lens
    {V K : Type u} [Finite K] [Nontrivial K]
    (reference : V) (H : Subgroup (Equiv.Perm V)) (visible : H) :
    (∀ {X Y : LensRealization V reference} [Fintype X.Fiber] (f : X ⟶ Y),
      (reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).map
        (ULift.up f) =
      (reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).map
        (ULift.up (LensSemanticFiniteDetermination.assembleTable X Y
          (FiniteReading.restrict
            (LensSemanticFiniteDetermination.readLensHomAt X Y)
            (LensSemanticFiniteDetermination.fullFiber X) f)))) ∧
    FiniteReading.Determining
      (fun change vertex => FinitePermutationReadingCriteria.readAt
        (FixedFFiniteExamples.completeUpdateGraph V) K
        (FixedFFiniteExamples.completeUpdateAutomorphism visible.1)
        (CSFixedFFiberD.lensFiberEquivPreserving (K := K) H visible change) vertex)
      ({reference} : Finset V)
      (FinitePermutationReadingCriteria.EdgeCoherent
        (FixedFFiniteExamples.completeUpdateGraph V) K {reference}) := by
  constructor
  · intro X Y _ f
    exact congrArg (fun g : X ⟶ Y =>
      (reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).map
        (ULift.up g))
      (CSFiniteValueQueryBridge.lens_assemble_restricted_values
        ⟨V, reference⟩ X Y f).symm
  · exact CSFixedFFiberD.lens_reference_determining_on_changes reference H visible

/-- The protocol family retains every general observation-preserving Hom
under its independently coherent complete vertex table in the same main
reader. The representative vertices determine each original fixed-u change
fiber without making the full graph finite in the general D theorem. -/
theorem aatLocalSemanticReconstruction_e2_protocol
    {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge] [DecidableEq F.Vertex]
    {K : Type u} [Finite K] [Nontrivial K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    (∀ {P Q : ProtocolRealization
        (CSProtocolKernelLocal.fixedProtocolInput F).schema
        (CSProtocolKernelLocal.fixedProtocolInput F).observation}
      [Fintype (ProtocolObservedFiniteDetermination.InputPoint P)]
      (f : P ⟶ Q),
      (reading (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
        Parameter.{u, u})).map (ULift.up f) =
      (reading (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
        Parameter.{u, u})).map
        (ULift.up (ProtocolObservedFiniteDetermination.assembleTable P Q
          (FiniteReading.restrict
            (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q)
            (ProtocolObservedFiniteDetermination.fullInput P) f)
          (ProtocolObservedFiniteDetermination.read_table_coherent P Q f)))) ∧
    FiniteReading.Determining
      (fun change vertex => FinitePermutationReadingCriteria.readAt F K visible.1
        (CSFixedFFiberD.protocolFiberEquivPreserving (K := K) H visible change)
        vertex)
      (CSFixedFDetermining.protocolRepresentativeSet F)
      (FinitePermutationReadingCriteria.EdgeCoherent F K
        (CSFixedFDetermining.protocolRepresentativeSet F)) := by
  constructor
  · intro P Q _ f
    exact congrArg (fun g : P ⟶ Q =>
      (reading (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
        Parameter.{u, u})).map (ULift.up g))
      (CSFiniteValueQueryBridge.protocol_assemble_restricted_values
        (CSProtocolKernelLocal.fixedProtocolInput F) P Q f).symm
  · exact CSFixedFFiberD.protocol_representatives_determining_on_changes H visible

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end G124MainTheorem
end AAT.AG.LocalSemanticReconstruction
