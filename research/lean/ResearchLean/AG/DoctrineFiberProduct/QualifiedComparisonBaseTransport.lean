import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonInputCharacterization
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonFixedDecision

/-!
# Generated base transport of qualified comparisons

This module implements G-118(C3).  The actual generated base and pulled maps
form a homomorphism on pairs of source composite-fiber automorphisms.  It sends
the qualified group of the source identity comparison into the qualified group
of the generated mate.  Reflection is characterized exactly by triviality of
the residual source subgroup `J_i`.

The injectivity proof packages each context-indexed Support, Axis, and
Observable map as a dependent Sigma-carrier map.  This turns equality after
the generated route into ordinary function equality, where surjectivity of the
reviewed realization equivalence cancels the route.  Direct cancellation of
the indexed maps would leave dependent context equalities implicit and would
not supply the heterogeneous equalities required by `GeometryTotalHom.ext`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-- The qualified group of an identity comparison is the diagonal subgroup. -/
theorem mem_qualifiedComparisonSubgroup_identity_iff
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    {pair : CompositeFiberAut G × CompositeFiberAut G} :
    pair ∈ qualifiedComparisonSubgroup (𝟙 G) ↔ pair.1 = pair.2 := by
  rw [mem_qualifiedComparisonSubgroup]
  constructor
  · intro equation
    apply Subtype.ext
    apply Iso.ext
    simpa only [Category.comp_id, Category.id_comp] using equation
  · intro equality
    rw [equality]
    change CompositeFiberAut.hom pair.2 = CompositeFiberAut.hom pair.2
    rfl

/-- Left composition by the forward map of an exact upper equivalence is
injective on exact upper maps. -/
theorem ExactUpperEquivalence.forward_comp_injective
    {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    (equivalence : ExactUpperEquivalence P Q) :
    Function.Injective (fun map : SignedExactCoreReadingHom Q R =>
      equivalence.forward.comp map) := by
  intro first second equality
  calc
    first = (SignedExactCoreReadingHom.refl Q).comp first := by
      symm
      apply SignedExactCoreReadingHom.ext <;> rfl
    _ = (equivalence.backward.comp equivalence.forward).comp first := by
      rw [equivalence.backward_forward]
    _ = equivalence.backward.comp (equivalence.forward.comp first) := by
      apply SignedExactCoreReadingHom.ext <;> rfl
    _ = equivalence.backward.comp (equivalence.forward.comp second) := by
      exact congrArg (fun map => equivalence.backward.comp map) equality
    _ = (equivalence.backward.comp equivalence.forward).comp second := by
      apply SignedExactCoreReadingHom.ext <;> rfl
    _ = (SignedExactCoreReadingHom.refl Q).comp second := by
      rw [equivalence.backward_forward]
    _ = second := by
      apply SignedExactCoreReadingHom.ext <;> rfl

namespace UpperGeometryCompatibleProblemInputData

/-- Total support-carrier map of a refinement geometry morphism. -/
noncomputable def refinementGeometrySupportSigmaMap
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : RefinementGeometryHom G H) :
    (Σ W : G.site.category, W.ctx.Support) →
      (Σ W : H.site.category, W.ctx.Support)
  | ⟨W, support⟩ => ⟨refinementGeometryContextForward hom.base W,
      hom.geometry.supportComp W support⟩

/-- Total support-carrier maps respect refinement geometry composition. -/
theorem refinementGeometrySupportSigmaMap_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : RefinementGeometryHom G H) (second : RefinementGeometryHom H K) :
    refinementGeometrySupportSigmaMap (first.comp second) =
      refinementGeometrySupportSigmaMap second ∘
        refinementGeometrySupportSigmaMap first :=
  rfl

/-- Total axis-carrier map of a refinement geometry morphism. -/
noncomputable def refinementGeometryAxisSigmaMap
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : RefinementGeometryHom G H) :
    (Σ W : G.site.category, W.ctx.Axis) →
      (Σ W : H.site.category, W.ctx.Axis)
  | ⟨W, axis⟩ => ⟨refinementGeometryContextForward hom.base W,
      hom.geometry.axisComp W axis⟩

/-- Total axis-carrier maps respect refinement geometry composition. -/
theorem refinementGeometryAxisSigmaMap_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : RefinementGeometryHom G H) (second : RefinementGeometryHom H K) :
    refinementGeometryAxisSigmaMap (first.comp second) =
      refinementGeometryAxisSigmaMap second ∘
        refinementGeometryAxisSigmaMap first :=
  rfl

/-- Total observable-carrier map of a refinement geometry morphism. -/
noncomputable def refinementGeometryObservableSigmaMap
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : RefinementGeometryHom G H) :
    (Σ W : G.site.category, W.ctx.Observable) →
      (Σ W : H.site.category, W.ctx.Observable)
  | ⟨W, observable⟩ => ⟨refinementGeometryContextForward hom.base W,
      hom.geometry.observableComp W observable⟩

/-- Total observable-carrier maps respect refinement geometry composition. -/
theorem refinementGeometryObservableSigmaMap_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : RefinementGeometryHom G H) (second : RefinementGeometryHom H K) :
    refinementGeometryObservableSigmaMap (first.comp second) =
      refinementGeometryObservableSigmaMap second ∘
        refinementGeometryObservableSigmaMap first :=
  rfl

/-- Equality of total support-carrier maps supplies the dependent support-map
equality needed by geometry extensionality. -/
theorem geometryTotalHom_supportComp_heq_of_sigmaMap_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (first second : GeometryTotalHom G H)
    (mapEquality :
      refinementGeometrySupportSigmaMap
          ((exactGeometryToRefinementGeometry U).map first) =
        refinementGeometrySupportSigmaMap
          ((exactGeometryToRefinementGeometry U).map second)) :
    HEq first.geometry.supportComp second.geometry.supportComp := by
  apply Function.hfunext rfl
  intro W W' contextEquality
  cases contextEquality
  apply Function.hfunext rfl
  intro support support' supportEquality
  cases supportEquality
  have totalEquality := congrFun mapEquality ⟨W, support⟩
  exact (Sigma.ext_iff.mp totalEquality).2

/-- Equality of total axis-carrier maps supplies the dependent axis-map
equality needed by geometry extensionality. -/
theorem geometryTotalHom_axisComp_heq_of_sigmaMap_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (first second : GeometryTotalHom G H)
    (mapEquality :
      refinementGeometryAxisSigmaMap
          ((exactGeometryToRefinementGeometry U).map first) =
        refinementGeometryAxisSigmaMap
          ((exactGeometryToRefinementGeometry U).map second)) :
    HEq first.geometry.axisComp second.geometry.axisComp := by
  apply Function.hfunext rfl
  intro W W' contextEquality
  cases contextEquality
  apply Function.hfunext rfl
  intro axis axis' axisEquality
  cases axisEquality
  have totalEquality := congrFun mapEquality ⟨W, axis⟩
  exact (Sigma.ext_iff.mp totalEquality).2

/-- Equality of total observable-carrier maps supplies the dependent
observable-map equality needed by geometry extensionality. -/
theorem geometryTotalHom_observableComp_heq_of_sigmaMap_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (first second : GeometryTotalHom G H)
    (mapEquality :
      refinementGeometryObservableSigmaMap
          ((exactGeometryToRefinementGeometry U).map first) =
        refinementGeometryObservableSigmaMap
          ((exactGeometryToRefinementGeometry U).map second)) :
    HEq first.geometry.observableComp second.geometry.observableComp := by
  apply Function.hfunext rfl
  intro W W' contextEquality
  cases contextEquality
  apply Function.hfunext rfl
  intro observable observable' observableEquality
  cases observableEquality
  have totalEquality := congrFun mapEquality ⟨W, observable⟩
  exact (Sigma.ext_iff.mp totalEquality).2

/-- The literal pulled route leg realizes the reviewed equivalence on total
support carriers. -/
theorem generatedPulledRoute_supportSigmaMap_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    refinementGeometrySupportSigmaMap (input.generatedPulledRouteLegAt i) =
      (input.generatedPulledRouteRealizationExactAt i).supportSigmaEquiv := by
  have upperEquality :=
    input.generatedPulledRouteUpperEquivalenceAt_forward_eq i
  cases upperEquality
  funext value
  rcases value with ⟨W, support⟩
  apply Sigma.ext
  · rfl
  · rfl

/-- The literal pulled route leg realizes the reviewed equivalence on total
axis carriers. -/
theorem generatedPulledRoute_axisSigmaMap_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    refinementGeometryAxisSigmaMap (input.generatedPulledRouteLegAt i) =
      (input.generatedPulledRouteRealizationExactAt i).axisSigmaEquiv := by
  have upperEquality :=
    input.generatedPulledRouteUpperEquivalenceAt_forward_eq i
  cases upperEquality
  funext value
  rcases value with ⟨W, axis⟩
  apply Sigma.ext
  · rfl
  · rfl

/-- The literal pulled route leg realizes the reviewed equivalence on total
observable carriers. -/
theorem generatedPulledRoute_observableSigmaMap_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    refinementGeometryObservableSigmaMap (input.generatedPulledRouteLegAt i) =
      (input.generatedPulledRouteRealizationExactAt i).observableSigmaEquiv := by
  have upperEquality :=
    input.generatedPulledRouteUpperEquivalenceAt_forward_eq i
  cases upperEquality
  funext value
  rcases value with ⟨W, observable⟩
  apply Sigma.ext
  · rfl
  · rfl

/-- The pulled comparator candidate has the source coefficient map: the
generated route leg is coefficient-trivial. -/
theorem generatedPulledGeometryComparatorCandidateAt_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorCandidateAt i automorphism).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  simp only [generatedPulledGeometryComparatorCandidateAt,
    RefinementGeometryHom.comp, RefinementGeomReadHom.comp,
    input.generatedPulledRouteLegAt_coefficient_id]
  ext value
  rfl

/-- The support Sigma-map of the pulled candidate is route composition with
the source automorphism Sigma-map. -/
theorem generatedPulledGeometryComparatorCandidateAt_supportSigmaMap
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    refinementGeometrySupportSigmaMap
        (input.generatedPulledGeometryComparatorCandidateAt i automorphism) =
      refinementGeometrySupportSigmaMap
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism)) ∘
        refinementGeometrySupportSigmaMap (input.generatedPulledRouteLegAt i) := by
  rw [generatedPulledGeometryComparatorCandidateAt]
  exact refinementGeometrySupportSigmaMap_comp _ _

/-- The axis Sigma-map of the pulled candidate is route composition with the
source automorphism Sigma-map. -/
theorem generatedPulledGeometryComparatorCandidateAt_axisSigmaMap
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    refinementGeometryAxisSigmaMap
        (input.generatedPulledGeometryComparatorCandidateAt i automorphism) =
      refinementGeometryAxisSigmaMap
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism)) ∘
        refinementGeometryAxisSigmaMap (input.generatedPulledRouteLegAt i) := by
  rw [generatedPulledGeometryComparatorCandidateAt]
  exact refinementGeometryAxisSigmaMap_comp _ _

/-- The observable Sigma-map of the pulled candidate is route composition
with the source automorphism Sigma-map. -/
theorem generatedPulledGeometryComparatorCandidateAt_observableSigmaMap
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    refinementGeometryObservableSigmaMap
        (input.generatedPulledGeometryComparatorCandidateAt i automorphism) =
      refinementGeometryObservableSigmaMap
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism)) ∘
        refinementGeometryObservableSigmaMap
          (input.generatedPulledRouteLegAt i) := by
  rw [generatedPulledGeometryComparatorCandidateAt]
  exact refinementGeometryObservableSigmaMap_comp _ _

/-- The generated pulled endpoint homomorphism is injective.  The lower
pointed maps of composite-fiber automorphisms are identities; coefficient
maps are reflected by coefficient-triviality of the generated route; and the
upper and three realization carriers are reflected through the generated
route equivalences. -/
theorem generatedPulledCompositeFiberAutHomAt_injective
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Function.Injective (input.generatedPulledCompositeFiberAutHomAt i) := by
  intro first second imageEquality
  let firstHom := CompositeFiberAut.hom first
  let secondHom := CompositeFiberAut.hom second
  have candidateEquality :
      input.generatedPulledGeometryComparatorCandidateAt i first =
        input.generatedPulledGeometryComparatorCandidateAt i second := by
    rw [← input.generatedPulledCompositeFiberAutAt_fac i first,
      ← input.generatedPulledCompositeFiberAutAt_fac i second]
    exact congrArg
      (fun automorphism =>
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom automorphism)).comp
            (input.generatedPulledRouteLegAt i)) imageEquality
  have upperCompositeEquality := congrArg
    (fun hom => hom.base.upper) candidateEquality
  have upperEquality : firstHom.base.upper = secondHom.base.upper := by
    change (input.generatedPulledRouteLegAt i).base.upper.comp
        firstHom.base.upper =
      (input.generatedPulledRouteLegAt i).base.upper.comp
        secondHom.base.upper at upperCompositeEquality
    rw [← input.generatedPulledRouteUpperEquivalenceAt_forward_eq i]
      at upperCompositeEquality
    exact ExactUpperEquivalence.forward_comp_injective
      (input.generatedPulledRouteUpperEquivalenceAt i) upperCompositeEquality
  have pointedEquality : firstHom.base.base = secondHom.base.base := by
    rw [CompositeFiberAut.hom_base_base_eq,
      CompositeFiberAut.hom_base_base_eq]
  have baseEquality : firstHom.base = secondHom.base := by
    apply PackageTotalHom.ext pointedEquality upperEquality
  have coefficientCompositeEquality := congrArg
    (fun hom => hom.geometry.coefficientHom) candidateEquality
  have coefficientEquality :
      firstHom.geometry.coefficientHom =
        secondHom.geometry.coefficientHom := by
    change
      (input.generatedPulledGeometryComparatorCandidateAt i first).geometry.coefficientHom =
        (input.generatedPulledGeometryComparatorCandidateAt i second).geometry.coefficientHom
      at coefficientCompositeEquality
    rw [input.generatedPulledGeometryComparatorCandidateAt_coefficientHom,
      input.generatedPulledGeometryComparatorCandidateAt_coefficientHom]
      at coefficientCompositeEquality
    exact coefficientCompositeEquality
  have supportCompositeEquality := congrArg refinementGeometrySupportSigmaMap
    candidateEquality
  have supportMapEquality :
      refinementGeometrySupportSigmaMap
          ((exactGeometryToRefinementGeometry U).map firstHom) =
        refinementGeometrySupportSigmaMap
          ((exactGeometryToRefinementGeometry U).map secondHom) := by
    have routeSurjective : Function.Surjective
        (input.generatedPulledRouteRealizationExactAt i).supportSigmaEquiv :=
      Equiv.surjective _
    apply routeSurjective.right_cancellable.mp
    rw [← input.generatedPulledRoute_supportSigmaMap_eq i]
    rw [input.generatedPulledGeometryComparatorCandidateAt_supportSigmaMap,
      input.generatedPulledGeometryComparatorCandidateAt_supportSigmaMap]
      at supportCompositeEquality
    exact supportCompositeEquality
  have axisCompositeEquality := congrArg refinementGeometryAxisSigmaMap
    candidateEquality
  have axisMapEquality :
      refinementGeometryAxisSigmaMap
          ((exactGeometryToRefinementGeometry U).map firstHom) =
        refinementGeometryAxisSigmaMap
          ((exactGeometryToRefinementGeometry U).map secondHom) := by
    have routeSurjective : Function.Surjective
        (input.generatedPulledRouteRealizationExactAt i).axisSigmaEquiv :=
      Equiv.surjective _
    apply routeSurjective.right_cancellable.mp
    rw [← input.generatedPulledRoute_axisSigmaMap_eq i]
    rw [input.generatedPulledGeometryComparatorCandidateAt_axisSigmaMap,
      input.generatedPulledGeometryComparatorCandidateAt_axisSigmaMap]
      at axisCompositeEquality
    exact axisCompositeEquality
  have observableCompositeEquality := congrArg refinementGeometryObservableSigmaMap
    candidateEquality
  have observableMapEquality :
      refinementGeometryObservableSigmaMap
          ((exactGeometryToRefinementGeometry U).map firstHom) =
        refinementGeometryObservableSigmaMap
          ((exactGeometryToRefinementGeometry U).map secondHom) := by
    have routeSurjective : Function.Surjective
        (input.generatedPulledRouteRealizationExactAt i).observableSigmaEquiv :=
      Equiv.surjective _
    apply routeSurjective.right_cancellable.mp
    rw [← input.generatedPulledRoute_observableSigmaMap_eq i]
    rw [input.generatedPulledGeometryComparatorCandidateAt_observableSigmaMap,
      input.generatedPulledGeometryComparatorCandidateAt_observableSigmaMap]
      at observableCompositeEquality
    exact observableCompositeEquality
  apply Subtype.ext
  apply Iso.ext
  apply GeometryTotalHom.ext baseEquality
  exact geomReadHom_heq_of_base_eq firstHom.geometry secondHom.geometry
    baseEquality coefficientEquality
    (geometryTotalHom_supportComp_heq_of_sigmaMap_eq firstHom secondHom
      supportMapEquality)
    (geometryTotalHom_axisComp_heq_of_sigmaMap_eq firstHom secondHom
      axisMapEquality)
    (geometryTotalHom_observableComp_heq_of_sigmaMap_eq firstHom secondHom
      observableMapEquality)

/-- The C3 pair map `(a,d) ↦ (H_B(a),H_P(d))` built from the actual generated
endpoint homomorphisms. -/
noncomputable def generatedComparisonPairHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package) →*
      (CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut (input.generatedPulledRouteGeometryAt i)) :=
  MonoidHom.prodMap (input.generatedBaseCompositeFiberAutHomAt i)
    (input.generatedPulledCompositeFiberAutHomAt i)

/-- Evaluation of the generated comparison pair hom is the literal pair of
the two generated endpoint images. -/
@[simp] theorem generatedComparisonPairHomAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedComparisonPairHomAt i pair =
      (input.generatedBaseCompositeFiberAutHomAt i pair.1,
        input.generatedPulledCompositeFiberAutHomAt i pair.2) :=
  rfl

/-- The generated pair map preserves qualified membership from the source
identity comparison to the actual generated mate. -/
theorem generatedComparisonPairHomAt_preserves_qualifiedComparison
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package}
    (sourceMembership : pair ∈ qualifiedComparisonSubgroup
      (𝟙 (input.sourceGeometry i).package)) :
    input.generatedComparisonPairHomAt i pair ∈
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  have equality := mem_qualifiedComparisonSubgroup_identity_iff.mp
    sourceMembership
  change input.GeneratedQualifiedComparisonRelation i pair.1 pair.2
  rw [equality]
  exact input.generatedQualifiedComparisonRelation_diagonal i pair.2

/-- Reflection of the generated comparison relation is equivalent to
triviality of the actual residual source subgroup `J_i`. -/
theorem generatedQualifiedComparisonRelation_reflects_iff_kernel_eq_bot
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (∀ baseChange pulledChange :
        CompositeFiberAut (input.sourceGeometry i).package,
      input.GeneratedQualifiedComparisonRelation i baseChange pulledChange →
        baseChange = pulledChange) ↔
      input.generatedPulledComparisonKernel i = ⊥ := by
  constructor
  · intro reflects
    apply (Subgroup.eq_bot_iff_forall _).2
    intro residual membership
    have relation : input.GeneratedQualifiedComparisonRelation i 1 residual :=
      (input.generatedQualifiedComparisonRelation_iff_difference_mem
        i 1 residual).2 (by simpa using membership)
    exact (reflects 1 residual relation).symm
  · intro kernelIdentity baseChange pulledChange relation
    have differenceMembership :=
      (input.generatedQualifiedComparisonRelation_iff_difference_mem
        i baseChange pulledChange).1 relation
    rw [kernelIdentity] at differenceMembership
    have differenceIdentity : pulledChange * baseChange⁻¹ = 1 := by
      simpa using differenceMembership
    have equalityAfterRightMultiplication := congrArg
      (fun change => change * baseChange) differenceIdentity
    simpa using equalityAfterRightMultiplication.symm

/-- The pair hom reflects the identity-comparison subgroup exactly when the
residual source subgroup is trivial. -/
theorem generatedComparisonPairHomAt_reflects_qualifiedComparison_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (∀ pair : CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package,
      input.generatedComparisonPairHomAt i pair ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt i) →
        pair ∈ qualifiedComparisonSubgroup
          (𝟙 (input.sourceGeometry i).package)) ↔
      input.generatedPulledComparisonKernel i = ⊥ := by
  rw [← input.generatedQualifiedComparisonRelation_reflects_iff_kernel_eq_bot i]
  constructor
  · intro reflects baseChange pulledChange relation
    exact mem_qualifiedComparisonSubgroup_identity_iff.mp
      (reflects (baseChange, pulledChange) relation)
  · intro reflects pair targetMembership
    exact mem_qualifiedComparisonSubgroup_identity_iff.mpr
      (reflects pair.1 pair.2 targetMembership)

/-- If the generated target stabilizer is trivial, the residual subgroup
`J_i` is exactly the kernel of the actual pulled endpoint homomorphism. -/
theorem generatedPulledComparisonKernel_eq_ker_of_targetStabilizer_eq_bot
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (targetStabilizerIdentity :
      qualifiedComparisonTargetStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) = ⊥) :
    input.generatedPulledComparisonKernel i =
      MonoidHom.ker (input.generatedPulledCompositeFiberAutHomAt i) := by
  rw [generatedPulledComparisonKernel, targetStabilizerIdentity]
  rfl

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- At the fixed decision datum the residual source subgroup is trivial.  The
target stabilizer is trivial because the generated comparison is an
isomorphism, and the actual pulled endpoint homomorphism is injective. -/
theorem generatedPulledComparisonKernel_eq_bot :
    problem.data.generatedPulledComparisonKernel PUnit.unit = ⊥ := by
  rw [problem.data.generatedPulledComparisonKernel_eq_ker_of_targetStabilizer_eq_bot
    PUnit.unit solution_targetStabilizer_eq_bot]
  exact (MonoidHom.ker_eq_bot_iff
    (problem.data.generatedPulledCompositeFiberAutHomAt PUnit.unit)).2
      (problem.data.generatedPulledCompositeFiberAutHomAt_injective PUnit.unit)

/-- The fixed relation reflects equality for every pair of source
automorphisms; this is the positive C3 decision branch. -/
theorem generatedQualifiedComparisonRelation_iff_eq
    (baseChange pulledChange : CompositeFiberAut package) :
    problem.data.GeneratedQualifiedComparisonRelation PUnit.unit
        baseChange pulledChange ↔
      baseChange = pulledChange := by
  constructor
  · intro relation
    exact
      ((problem.data.generatedQualifiedComparisonRelation_reflects_iff_kernel_eq_bot
        PUnit.unit).2 generatedPulledComparisonKernel_eq_bot)
        baseChange pulledChange relation
  · intro equality
    rw [equality]
    exact problem.data.generatedQualifiedComparisonRelation_diagonal
      PUnit.unit pulledChange

/-- At the fixed datum, generated target membership of the actual pair map is
equivalent to source membership in the identity-comparison subgroup. -/
theorem solution_generatedComparisonPairHom_mem_iff_source_identity_mem
    (pair : CompositeFiberAut package × CompositeFiberAut package) :
    problem.data.generatedComparisonPairHomAt PUnit.unit pair ∈
        qualifiedComparisonSubgroup (solution.component PUnit.unit) ↔
      pair ∈ qualifiedComparisonSubgroup (𝟙 package) := by
  constructor
  · intro targetMembership
    exact
      ((problem.data.generatedComparisonPairHomAt_reflects_qualifiedComparison_iff
        PUnit.unit).2 generatedPulledComparisonKernel_eq_bot)
        pair targetMembership
  · exact problem.data.generatedComparisonPairHomAt_preserves_qualifiedComparison
      PUnit.unit

/-- The B1 computational characterization of `J_*` is therefore inhabited
only by the identity source change. -/
theorem generatedPulledKernelInputConditions_iff_eq_one
    (change : CompositeFiberAut package) :
    problem.data.GeneratedPulledKernelInputConditions PUnit.unit change ↔
      change = 1 := by
  rw [← problem.data.mem_generatedPulledComparisonKernel_iff_inputConditions]
  constructor
  · intro membership
    rw [generatedPulledComparisonKernel_eq_bot] at membership
    simpa using membership
  · rintro rfl
    exact Subgroup.one_mem _

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
