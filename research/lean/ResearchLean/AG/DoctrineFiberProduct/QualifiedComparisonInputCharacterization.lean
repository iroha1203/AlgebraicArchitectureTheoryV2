import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonGeneratedClassification

/-!
# Actual input-map characterization of the generated residual subgroup

G-118(B1) requires the residual subgroup condition to be readable from the
computational maps of the actual generated geometry homomorphisms.  This file
separates those maps into the exact pointed-core, signed-core, equation,
coefficient, support, axis, and observable components used by the existing
extensionality theorems.

Implementation notes: equation transport is reconstructed from its three
computational fields; proof-only law fields are eliminated by proof
irrelevance.  The final equality is then assembled through
`SignedExactCoreReadingHom.ext`, `PackageTotalHom.ext`, `GeomReadHom.ext`, and
`GeometryTotalHom.ext`.  No equality of complete homomorphisms is stored in the
condition package.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Equation transports with equal parameter maps are determined by their
context, equation-index, and observable computational equivalences. -/
theorem equationSystemExactTransport_heq_of_computational
    {U : AtomCarrier.{u}}
    {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv₁ atomEquiv₂ : U.Atom ≃ U.Atom}
    {objectMap₁ objectMap₂ : ArchitectureObject U → ArchitectureObject U}
    {first : EquationSystemExactTransport E F atomEquiv₁ objectMap₁}
    {second : EquationSystemExactTransport E F atomEquiv₂ objectMap₂}
    (hatom : atomEquiv₁ = atomEquiv₂)
    (hobject : objectMap₁ = objectMap₂)
    (hcontext : HEq first.contextEquivalence second.contextEquivalence)
    (hequation : HEq first.equationEquiv second.equationEquiv)
    (hobservable : HEq first.observableEquiv second.observableEquiv) :
    HEq first second := by
  subst atomEquiv₂
  subst objectMap₂
  apply heq_of_eq
  cases first
  cases second
  cases hcontext
  cases hequation
  cases hobservable
  rfl

namespace UpperGeometryCompatibleProblemInputData

/-- The actual generated pulled endpoint endomorphism attached to a source
change in G-118(B1). -/
noncomputable abbrev generatedPulledEndpointHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (change : CompositeFiberAut (input.sourceGeometry i).package) :
    GeometryTotalHom (input.generatedPulledRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  CompositeFiberAut.hom
    (input.generatedPulledCompositeFiberAutHomAt i change)

/-- The mate followed by the actual generated pulled endpoint endomorphism. -/
noncomputable abbrev generatedPulledComparisonCompositeAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (change : CompositeFiberAut (input.sourceGeometry i).package) :
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  (input.generatedCompatibleUpperGeometryMateAt i).comp
    (input.generatedPulledEndpointHomAt i change)

/-- Computational equality conditions for two complete geometry homomorphisms.
The fields are precisely the data used by the core and geometry extensionality
theorems; no whole-hom equality occurs as an input field. -/
structure GeometryTotalHomInputConditions
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (first second : GeometryTotalHom G H) : Prop where
  pointedSourceMap :
    first.base.base.doctrineHom.sourceMap =
      second.base.base.doctrineHom.sourceMap
  pointedAtomEquiv :
    first.base.base.doctrineHom.atomEquiv =
      second.base.base.doctrineHom.atomEquiv
  atomEquiv :
    first.base.upper.atomEquiv = second.base.upper.atomEquiv
  objectMap :
    first.base.upper.objectMap = second.base.upper.objectMap
  equationContext : HEq
    first.base.upper.equationTransport.contextEquivalence
    second.base.upper.equationTransport.contextEquivalence
  equationIndex : HEq
    first.base.upper.equationTransport.equationEquiv
    second.base.upper.equationTransport.equationEquiv
  equationObservable : HEq
    first.base.upper.equationTransport.observableEquiv
    second.base.upper.equationTransport.observableEquiv
  operationMap : HEq
    (@SignedExactCoreReadingHom.operationMap U G.core H.core first.base.upper)
    (@SignedExactCoreReadingHom.operationMap U G.core H.core second.base.upper)
  invariantMap : HEq
    first.base.upper.invariantMap second.base.upper.invariantMap
  axisMap : HEq
    first.base.upper.axisMap second.base.upper.axisMap
  coordinateEquiv : HEq
    first.base.upper.coordinateEquiv second.base.upper.coordinateEquiv
  coefficientHom :
    first.geometry.coefficientHom = second.geometry.coefficientHom
  supportImageFixed : HEq
    first.geometry.supportComp second.geometry.supportComp
  axisImageFixed : HEq
    first.geometry.axisComp second.geometry.axisComp
  observableImageFixed : HEq
    first.geometry.observableComp second.geometry.observableComp

/-- Equality of complete geometry homomorphisms yields all computational input
conditions. -/
theorem GeometryTotalHomInputConditions.of_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : GeometryTotalHom G H} (equality : first = second) :
    GeometryTotalHomInputConditions first second := by
  subst second
  constructor <;> rfl

/-- Geometry homs over equal base maps are heterogeneously equal when their
four computational geometry components agree. -/
theorem geomReadHom_heq_of_base_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {firstBase secondBase : PackageTotalHom G.core H.core}
    (first : GeomReadHom G H firstBase)
    (second : GeomReadHom G H secondBase)
    (baseEquality : firstBase = secondBase)
    (coefficientEquality : first.coefficientHom = second.coefficientHom)
    (supportEquality : HEq first.supportComp second.supportComp)
    (axisEquality : HEq first.axisComp second.axisComp)
    (observableEquality : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases baseEquality
  exact heq_of_eq (GeomReadHom.ext coefficientEquality supportEquality
    axisEquality observableEquality)

/-- The literal input-map conditions reconstruct complete geometry-hom
equality through the core and geometry extensionality spine. -/
theorem GeometryTotalHomInputConditions.eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : GeometryTotalHom G H}
    (conditions : GeometryTotalHomInputConditions first second) :
    first = second := by
  have hpointed : first.base.base = second.base.base := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · exact conditions.pointedSourceMap
    · exact conditions.pointedAtomEquiv
  have hequation : HEq first.base.upper.equationTransport
      second.base.upper.equationTransport :=
    equationSystemExactTransport_heq_of_computational
      conditions.atomEquiv conditions.objectMap conditions.equationContext
      conditions.equationIndex conditions.equationObservable
  have hupper : first.base.upper = second.base.upper := by
    apply SignedExactCoreReadingHom.ext
    · exact conditions.atomEquiv
    · exact conditions.objectMap
    · exact hequation
    · exact conditions.operationMap
    · exact conditions.invariantMap
    · exact conditions.axisMap
    · exact conditions.coordinateEquiv
  have hbase : first.base = second.base := by
    apply PackageTotalHom.ext
    · exact hpointed
    · exact hupper
  apply GeometryTotalHom.ext hbase
  exact geomReadHom_heq_of_base_eq _ _ hbase conditions.coefficientHom
    conditions.supportImageFixed conditions.axisImageFixed
    conditions.observableImageFixed

/-- G-118(B1) literal computational conditions saying that a generated pulled
source change fixes the comparison. -/
abbrev GeneratedPulledKernelInputConditions
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (change : CompositeFiberAut (input.sourceGeometry i).package) : Prop :=
  GeometryTotalHomInputConditions
    (input.generatedPulledComparisonCompositeAt i change)
    (input.generatedCompatibleUpperGeometryMateAt i)

/-- G-118(B1) actual-map characterization of `J_i`: source membership is
equivalent to the complete list of pointed-core, signed-core, equation,
coefficient, support-image, axis-image, and observable-image conditions. -/
theorem mem_generatedPulledComparisonKernel_iff_inputConditions
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (change : CompositeFiberAut (input.sourceGeometry i).package) :
    change ∈ input.generatedPulledComparisonKernel i ↔
      input.GeneratedPulledKernelInputConditions i change := by
  change input.generatedPulledComparisonCompositeAt i change =
      input.generatedCompatibleUpperGeometryMateAt i ↔ _
  exact ⟨GeometryTotalHomInputConditions.of_eq,
    GeometryTotalHomInputConditions.eq⟩

/-- The generated comparison relation is therefore characterized directly by
the computational input maps of the residual source difference.  This is the
connection between the right-coset classification and the literal B1 input
conditions. -/
theorem generatedQualifiedComparisonRelation_iff_inputConditions
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (baseChange pulledChange :
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.GeneratedQualifiedComparisonRelation i baseChange pulledChange ↔
      input.GeneratedPulledKernelInputConditions i
        (pulledChange * baseChange⁻¹) := by
  rw [input.generatedQualifiedComparisonRelation_iff_difference_mem]
  exact input.mem_generatedPulledComparisonKernel_iff_inputConditions i _

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The literal input conditions are inhabited: the identity residual fixes
every computational component of the generated comparison. -/
theorem generatedPulledKernelInputConditions_one :
    problem.data.GeneratedPulledKernelInputConditions PUnit.unit 1 := by
  rw [← problem.data.mem_generatedPulledComparisonKernel_iff_inputConditions]
  exact Subgroup.one_mem _

/-- The fixed negative comparison pair also fails the literal input-map
conditions.  Thus the characterization distinguishes actual generated data
and is not vacuous. -/
theorem generatedPulledKernelInputConditions_comparator_inv_not :
    ¬ problem.data.GeneratedPulledKernelInputConditions PUnit.unit
      ((problem.data.sourceTransport.comparator
        DecisionCell.comparison)⁻¹) := by
  intro conditions
  apply generatedQualifiedComparisonRelation_base_identity_not
  rw [problem.data.generatedQualifiedComparisonRelation_iff_inputConditions]
  simpa using conditions

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
