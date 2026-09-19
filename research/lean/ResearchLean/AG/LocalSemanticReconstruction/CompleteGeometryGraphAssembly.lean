import ResearchLean.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence
import Formal.Util.AssertStandardAxioms

/-!
# Complete geometry assembly from independent graph codes

Cycle 71 closes the relative ambient input left by Cycle 70.  The package
part is assembled from primitive function graphs, the Cycle 67 algebraic
codes, the Cycle 69 context/observable code, and the Cycle 70 operation,
invariant, and signature codes.  The complete code then adds the Cycle 70
realization/raw data and local coverage/overlap data.  Neither code stores a
`PackageTotalHom` or a `GeometryTotalHom`.

The main result is an exact equivalence between these independent codes and
actual complete geometry morphisms.  Thus the construction supplies both
assembly and separation, not merely a new record or a one-way decoder.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport
open CompleteGeometryFunctionGraphSeparation

noncomputable section

namespace CompleteGeometryGraphAssembly

universe u v

abbrev GraphCode := PrimitiveFunctionGraph.GraphCode

/-- Dependent coordinate component of the Cycle 70 signature read/assemble
law, exposed separately for complete-core extensionality. -/
theorem signature_read_assemble_coordinate_heq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (supply : RemainingComponentGraphCoherence.SignatureTransportSupply
      P Q objectMap) :
    HEq (RemainingComponentGraphCoherence.SignatureGraphCode.read
      supply).assemble.coordinateEquiv supply.coordinateEquiv := by
  simp only [RemainingComponentGraphCoherence.SignatureGraphCode.read,
    RemainingComponentGraphCoherence.SignatureGraphCode.assemble]
  apply HEq.trans
    (RemainingComponentGraphCoherence.IndexedEquivGraphCode.reindex_assemble_heq
      (PrimitiveFunctionGraph.GraphCode.assemble_read supply.axisMap)
      (DependentAlgebraicGraphCoherence.IndexedEquivGraphCode.read
        supply.coordinateEquiv))
  exact heq_of_eq
    (DependentAlgebraicGraphCoherence.IndexedEquivGraphCode.assemble_read _)

/-! ## Independent package code -/

/-- Computational package data assembled from the graph-code APIs of Cycles
67, 69, and 70.  All noncomputational compatibility statements are kept in
`IsPackageGraphCode`. -/
structure PackageGraphData {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  source : GraphCode G.core.reading.doctrine.Source
    H.core.reading.doctrine.Source
  pointedAtom : U.Atom ≃ U.Atom
  pointedAtomGraph : AlgebraicGraphCoherence.EquivGraphCode U.Atom U.Atom
  atomEquiv : U.Atom ≃ U.Atom
  atomGraph : AlgebraicGraphCoherence.EquivGraphCode U.Atom U.Atom
  objectMap : ArchitectureObject U → ArchitectureObject U
  objectGraph : GraphCode (ArchitectureObject U) (ArchitectureObject U)
  configuration : ∀ A,
    ConfigurationHom A.configuration (objectMap A).configuration
  equation : AlgebraicGraphCoherence.EquivGraphCode
    G.core.algebra.equationSystem.Index H.core.algebra.equationSystem.Index
  equationTransport : EquationSystemExactTransport
    G.core.algebra.equationSystem H.core.algebra.equationSystem
    atomEquiv objectMap
  contextObservable : ContextObservableGraphCoherence.ContextObservableGraphCode
    G.core.algebra.equationSystem H.core.algebra.equationSystem
  operation : RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode
    objectMap objectMap
    (fun A B => G.core.reading.operationReading.Op A B)
    (fun A B => H.core.reading.operationReading.Op A B)
  invariant : GraphCode G.core.reading.invariantReading.Index
    H.core.reading.invariantReading.Index
  signature : RemainingComponentGraphCoherence.SignatureGraphCode
    G.core H.core objectMap

namespace PackageGraphData

/-- The equation transport assembled from Cycle 67 and Cycle 69 data, before
the equation-specific compatibility laws are attached. -/
def contextEquivalence {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (data : PackageGraphData G H) :
    G.site.category ≌ H.site.category :=
  data.contextObservable.context.assemble

end PackageGraphData

/-- Local laws for `PackageGraphData`.  The fields mention only decoded graph
functions and fixed source/target packages; no completed package morphism is
used as a certificate. -/
structure IsPackageGraphCode {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (data : PackageGraphData G H) : Prop where
  object_graph_eq : data.objectGraph.assemble = data.objectMap
  pointed_atom_graph_eq : data.pointedAtomGraph.assemble = data.pointedAtom
  atom_graph_eq : data.atomGraph.assemble = data.atomEquiv
  equation_eq : data.equation.assemble =
    data.equationTransport.equationEquiv
  context_eq : data.contextObservable.context.assemble =
    data.equationTransport.contextEquivalence
  observable_iso_eq : HEq
    data.contextObservable.observable.assembleIso
    data.equationTransport.observablePresheafIso
  context_observable_canonical : data.contextObservable =
    ContextObservableGraphCoherence.ContextObservableGraphCode.read
      data.equationTransport
  normalize_eq : ∀ source,
    H.core.reading.doctrine.normalize (data.source.assemble source) =
      data.source.assemble (G.core.reading.doctrine.normalize source)
  extraction_iff : ∀ source atom,
    G.core.reading.doctrine.extracts source atom ↔
      H.core.reading.doctrine.extracts (data.source.assemble source)
        (data.pointedAtom atom)
  source_eq : data.source.assemble G.core.reading.source = H.core.reading.source
  atom_eq : data.atomEquiv = data.pointedAtom
  extraction_eq : H.core.family = G.core.family.transport data.atomEquiv
  composition_eq : ∀ (F : AtomFamily U) (hF : F.ListFinite),
    H.core.reading.composition.compose
        (F.transport data.atomEquiv) (hF.transport data.atomEquiv) =
      (G.core.reading.composition.compose F hF).transport data.atomEquiv
  object_formation_eq : ∀ C,
    data.objectMap (G.core.reading.objectReading.object C) =
      H.core.reading.objectReading.object (C.transport data.atomEquiv)
  configuration_eq : ∀ A,
    (data.objectMap A).configuration =
      A.configuration.transport data.atomEquiv
  configuration_atom : ∀ A,
    (data.configuration A).atomMap = data.atomEquiv
  detectorCode_eq : ∀ i,
    H.core.algebra.circuits.code (data.equation.assemble i) =
      (G.core.algebra.circuits.code i).transport data.atomEquiv
  operation_naturality : RemainingComponentGraphCoherence.IsOperationNatural
    G.core H.core data.objectMap
      data.configuration
      data.operation.assemble
  invariant_transport : RemainingComponentGraphCoherence.IsInvariantTransport
    G.core H.core data.objectMap data.invariant.assemble
  axis_selected_iff : ∀ i,
    G.core.reading.signatureReading.selected i ↔
      H.core.reading.signatureReading.selected
        ((RemainingComponentGraphCoherence.SignatureGraphCode.assemble
          data.signature).axisMap i)
  coordinate_eq : ∀ A i,
    (RemainingComponentGraphCoherence.SignatureGraphCode.assemble
      data.signature).coordinateEquiv i
        (G.core.reading.signatureReading.coordinate A i) =
      H.core.reading.signatureReading.coordinate
        (data.objectMap A)
        ((RemainingComponentGraphCoherence.SignatureGraphCode.assemble
          data.signature).axisMap i)

/-- Independent package graph code. -/
abbrev PackageGraphCode {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) :=
  { data : PackageGraphData G H // IsPackageGraphCode data }

namespace PackageGraphCode

/-- Canonical configuration map forced by the Atom graph and the decoded
object-configuration equation. -/
def configurationMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : PackageGraphCode G H) (A) :
    ConfigurationHom A.configuration (code.1.objectMap A).configuration :=
  code.1.configuration A

/-- Assemble the Cycle 69 equation transport from its independent context and
observable graphs and the equation-specific local laws. -/
def equationTransport {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : PackageGraphCode G H) :
    EquationSystemExactTransport G.core.algebra.equationSystem
      H.core.algebra.equationSystem code.1.atomEquiv
      code.1.objectMap :=
  code.1.equationTransport

/-- Assemble the complete upper core morphism from independent graph data. -/
def upper {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : SignedExactCoreReadingHom G.core H.core where
  atomEquiv := code.1.atomEquiv
  extraction_eq := code.2.extraction_eq
  composition_eq := code.2.composition_eq
  objectMap := code.1.objectMap
  object_formation_eq := code.2.object_formation_eq
  configurationMap := code.configurationMap
  configurationMap_atomMap := code.2.configuration_atom
  configuration_eq := code.2.configuration_eq
  equationTransport := code.equationTransport
  detectorCode_eq i := by
    change H.core.algebra.circuits.code
      (code.1.equationTransport.equationEquiv i) = _
    exact (congrArg (fun equivalence =>
      H.core.algebra.circuits.code (equivalence i))
        code.2.equation_eq).symm.trans (code.2.detectorCode_eq i)
  operationMap := fun {A B} op => code.1.operation.assemble A B op
  operation_naturality := fun op => code.2.operation_naturality _ _ op
  invariantMap := code.1.invariant.assemble
  invariant_transport := code.2.invariant_transport
  axisMap := (RemainingComponentGraphCoherence.SignatureGraphCode.assemble
    code.1.signature).axisMap
  coordinateEquiv := (RemainingComponentGraphCoherence.SignatureGraphCode.assemble
    code.1.signature).coordinateEquiv
  axis_selected_iff := code.2.axis_selected_iff
  coordinate_eq := code.2.coordinate_eq

/-- Assemble the lower pointed doctrine morphism. -/
def lower {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) :
    ExtInstHom (packagePoint G.core) (packagePoint H.core) where
  doctrineHom := {
    sourceMap := code.1.source.assemble
    atomEquiv := code.1.pointedAtom
    normalize_eq := code.2.normalize_eq
    extraction_iff := code.2.extraction_iff }
  source_eq := code.2.source_eq

/-- Cycle 71 package assembler.  Its input contains no completed package
morphism. -/
def assemble {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : PackageTotalHom G.core H.core where
  base := code.lower
  upper := code.upper
  atomEquiv_eq := by simpa [upper, lower] using code.2.atom_eq

/-- Read an actual package morphism into independent graph codes.  Geometry
packages are parameters only; no geometry morphism is retained. -/
def read {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (morphism : PackageTotalHom G.core H.core) : PackageGraphCode G H := by
  let source := PrimitiveFunctionGraph.GraphCode.read
    morphism.base.doctrineHom.sourceMap
  let pointedAtomGraph := AlgebraicGraphCoherence.EquivGraphCode.read
    morphism.base.doctrineHom.atomEquiv
  let atomGraph := AlgebraicGraphCoherence.EquivGraphCode.read morphism.upper.atomEquiv
  let objectGraph := PrimitiveFunctionGraph.GraphCode.read morphism.upper.objectMap
  have object_eq : objectGraph.assemble = morphism.upper.objectMap :=
    PrimitiveFunctionGraph.GraphCode.assemble_read _
  let configuration : ∀ A,
      ConfigurationHom A.configuration (morphism.upper.objectMap A).configuration :=
    morphism.upper.configurationMap
  let equation := AlgebraicGraphCoherence.EquivGraphCode.read
    morphism.upper.equationTransport.equationEquiv
  let contextObservable := ContextObservableGraphCoherence.ContextObservableGraphCode.read
    morphism.upper.equationTransport
  let operation : RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode
      morphism.upper.objectMap morphism.upper.objectMap
      (fun A B => G.core.reading.operationReading.Op A B)
      (fun A B => H.core.reading.operationReading.Op A B) := by
    exact RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.read
      (fun A B => @morphism.upper.operationMap A B)
  let invariant := PrimitiveFunctionGraph.GraphCode.read morphism.upper.invariantMap
  let signatureSupply : RemainingComponentGraphCoherence.SignatureTransportSupply
      G.core H.core morphism.upper.objectMap := {
      axisMap := morphism.upper.axisMap
      coordinateEquiv := morphism.upper.coordinateEquiv
      axis_selected_iff := morphism.upper.axis_selected_iff
      coordinate_eq := morphism.upper.coordinate_eq }
  let signature : RemainingComponentGraphCoherence.SignatureGraphCode
      G.core H.core morphism.upper.objectMap :=
    RemainingComponentGraphCoherence.SignatureGraphCode.read signatureSupply
  refine ⟨{
    source := source
    pointedAtom := morphism.base.doctrineHom.atomEquiv
    pointedAtomGraph := pointedAtomGraph
    atomEquiv := morphism.upper.atomEquiv
    atomGraph := atomGraph
    objectMap := morphism.upper.objectMap
    objectGraph := objectGraph
    configuration := configuration
    equation := equation
    equationTransport := morphism.upper.equationTransport
    contextObservable := contextObservable
    operation := operation
    invariant := invariant
    signature := signature }, ?_⟩
  constructor
  · exact object_eq
  · exact AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  · exact AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  · exact AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  · exact ContextObservableGraphCoherence.ContextObservableGraphCode.read_context_assemble _
  · exact ContextObservableGraphCoherence.ContextObservableGraphCode.read_observable_assembleIso _
  · rfl
  · simpa [source] using morphism.base.doctrineHom.normalize_eq
  · simpa [source] using morphism.base.doctrineHom.extraction_iff
  · simpa [source] using morphism.base.source_eq
  · exact morphism.atomEquiv_eq
  · exact morphism.upper.extraction_eq
  · exact morphism.upper.composition_eq
  · exact morphism.upper.object_formation_eq
  · exact morphism.upper.configuration_eq
  · intro A
    exact morphism.upper.configurationMap_atomMap A
  · simpa [equation] using morphism.upper.detectorCode_eq
  · intro A B op
    have law := morphism.upper.operation_naturality op
    apply ConfigurationHom.ext
    have supplied := congrArg ConfigurationHom.atomMap law
    simpa [operation, configuration] using supplied
  · simpa [invariant] using morphism.upper.invariant_transport
  · rw [show signature.assemble = signatureSupply by
      exact RemainingComponentGraphCoherence.SignatureGraphCode.assemble_read _]
    exact signatureSupply.axis_selected_iff
  · rw [show signature.assemble = signatureSupply by
      exact RemainingComponentGraphCoherence.SignatureGraphCode.assemble_read _]
    exact signatureSupply.coordinate_eq

/-- Package reading followed by assembly recovers the actual package morphism. -/
@[simp]
theorem assemble_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : PackageTotalHom G.core H.core) :
    assemble (read morphism) = morphism := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · simp [assemble, lower, read]
    · simp [assemble, lower, read]
  · apply SignedExactCoreReadingHom.ext
    · simp [assemble, upper, read]
    · rfl
    · rfl
    · apply heq_of_eq
      simp [assemble, upper, read]
    · simp [assemble, upper, read]
    · apply heq_of_eq
      simp [assemble, upper, read]
    · let supply : RemainingComponentGraphCoherence.SignatureTransportSupply
          G.core H.core morphism.upper.objectMap := {
        axisMap := morphism.upper.axisMap
        coordinateEquiv := morphism.upper.coordinateEquiv
        axis_selected_iff := morphism.upper.axis_selected_iff
        coordinate_eq := morphism.upper.coordinate_eq }
      simpa [assemble, upper, read, supply] using
        signature_read_assemble_coordinate_heq supply

/-- Independent package codes are recovered exactly after package assembly. -/
@[simp]
theorem read_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : PackageGraphCode G H) :
    read code.assemble = code := by
  apply Subtype.ext
  cases code with
  | mk data law =>
      rcases data with ⟨source, pointedAtom, pointedAtomGraph, atomEquiv,
        atomGraph, objectMap, objectGraph, configuration, equation,
        equationTransportData, contextObservable, operation, invariant,
        signature⟩
      simp [read, assemble, upper, lower]
      refine ⟨?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
      · calc
          AlgebraicGraphCoherence.EquivGraphCode.read pointedAtom =
              AlgebraicGraphCoherence.EquivGraphCode.read
                pointedAtomGraph.assemble := by rw [law.pointed_atom_graph_eq]
          _ = pointedAtomGraph :=
            AlgebraicGraphCoherence.EquivGraphCode.read_assemble _
      · calc
          AlgebraicGraphCoherence.EquivGraphCode.read atomEquiv =
              AlgebraicGraphCoherence.EquivGraphCode.read atomGraph.assemble := by
                rw [law.atom_graph_eq]
          _ = atomGraph :=
            AlgebraicGraphCoherence.EquivGraphCode.read_assemble _
      · calc
          PrimitiveFunctionGraph.GraphCode.read objectMap =
              PrimitiveFunctionGraph.GraphCode.read objectGraph.assemble := by
                rw [law.object_graph_eq]
          _ = objectGraph := PrimitiveFunctionGraph.GraphCode.read_assemble _
      · calc
          AlgebraicGraphCoherence.EquivGraphCode.read
              equationTransportData.equationEquiv =
              AlgebraicGraphCoherence.EquivGraphCode.read equation.assemble := by
                rw [law.equation_eq]
          _ = equation :=
            AlgebraicGraphCoherence.EquivGraphCode.read_assemble _
      · exact law.context_observable_canonical.symm
      · exact RemainingComponentGraphCoherence.SignatureGraphCode.read_assemble _

end PackageGraphCode

/-! ## Complete geometry code and two-sided assembly -/

/-- Local Cycle 70 supply extracted from a geometry-stage hom over an explicit
base. -/
def remainingSupplyOfGeometry {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {base : PackageTotalHom G.core H.core}
    (geometry : GeomReadHom G H base) :
    RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentSupply
      G H base geometry.coefficientHom where
  operation := ⟨(fun A B op => @base.upper.operationMap A B op),
    by intro A B op; exact base.upper.operation_naturality op⟩
  invariant := ⟨base.upper.invariantMap, base.upper.invariant_transport⟩
  signature := {
    axisMap := base.upper.axisMap
    coordinateEquiv := base.upper.coordinateEquiv
    axis_selected_iff := base.upper.axis_selected_iff
    coordinate_eq := base.upper.coordinate_eq }
  realization := {
    supportComp := geometry.supportComp
    axisComp := geometry.axisComp
    observableComp := geometry.observableComp
    supportReads := geometry.supportReads
    axisReads := geometry.axisReads
    observableReads := geometry.observableReads
    support_naturality := geometry.support_naturality
    axis_naturality := geometry.axis_naturality
    observable_naturality := geometry.observable_naturality }
  rawCoherent := geometry.raw_eq

/-- Reading the local supply commutes, up to dependent equality, with a change
of the explicit base index. -/
theorem remainingRead_cast_heq {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {first second : PackageTotalHom G.core H.core}
    (base_eq : first = second) (geometry : GeomReadHom G H second) :
    HEq
      (RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode.read
        (remainingSupplyOfGeometry (base_eq.symm ▸ geometry)))
      (RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode.read
        (remainingSupplyOfGeometry geometry)) := by
  cases base_eq
  rfl

/-- Coverage and overlap are local endpoint conditions over the independently
assembled package code.  The remaining computational fields use the Cycle 70
graph presentation. -/
structure CompleteGeometryGraphCode {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  package : PackageGraphCode G H
  coefficientHom : G.Coefficient →+* H.Coefficient
  coefficientGraph : AlgebraicGraphCoherence.RingHomGraphCode
    G.Coefficient H.Coefficient
  coefficient_graph_eq : coefficientGraph.assemble = coefficientHom
  remaining : RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode
    G H package.assemble coefficientHom
  remaining_canonical : remaining =
    RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode.read
      (remainingSupplyOfGeometry ({
        coverage := coverage
        overlap := overlap
        coefficientHom := coefficientHom
        raw_eq := remaining.assemble.rawCoherent
        supportComp := remaining.assemble.realization.supportComp
        axisComp := remaining.assemble.realization.axisComp
        observableComp := remaining.assemble.realization.observableComp
        supportReads := remaining.assemble.realization.supportReads
        axisReads := remaining.assemble.realization.axisReads
        observableReads := remaining.assemble.realization.observableReads
        support_naturality := remaining.assemble.realization.support_naturality
        axis_naturality := remaining.assemble.realization.axis_naturality
        observable_naturality := remaining.assemble.realization.observable_naturality } :
        GeomReadHom G H package.assemble))
  coverage : CoverageTransport G H package.assemble
  overlap : OverlapTransport G H package.assemble

namespace CompleteGeometryGraphCode

/-- Transporting a geometry hom along equality of its base leaves the
coefficient map unchanged. -/
theorem cast_coefficientHom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PackageTotalHom G.core H.core}
    (base_eq : first = second) (geometry : GeomReadHom G H second) :
    (base_eq.symm ▸ geometry).coefficientHom = geometry.coefficientHom := by
  cases base_eq
  rfl

/-- The support family is unchanged up to the dependent equality forced by
base transport. -/
theorem cast_supportComp_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PackageTotalHom G.core H.core}
    (base_eq : first = second) (geometry : GeomReadHom G H second) :
    HEq (base_eq.symm ▸ geometry).supportComp geometry.supportComp := by
  cases base_eq
  rfl

/-- The axis family is unchanged up to base transport. -/
theorem cast_axisComp_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PackageTotalHom G.core H.core}
    (base_eq : first = second) (geometry : GeomReadHom G H second) :
    HEq (base_eq.symm ▸ geometry).axisComp geometry.axisComp := by
  cases base_eq
  rfl

/-- The observable family is unchanged up to base transport. -/
theorem cast_observableComp_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PackageTotalHom G.core H.core}
    (base_eq : first = second) (geometry : GeomReadHom G H second) :
    HEq (base_eq.symm ▸ geometry).observableComp geometry.observableComp := by
  cases base_eq
  rfl

/-- Assemble all independent components into an actual complete geometry
morphism. -/
def assemble {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : CompleteGeometryGraphCode G H) : GeometryTotalHom G H where
  base := code.package.assemble
  geometry := {
    coverage := code.coverage
    overlap := code.overlap
    coefficientHom := code.coefficientHom
    raw_eq := code.remaining.assemble.rawCoherent
    supportComp := code.remaining.assemble.realization.supportComp
    axisComp := code.remaining.assemble.realization.axisComp
    observableComp := code.remaining.assemble.realization.observableComp
    supportReads := code.remaining.assemble.realization.supportReads
    axisReads := code.remaining.assemble.realization.axisReads
    observableReads := code.remaining.assemble.realization.observableReads
    support_naturality := code.remaining.assemble.realization.support_naturality
    axis_naturality := code.remaining.assemble.realization.axis_naturality
    observable_naturality :=
      code.remaining.assemble.realization.observable_naturality }

/-- Actual geometry data read relative to the package code reconstructed from
its base. -/
def read {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (morphism : GeometryTotalHom G H) : CompleteGeometryGraphCode G H := by
  let package := PackageGraphCode.read morphism.base
  have base_eq : package.assemble = morphism.base :=
    PackageGraphCode.assemble_read morphism.base
  let geometry : GeomReadHom G H package.assemble :=
    base_eq.symm ▸ morphism.geometry
  let coefficientGraph := AlgebraicGraphCoherence.RingHomGraphCode.read
    geometry.coefficientHom
  let remainingSupply := remainingSupplyOfGeometry geometry
  let remaining := RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode.read
    remainingSupply
  refine {
    package := package
    coefficientHom := geometry.coefficientHom
    coefficientGraph := coefficientGraph
    coefficient_graph_eq :=
      AlgebraicGraphCoherence.RingHomGraphCode.assemble_read _
    remaining := remaining
    remaining_canonical := ?_
    coverage := geometry.coverage
    overlap := geometry.overlap }
  · intro coverage overlap
    simp [remaining, remainingSupply, remainingSupplyOfGeometry]

/-- Reading and reassembling an actual complete morphism recovers it exactly. -/
@[simp]
theorem assemble_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    assemble (read morphism) = morphism := by
  apply GeometryTotalHom.ext
  · exact PackageGraphCode.assemble_read morphism.base
  · let package := PackageGraphCode.read morphism.base
    have base_eq : package.assemble = morphism.base :=
      PackageGraphCode.assemble_read morphism.base
    let geometry : GeomReadHom G H package.assemble :=
      base_eq.symm ▸ morphism.geometry
    have hlocal : (assemble (read morphism)).geometry = geometry := by
      apply GeometryTransport.GeomReadHom.ext
      · rfl
      · apply heq_of_eq
        simp [assemble, read, geometry, package, remainingSupplyOfGeometry]
      · apply heq_of_eq
        simp [assemble, read, geometry, package, remainingSupplyOfGeometry]
      · apply heq_of_eq
        simp [assemble, read, geometry, package, remainingSupplyOfGeometry]
    exact (heq_of_eq hlocal).trans (eqRec_heq base_eq.symm morphism.geometry)

/-- Overlap transports over a fixed base are unique because all selected
context categories are thin. -/
theorem overlap_ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {base : PackageTotalHom G.core H.core}
    (first second : OverlapTransport G H base) : first = second := by
  cases first with
  | mk firstIso =>
      cases second with
      | mk secondIso =>
          congr
          funext baseContext left right
          exact Subsingleton.elim _ _

/-- Complete codes are determined by their computational local inputs; all
coverage and canonicality witnesses are propositions, and overlap data are
unique in the thin target category. -/
theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {first second : CompleteGeometryGraphCode G H}
    (package : first.package = second.package)
    (coefficient : first.coefficientHom = second.coefficientHom)
    (coefficientGraph : first.coefficientGraph = second.coefficientGraph)
    (remaining : HEq first.remaining second.remaining) : first = second := by
  cases first
  cases second
  cases package
  cases coefficient
  cases coefficientGraph
  cases remaining
  congr
  exact overlap_ext _ _

/-- Assembling and rereading an independent complete code recovers every
graph and local condition. -/
@[simp]
theorem read_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : CompleteGeometryGraphCode G H) :
    read code.assemble = code := by
  let package' := PackageGraphCode.read code.package.assemble
  have base_eq : package'.assemble = code.package.assemble :=
    PackageGraphCode.assemble_read code.package.assemble
  let targetGeometry : GeomReadHom G H code.package.assemble :=
    code.assemble.geometry
  have coefficient_eq : (base_eq.symm ▸ targetGeometry).coefficientHom =
      code.coefficientHom :=
    cast_coefficientHom base_eq targetGeometry
  apply ext
  · exact PackageGraphCode.read_assemble code.package
  · simpa [read, assemble, package', targetGeometry] using coefficient_eq
  · calc
      (read code.assemble).coefficientGraph =
          AlgebraicGraphCoherence.RingHomGraphCode.read code.coefficientHom := by
            simp only [read, assemble]
            exact congrArg AlgebraicGraphCoherence.RingHomGraphCode.read
              coefficient_eq
      _ =
          AlgebraicGraphCoherence.RingHomGraphCode.read
            code.coefficientGraph.assemble := by rw [code.coefficient_graph_eq]
      _ = code.coefficientGraph :=
        AlgebraicGraphCoherence.RingHomGraphCode.read_assemble _
  · simpa only [read, assemble] using
      (remainingRead_cast_heq base_eq targetGeometry).trans
        (heq_of_eq code.remaining_canonical.symm)

/-- Exact two-sided equivalence promised by Cycle 71. -/
noncomputable def equivGeometryTotalHom {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} :
    CompleteGeometryGraphCode G H ≃ GeometryTotalHom G H where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Cycle 71 separation theorem.
Premise summary: there are no additional hypotheses; equality of the assembled
complete morphisms forces equality of every independent graph code and local
condition. -/
theorem assemble_injective {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} :
    Function.Injective
      (assemble : CompleteGeometryGraphCode G H → GeometryTotalHom G H) :=
  equivGeometryTotalHom.injective

/-- Cycle 71 common-surface connection.
Premise summary: a lawful independent code is the only input.  The result is
the repository's established graph reading of its assembled complete
morphism, rather than a second graph format. -/
noncomputable def completeMapGraphs {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : CompleteGeometryGraphCode G H) : CompleteMapGraphs G H :=
  readCompleteMapGraphs code.assemble

/-- Reading an actual complete morphism into the new independent code and
then exposing the common graph surface returns its original common reading.
Premise summary: no compatibility premise is added; the right inverse law of
complete assembly discharges the statement. -/
@[simp]
theorem completeMapGraphs_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    completeMapGraphs (read morphism) = readCompleteMapGraphs morphism := by
  simp [completeMapGraphs]

/-- The established common graph surface separates the new complete codes.
Premise summary: equality of all common graph components is the sole premise;
existing graph separation first recovers the assembled morphisms, and the new
left inverse then recovers the independent codes. -/
theorem completeMapGraphs_injective {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} :
    Function.Injective
      (completeMapGraphs : CompleteGeometryGraphCode G H → CompleteMapGraphs G H) := by
  intro first second graph_eq
  apply assemble_injective
  exact readCompleteMapGraphs_injective graph_eq

end CompleteGeometryGraphCode

end CompleteGeometryGraphAssembly

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly

end

end AAT.AG.LocalSemanticReconstruction
