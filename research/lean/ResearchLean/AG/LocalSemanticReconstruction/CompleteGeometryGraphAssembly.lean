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

## Implementation notes

The package code retains primitive graph families and local compatibility
laws only.  In particular, it does not retain an equation transport, a
package morphism, a geometry morphism, or a premise saying that the whole
input already lies in the image of a canonical reader.  Assembly constructs
those global maps.  Configuration morphisms are also constructed from the
Atom graph and the object-configuration equation rather than stored.  Both
inverse laws recover every input component, and the finite negative fixture
below shows that the Atom-agreement law rejects an independently altered
graph.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport
open CompleteGeometryFunctionGraphSeparation

noncomputable section

namespace CompleteGeometryGraphAssembly

universe u v w x

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

/-- Rebuilding a signature supply from all of its projections is exact. -/
theorem signatureSupply_eta
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (supply : RemainingComponentGraphCoherence.SignatureTransportSupply
      P Q objectMap) :
    ({ axisMap := supply.axisMap
       coordinateEquiv := supply.coordinateEquiv
       axis_selected_iff := supply.axis_selected_iff
       coordinate_eq := supply.coordinate_eq } :
      RemainingComponentGraphCoherence.SignatureTransportSupply
        P Q objectMap) = supply := by
  cases supply
  rfl

/-! ## Independent package code -/

/-- Computational package data assembled from the graph-code APIs of Cycles
67, 69, and 70.  All noncomputational compatibility statements are kept in
`IsPackageGraphCode`. -/
structure PackageGraphData {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  source : GraphCode G.core.reading.doctrine.Source
    H.core.reading.doctrine.Source
  pointedAtom : AlgebraicGraphCoherence.EquivGraphCode U.Atom U.Atom
  atom : AlgebraicGraphCoherence.EquivGraphCode U.Atom U.Atom
  object : GraphCode (ArchitectureObject U) (ArchitectureObject U)
  equation : AlgebraicGraphCoherence.EquivGraphCode
    G.core.algebra.equationSystem.Index H.core.algebra.equationSystem.Index
  contextObservable : ContextObservableGraphCoherence.ContextObservableGraphCode
    G.core.algebra.equationSystem H.core.algebra.equationSystem
  operation : RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode
    object.assemble object.assemble
    (fun A B => G.core.reading.operationReading.Op A B)
    (fun A B => H.core.reading.operationReading.Op A B)
  invariant : GraphCode G.core.reading.invariantReading.Index
    H.core.reading.invariantReading.Index
  signature : RemainingComponentGraphCoherence.SignatureGraphCode
    G.core H.core object.assemble

namespace PackageGraphData

/-- The equation transport assembled from Cycle 67 and Cycle 69 data, before
the equation-specific compatibility laws are attached. -/
def contextEquivalence {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (data : PackageGraphData G H) :
    G.site.category ≌ H.site.category :=
  data.contextObservable.context.assemble

/-- Construct the configuration morphism from the Atom graph and the local
object-configuration equation; no completed configuration morphism is stored
in `PackageGraphData`. -/
def configurationMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (data : PackageGraphData G H)
    (configuration_eq : ∀ A,
      (data.object.assemble A).configuration =
        A.configuration.transport data.atom.assemble)
    (A) :
    ConfigurationHom A.configuration (data.object.assemble A).configuration :=
  (configuration_eq A).symm ▸
    AtomConfiguration.transportHom data.atom.assemble A.configuration

/-- Casting only the target configuration of a configuration morphism does
not change its Atom function. -/
theorem configurationHom_cast_atomMap {U : AtomCarrier.{u}}
    {C D E : AtomConfiguration U} (target_eq : D = E)
    (morphism : ConfigurationHom C E) :
    ((target_eq.symm ▸ morphism : ConfigurationHom C D).atomMap) =
      morphism.atomMap := by
  cases target_eq
  rfl

/-- The locally constructed configuration morphism computes the Atom graph. -/
theorem configurationMap_atomMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (data : PackageGraphData G H)
    (configuration_eq : ∀ A,
      (data.object.assemble A).configuration =
        A.configuration.transport data.atom.assemble)
    (A) : (data.configurationMap configuration_eq A).atomMap =
      data.atom.assemble := by
  unfold configurationMap
  calc
    ((configuration_eq A).symm ▸
          AtomConfiguration.transportHom data.atom.assemble A.configuration :
        ConfigurationHom A.configuration
          (data.object.assemble A).configuration).atomMap =
        (AtomConfiguration.transportHom
          data.atom.assemble A.configuration).atomMap :=
      configurationHom_cast_atomMap (configuration_eq A) _
    _ = data.atom.assemble :=
      AtomConfiguration.transportHom_atomMap _ _

end PackageGraphData

/-- Local laws for `PackageGraphData`.  The fields mention only decoded graph
functions and fixed source/target packages; no completed package morphism is
used as a certificate. -/
structure IsPackageGraphCode {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (data : PackageGraphData G H) : Prop where
  equation_role_eq : ∀ i,
    H.core.algebra.equationSystem.role (data.equation.assemble i) =
      G.core.algebra.equationSystem.role i
  violationCoordinate_eq : ∀ W i atom,
    data.contextObservable.observable.1.observable.assemble W
        (G.core.algebra.equationSystem.violationCoordinate W i atom) =
      H.core.algebra.equationSystem.violationCoordinate
        (data.contextObservable.context.assemble.functor.obj W)
        (data.equation.assemble i) (data.atom.assemble atom)
  equationResidual_eq : ∀ W A i atom,
    data.contextObservable.observable.1.observable.assemble W
        (G.core.algebra.equationSystem.equationResidual W A i atom) =
      H.core.algebra.equationSystem.equationResidual
        (data.contextObservable.context.assemble.functor.obj W)
        (data.object.assemble A) (data.equation.assemble i)
        (data.atom.assemble atom)
  normalize_eq : ∀ source,
    H.core.reading.doctrine.normalize (data.source.assemble source) =
      data.source.assemble (G.core.reading.doctrine.normalize source)
  extraction_iff : ∀ source atom,
    G.core.reading.doctrine.extracts source atom ↔
      H.core.reading.doctrine.extracts (data.source.assemble source)
        (data.pointedAtom.assemble atom)
  source_eq : data.source.assemble G.core.reading.source = H.core.reading.source
  atom_eq : data.atom.assemble = data.pointedAtom.assemble
  extraction_eq : H.core.family = G.core.family.transport data.atom.assemble
  composition_eq : ∀ (F : AtomFamily U) (hF : F.ListFinite),
    H.core.reading.composition.compose
        (F.transport data.atom.assemble) (hF.transport data.atom.assemble) =
      (G.core.reading.composition.compose F hF).transport data.atom.assemble
  object_formation_eq : ∀ C,
    data.object.assemble (G.core.reading.objectReading.object C) =
      H.core.reading.objectReading.object (C.transport data.atom.assemble)
  configuration_eq : ∀ A,
    (data.object.assemble A).configuration =
      A.configuration.transport data.atom.assemble
  detectorCode_eq : ∀ i,
    H.core.algebra.circuits.code (data.equation.assemble i) =
      (G.core.algebra.circuits.code i).transport data.atom.assemble
  operation_naturality : RemainingComponentGraphCoherence.IsOperationNatural
    G.core H.core data.object.assemble
      (data.configurationMap configuration_eq)
      data.operation.assemble
  invariant_transport : RemainingComponentGraphCoherence.IsInvariantTransport
    G.core H.core data.object.assemble data.invariant.assemble
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
        (data.object.assemble A)
        ((RemainingComponentGraphCoherence.SignatureGraphCode.assemble
          data.signature).axisMap i)

/-- Independent package graph code. -/
abbrev PackageGraphCode {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) :=
  { data : PackageGraphData G H // IsPackageGraphCode data }

namespace PackageGraphCode

/-- Dependent congruence exposed as heterogeneous equality. -/
theorem dependent_apply_heq {A : Type*} {B : A → Type*}
    {first second : A} (index_eq : first = second) (value : ∀ index, B index) :
    HEq (value first) (value second) := by
  cases index_eq
  rfl

/-- Reindex one target operation family along equality of its object map. -/
def reindexOperationFamily {U : AtomCarrier.{u}}
    (Q : AATCorePackage U)
    {X : ArchitectureObject U → ArchitectureObject U → Type*}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (family : ∀ A B, X A B →
      Q.reading.operationReading.Op (second A) (second B)) :
    ∀ A B, X A B → Q.reading.operationReading.Op (first A) (first B) := by
  cases object_eq
  exact family

/-- Reindexing a dependent operation family is heterogeneously equal to the
original family. -/
theorem reindexOperationFamily_heq {U : AtomCarrier.{u}}
    (Q : AATCorePackage U)
    {X : ArchitectureObject U → ArchitectureObject U → Type*}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (family : ∀ A B, X A B →
      Q.reading.operationReading.Op (second A) (second B)) :
    HEq (reindexOperationFamily Q object_eq family) family := by
  cases object_eq
  rfl

/-- Reading a reindexed dependent operation family agrees heterogeneously
with reading the original family. -/
theorem read_reindexOperationFamily_heq {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (family : ∀ A B, P.reading.operationReading.Op A B →
      Q.reading.operationReading.Op (second A) (second B)) :
    HEq
      (RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.read
        (reindexOperationFamily Q object_eq family))
      (RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.read
        family) := by
  cases object_eq
  rfl

/-- Reindexing an operation does not change the Atom map of its attached
configuration morphism. -/
theorem reindexOperationFamily_configuration_atomMap
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    {X : ArchitectureObject U → ArchitectureObject U → Type*}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (family : ∀ A B, X A B →
      Q.reading.operationReading.Op (second A) (second B))
    (A B) (value : X A B) :
    (Q.reading.operationReading.configurationMap
      (reindexOperationFamily Q object_eq family A B value)).atomMap =
    (Q.reading.operationReading.configurationMap
      (family A B value)).atomMap := by
  cases object_eq
  rfl

/-- Reindexing an observable graph code changes only its functor index, not
the value computed at a source context. -/
theorem reindexObservable_apply_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : G.site.category ⥤ H.site.category}
    (functor_eq : first = second)
    (code : ContextObservableGraphCoherence.ObservablePresheafGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem second)
    (W) (value : G.core.algebra.equationSystem.Observable W) :
    HEq
      ((ContextObservableGraphCoherence.ObservablePresheafGraphCode.reindex
        functor_eq code).1.observable.assemble W value)
      (code.1.observable.assemble W value) := by
  cases functor_eq
  rfl

/-- The observable component read from an actual equation transport agrees
with the original component up to the context-functor transport. -/
theorem readObservable_apply_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      atomEquiv objectMap)
    (W) (value : G.core.algebra.equationSystem.Observable W) :
    HEq
      ((ContextObservableGraphCoherence.ContextObservableGraphCode.read
        transport).observable.1.observable.assemble W value)
      (transport.observableEquiv W value) := by
  let context := ContextObservableGraphCoherence.ThinEquivalenceGraphCode.read
    transport.contextEquivalence
  have functor_eq : context.forwardFunctor = transport.contextFunctor :=
    congrArg CategoryTheory.Equivalence.functor
      (ContextObservableGraphCoherence.ThinEquivalenceGraphCode.assemble_read _)
  let observable :=
    ContextObservableGraphCoherence.ObservablePresheafGraphCode.readTransport
      transport
  have hreindex := reindexObservable_apply_heq functor_eq observable W value
  have hassemble :=
    ContextObservableGraphCoherence.ObservablePresheafGraphCode.readTransport_observable_assemble
      transport W
  exact hreindex.trans (heq_of_eq (congrArg (fun equivalence => equivalence value)
    hassemble))

/-- The target observable selected by the context code read from a transport
agrees heterogeneously with the original target observable. -/
theorem readContext_violation_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      atomEquiv objectMap)
    (W) (i) (atom : U.Atom) :
    HEq
      (H.core.algebra.equationSystem.violationCoordinate
        ((ContextObservableGraphCoherence.ContextObservableGraphCode.read
          transport).context.assemble.functor.obj W)
        (transport.equationEquiv i) (atomEquiv atom))
      (H.core.algebra.equationSystem.violationCoordinate
        (transport.contextEquivalence.functor.obj W)
        (transport.equationEquiv i) (atomEquiv atom)) := by
  have hcontext :=
    ContextObservableGraphCoherence.ContextObservableGraphCode.read_context_assemble
      transport
  exact dependent_apply_heq
    (congrArg (fun equivalence => equivalence.functor.obj W) hcontext)
    (fun context => H.core.algebra.equationSystem.violationCoordinate
      context (transport.equationEquiv i) (atomEquiv atom))

/-- Residual generators obey the same heterogeneous context-read recovery. -/
theorem readContext_residual_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      atomEquiv objectMap)
    (W) (A) (i) (atom : U.Atom) :
    HEq
      (H.core.algebra.equationSystem.equationResidual
        ((ContextObservableGraphCoherence.ContextObservableGraphCode.read
          transport).context.assemble.functor.obj W)
        (objectMap A) (transport.equationEquiv i) (atomEquiv atom))
      (H.core.algebra.equationSystem.equationResidual
        (transport.contextEquivalence.functor.obj W)
        (objectMap A) (transport.equationEquiv i) (atomEquiv atom)) := by
  have hcontext :=
    ContextObservableGraphCoherence.ContextObservableGraphCode.read_context_assemble
      transport
  exact dependent_apply_heq
    (congrArg (fun equivalence => equivalence.functor.obj W) hcontext)
    (fun context => H.core.algebra.equationSystem.equationResidual
      context (objectMap A) (transport.equationEquiv i) (atomEquiv atom))

/-- Canonical configuration map forced by the Atom graph and the decoded
object-configuration equation. -/
def configurationMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : PackageGraphCode G H) (A) :
    ConfigurationHom A.configuration (code.1.object.assemble A).configuration :=
  code.1.configurationMap code.2.configuration_eq A

/-- The constructed configuration morphism has exactly the decoded Atom map. -/
theorem configurationMap_atomMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : PackageGraphCode G H) (A) :
    (code.configurationMap A).atomMap = code.1.atom.assemble := by
  exact code.1.configurationMap_atomMap code.2.configuration_eq A

/-- Assemble the Cycle 69 equation transport from its independent context and
observable graphs and the equation-specific local laws. -/
def equationTransport {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (code : PackageGraphCode G H) :
    EquationSystemExactTransport G.core.algebra.equationSystem
      H.core.algebra.equationSystem code.1.atom.assemble
      code.1.object.assemble where
  contextEquivalence := code.1.contextObservable.context.assemble
  equationEquiv := code.1.equation.assemble
  role_eq := code.2.equation_role_eq
  observableEquiv := code.1.contextObservable.observable.1.observable.assemble
  observable_naturality := code.1.contextObservable.observable.2.observable_naturality
  violationCoordinate_eq := code.2.violationCoordinate_eq
  equationResidual_eq := code.2.equationResidual_eq

/-- Reading the equation transport assembled from a package code recovers its
independent context and observable graph codes. -/
theorem contextObservable_ext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : ContextObservableGraphCoherence.ContextObservableGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem}
    (context : first.context = second.context)
    (observable : HEq first.observable second.observable) : first = second := by
  cases first
  cases second
  cases context
  cases observable
  rfl

/-- Observable graph codes over propositionally equal context functors are
heterogeneously equal when their computational ring graphs agree. -/
theorem observableCode_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {firstFunctor secondFunctor :
      CategoryTheory.Functor
        (Site.ContextCategoryObject G.core.algebra.contextPreorder)
        (Site.ContextCategoryObject H.core.algebra.contextPreorder)}
    (functor_eq : firstFunctor = secondFunctor)
    (first : ContextObservableGraphCoherence.ObservablePresheafGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem firstFunctor)
    (second : ContextObservableGraphCoherence.ObservablePresheafGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem secondFunctor)
    (observable : HEq first.1.observable second.1.observable) :
    HEq first second := by
  cases functor_eq
  rcases first with ⟨⟨firstObservable⟩, firstLaw⟩
  rcases second with ⟨⟨secondObservable⟩, secondLaw⟩
  change HEq firstObservable secondObservable at observable
  cases observable
  rfl

/-- Reindexing an observable code changes only its dependent functor index. -/
theorem observableCode_reindex_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {firstFunctor secondFunctor :
      CategoryTheory.Functor
        (Site.ContextCategoryObject G.core.algebra.contextPreorder)
        (Site.ContextCategoryObject H.core.algebra.contextPreorder)}
    (functor_eq : firstFunctor = secondFunctor)
    (code : ContextObservableGraphCoherence.ObservablePresheafGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem secondFunctor) :
    HEq
      (ContextObservableGraphCoherence.ObservablePresheafGraphCode.reindex
        functor_eq code) code := by
  cases functor_eq
  rfl

/-- Pointwise ring graph families over equal index maps are heterogeneously
equal when every fiber graph is. -/
theorem indexedRingGraph_heq
    {I J : Type*} {A : I → Type*} {B : J → Type*}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    {firstIndex secondIndex : I → J}
    (index_eq : firstIndex = secondIndex)
    (first : DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode
      firstIndex A B)
    (second : DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode
      secondIndex A B)
    (fiber : ∀ i, HEq (first i) (second i)) : HEq first second := by
  cases index_eq
  apply heq_of_eq
  funext i
  exact eq_of_heq (fiber i)

theorem contextObservable_read_equationTransport
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) :
    ContextObservableGraphCoherence.ContextObservableGraphCode.read
      code.equationTransport = code.1.contextObservable := by
  apply contextObservable_ext
  · exact ContextObservableGraphCoherence.ThinEquivalenceGraphCode.read_assemble _
  · let context :=
      ContextObservableGraphCoherence.ThinEquivalenceGraphCode.read
        code.equationTransport.contextEquivalence
    have functor_eq : context.forwardFunctor =
        code.equationTransport.contextFunctor :=
      congrArg CategoryTheory.Equivalence.functor
        (ContextObservableGraphCoherence.ThinEquivalenceGraphCode.assemble_read _)
    let readObservable :=
      ContextObservableGraphCoherence.ObservablePresheafGraphCode.readTransport
        code.equationTransport
    have hreindex : HEq
        (ContextObservableGraphCoherence.ObservablePresheafGraphCode.reindex
          functor_eq readObservable) readObservable := by
      exact observableCode_reindex_heq functor_eq readObservable
    have hfunctor : code.equationTransport.contextFunctor =
        code.1.contextObservable.context.forwardFunctor := rfl
    have hgraph : HEq readObservable.1.observable
        code.1.contextObservable.observable.1.observable := by
      apply indexedRingGraph_heq
        (congrArg CategoryTheory.Functor.obj hfunctor)
      intro W
      exact heq_of_eq
        (DependentAlgebraicGraphCoherence.RingEquivGraphCode.read_assemble _)
    exact hreindex.trans
      (observableCode_heq hfunctor readObservable
        code.1.contextObservable.observable hgraph)

/-- Equation transports are determined by their three computational
components; all remaining fields are propositions. -/
theorem equationTransport_ext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {first second : EquationSystemExactTransport
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      atomEquiv objectMap}
    (context : first.contextEquivalence = second.contextEquivalence)
    (equation : first.equationEquiv = second.equationEquiv)
    (observable : HEq first.observableEquiv second.observableEquiv) :
    first = second := by
  cases first
  cases second
  cases context
  cases equation
  cases observable
  rfl

/-- Equation transports over propositionally equal Atom and object maps are
heterogeneously equal when their three computational components agree. -/
theorem equationTransport_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {firstAtom secondAtom : U.Atom ≃ U.Atom}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (atom_eq : firstAtom = secondAtom)
    (object_eq : firstObject = secondObject)
    (first : EquationSystemExactTransport
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      firstAtom firstObject)
    (second : EquationSystemExactTransport
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      secondAtom secondObject)
    (context : first.contextEquivalence = second.contextEquivalence)
    (equation : first.equationEquiv = second.equationEquiv)
    (observable : ∀ W value,
      HEq (first.observableEquiv W value)
        (second.observableEquiv W value)) :
    HEq first second := by
  cases atom_eq
  cases object_eq
  rcases first with ⟨firstContext, firstEquation, firstRole,
    firstObservable, firstNaturality, firstViolation, firstResidual⟩
  rcases second with ⟨secondContext, secondEquation, secondRole,
    secondObservable, secondNaturality, secondViolation, secondResidual⟩
  cases context
  cases equation
  congr 1
  funext W
  apply RingEquiv.ext
  intro value
  exact eq_of_heq (observable W value)

/-- Signature readings over propositionally equal object maps agree
heterogeneously once their two computational families agree. -/
theorem signatureRead_heq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (object_eq : firstObject = secondObject)
    (first : RemainingComponentGraphCoherence.SignatureTransportSupply
      P Q firstObject)
    (second : RemainingComponentGraphCoherence.SignatureTransportSupply
      P Q secondObject)
    (axis : first.axisMap = second.axisMap)
    (coordinate : HEq first.coordinateEquiv second.coordinateEquiv) :
    HEq
      (RemainingComponentGraphCoherence.SignatureGraphCode.read first)
      (RemainingComponentGraphCoherence.SignatureGraphCode.read second) := by
  cases object_eq
  have supply_eq : first = second :=
    RemainingComponentGraphCoherence.SignatureGraphCode.supply_ext
      axis coordinate
  cases supply_eq
  rfl

/-- Assemble the complete upper core morphism from independent graph data. -/
def upper {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : SignedExactCoreReadingHom G.core H.core where
  atomEquiv := code.1.atom.assemble
  extraction_eq := code.2.extraction_eq
  composition_eq := code.2.composition_eq
  objectMap := code.1.object.assemble
  object_formation_eq := code.2.object_formation_eq
  configurationMap := code.configurationMap
  configurationMap_atomMap := code.configurationMap_atomMap
  configuration_eq := code.2.configuration_eq
  equationTransport := code.equationTransport
  detectorCode_eq i := by
    change H.core.algebra.circuits.code
      (code.1.equation.assemble i) = _
    exact code.2.detectorCode_eq i
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
    atomEquiv := code.1.pointedAtom.assemble
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

/-- Lawful package codes are determined by their graph components.  The
configuration maps are then forced by their common Atom graph. -/
theorem ext {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PackageGraphCode G H}
    (source : first.1.source = second.1.source)
    (pointedAtom : first.1.pointedAtom = second.1.pointedAtom)
    (atom : first.1.atom = second.1.atom)
    (object : first.1.object = second.1.object)
    (equation : first.1.equation = second.1.equation)
    (contextObservable : HEq first.1.contextObservable second.1.contextObservable)
    (operation : HEq first.1.operation second.1.operation)
    (invariant : first.1.invariant = second.1.invariant)
    (signature : HEq first.1.signature second.1.signature) : first = second := by
  rcases first with ⟨⟨firstSource, firstPointed, firstAtom, firstObject,
    firstEquation, firstContext, firstOperation,
    firstInvariant, firstSignature⟩, firstLaw⟩
  rcases second with ⟨⟨secondSource, secondPointed, secondAtom, secondObject,
    secondEquation, secondContext, secondOperation,
    secondInvariant, secondSignature⟩, secondLaw⟩
  change firstSource = secondSource at source
  change firstPointed = secondPointed at pointedAtom
  change firstAtom = secondAtom at atom
  change firstObject = secondObject at object
  change firstEquation = secondEquation at equation
  change HEq firstContext secondContext at contextObservable
  change HEq firstOperation secondOperation at operation
  change firstInvariant = secondInvariant at invariant
  change HEq firstSignature secondSignature at signature
  cases source
  cases pointedAtom
  cases atom
  cases object
  cases equation
  cases contextObservable
  cases operation
  cases invariant
  cases signature
  rfl

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
  have pointed_eq : pointedAtomGraph.assemble =
      morphism.base.doctrineHom.atomEquiv :=
    AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  have atom_eq : atomGraph.assemble = morphism.upper.atomEquiv :=
    AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  have object_eq : objectGraph.assemble = morphism.upper.objectMap :=
    PrimitiveFunctionGraph.GraphCode.assemble_read _
  let equation := AlgebraicGraphCoherence.EquivGraphCode.read
    morphism.upper.equationTransport.equationEquiv
  let contextObservable := ContextObservableGraphCoherence.ContextObservableGraphCode.read
    morphism.upper.equationTransport
  let operationFamily : ∀ A B, G.core.reading.operationReading.Op A B →
      H.core.reading.operationReading.Op
        (objectGraph.assemble A) (objectGraph.assemble B) :=
    reindexOperationFamily H.core object_eq
      (fun A B op => @morphism.upper.operationMap A B op)
  let operation : RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode
      objectGraph.assemble objectGraph.assemble
      (fun A B => G.core.reading.operationReading.Op A B)
      (fun A B => H.core.reading.operationReading.Op A B) := by
    exact RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.read
      operationFamily
  let invariant := PrimitiveFunctionGraph.GraphCode.read morphism.upper.invariantMap
  let signatureSupply : RemainingComponentGraphCoherence.SignatureTransportSupply
      G.core H.core objectGraph.assemble := {
    axisMap := morphism.upper.axisMap
    coordinateEquiv := morphism.upper.coordinateEquiv
    axis_selected_iff := morphism.upper.axis_selected_iff
    coordinate_eq := by
      intro A i
      rw [object_eq]
      exact morphism.upper.coordinate_eq A i }
  let signature : RemainingComponentGraphCoherence.SignatureGraphCode
      G.core H.core objectGraph.assemble :=
    RemainingComponentGraphCoherence.SignatureGraphCode.read signatureSupply
  have equation_eq : equation.assemble =
      morphism.upper.equationTransport.equationEquiv :=
    AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  have context_eq : contextObservable.context.assemble =
      morphism.upper.equationTransport.contextEquivalence :=
    ContextObservableGraphCoherence.ContextObservableGraphCode.read_context_assemble _
  have configuration_eq : ∀ A,
      (objectGraph.assemble A).configuration =
        A.configuration.transport atomGraph.assemble := by
    intro A
    rw [atom_eq, object_eq]
    exact morphism.upper.configuration_eq A
  let data : PackageGraphData G H := {
    source := source
    pointedAtom := pointedAtomGraph
    atom := atomGraph
    object := objectGraph
    equation := equation
    contextObservable := contextObservable
    operation := operation
    invariant := invariant
    signature := signature }
  refine ⟨data, {
    equation_role_eq := ?_
    violationCoordinate_eq := ?_
    equationResidual_eq := ?_
    normalize_eq := ?_
    extraction_iff := ?_
    source_eq := ?_
    atom_eq := ?_
    extraction_eq := ?_
    composition_eq := ?_
    object_formation_eq := ?_
    configuration_eq := configuration_eq
    detectorCode_eq := ?_
    operation_naturality := ?_
    invariant_transport := ?_
    axis_selected_iff := ?_
    coordinate_eq := ?_ }⟩
  · dsimp only [data]
    rw [equation_eq]
    exact morphism.upper.equationTransport.role_eq
  · dsimp [data]
    intro W i atom
    change contextObservable.observable.1.observable.assemble W
        (G.core.algebra.equationSystem.violationCoordinate W i atom) =
      H.core.algebra.equationSystem.violationCoordinate
        (contextObservable.context.assemble.functor.obj W)
        (equation.assemble i) (atomGraph.assemble atom)
    rw [equation_eq, atom_eq]
    apply eq_of_heq
    exact (readObservable_apply_heq
      morphism.upper.equationTransport W
        (G.core.algebra.equationSystem.violationCoordinate W i atom)).trans
      ((heq_of_eq
        (morphism.upper.equationTransport.violationCoordinate_eq W i atom)).trans
        (readContext_violation_heq
          morphism.upper.equationTransport W i atom).symm)
  · dsimp [data]
    intro W A i atom
    change contextObservable.observable.1.observable.assemble W
        (G.core.algebra.equationSystem.equationResidual W A i atom) =
      H.core.algebra.equationSystem.equationResidual
        (contextObservable.context.assemble.functor.obj W)
        (objectGraph.assemble A) (equation.assemble i)
        (atomGraph.assemble atom)
    rw [equation_eq, atom_eq, object_eq]
    apply eq_of_heq
    exact (readObservable_apply_heq
      morphism.upper.equationTransport W
        (G.core.algebra.equationSystem.equationResidual W A i atom)).trans
      ((heq_of_eq
        (morphism.upper.equationTransport.equationResidual_eq W A i atom)).trans
        (readContext_residual_heq
          morphism.upper.equationTransport W A i atom).symm)
  · simpa [data, source] using morphism.base.doctrineHom.normalize_eq
  · dsimp [data]
    change ∀ sourceValue atom,
      G.core.reading.doctrine.extracts sourceValue atom ↔
        H.core.reading.doctrine.extracts (source.assemble sourceValue)
          (pointedAtomGraph.assemble atom)
    rw [pointed_eq]
    simpa [source] using morphism.base.doctrineHom.extraction_iff
  · simpa [data, source] using morphism.base.source_eq
  · dsimp [data]
    rw [atom_eq, pointed_eq]
    exact morphism.atomEquiv_eq
  · dsimp [data]
    rw [atom_eq]
    exact morphism.upper.extraction_eq
  · dsimp [data]
    rw [atom_eq]
    exact morphism.upper.composition_eq
  · dsimp [data]
    rw [atom_eq, object_eq]
    exact morphism.upper.object_formation_eq
  · dsimp [data]
    change ∀ i,
      H.core.algebra.circuits.code (equation.assemble i) =
        (G.core.algebra.circuits.code i).transport atomGraph.assemble
    rw [equation_eq, atom_eq]
    exact morphism.upper.detectorCode_eq
  · dsimp [data]
    change RemainingComponentGraphCoherence.IsOperationNatural
      G.core H.core objectGraph.assemble
        (PackageGraphData.configurationMap data configuration_eq)
        operation.assemble
    rw [show operation.assemble = operationFamily by
      exact RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.assemble_read _]
    intro A B op
    have law := morphism.upper.operation_naturality op
    apply ConfigurationHom.ext
    simp only [ConfigurationHom.comp]
    rw [PackageGraphData.configurationMap_atomMap,
      PackageGraphData.configurationMap_atomMap]
    have supplied := congrArg ConfigurationHom.atomMap law
    funext input
    have operation_atom := congrFun
      (reindexOperationFamily_configuration_atomMap H.core object_eq
        (fun A B op => @morphism.upper.operationMap A B op) A B op)
      (atomGraph.assemble input)
    change
      (H.core.reading.operationReading.configurationMap
        (reindexOperationFamily H.core object_eq
          (fun A B op => @morphism.upper.operationMap A B op) A B op)).atomMap
          (atomGraph.assemble input) =
        atomGraph.assemble
          ((G.core.reading.operationReading.configurationMap op).atomMap input)
    rw [operation_atom, atom_eq]
    have supplied_at := congrFun supplied input
    simpa [ConfigurationHom.comp, Function.comp_apply,
      PackageGraphData.configurationMap,
      morphism.upper.configurationMap_atomMap]
      using supplied_at
  · dsimp [data]
    rw [object_eq]
    simpa [invariant] using morphism.upper.invariant_transport
  · dsimp [data]
    rw [show signature.assemble = signatureSupply by
      exact RemainingComponentGraphCoherence.SignatureGraphCode.assemble_read _]
    exact signatureSupply.axis_selected_iff
  · dsimp [data]
    rw [show signature.assemble = signatureSupply by
      exact RemainingComponentGraphCoherence.SignatureGraphCode.assemble_read _]
    exact signatureSupply.coordinate_eq

/-- The equation transport assembled after reading an actual package map
recovers the original completed transport. -/
theorem equationTransport_read
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (morphism : PackageTotalHom G.core H.core) :
    HEq (read morphism).equationTransport
      morphism.upper.equationTransport := by
  apply equationTransport_heq
    (AlgebraicGraphCoherence.EquivGraphCode.assemble_read _)
    (PrimitiveFunctionGraph.GraphCode.assemble_read _)
  · exact ContextObservableGraphCoherence.ContextObservableGraphCode.read_context_assemble _
  · exact AlgebraicGraphCoherence.EquivGraphCode.assemble_read _
  · intro W value
    exact readObservable_apply_heq
      morphism.upper.equationTransport W value

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
    · simp [assemble, upper, read]
    · exact equationTransport_read morphism
    · simpa [assemble, upper, read] using
        (reindexOperationFamily_heq H.core
          (PrimitiveFunctionGraph.GraphCode.assemble_read
            morphism.upper.objectMap)
          (fun A B op => @morphism.upper.operationMap A B op))
    · simp [assemble, upper, read]
    · simp [assemble, upper, read]
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
  apply ext
  · exact PrimitiveFunctionGraph.GraphCode.read_assemble _
  · exact AlgebraicGraphCoherence.EquivGraphCode.read_assemble _
  · exact AlgebraicGraphCoherence.EquivGraphCode.read_assemble _
  · exact PrimitiveFunctionGraph.GraphCode.read_assemble _
  · exact AlgebraicGraphCoherence.EquivGraphCode.read_assemble _
  · exact heq_of_eq (contextObservable_read_equationTransport code)
  · let object_eq := PrimitiveFunctionGraph.GraphCode.assemble_read
      code.1.object.assemble
    exact (read_reindexOperationFamily_heq G.core H.core object_eq
      (fun A B op => code.1.operation.assemble A B op)).trans
      (heq_of_eq
        (RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.read_assemble
          code.1.operation))
  · exact PrimitiveFunctionGraph.GraphCode.read_assemble _
  · simp only [read, assemble, upper]
    apply HEq.trans ?_
      (heq_of_eq
        (RemainingComponentGraphCoherence.SignatureGraphCode.read_assemble
          code.1.signature))
    apply signatureRead_heq
      (PrimitiveFunctionGraph.GraphCode.assemble_read
        code.1.object.assemble)
    · rfl
    · exact HEq.rfl

end PackageGraphCode

/-! ## Refutation-control fixture -/

namespace PackageGraphNegativeFixture

abbrev package := GeometryTransport.FiniteGeometryWitness.package

/-- Lawful identity reading used only as the baseline for the negative
certificate fixture. -/
noncomputable def identityCode : PackageGraphCode package package :=
  PackageGraphCode.read (PackageTotalHom.id package.core)

/-- Independently replace only the pointed Atom graph by the concrete finite
swap, leaving the upper Atom graph unchanged. -/
noncomputable def mismatchedPointedData : PackageGraphData package package :=
  { identityCode.1 with
    pointedAtom := AlgebraicGraphCoherence.EquivGraphCode.read
      GeometryTransport.FiniteGeometryWitness.swapEquiv }

/-- The local package certificate rejects the mismatched Atom graphs. -/
theorem not_isPackageGraphCode_mismatchedPointed :
    ¬ IsPackageGraphCode mismatchedPointedData := by
  intro certificate
  have atomFunction := congrArg Equiv.toFun certificate.atom_eq
  have atA := congrFun atomFunction
    FiniteModel.FiniteAtom.componentA
  simp [mismatchedPointedData, identityCode, PackageGraphCode.read,
    PackageTotalHom.id, SignedExactCoreReadingHom.refl,
    GeometryTransport.FiniteGeometryWitness.swapEquiv,
    GeometryTransport.FiniteGeometryWitness.swapAtom] at atA

end PackageGraphNegativeFixture

/-! ## Complete geometry code and two-sided assembly -/

/-- The fiberwise realization part of a geometry-stage hom, without the core
operation, invariant, and signature fields already owned by the package code. -/
def realizationSupplyOfGeometry {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {base : PackageTotalHom G.core H.core}
    (geometry : GeomReadHom G H base) :
    RealizationTransportSupply G.core H.core base where
  supportComp := geometry.supportComp
  axisComp := geometry.axisComp
  observableComp := geometry.observableComp
  supportReads := geometry.supportReads
  axisReads := geometry.axisReads
  observableReads := geometry.observableReads
  support_naturality := geometry.support_naturality
  axis_naturality := geometry.axis_naturality
  observable_naturality := geometry.observable_naturality

/-- Realization reading commutes heterogeneously with transport of the package
base index. -/
theorem realizationRead_cast_heq {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {first second : PackageTotalHom G.core H.core}
    (base_eq : first = second) (geometry : GeomReadHom G H second) :
    HEq
      (RemainingComponentGraphCoherence.RealizationGraphCode.read
        (realizationSupplyOfGeometry (base_eq.symm ▸ geometry)))
      (RemainingComponentGraphCoherence.RealizationGraphCode.read
        (realizationSupplyOfGeometry geometry)) := by
  cases base_eq
  rfl

/-! ## Primitive overlap comparisons -/

/-- Source overlap object selected by the independently assembled base map. -/
abbrev overlapSource {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (baseHom : PackageTotalHom G.core H.core)
    (base left right : Site.ArchCtx H.core.object) :=
  contextForward baseHom
    ⟨G.geometry.overlap.overlap
      (contextBackwardMap baseHom base)
      (contextBackwardMap baseHom left)
      (contextBackwardMap baseHom right)⟩

/-- Target overlap object selected at the endpoint package. -/
abbrev overlapTarget {U : AtomCarrier.{u}}
    {H : GeometryPackage.{u, v} U}
    (base left right : Site.ArchCtx H.core.object) :
    Site.ContextCategoryObject H.core.contextPreorder :=
  ⟨H.geometry.overlap.overlap base left right⟩

/-- Assemble the two order comparisons into the standard selected overlap
isomorphism. -/
noncomputable def assembleOverlap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    (forward : ∀ base left right,
      overlapSource baseHom base left right ≤ overlapTarget base left right)
    (backward : ∀ base left right,
      overlapTarget base left right ≤ overlapSource baseHom base left right) :
    OverlapTransport G H baseHom where
  overlapIso base left right := {
    hom := homOfLE (forward base left right)
    inv := homOfLE (backward base left right) }

/-- Coverage remains an explicit premise certificate, while overlap is retained
only as two local order comparisons over the independently assembled package
code. The remaining computational fields use the Cycle 70 graph presentation. -/
structure CompleteGeometryGraphCode {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  package : PackageGraphCode G H
  coefficientGraph : AlgebraicGraphCoherence.RingHomGraphCode
    G.Coefficient H.Coefficient
  coverage : CoverageTransport G H package.assemble
  overlapForward : ∀ base left right,
    overlapSource package.assemble base left right ≤ overlapTarget base left right
  overlapBackward : ∀ base left right,
    overlapTarget base left right ≤ overlapSource package.assemble base left right
  realization : RemainingComponentGraphCoherence.RealizationGraphCode
    G.core H.core package.assemble
  rawCoherent :
    RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.IsRawTransportCoherent
    G H package.assemble coefficientGraph.assemble

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
    overlap := assembleOverlap code.overlapForward code.overlapBackward
    coefficientHom := code.coefficientGraph.assemble
    raw_eq := code.rawCoherent
    supportComp := code.realization.assemble.supportComp
    axisComp := code.realization.assemble.axisComp
    observableComp := code.realization.assemble.observableComp
    supportReads := code.realization.assemble.supportReads
    axisReads := code.realization.assemble.axisReads
    observableReads := code.realization.assemble.observableReads
    support_naturality := code.realization.assemble.support_naturality
    axis_naturality := code.realization.assemble.axis_naturality
    observable_naturality :=
      code.realization.assemble.observable_naturality }

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
  have coefficient_eq : coefficientGraph.assemble = geometry.coefficientHom :=
    AlgebraicGraphCoherence.RingHomGraphCode.assemble_read _
  let geometry' : GeomReadHom G H package.assemble := {
    geometry with
    coefficientHom := coefficientGraph.assemble
    raw_eq := by rw [coefficient_eq]; exact geometry.raw_eq }
  let realization := RemainingComponentGraphCoherence.RealizationGraphCode.read
    (realizationSupplyOfGeometry geometry')
  refine {
    package := package
    coefficientGraph := coefficientGraph
    coverage := geometry.coverage
    overlapForward := fun base left right =>
      leOfHom (geometry.overlap.overlapIso base left right).hom
    overlapBackward := fun base left right =>
      leOfHom (geometry.overlap.overlapIso base left right).inv
    realization := realization
    rawCoherent := geometry'.raw_eq }

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
      · simp [assemble, read, geometry, package]
      · apply heq_of_eq
        simp [assemble, read, geometry, package, realizationSupplyOfGeometry]
      · apply heq_of_eq
        simp [assemble, read, geometry, package, realizationSupplyOfGeometry]
      · apply heq_of_eq
        simp [assemble, read, geometry, package, realizationSupplyOfGeometry]
    exact (heq_of_eq hlocal).trans (eqRec_heq base_eq.symm morphism.geometry)

/-- Complete codes are determined by their computational local inputs; all
coverage and canonicality witnesses are propositions, and overlap data are
unique in the thin target category. -/
theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {first second : CompleteGeometryGraphCode G H}
    (package : first.package = second.package)
    (coefficientGraph : first.coefficientGraph = second.coefficientGraph)
    (realization : HEq first.realization second.realization) : first = second := by
  cases first
  cases second
  cases package
  cases coefficientGraph
  cases realization
  rfl

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
      code.coefficientGraph.assemble :=
    cast_coefficientHom base_eq targetGeometry
  apply ext
  · exact PackageGraphCode.read_assemble code.package
  · calc
      (read code.assemble).coefficientGraph =
          AlgebraicGraphCoherence.RingHomGraphCode.read
            code.coefficientGraph.assemble := by
            simp only [read, assemble]
            exact congrArg AlgebraicGraphCoherence.RingHomGraphCode.read
              coefficient_eq
      _ = code.coefficientGraph :=
        AlgebraicGraphCoherence.RingHomGraphCode.read_assemble _
  · simpa only [read, assemble] using
      (realizationRead_cast_heq base_eq targetGeometry).trans
        (heq_of_eq
          (RemainingComponentGraphCoherence.RealizationGraphCode.read_assemble
            code.realization))

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
