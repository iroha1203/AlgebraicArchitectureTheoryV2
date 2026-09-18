import ResearchLean.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonInputCharacterization
import Formal.Util.AssertStandardAxioms

/-!
# Complete computational graph separation for geometry morphisms

The ordinary maps used by `GeometryTotalHom.ext` are read into the independent
total-functional Bool graph presentation.  Dependent families are exposed as
ordinary maps between tagged sigma types, so no completed geometry morphism is
stored in a local value.  Equality of the resulting graph bundle reconstructs
all literal computational equality conditions and therefore separates arbitrary
complete geometry morphisms.

This module proves separation, not assembly of an arbitrary graph bundle.  In
particular, graph compatibility is not defined by existence of a completed
geometry morphism, and no extension witness is hidden in the graph data.

## Implementation notes

Dependent families are represented by ordinary maps between tagged sigma
types.  This keeps the index action visible and lets equality of a single
ordinary function recover the fiber maps by heterogeneous equality.  Storing
the family behind a completed morphism or an existential compatibility
certificate was rejected because either choice would make separation
tautological.  Both object actions of the selected-context equivalence are
stored; thinness then reconstructs its functors and inverse data.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport

noncomputable section

namespace CompleteGeometryFunctionGraphSeparation

universe u v uI uJ uA uB

namespace PFG

/-- Short name for total-functional primitive graph codes. -/
abbrev GraphCode := PrimitiveFunctionGraph.GraphCode

end PFG

/-! ## Tagged ordinary maps for dependent computational families -/

/-- Turn a dependent family of maps into one ordinary map between tagged sums. -/
def taggedMap {I : Type uI} {J : Type uJ}
    {A : I → Type uA} {B : J → Type uB}
    (indexMap : I → J) (fiberMap : ∀ i, A i → B (indexMap i)) :
    (Σ i, A i) → (Σ j, B j) :=
  fun value => ⟨indexMap value.1, fiberMap value.1 value.2⟩

/-- Equality of index maps and tagged maps recovers heterogeneous equality of
the underlying dependent map families. -/
theorem fiberMap_heq_of_taggedMap_eq
    {I : Type uI} {J : Type uJ}
    {A : I → Type uA} {B : J → Type uB}
    {firstIndex secondIndex : I → J}
    {firstMap : ∀ i, A i → B (firstIndex i)}
    {secondMap : ∀ i, A i → B (secondIndex i)}
    (index_eq : firstIndex = secondIndex)
    (tagged_eq : taggedMap firstIndex firstMap =
      taggedMap secondIndex secondMap) :
    HEq firstMap secondMap := by
  subst secondIndex
  apply heq_of_eq
  funext index value
  have value_eq := congrFun tagged_eq (Sigma.mk index value)
  exact eq_of_heq (Sigma.mk.inj_iff.mp value_eq).2

/-- The same recovery principle for families indexed by two independent
endpoint maps. -/
theorem fiberMap₂_heq_of_taggedMap_eq
    {I : Type uI} {J : Type uJ}
    {A : I → I → Type uA} {B : J → J → Type uB}
    {firstIndex secondIndex : I → J}
    {firstMap : ∀ i j, A i j → B (firstIndex i) (firstIndex j)}
    {secondMap : ∀ i j, A i j → B (secondIndex i) (secondIndex j)}
    (index_eq : firstIndex = secondIndex)
    (tagged_eq :
      (fun value : Σ i, Σ j, A i j =>
        (⟨firstIndex value.1, firstIndex value.2.1,
          firstMap value.1 value.2.1 value.2.2⟩ : Σ i, Σ j, B i j)) =
      (fun value : Σ i, Σ j, A i j =>
        (⟨secondIndex value.1, secondIndex value.2.1,
          secondMap value.1 value.2.1 value.2.2⟩ : Σ i, Σ j, B i j))) :
    HEq firstMap secondMap := by
  subst secondIndex
  apply heq_of_eq
  funext firstIndex secondIndex value
  have value_eq := congrFun tagged_eq
    (Sigma.mk firstIndex (Sigma.mk secondIndex value))
  have tail_eq := (Sigma.mk.inj_iff.mp value_eq).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp (eq_of_heq tail_eq)).2

/-- Tagged equality determines a family of equivalences after the index map is
fixed. -/
theorem equivFamily_heq_of_taggedMap_eq
    {I : Type uI} {J : Type uJ}
    {A : I → Type uA} {B : J → Type uB}
    {firstIndex secondIndex : I → J}
    {firstMap : ∀ i, A i ≃ B (firstIndex i)}
    {secondMap : ∀ i, A i ≃ B (secondIndex i)}
    (index_eq : firstIndex = secondIndex)
    (tagged_eq : taggedMap firstIndex (fun i value => firstMap i value) =
      taggedMap secondIndex (fun i value => secondMap i value)) :
    HEq firstMap secondMap := by
  subst secondIndex
  apply heq_of_eq
  funext index
  apply Equiv.ext
  intro value
  have value_eq := congrFun tagged_eq (Sigma.mk index value)
  exact eq_of_heq (Sigma.mk.inj_iff.mp value_eq).2

/-- Tagged equality likewise determines a family of ring equivalences. -/
theorem ringEquivFamily_heq_of_taggedMap_eq
    {I : Type uI} {J : Type uJ}
    {A : I → Type uA} {B : J → Type uB}
    [(i : I) → NonAssocSemiring (A i)]
    [(j : J) → NonAssocSemiring (B j)]
    {firstIndex secondIndex : I → J}
    {firstMap : ∀ i, A i ≃+* B (firstIndex i)}
    {secondMap : ∀ i, A i ≃+* B (secondIndex i)}
    (index_eq : firstIndex = secondIndex)
    (tagged_eq : taggedMap firstIndex (fun i value => firstMap i value) =
      taggedMap secondIndex (fun i value => secondMap i value)) :
    HEq firstMap secondMap := by
  subst secondIndex
  apply heq_of_eq
  funext index
  apply RingEquiv.ext
  intro value
  have value_eq := congrFun tagged_eq (Sigma.mk index value)
  exact eq_of_heq (Sigma.mk.inj_iff.mp value_eq).2

/-- Heterogeneous equality in subsingleton types follows from equality of the
types themselves. -/
theorem subsingleton_heq_of_type_eq
    {alpha beta : Sort u} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-! ## Total tagged functions carried by one complete geometry morphism -/

/-- Forward action on the selected context objects of the equation system. -/
def equationContextForwardMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    G.site.category → H.site.category :=
  morphism.base.upper.equationTransport.contextEquivalence.functor.obj

/-- Backward action on the selected context objects of the equation system. -/
def equationContextBackwardMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    H.site.category → G.site.category :=
  morphism.base.upper.equationTransport.contextEquivalence.inverse.obj

/-- Tagged equation-observable action. -/
def equationObservableMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (Σ W : G.site.category,
      G.core.algebra.equationSystem.Observable W) →
    (Σ W : H.site.category,
      H.core.algebra.equationSystem.Observable W) :=
  taggedMap (equationContextForwardMap morphism)
    (fun W value =>
      morphism.base.upper.equationTransport.observableEquiv W value)

/-- Tagged operation action, retaining both operation endpoints. -/
def operationMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (Σ A : ArchitectureObject U, Σ B : ArchitectureObject U,
      G.core.reading.operationReading.Op A B) →
    (Σ A : ArchitectureObject U, Σ B : ArchitectureObject U,
      H.core.reading.operationReading.Op A B) :=
  fun value =>
    ⟨morphism.base.upper.objectMap value.1,
      morphism.base.upper.objectMap value.2.1,
      morphism.base.upper.operationMap value.2.2⟩

/-- Tagged signature-coordinate action. -/
def coordinateMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (Σ axis : G.core.reading.signatureReading.Axis,
      G.core.reading.signatureReading.Coordinate axis) →
    (Σ axis : H.core.reading.signatureReading.Axis,
      H.core.reading.signatureReading.Coordinate axis) :=
  taggedMap morphism.base.upper.axisMap
    (fun axis coordinate =>
      morphism.base.upper.coordinateEquiv axis coordinate)

/-- Tagged geometry-support action. -/
def supportMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (Σ W : G.site.category, W.ctx.Support) →
    (Σ W : H.site.category, W.ctx.Support) :=
  fun value =>
    ⟨equationContextForwardMap morphism value.1,
      morphism.geometry.supportComp value.1 value.2⟩

/-- Tagged geometry-axis action. -/
def geometryAxisMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (Σ W : G.site.category, W.ctx.Axis) →
    (Σ W : H.site.category, W.ctx.Axis) :=
  fun value =>
    ⟨equationContextForwardMap morphism value.1,
      morphism.geometry.axisComp value.1 value.2⟩

/-- Tagged geometry-observable action. -/
def geometryObservableMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (Σ W : G.site.category, W.ctx.Observable) →
    (Σ W : H.site.category, W.ctx.Observable) :=
  fun value =>
    ⟨equationContextForwardMap morphism value.1,
      morphism.geometry.observableComp value.1 value.2⟩

/-! ## Complete graph reading and joint separation -/

/-- Graphs of every computational component used by complete-geometry
extensionality.  Proof-only preservation laws are deliberately absent. -/
structure CompleteMapGraphs {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  /-- The five ordinary maps already exposed by Cycle 63. -/
  primitive : G122PrimitiveFunctionGraphReading.PrimitiveMapGraphs G H
  /-- Lower pointed Atom action, independently of the upper Atom action. -/
  pointedAtom : PFG.GraphCode U.Atom U.Atom
  /-- Forward selected-context action. -/
  contextForward : PFG.GraphCode G.site.category H.site.category
  /-- Backward selected-context action. -/
  contextBackward : PFG.GraphCode H.site.category G.site.category
  /-- Equation-index action. -/
  equation : PFG.GraphCode G.core.algebra.equationSystem.Index
    H.core.algebra.equationSystem.Index
  /-- Tagged observable-ring action of the equation transport. -/
  equationObservable : PFG.GraphCode
    (Σ W : G.site.category, G.core.algebra.equationSystem.Observable W)
    (Σ W : H.site.category, H.core.algebra.equationSystem.Observable W)
  /-- Tagged operation action. -/
  operation : PFG.GraphCode
    (Σ A : ArchitectureObject U, Σ B : ArchitectureObject U,
      G.core.reading.operationReading.Op A B)
    (Σ A : ArchitectureObject U, Σ B : ArchitectureObject U,
      H.core.reading.operationReading.Op A B)
  /-- Invariant-index action. -/
  invariant : PFG.GraphCode G.core.reading.invariantReading.Index
    H.core.reading.invariantReading.Index
  /-- Signature-axis action. -/
  signatureAxis : PFG.GraphCode G.core.reading.signatureReading.Axis
    H.core.reading.signatureReading.Axis
  /-- Tagged coordinate action. -/
  coordinate : PFG.GraphCode
    (Σ axis : G.core.reading.signatureReading.Axis,
      G.core.reading.signatureReading.Coordinate axis)
    (Σ axis : H.core.reading.signatureReading.Axis,
      H.core.reading.signatureReading.Coordinate axis)
  /-- Tagged geometry-support action. -/
  support : PFG.GraphCode (Σ W : G.site.category, W.ctx.Support)
    (Σ W : H.site.category, W.ctx.Support)
  /-- Tagged geometry-axis action. -/
  geometryAxis : PFG.GraphCode (Σ W : G.site.category, W.ctx.Axis)
    (Σ W : H.site.category, W.ctx.Axis)
  /-- Tagged geometry-observable action. -/
  geometryObservable : PFG.GraphCode
    (Σ W : G.site.category, W.ctx.Observable)
    (Σ W : H.site.category, W.ctx.Observable)

/-- Read every computational component of an arbitrary complete geometry
morphism as an independent total-functional Bool graph. -/
noncomputable def readCompleteMapGraphs {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    CompleteMapGraphs G H where
  primitive := G122PrimitiveFunctionGraphReading.readPrimitiveMaps morphism
  pointedAtom := PrimitiveFunctionGraph.GraphCode.read
    morphism.base.base.doctrineHom.atomEquiv
  contextForward := PrimitiveFunctionGraph.GraphCode.read
    (equationContextForwardMap morphism)
  contextBackward := PrimitiveFunctionGraph.GraphCode.read
    (equationContextBackwardMap morphism)
  equation := PrimitiveFunctionGraph.GraphCode.read
    morphism.base.upper.equationTransport.equationEquiv
  equationObservable := PrimitiveFunctionGraph.GraphCode.read
    (equationObservableMap morphism)
  operation := PrimitiveFunctionGraph.GraphCode.read (operationMap morphism)
  invariant := PrimitiveFunctionGraph.GraphCode.read
    morphism.base.upper.invariantMap
  signatureAxis := PrimitiveFunctionGraph.GraphCode.read
    morphism.base.upper.axisMap
  coordinate := PrimitiveFunctionGraph.GraphCode.read (coordinateMap morphism)
  support := PrimitiveFunctionGraph.GraphCode.read (supportMap morphism)
  geometryAxis := PrimitiveFunctionGraph.GraphCode.read
    (geometryAxisMap morphism)
  geometryObservable := PrimitiveFunctionGraph.GraphCode.read
    (geometryObservableMap morphism)

/-! ## Recovery of the extensionality inputs -/

/-- Equality of graph codes implies equality of their assembled functions. -/
theorem assemble_eq_of_graph_eq {alpha beta : Type*}
    {first second : PFG.GraphCode alpha beta} (graph_eq : first = second) :
    PrimitiveFunctionGraph.GraphCode.assemble first =
      PrimitiveFunctionGraph.GraphCode.assemble second :=
  congrArg PrimitiveFunctionGraph.GraphCode.assemble graph_eq

/-- The two stored context-object actions determine the complete context
equivalence because the selected context categories are thin. -/
theorem contextEquivalence_eq_of_object_maps_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : GeometryTotalHom G H}
    (forward_eq : equationContextForwardMap first =
      equationContextForwardMap second)
    (backward_eq : equationContextBackwardMap first =
      equationContextBackwardMap second) :
    first.base.upper.equationTransport.contextEquivalence =
      second.base.upper.equationTransport.contextEquivalence := by
  let firstEquivalence :=
    first.base.upper.equationTransport.contextEquivalence
  let secondEquivalence :=
    second.base.upper.equationTransport.contextEquivalence
  have functor_eq : firstEquivalence.functor = secondEquivalence.functor := by
    refine CategoryTheory.Functor.ext (fun context => ?_) ?_
    · exact congrFun forward_eq context
    · intros
      exact Subsingleton.elim _ _
  have inverse_eq : firstEquivalence.inverse = secondEquivalence.inverse := by
    refine CategoryTheory.Functor.ext (fun context => ?_) ?_
    · exact congrFun backward_eq context
    · intros
      exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext functor_eq inverse_eq
  · apply subsingleton_heq_of_type_eq
    apply congrArg
      (fun functor => (𝟭 G.site.category) ≅ functor)
    rw [functor_eq, inverse_eq]
  · apply subsingleton_heq_of_type_eq
    apply congrArg
      (fun functor => functor ≅ (𝟭 H.site.category))
    rw [functor_eq, inverse_eq]

/-- Complete graph equality yields the literal computational conditions of
the accepted complete-geometry extensionality spine. -/
theorem inputConditions_of_graph_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : GeometryTotalHom G H}
    (graph_eq : readCompleteMapGraphs first =
      readCompleteMapGraphs second) :
    UpperGeometryCompatibleProblemInputData.GeometryTotalHomInputConditions
      first second := by
  have source_eq : first.base.base.doctrineHom.sourceMap =
      second.base.base.doctrineHom.sourceMap := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.primitive.source) graph_eq)
    simpa [readCompleteMapGraphs,
      G122PrimitiveFunctionGraphReading.readPrimitiveMaps] using equality
  have pointed_atom_eq : first.base.base.doctrineHom.atomEquiv =
      second.base.base.doctrineHom.atomEquiv := by
    apply Equiv.ext
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.pointedAtom) graph_eq)
    exact congrFun (by simpa [readCompleteMapGraphs] using equality)
  have atom_eq : first.base.upper.atomEquiv = second.base.upper.atomEquiv := by
    apply Equiv.ext
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.primitive.atom) graph_eq)
    exact congrFun (by simpa [readCompleteMapGraphs,
      G122PrimitiveFunctionGraphReading.readPrimitiveMaps,
      SignedExactCoreReadingHom.atomMap] using equality)
  have object_eq : first.base.upper.objectMap =
      second.base.upper.objectMap := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.primitive.object) graph_eq)
    simpa [readCompleteMapGraphs,
      G122PrimitiveFunctionGraphReading.readPrimitiveMaps] using equality
  have context_forward_eq : equationContextForwardMap first =
      equationContextForwardMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.contextForward) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have context_backward_eq : equationContextBackwardMap first =
      equationContextBackwardMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.contextBackward) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have context_eq :
      first.base.upper.equationTransport.contextEquivalence =
        second.base.upper.equationTransport.contextEquivalence :=
    contextEquivalence_eq_of_object_maps_eq
      context_forward_eq context_backward_eq
  have equation_eq :
      first.base.upper.equationTransport.equationEquiv =
        second.base.upper.equationTransport.equationEquiv := by
    apply Equiv.ext
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.equation) graph_eq)
    exact congrFun (by simpa [readCompleteMapGraphs] using equality)
  have equation_observable_tagged_eq : equationObservableMap first =
      equationObservableMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.equationObservable) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have equation_observable_eq : HEq
      first.base.upper.equationTransport.observableEquiv
      second.base.upper.equationTransport.observableEquiv := by
    exact ringEquivFamily_heq_of_taggedMap_eq context_forward_eq
      equation_observable_tagged_eq
  have operation_tagged_eq : operationMap first = operationMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.operation) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have operation_eq : HEq
      (@SignedExactCoreReadingHom.operationMap U G.core H.core
        first.base.upper)
      (@SignedExactCoreReadingHom.operationMap U G.core H.core
        second.base.upper) := by
    exact fiberMap₂_heq_of_taggedMap_eq object_eq operation_tagged_eq
  have invariant_eq : HEq first.base.upper.invariantMap
      second.base.upper.invariantMap := by
    apply heq_of_eq
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.invariant) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have signature_axis_eq : HEq first.base.upper.axisMap
      second.base.upper.axisMap := by
    apply heq_of_eq
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.signatureAxis) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have coordinate_tagged_eq : coordinateMap first = coordinateMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.coordinate) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have coordinate_eq : HEq first.base.upper.coordinateEquiv
      second.base.upper.coordinateEquiv := by
    exact equivFamily_heq_of_taggedMap_eq
      (eq_of_heq signature_axis_eq) coordinate_tagged_eq
  have coefficient_function_eq :
      (first.geometry.coefficientHom : G.Coefficient → H.Coefficient) =
        second.geometry.coefficientHom := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.primitive.coefficient) graph_eq)
    simpa [readCompleteMapGraphs,
      G122PrimitiveFunctionGraphReading.readPrimitiveMaps] using equality
  have coefficient_eq : first.geometry.coefficientHom =
      second.geometry.coefficientHom := by
    apply RingHom.ext
    exact congrFun coefficient_function_eq
  have support_tagged_eq : supportMap first = supportMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.support) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have support_eq : HEq first.geometry.supportComp
      second.geometry.supportComp := by
    exact fiberMap_heq_of_taggedMap_eq
      (A := fun W : G.site.category => W.ctx.Support)
      (B := fun W : H.site.category => W.ctx.Support)
      (firstIndex := equationContextForwardMap first)
      (secondIndex := equationContextForwardMap second)
      (firstMap := fun W value => first.geometry.supportComp W value)
      (secondMap := fun W value => second.geometry.supportComp W value)
      context_forward_eq support_tagged_eq
  have geometry_axis_tagged_eq : geometryAxisMap first =
      geometryAxisMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.geometryAxis) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have geometry_axis_eq : HEq first.geometry.axisComp
      second.geometry.axisComp := by
    exact fiberMap_heq_of_taggedMap_eq
      (A := fun W : G.site.category => W.ctx.Axis)
      (B := fun W : H.site.category => W.ctx.Axis)
      (firstIndex := equationContextForwardMap first)
      (secondIndex := equationContextForwardMap second)
      (firstMap := fun W value => first.geometry.axisComp W value)
      (secondMap := fun W value => second.geometry.axisComp W value)
      context_forward_eq geometry_axis_tagged_eq
  have geometry_observable_tagged_eq : geometryObservableMap first =
      geometryObservableMap second := by
    have equality := assemble_eq_of_graph_eq
      (congrArg (fun graphs => graphs.geometryObservable) graph_eq)
    simpa [readCompleteMapGraphs] using equality
  have geometry_observable_eq : HEq first.geometry.observableComp
      second.geometry.observableComp := by
    exact fiberMap_heq_of_taggedMap_eq
      (A := fun W : G.site.category => W.ctx.Observable)
      (B := fun W : H.site.category => W.ctx.Observable)
      (firstIndex := equationContextForwardMap first)
      (secondIndex := equationContextForwardMap second)
      (firstMap := fun W value => first.geometry.observableComp W value)
      (secondMap := fun W value => second.geometry.observableComp W value)
      context_forward_eq geometry_observable_tagged_eq
  exact {
    pointedSourceMap := source_eq
    pointedAtomEquiv := pointed_atom_eq
    atomEquiv := atom_eq
    objectMap := object_eq
    equationContext := heq_of_eq context_eq
    equationIndex := heq_of_eq equation_eq
    equationObservable := equation_observable_eq
    operationMap := operation_eq
    invariantMap := invariant_eq
    axisMap := signature_axis_eq
    coordinateEquiv := coordinate_eq
    coefficientHom := coefficient_eq
    supportImageFixed := support_eq
    axisImageFixed := geometry_axis_eq
    observableImageFixed := geometry_observable_eq }

/-- The complete total-functional graph reading jointly separates arbitrary
complete geometry morphisms. -/
theorem readCompleteMapGraphs_injective
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} :
    Function.Injective
      (readCompleteMapGraphs : GeometryTotalHom G H → CompleteMapGraphs G H) := by
  intro first second graph_eq
  exact (inputConditions_of_graph_eq graph_eq).eq

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation

end CompleteGeometryFunctionGraphSeparation

end

end AAT.AG.LocalSemanticReconstruction
