import ResearchLean.AG.LocalSemanticReconstruction.PrimitiveFunctionGraphCategory
import ResearchLean.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe
import Formal.Util.AssertStandardAxioms

/-!
# Primitive function-graph readings for arbitrary G-122 geometry morphisms

Every geometry morphism carries several ordinary computational maps before the
dependent operation, equation, and raw-relation layers are considered.  This
module reads five such maps into the independent Bool graph presentation:
lower-doctrine sources, primitive Atoms, architecture objects, raw contexts,
and coefficients.

The five readings are bundled without adding laws or a completed geometry
morphism.  Assembly recovers every underlying function pointwise, and reading
respects identity and composition component by component.  For the fixed
G-122 comparison image, the accepted two-point object probe factors through
the object graph.  Its existing separation and assembly theorem is therefore
re-expressed through the new arbitrary-function surface in the same module.

## Implementation notes

The bundle is deliberately not claimed to separate complete geometry
morphisms.  The dependent operation, equation, invariant, axis, coordinate,
support, observable, and raw-relation maps remain additional readings.  The
five fields here are primitive graph codes, not completed `GeometryTotalHom`
values.  The fixed finite probe connection is included now rather than left as
a later common-surface wrapper.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport
open AAT.AG.RealizationReconstruction

noncomputable section

namespace G122PrimitiveFunctionGraphReading

universe u v

namespace PFG

/-- Short name for the total-functional primitive graph codes used below. -/
abbrev GraphCode := PrimitiveFunctionGraph.GraphCode

end PFG

/-- Five independent primitive graph readings carried by an arbitrary geometry
morphism.  No compatibility law or completed morphism is stored. -/
structure PrimitiveMapGraphs {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  /-- Graph of the lower extraction-doctrine source map. -/
  source : PFG.GraphCode
    G.core.reading.doctrine.Source H.core.reading.doctrine.Source
  /-- Graph of the primitive Atom map. -/
  atom : PFG.GraphCode U.Atom U.Atom
  /-- Graph of the architecture-object map. -/
  object : PFG.GraphCode (ArchitectureObject U) (ArchitectureObject U)
  /-- Graph of the raw architecture-context map. -/
  context : PFG.GraphCode
    (Site.ArchCtx G.core.object) (Site.ArchCtx H.core.object)
  /-- Graph of the coefficient-ring map viewed as an ordinary function. -/
  coefficient : PFG.GraphCode G.Coefficient H.Coefficient

namespace PrimitiveMapGraphs

/-- A five-component graph bundle is determined componentwise. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PrimitiveMapGraphs G H}
    (source_eq : first.source = second.source)
    (atom_eq : first.atom = second.atom)
    (object_eq : first.object = second.object)
    (context_eq : first.context = second.context)
    (coefficient_eq : first.coefficient = second.coefficient) :
    first = second := by
  cases first
  cases second
  cases source_eq
  cases atom_eq
  cases object_eq
  cases context_eq
  cases coefficient_eq
  rfl

/-- Componentwise identity graph bundle. -/
noncomputable def id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) : PrimitiveMapGraphs G G where
  source := PrimitiveFunctionGraph.GraphCode.id
  atom := PrimitiveFunctionGraph.GraphCode.id
  object := PrimitiveFunctionGraph.GraphCode.id
  context := PrimitiveFunctionGraph.GraphCode.id
  coefficient := PrimitiveFunctionGraph.GraphCode.id

/-- Componentwise composition of five primitive graph readings. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : PrimitiveMapGraphs G H) (second : PrimitiveMapGraphs H K) :
    PrimitiveMapGraphs G K where
  source := PrimitiveFunctionGraph.GraphCode.comp first.source second.source
  atom := PrimitiveFunctionGraph.GraphCode.comp first.atom second.atom
  object := PrimitiveFunctionGraph.GraphCode.comp first.object second.object
  context := PrimitiveFunctionGraph.GraphCode.comp first.context second.context
  coefficient := PrimitiveFunctionGraph.GraphCode.comp
    first.coefficient second.coefficient

end PrimitiveMapGraphs

/-- Read the five ordinary computational maps of an arbitrary geometry
morphism as primitive Bool graphs. -/
noncomputable def readPrimitiveMaps {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    PrimitiveMapGraphs G H where
  source := PrimitiveFunctionGraph.GraphCode.read
    morphism.base.base.doctrineHom.sourceMap
  atom := PrimitiveFunctionGraph.GraphCode.read morphism.base.upper.atomMap
  object := PrimitiveFunctionGraph.GraphCode.read morphism.base.upper.objectMap
  context := PrimitiveFunctionGraph.GraphCode.read (contextMap morphism.base)
  coefficient := PrimitiveFunctionGraph.GraphCode.read
    morphism.geometry.coefficientHom

/-- Assembly recovers all five underlying functions of an arbitrary geometry
morphism. -/
theorem assemble_readPrimitiveMaps {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    PrimitiveFunctionGraph.GraphCode.assemble
        (readPrimitiveMaps morphism).source =
        morphism.base.base.doctrineHom.sourceMap ∧
      PrimitiveFunctionGraph.GraphCode.assemble
          (readPrimitiveMaps morphism).atom =
        morphism.base.upper.atomMap ∧
      PrimitiveFunctionGraph.GraphCode.assemble
          (readPrimitiveMaps morphism).object =
        morphism.base.upper.objectMap ∧
      PrimitiveFunctionGraph.GraphCode.assemble
          (readPrimitiveMaps morphism).context =
        contextMap morphism.base ∧
      PrimitiveFunctionGraph.GraphCode.assemble
          (readPrimitiveMaps morphism).coefficient =
        morphism.geometry.coefficientHom := by
  simp [readPrimitiveMaps]

/-- Reading the identity geometry morphism yields the componentwise identity
graph bundle. -/
theorem readPrimitiveMaps_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    readPrimitiveMaps (GeometryTotalHom.id G) = PrimitiveMapGraphs.id G := by
  apply PrimitiveMapGraphs.ext <;>
    apply PrimitiveFunctionGraph.GraphCode.assemble_injective <;>
    rfl

/-- Reading respects arbitrary geometry-morphism composition in all five
primitive components. -/
theorem readPrimitiveMaps_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : GeometryTotalHom G H) (second : GeometryTotalHom H K) :
    readPrimitiveMaps (GeometryTotalHom.comp first second) =
      PrimitiveMapGraphs.comp
        (readPrimitiveMaps first) (readPrimitiveMaps second) := by
  apply PrimitiveMapGraphs.ext <;>
    apply PrimitiveFunctionGraph.GraphCode.assemble_injective <;>
    simp [readPrimitiveMaps, PrimitiveMapGraphs.comp, Function.comp_def] <;>
    rfl

/-! ## Fixed comparison probe through the object graph -/

open G122PrimitiveComparisonProbe G122FixedComparisonLocalSlice

/-- Object graph of an arbitrary morphism between the fixed direct and
via-base G-122 endpoints. -/
noncomputable def fixedComparisonObjectGraph
    (morphism : G122PrimitiveComparisonProbe.Direct ⟶
      G122PrimitiveComparisonProbe.ViaBase) :
    PFG.GraphCode (ArchitectureObject FiniteModel.carrier)
      (ArchitectureObject FiniteModel.carrier) :=
  (readPrimitiveMaps morphism).object

/-- Assembly of the fixed object graph is the original complete object map. -/
@[simp]
theorem assemble_fixedComparisonObjectGraph
    (morphism : G122PrimitiveComparisonProbe.Direct ⟶
      G122PrimitiveComparisonProbe.ViaBase) :
    PrimitiveFunctionGraph.GraphCode.assemble
        (fixedComparisonObjectGraph morphism) =
      morphism.base.upper.objectMap := by
  exact (assemble_readPrimitiveMaps morphism).2.2.1

/-- Restrict a complete fixed object graph to the accepted two probe points. -/
noncomputable def graphProbeRestriction
    (morphism : G122PrimitiveComparisonProbe.Direct ⟶
      G122PrimitiveComparisonProbe.ViaBase) :
    Fin G122PrimitiveComparisonProbe.coreProbe.objectCard →
      ArchitectureObject FiniteModel.carrier :=
  fun index => PrimitiveFunctionGraph.GraphCode.assemble
    (fixedComparisonObjectGraph morphism)
    (G122PrimitiveComparisonProbe.coreProbe.objectValue index)

/-- The accepted finite object restriction factors through primitive graph
assembly. -/
theorem graphProbeRestriction_eq_coreProbe_objectRestriction
    (morphism : G122PrimitiveComparisonProbe.Direct ⟶
      G122PrimitiveComparisonProbe.ViaBase) :
    graphProbeRestriction morphism =
      G122PrimitiveComparisonProbe.coreProbe.objectRestriction morphism := by
  funext index
  simp [graphProbeRestriction,
    G122FiniteCoreProbe.objectRestriction]

/-- Read the fixed semantic image solely through its assembled primitive object
graph on the two accepted probe points. -/
noncomputable def graphPrimitiveRead
    (morphism : G122FixedComparisonLocalSlice.SemanticImage) :
    G122FixedComparisonLocalSlice.LocalValue := by
  classical
  exact if graphProbeRestriction morphism.1 =
      graphProbeRestriction
        G122ClosedFamilyExpansion.finiteAxisFoldBarAlpha then
    .alpha
  else
    .generated

/-- The graph-factorized reading is exactly the accepted primitive probe
reading. -/
theorem graphPrimitiveRead_eq_primitiveRead
    (morphism : G122FixedComparisonLocalSlice.SemanticImage) :
    graphPrimitiveRead morphism =
      G122PrimitiveComparisonProbe.primitiveRead morphism := by
  simp only [graphPrimitiveRead,
    G122PrimitiveComparisonProbe.primitiveRead]
  rw [graphProbeRestriction_eq_coreProbe_objectRestriction,
    graphProbeRestriction_eq_coreProbe_objectRestriction]

/-- Graph-factorized reading after accepted assembly is identity. -/
@[simp]
theorem graphPrimitiveRead_assemble
    (value : G122FixedComparisonLocalSlice.LocalValue) :
    graphPrimitiveRead
        (G122FixedComparisonLocalSlice.assemble value) = value := by
  rw [graphPrimitiveRead_eq_primitiveRead]
  exact G122PrimitiveComparisonProbe.primitiveRead_assemble value

/-- Accepted assembly after graph-factorized reading recovers every morphism in
the fixed comparison image. -/
@[simp]
theorem assemble_graphPrimitiveRead
    (morphism : G122FixedComparisonLocalSlice.SemanticImage) :
    G122FixedComparisonLocalSlice.assemble (graphPrimitiveRead morphism) =
      morphism := by
  rw [graphPrimitiveRead_eq_primitiveRead]
  exact G122PrimitiveComparisonProbe.assemble_primitiveRead morphism

/-- The fixed local image is reconstructed through the primitive object graph
and its accepted two-point restriction. -/
noncomputable def graphPrimitiveSemanticEquivLocal :
    G122FixedComparisonLocalSlice.SemanticImage ≃
      G122FixedComparisonLocalSlice.LocalValue where
  toFun := graphPrimitiveRead
  invFun := G122FixedComparisonLocalSlice.assemble
  left_inv := assemble_graphPrimitiveRead
  right_inv := graphPrimitiveRead_assemble

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading

end G122PrimitiveFunctionGraphReading

end

end AAT.AG.LocalSemanticReconstruction
