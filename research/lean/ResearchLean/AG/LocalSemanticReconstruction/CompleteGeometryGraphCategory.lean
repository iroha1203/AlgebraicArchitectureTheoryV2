import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# The category of raw complete geometry graphs

Every computational graph in `CompleteMapGraphs` has an independently defined
identity and composition.  Componentwise operations therefore make raw graph
bundles into a category without requiring that they arise from a completed
geometry morphism.  The backward context graph composes in the opposite order,
as required by its reversed source and target.

Reading every computational component of a geometry morphism preserves these
operations, including all dependent tagged maps.  It defines an
underlying-package-preserving functor into the raw graph category, and Cycle 64 joint
separation makes this functor faithful.  Its object assembly is immediate.
Fullness, equivalently Hom assembly for arbitrary raw graph bundles, is not
claimed; independent coherence conditions remain necessary.

## Implementation notes

The target Hom type is the raw `CompleteMapGraphs` structure itself, not an
image subtype and not a bundle containing a completed morphism.  Category laws
are reduced componentwise to the proven read/assemble inverse for primitive
function graphs.  This construction deliberately exposes the fullness gap
rather than hiding it in the definition of local morphisms.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace CompleteGeometryGraphCategory

universe u v

open CompleteGeometryFunctionGraphSeparation
open G122PrimitiveFunctionGraphReading
open LocalReconstructionEquivalence

namespace GraphCode

/-- Primitive total-functional function-graph code, used as the component Hom
type for complete graph bundles. -/
abbrev Code := PrimitiveFunctionGraph.GraphCode

/-- Left identity for graph-code composition, proved through graph assembly.
As a simp rule, it eliminates a leading identity. -/
@[simp]
theorem id_comp {A B : Type*} (graph : Code A B) :
    PrimitiveFunctionGraph.GraphCode.comp
      PrimitiveFunctionGraph.GraphCode.id graph = graph := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  simp

/-- Right identity for graph-code composition, proved through graph assembly.
As a simp rule, it eliminates a trailing identity. -/
@[simp]
theorem comp_id {A B : Type*} (graph : Code A B) :
    PrimitiveFunctionGraph.GraphCode.comp graph
      PrimitiveFunctionGraph.GraphCode.id = graph := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  simp

/-- Associativity of graph-code composition, proved through graph assembly.
As a simp rule, it normalizes left-associated composition to the right. -/
@[simp]
theorem assoc {A B C D : Type*}
    (first : Code A B) (second : Code B C) (third : Code C D) :
    PrimitiveFunctionGraph.GraphCode.comp
        (PrimitiveFunctionGraph.GraphCode.comp first second) third =
      PrimitiveFunctionGraph.GraphCode.comp first
        (PrimitiveFunctionGraph.GraphCode.comp second third) := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  simp [Function.comp_def]

end GraphCode

namespace PrimitiveMapGraphs

/-- Left identity for componentwise primitive-map graph composition.  As a simp
rule, it eliminates a leading identity bundle. -/
@[simp]
theorem id_comp {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (graphs : PrimitiveMapGraphs G H) :
    PrimitiveMapGraphs.comp (PrimitiveMapGraphs.id G) graphs = graphs := by
  apply PrimitiveMapGraphs.ext <;> simp [PrimitiveMapGraphs.comp,
    PrimitiveMapGraphs.id]

/-- Right identity for componentwise primitive-map graph composition.  As a
simp rule, it eliminates a trailing identity bundle. -/
@[simp]
theorem comp_id {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (graphs : PrimitiveMapGraphs G H) :
    PrimitiveMapGraphs.comp graphs (PrimitiveMapGraphs.id H) = graphs := by
  apply PrimitiveMapGraphs.ext <;> simp [PrimitiveMapGraphs.comp,
    PrimitiveMapGraphs.id]

/-- Associativity of componentwise primitive-map graph composition.  As a simp
rule, it normalizes left-associated composition to the right. -/
@[simp]
theorem assoc {U : AtomCarrier.{u}} {G H K L : GeometryPackage.{u, v} U}
    (first : PrimitiveMapGraphs G H) (second : PrimitiveMapGraphs H K)
    (third : PrimitiveMapGraphs K L) :
    PrimitiveMapGraphs.comp (PrimitiveMapGraphs.comp first second) third =
      PrimitiveMapGraphs.comp first (PrimitiveMapGraphs.comp second third) := by
  apply PrimitiveMapGraphs.ext <;> simp [PrimitiveMapGraphs.comp]

end PrimitiveMapGraphs

namespace CompleteMapGraphs

/-- Complete graph bundles are determined by all thirteen independent graph
components. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : CompleteMapGraphs G H}
    (primitive : first.primitive = second.primitive)
    (pointedAtom : first.pointedAtom = second.pointedAtom)
    (contextForward : first.contextForward = second.contextForward)
    (contextBackward : first.contextBackward = second.contextBackward)
    (equation : first.equation = second.equation)
    (equationObservable : first.equationObservable = second.equationObservable)
    (operation : first.operation = second.operation)
    (invariant : first.invariant = second.invariant)
    (signatureAxis : first.signatureAxis = second.signatureAxis)
    (coordinate : first.coordinate = second.coordinate)
    (support : first.support = second.support)
    (geometryAxis : first.geometryAxis = second.geometryAxis)
    (geometryObservable : first.geometryObservable = second.geometryObservable) :
    first = second := by
  cases first
  cases second
  cases primitive
  cases pointedAtom
  cases contextForward
  cases contextBackward
  cases equation
  cases equationObservable
  cases operation
  cases invariant
  cases signatureAxis
  cases coordinate
  cases support
  cases geometryAxis
  cases geometryObservable
  rfl

/-- Componentwise identity complete graph bundle. -/
def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    CompleteMapGraphs G G where
  primitive := PrimitiveMapGraphs.id G
  pointedAtom := PrimitiveFunctionGraph.GraphCode.id
  contextForward := PrimitiveFunctionGraph.GraphCode.id
  contextBackward := PrimitiveFunctionGraph.GraphCode.id
  equation := PrimitiveFunctionGraph.GraphCode.id
  equationObservable := PrimitiveFunctionGraph.GraphCode.id
  operation := PrimitiveFunctionGraph.GraphCode.id
  invariant := PrimitiveFunctionGraph.GraphCode.id
  signatureAxis := PrimitiveFunctionGraph.GraphCode.id
  coordinate := PrimitiveFunctionGraph.GraphCode.id
  support := PrimitiveFunctionGraph.GraphCode.id
  geometryAxis := PrimitiveFunctionGraph.GraphCode.id
  geometryObservable := PrimitiveFunctionGraph.GraphCode.id

/-- Componentwise composition.  The backward context graph reverses order. -/
def comp {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : CompleteMapGraphs G H) (second : CompleteMapGraphs H K) :
    CompleteMapGraphs G K where
  primitive := PrimitiveMapGraphs.comp first.primitive second.primitive
  pointedAtom := PrimitiveFunctionGraph.GraphCode.comp
    first.pointedAtom second.pointedAtom
  contextForward := PrimitiveFunctionGraph.GraphCode.comp
    first.contextForward second.contextForward
  contextBackward := PrimitiveFunctionGraph.GraphCode.comp
    second.contextBackward first.contextBackward
  equation := PrimitiveFunctionGraph.GraphCode.comp first.equation second.equation
  equationObservable := PrimitiveFunctionGraph.GraphCode.comp
    first.equationObservable second.equationObservable
  operation := PrimitiveFunctionGraph.GraphCode.comp
    first.operation second.operation
  invariant := PrimitiveFunctionGraph.GraphCode.comp
    first.invariant second.invariant
  signatureAxis := PrimitiveFunctionGraph.GraphCode.comp
    first.signatureAxis second.signatureAxis
  coordinate := PrimitiveFunctionGraph.GraphCode.comp
    first.coordinate second.coordinate
  support := PrimitiveFunctionGraph.GraphCode.comp first.support second.support
  geometryAxis := PrimitiveFunctionGraph.GraphCode.comp
    first.geometryAxis second.geometryAxis
  geometryObservable := PrimitiveFunctionGraph.GraphCode.comp
    first.geometryObservable second.geometryObservable

/-- Left identity for complete-map graph composition across all components.  As
a simp rule, it eliminates a leading identity bundle. -/
@[simp]
theorem id_comp {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (graphs : CompleteMapGraphs G H) : comp (id G) graphs = graphs := by
  apply ext <;> simp [id, comp]

/-- Right identity for complete-map graph composition across all components.  As
a simp rule, it eliminates a trailing identity bundle. -/
@[simp]
theorem comp_id {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (graphs : CompleteMapGraphs G H) : comp graphs (id H) = graphs := by
  apply ext <;> simp [id, comp]

/-- Associativity of complete-map graph composition across all components.  As
a simp rule, it normalizes left-associated composition to the right. -/
@[simp]
theorem assoc {U : AtomCarrier.{u}}
    {G H K L : GeometryPackage.{u, v} U}
    (first : CompleteMapGraphs G H) (second : CompleteMapGraphs H K)
    (third : CompleteMapGraphs K L) :
    comp (comp first second) third = comp first (comp second third) := by
  apply ext <;> simp [comp]

end CompleteMapGraphs

/-- A geometry package regarded as an object of the raw complete-graph
category. -/
structure Object (U : AtomCarrier.{u}) where
  /-- The package whose computational types index local graph morphisms. -/
  package : GeometryPackage.{u, v} U

namespace Object

/-- Raw complete graph bundles form a category independently of global
geometry morphisms. -/
instance {U : AtomCarrier.{u}} : Category (Object.{u, v} U) where
  Hom source target := CompleteMapGraphs source.package target.package
  id object := CompleteMapGraphs.id object.package
  comp first second := CompleteMapGraphs.comp first second
  id_comp := CompleteMapGraphs.id_comp
  comp_id := CompleteMapGraphs.comp_id
  assoc := CompleteMapGraphs.assoc

end Object

/-! ## Complete geometry reading as a faithful functor -/

/-- Reading the identity geometry morphism gives the independent identity graph
bundle. -/
theorem readCompleteMapGraphs_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    readCompleteMapGraphs (GeometryTotalHom.id G) = CompleteMapGraphs.id G := by
  apply CompleteMapGraphs.ext
  · exact readPrimitiveMaps_id G
  all_goals
    apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    simp [readCompleteMapGraphs, CompleteMapGraphs.id, equationObservableMap,
      coordinateMap, equationContextForwardMap,
      equationContextBackwardMap]; rfl

/-- Complete graph reading preserves composition in every primitive and
dependent tagged component. -/
theorem readCompleteMapGraphs_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : GeometryTotalHom G H) (second : GeometryTotalHom H K) :
    readCompleteMapGraphs (GeometryTotalHom.comp first second) =
      CompleteMapGraphs.comp (readCompleteMapGraphs first)
        (readCompleteMapGraphs second) := by
  apply CompleteMapGraphs.ext
  · exact readPrimitiveMaps_comp first second
  all_goals
    apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    simp [readCompleteMapGraphs, CompleteMapGraphs.comp, equationObservableMap,
      operationMap, coordinateMap, supportMap, geometryAxisMap,
      geometryObservableMap, equationContextForwardMap,
      equationContextBackwardMap, taggedMap, Function.comp_def,
      GeometryTotalHom.comp, GeomReadHom.comp, PackageTotalHom.comp,
      SignedExactCoreReadingHom.comp, EquationSystemExactTransport.comp] <;> rfl

/-- Read a geometry package and all of its morphisms into the raw complete-graph
category. -/
def readingFunctor (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ Object.{u, v} U where
  obj package := ⟨package⟩
  map morphism := readCompleteMapGraphs morphism
  map_id := readCompleteMapGraphs_id
  map_comp := readCompleteMapGraphs_comp

/-- Complete graph reading is faithful by Cycle 64 joint separation. -/
def readingFunctorHomSeparation (U : AtomCarrier.{u}) :
    HomSeparation (readingFunctor.{u, v} U) where
  hom _ _ := ⟨readCompleteMapGraphs_injective⟩

/-- Complete graph reading is a faithful functor. -/
instance readingFunctorFaithful (U : AtomCarrier.{u}) :
    (readingFunctor.{u, v} U).Faithful where
  map_injective := fun {X Y} =>
    (readingFunctorHomSeparation U).hom X Y |>.injective

/-- Object assembly is already exact because the reading functor is identity
on the underlying package. -/
def readingFunctorObjectAssembly (U : AtomCarrier.{u}) :
    ObjectAssembly (readingFunctor.{u, v} U) where
  assembleObject object := object.package
  readAssembledIso _ := Iso.refl _

/-- Any independently proved Hom assembly upgrades complete graph reading to a
categorical equivalence through the Cycle 65 reconstruction theorem. -/
def reconstructionDataOfHomAssembly (U : AtomCarrier.{u})
    (assembly : HomAssembly (readingFunctor.{u, v} U)) :
    ReconstructionData (readingFunctor.{u, v} U) where
  separation := readingFunctorHomSeparation U
  homAssembly := assembly
  objectAssembly := readingFunctorObjectAssembly U

/-- Fullness is sufficient for the remaining Hom-assembly obligation; the
chosen preimage is kept outside the raw local graph data. -/
def homAssemblyOfFull (U : AtomCarrier.{u})
    [(readingFunctor.{u, v} U).Full] :
    HomAssembly (readingFunctor.{u, v} U) where
  assemble := (readingFunctor U).preimage
  map_assemble := (readingFunctor U).map_preimage

/-- For complete graph reading, the remaining Hom-assembly obligation is
exactly fullness. -/
theorem nonempty_homAssembly_iff_full (U : AtomCarrier.{u}) :
    Nonempty (HomAssembly (readingFunctor.{u, v} U)) ↔
      (readingFunctor.{u, v} U).Full := by
  constructor
  · rintro ⟨assembly⟩
    exact (reconstructionDataOfHomAssembly U assembly).fullyFaithful.full
  · intro fullness
    letI : (readingFunctor.{u, v} U).Full := fullness
    exact ⟨homAssemblyOfFull U⟩

/-- Once Hom assembly is proved independently, the complete graph reading
functor is an equivalence. -/
def equivalenceOfHomAssembly (U : AtomCarrier.{u})
    (assembly : HomAssembly (readingFunctor.{u, v} U)) :
    GeomReadCategory.{u, v} U ≌ Object.{u, v} U :=
  (reconstructionDataOfHomAssembly U assembly).equivalence

end CompleteGeometryGraphCategory

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory

end

end AAT.AG.LocalSemanticReconstruction
