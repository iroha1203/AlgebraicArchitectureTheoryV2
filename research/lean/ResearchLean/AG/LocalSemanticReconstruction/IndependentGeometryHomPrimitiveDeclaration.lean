import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.IndependentCarrierGraphReadings
import Formal.Util.AssertStandardAxioms

/-!
# Common primitive query roles for both complete geometry Hom modes

This declaration precedes selected source/target geometry objects and selected
base maps. All local values are point-pair Booleans. Native primitive carrier,
object, configuration, context, and actual context-morphism references occur
only as the arguments of their declared field roles.

Representative Homs have directed realization maps and no separate raw-map
cells. Explicit Homs retain raw coordinate/local-data/relation equivalences,
realization carrier equivalences, and actual context-morphism actions. No
completed package map, raw map, realization supply, or geometry Hom is a cell.
The native-role laws and the full reading/assembly equivalences are subsequent
construction obligations; the declaration alone does not discharge them.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

universe u v

open Site

variable {U : AtomCarrier.{u}}

/-- The two original complete geometry Hom meanings remain distinct profiles. -/
inductive Mode where
  /-- Strict representative raw transport with directed representative realization maps. -/
  | representative
  /-- Explicit coordinate/raw and actual-context realization transport. -/
  | explicit

/-- Point directions for native equivalence fields, independent of a selected inverse map. -/
inductive Direction where
  /-- Source-to-target point image. -/
  | forward
  /-- Target-to-source point image, recorded using the same ordered source/target pair. -/
  | backward

/-- Explicit raw-map point roles use a candidate inverse-context pair and candidate primitive carriers. -/
inductive RawQuery (A B : ArchitectureObject U) : Mode → Type (u + 1) where
  /-- Coordinate-equivalence graph at a candidate source/target context pair. -/
  | coordinate (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
      (q : IndependentCarrierGraph.Query.{u, u}) : RawQuery A B .explicit
  /-- Local-data equivalence at a candidate coordinate point pair. -/
  | localData (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
      (C D : Type u) (c : C) (d : D) (q : IndependentCarrierGraph.Query.{u, u}) : RawQuery A B .explicit
  /-- Relation-generator equivalence at a candidate inverse-context pair. -/
  | relation (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
      (q : IndependentCarrierGraph.Query.{u, u}) : RawQuery A B .explicit

/-- Realization roles retain each mode's original direction and actual-morphism requirements. -/
inductive RealizationQuery (A B : ArchitectureObject U) : Mode → Type (u + 1) where
  /-- Directed representative support map at a candidate forward-context pair. -/
  | representativeSupport (W : ArchCtx A) (V : ArchCtx B) (x : W.Support) (y : V.Support) :
      RealizationQuery A B .representative
  /-- Directed representative axis map at a candidate forward-context pair. -/
  | representativeAxis (W : ArchCtx A) (V : ArchCtx B) (x : W.Axis) (y : V.Axis) :
      RealizationQuery A B .representative
  /-- Directed representative observable comparison at a candidate forward-context pair. -/
  | representativeObservable (W : ArchCtx A) (V : ArchCtx B) (x : W.Observable) (y : V.Observable) :
      RealizationQuery A B .representative
  /-- Explicit support-equivalence graph with its native forward/backward direction. -/
  | explicitSupport (direction : Direction) (W : ArchCtx A) (V : ArchCtx B) (x : W.Support) (y : V.Support) :
      RealizationQuery A B .explicit
  /-- Explicit axis-equivalence graph with its native forward/backward direction. -/
  | explicitAxis (direction : Direction) (W : ArchCtx A) (V : ArchCtx B) (x : W.Axis) (y : V.Axis) :
      RealizationQuery A B .explicit
  /-- Explicit observable-equivalence graph with its native forward/backward direction. -/
  | explicitObservable (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
      (x : W.Observable) (y : V.Observable) : RealizationQuery A B .explicit
  /-- Support action of an actual source context morphism at candidate target contexts. -/
  | actualSupport (W X : ArchCtx A) (V Y : ArchCtx B) (g : ContextMorphism W X)
      (input : V.Support) (output : Y.Support) : RealizationQuery A B .explicit
  /-- Axis action of that actual source context morphism. -/
  | actualAxis (W X : ArchCtx A) (V Y : ArchCtx B) (g : ContextMorphism W X)
      (input : V.Axis) (output : Y.Axis) : RealizationQuery A B .explicit
  /-- Contravariant observable action of that actual source context morphism. -/
  | actualObservable (W X : ArchCtx A) (V Y : ArchCtx B) (g : ContextMorphism W X)
      (input : Y.Observable) (output : V.Observable) : RealizationQuery A B .explicit

/-- Hom point roles referring to candidate architecture objects, with no selected site or base map. -/
inductive DependentQuery (mode : Mode) (A B : ArchitectureObject U) where
  /-- Forward/backward equation-index graph at candidate raw carriers. -/
  | equation (direction : Direction) (q : IndependentCarrierGraph.Query.{u, u})
  /-- Forward/backward context-object graph, retaining preorder equivalence rather than object bijectivity. -/
  | context (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
  /-- Observable ring-equivalence graph at a candidate forward-context pair. -/
  | observable (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
      (q : IndependentCarrierGraph.Query.{u, u})
  /-- Mode-specific explicit raw-map points. -/
  | raw (q : RawQuery A B mode)
  /-- Mode-specific representative or actual-context realization points. -/
  | realization (q : RealizationQuery A B mode)

/-- One closed common Hom declaration on native primitive references and point pairs. -/
inductive Query (U : AtomCarrier.{u}) (mode : Mode) where
  /-- Directed map of the lower doctrine's source carrier. -/
  | source (q : IndependentCarrierGraph.Query.{u, u})
  /-- The lower pointed Atom equivalence is retained separately from the upper Atom equivalence. -/
  | pointedAtom (direction : Direction) (a b : U.Atom)
  /-- The upper Atom equivalence, with its pointwise agreement law imposed later. -/
  | atom (direction : Direction) (a b : U.Atom)
  /-- Directed architecture-object map, using one source/target reference pair. -/
  | object (A B : ArchitectureObject U)
  /-- Directed invariant-index map at candidate primitive carriers. -/
  | invariant (q : IndependentCarrierGraph.Query.{u, u})
  /-- Directed operation map at candidate source and image endpoint references. -/
  | operation (A B A' B' : ArchitectureObject U) (q : IndependentCarrierGraph.Query.{u, u})
  /-- Directed signature-axis map at candidate primitive carriers. -/
  | signatureAxis (q : IndependentCarrierGraph.Query.{u, u})
  /-- Signature-coordinate equivalence at a candidate signature-axis pair. -/
  | signatureCoordinate (direction : Direction) (I J : Type u) (i : I) (j : J)
      (q : IndependentCarrierGraph.Query.{u, u})
  /-- Directed coefficient map; no backward coefficient map is required. -/
  | coefficient (q : IndependentCarrierGraph.Query.{v, v})
  /-- Derived transport matching of candidate Atom-family references. -/
  | familyTransport (F F' : AtomFamily U)
  /-- Derived transport matching of candidate configuration references. -/
  | configurationTransport (C C' : AtomConfiguration U)
  /-- A dependent Hom point at candidate source/target architecture references. -/
  | atObjects (A B : ArchitectureObject U) (q : DependentQuery mode A B)

/-- Every common Hom cell is a single Boolean, with normalized false values at inactive references. -/
abbrev Table (U : AtomCarrier.{u}) (mode : Mode) := Query.{u, v} U mode → Bool

/-- Source-carrier point graphs are a direct role projection of the common Hom table. -/
def source {mode : Mode} (t : Table.{u, v} U mode) : IndependentCarrierGraph.Table.{u, u} :=
  fun q => t (.source q)

/-- Coefficient point graphs retain the original directed map and coefficient universe. -/
def coefficient {mode : Mode} (t : Table.{u, v} U mode) : IndependentCarrierGraph.Table.{v, v} :=
  fun q => t (.coefficient q)

/-- Invariant-index points are a direct role projection, without a selected invariant family in their type. -/
def invariant {mode : Mode} (t : Table.{u, v} U mode) : IndependentCarrierGraph.Table.{u, u} :=
  fun q => t (.invariant q)

/-- Signature-axis points are a direct role projection. -/
def signatureAxis {mode : Mode} (t : Table.{u, v} U mode) : IndependentCarrierGraph.Table.{u, u} :=
  fun q => t (.signatureAxis q)

/-- Dependent points are addressed by raw candidate references before native object assembly. -/
def dependent {mode : Mode} (t : Table.{u, v} U mode) (A B : ArchitectureObject U) :
    DependentQuery mode A B → Bool := fun q => t (.atObjects A B q)

/-- Either inactive endpoint forces the corresponding dependent Hom row to be uniformly false. -/
def IsActiveTyped {mode : Mode}
    (s t : IndependentGeometryPrimitive.Table.{u, v} U) (h : Table.{u, v} U mode) : Prop :=
  ∀ A B (q : DependentQuery mode A B),
    (IndependentGeometryPrimitive.matching s (.object A) = false ∨
      IndependentGeometryPrimitive.matching t (.object B) = false) → h (.atObjects A B q) = false

/-- The representative mode cannot accidentally acquire explicit raw-isomorphism data. -/
theorem representative_has_no_raw_query {A B : ArchitectureObject U} (q : RawQuery A B .representative) :
    False := by cases q

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive
