import ResearchLean.AG.LocalSemanticReconstruction.FiniteCommonHomReading
import Formal.Util.AssertStandardAxioms

/-! Application readings decoded from the shared primitive Hom table. -/

namespace AAT.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders

open CategoryTheory IndependentAATPrimitiveReconstruction
open AAT.AG.RealizationReconstruction
open IndependentGeometryHomPrimitive

universe u

private abbrev LensParameter (input : LensFamilyInput.{u}) : Parameter.{u, u} :=
  .lens input

/-- The selected lens point query uses the actual source and target state carriers. -/
def lensPointQuery (input : LensFamilyInput.{u})
    (source target : NativeCategory (LensParameter input))
    (x : (ULiftHom.objDown source).Carrier)
    (y : (ULiftHom.objDown target).Carrier) :
    HomQuery (LensParameter input) :=
  .edge (ULiftHom.objDown source).Carrier (ULiftHom.objDown target).Carrier x y

/-- Decode one semantic lens state-map point from the common local Hom table. -/
def decodeLensPoint (input : LensFamilyInput.{u})
    (source target : NativeCategory (LensParameter input))
    (x : (ULiftHom.objDown source).Carrier)
    (y : (ULiftHom.objDown target).Carrier)
    (table : HomTable (LensParameter input)) : Bool :=
  table (lensPointQuery input source target x y)

/-- The semantic state-map reading is recovered from the common main reader. -/
theorem lensPoint_decode (input : LensFamilyInput.{u})
    {source target : NativeCategory (LensParameter input)}
    (morphism : source ⟶ target)
    (x : (ULiftHom.objDown source).Carrier)
    (y : (ULiftHom.objDown target).Carrier) :
    decodeLensPoint input source target x y
        (localHomTable (LensParameter input)
          ((reading (LensParameter input)).map morphism)) = true ↔
      morphism.down.toFun x = y := by
  rw [decodeLensPoint, FiniteCommonHomReading.homPoint_read]
  exact IndependentCarrierGraph.read_edge _ _ morphism.down.toFun x y

/-- One lens point requires exactly one primitive Hom query. -/
def lensPointSupport (input : LensFamilyInput.{u})
    (source target : NativeCategory (LensParameter input))
    (x : (ULiftHom.objDown source).Carrier)
    (y : (ULiftHom.objDown target).Carrier) :
    Finset (HomQuery (LensParameter input)) :=
  {lensPointQuery input source target x y}

theorem lensPointSupport_read (input : LensFamilyInput.{u})
    {source target : NativeCategory (LensParameter input)}
    (morphism : source ⟶ target)
    (x : (ULiftHom.objDown source).Carrier)
    (y : (ULiftHom.objDown target).Carrier) :
    ∀ query : {query // query ∈ lensPointSupport input source target x y},
      localHomTable (LensParameter input)
          ((reading (LensParameter input)).map morphism) query.1 =
        nativeHomTable (LensParameter input) morphism query.1 :=
  FiniteCommonHomReading.finiteHomSupport_read _ morphism _

private abbrev ProtocolParameter (input : ProtocolFamilyInput.{u}) :
    Parameter.{u, u} := .protocol input

/-- A named protocol vertex and point pair select one common Hom cell. -/
def protocolPointQuery (input : ProtocolFamilyInput.{u})
    (source target : NativeCategory (ProtocolParameter input))
    (vertex : input.schema.Vertex)
    (x : (ULiftHom.objDown source).toFunctor.obj
      (input.schema.vertexObject vertex))
    (y : (ULiftHom.objDown target).toFunctor.obj
      (input.schema.vertexObject vertex)) :
    HomQuery (ProtocolParameter input) :=
  .map vertex (.edge _ _ x y)

/-- Decode one vertex-map point from the shared local Hom table. -/
def decodeProtocolPoint (input : ProtocolFamilyInput.{u})
    (source target : NativeCategory (ProtocolParameter input))
    (vertex : input.schema.Vertex)
    (x : (ULiftHom.objDown source).toFunctor.obj
      (input.schema.vertexObject vertex))
    (y : (ULiftHom.objDown target).toFunctor.obj
      (input.schema.vertexObject vertex))
    (table : HomTable (ProtocolParameter input)) : Bool :=
  table (protocolPointQuery input source target vertex x y)

/-- The protocol semantic generator map is read at the same primitive point. -/
theorem protocolPoint_decode (input : ProtocolFamilyInput.{u})
    {source target : NativeCategory (ProtocolParameter input)}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex)
    (x : (ULiftHom.objDown source).toFunctor.obj
      (input.schema.vertexObject vertex))
    (y : (ULiftHom.objDown target).toFunctor.obj
      (input.schema.vertexObject vertex)) :
    decodeProtocolPoint input source target vertex x y
        (localHomTable (ProtocolParameter input)
          ((reading (ProtocolParameter input)).map morphism)) = true ↔
      (ProtocolRealization.res morphism.down).component vertex x = y := by
  rw [decodeProtocolPoint, FiniteCommonHomReading.homPoint_read]
  exact IndependentCarrierGraph.read_edge _ _
    ((ProtocolRealization.res morphism.down).component vertex) x y

/-- Each selected protocol vertex-map point has one primitive Hom query. -/
def protocolPointSupport (input : ProtocolFamilyInput.{u})
    (source target : NativeCategory (ProtocolParameter input))
    (vertex : input.schema.Vertex)
    (x : (ULiftHom.objDown source).toFunctor.obj
      (input.schema.vertexObject vertex))
    (y : (ULiftHom.objDown target).toFunctor.obj
      (input.schema.vertexObject vertex)) :
    Finset (HomQuery (ProtocolParameter input)) :=
  {protocolPointQuery input source target vertex x y}

theorem protocolPointSupport_read (input : ProtocolFamilyInput.{u})
    {source target : NativeCategory (ProtocolParameter input)}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex)
    (x : (ULiftHom.objDown source).toFunctor.obj
      (input.schema.vertexObject vertex))
    (y : (ULiftHom.objDown target).toFunctor.obj
      (input.schema.vertexObject vertex)) :
    ∀ query : {query // query ∈ protocolPointSupport input source target vertex x y},
      localHomTable (ProtocolParameter input)
          ((reading (ProtocolParameter input)).map morphism) query.1 =
        nativeHomTable (ProtocolParameter input) morphism query.1 :=
  FiniteCommonHomReading.finiteHomSupport_read _ morphism _

private abbrev TagParameter : Parameter.{0, 0} :=
  .geometry FiniteModel.carrier Mode.explicit

/-- Test the actual tagged identity operation against its true-tag output. -/
noncomputable def tagPointQuery
    (source : ArchitectureObject FiniteModel.carrier) :
    HomQuery TagParameter :=
  .operation source source source source
    (.edge _ _ (taggedIdentityOperation source)
      ((taggedIdentityOperation source).1, true))

/-- The tag decoder reads an operation point, never a source-map point. -/
noncomputable def decodeTagAt
    (source : ArchitectureObject FiniteModel.carrier)
    (table : HomTable TagParameter) : Bool :=
  table (tagPointQuery source)

/-- One tag reading depends on a singleton operation query. -/
noncomputable def tagPointSupport
    (source : ArchitectureObject FiniteModel.carrier) :
    Finset (HomQuery TagParameter) :=
  {tagPointQuery source}

theorem tagPointSupport_read
    (choice : ArchitectureObject FiniteModel.carrier → Bool)
    (source : ArchitectureObject FiniteModel.carrier) :
    ∀ query : {query // query ∈ tagPointSupport source},
      localHomTable TagParameter
          ((reading TagParameter).map
            (taggedSourceChoiceNativeHom choice)) query.1 =
        nativeHomTable TagParameter (taggedSourceChoiceNativeHom choice) query.1 :=
  FiniteCommonHomReading.finiteHomSupport_read _ _ _

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders

end AAT.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders
