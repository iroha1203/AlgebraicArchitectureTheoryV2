import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryCategoryReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomIntegrationControls
import ResearchLean.AG.LocalSemanticReconstruction.IndependentLensPrimitiveReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.IndependentProtocolPrimitiveReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.AATFourFamilyTotalReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel
import ResearchLean.AG.RealizationReconstruction.G122OriginalInput
import ResearchLean.AG.RealizationReconstruction.CSAATIndependentPackageCategories
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Comma.Arrow
import Formal.Util.AssertStandardAxioms

/-!
# Common independent primitive reconstruction for AAT

The representative and explicit geometry readings and the two CS primitive
readings are selected by one parameter.  Each branch retains its existing
native and local category, with `ULiftHom` used only to align Hom universes.
The common reconstruction data is built from the concrete separation and
assembly data of each branch.  The main equivalence is then obtained by one
application of the general reconstruction theorem.

The common query declaration only tags the existing object and Hom queries by
their source, target, or Hom role.  Its finite fragments are the existing
dependent finite fragments specialized to that declaration.

Implementation notes: the common certificates reuse the law and data carried
by each existing branch.  Geometry keeps the canonical `Presentation`
obtained by reading its assembled invariant witness, while the two CS branches
lift their existing propositions into data.  This construction does not choose
one of the four completed equivalences: those equivalences are consequences of
the common reconstruction and would make its input depend on its output.  A
geometry presentation is also not hidden behind propositional existence,
because the inverse construction must consume that presentation directly.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory CategoryTheory.Idempotents AtomFoundation GeometryTransport
open AAT.AG.RealizationReconstruction
open LocalReconstructionEquivalence
open IndependentGeometryHomPrimitive

noncomputable section

namespace IndependentAATPrimitiveReconstruction

universe u v u₁ u₂ u₃ v₁ v₂ v₃ w

attribute [local instance] uliftCategory

/-- One parameter selecting representative geometry, explicit geometry,
lens, or protocol primitive reconstruction. -/
inductive Parameter : Type (max (u + 1) (v + 1))
  | geometry (carrier : AtomCarrier.{u}) (mode : Mode)
  | lens (input : LensFamilyInput.{max u v})
  | protocol (input : ProtocolFamilyInput.{max u v})

/-- Existing native categories selected by the common parameter. -/
def NativeCategory : Parameter.{u, v} → Type (max (u + 1) (v + 1))
  | .geometry carrier .representative =>
      ULiftHom.{max (u + 1) v} (GeomReadCategory.{u, v} carrier)
  | .geometry carrier .explicit =>
      ULiftHom.{max (u + 1) v} (ExplicitExactGeomCategory.{u, v} carrier)
  | .lens input => ULiftHom.{max (u + 1) v}
      (LensRealization input.View input.reference)
  | .protocol input => ULiftHom.{max (u + 1) v}
      (ProtocolRealization input.schema input.observation)

/-- Existing primitive local categories selected by the common parameter. -/
def LocalCategory : Parameter.{u, v} → Type (max (u + 1) (v + 1))
  | .geometry carrier .representative =>
      ULiftHom.{max (u + 1) v}
        (IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
          carrier)
  | .geometry carrier .explicit =>
      ULiftHom.{max (u + 1) v}
        (IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
          carrier)
  | .lens input => ULiftHom.{max (u + 1) v}
      (IndependentLensPrimitiveReconstruction.Object input)
  | .protocol input => ULiftHom.{max (u + 1) v}
      (IndependentProtocolPrimitiveReconstruction.Object input)

/-- Every selected native type carries the original category structure after
the minimal universe lift. -/
noncomputable instance nativeCategoryInstance (parameter : Parameter.{u, v}) :
    Category (NativeCategory parameter) := by
  cases parameter with
  | geometry carrier mode =>
      cases mode <;> simp only [NativeCategory] <;> infer_instance
  | lens input => simp only [NativeCategory]; infer_instance
  | protocol input => simp only [NativeCategory]; infer_instance

/-- Every selected local type carries its directly defined primitive category
structure after the minimal universe lift. -/
noncomputable instance localCategoryInstance (parameter : Parameter.{u, v}) :
    Category (LocalCategory parameter) := by
  cases parameter with
  | geometry carrier mode =>
      cases mode <;> simp only [LocalCategory] <;> infer_instance
  | lens input => simp only [LocalCategory]; infer_instance
  | protocol input => simp only [LocalCategory]; infer_instance

/-! ### One primitive declaration and its finite fragments -/

/-- Existing primitive object queries selected by the common parameter. -/
def ObjectQuery : Parameter.{u, v} → Type (max (u + 1) (v + 1))
  | .geometry carrier _ => IndependentGeometryPrimitive.Query.{u, v} carrier
  | .lens input => IndependentLensPrimitiveReconstruction.ObjectQuery input
  | .protocol input => IndependentProtocolPrimitiveReconstruction.ObjectQuery input

/-- Existing dependent primitive object values selected by the common
parameter. -/
def ObjectValue {parameter : Parameter.{u, v}} :
    ObjectQuery parameter → Type (max (u + 1) (v + 1)) := by
  cases parameter with
  | geometry carrier mode =>
      exact fun query => IndependentGeometryPrimitive.Query.Value query
  | lens input =>
      exact fun query => IndependentLensPrimitiveReconstruction.ObjectValue query
  | protocol input =>
      exact fun query => IndependentProtocolPrimitiveReconstruction.ObjectValue query

/-- Existing primitive Hom queries selected by the common parameter. -/
def HomQuery : Parameter.{u, v} → Type (max (u + 1) (v + 1))
  | .geometry carrier mode =>
      IndependentGeometryHomPrimitive.Query.{u, v} carrier mode
  | .lens _ => IndependentCarrierGraph.Query.{max u v, max u v}
  | .protocol input =>
      IndependentProtocolPrimitiveReconstruction.HomTableQuery input

/-- All selected Hom queries have the existing Boolean response. -/
abbrev HomValue {parameter : Parameter.{u, v}} (_ : HomQuery parameter) :=
  ULift.{max (u + 1) (v + 1)} Bool

/-- Common source-object, target-object, and Hom query roles. -/
inductive Query (parameter : Parameter.{u, v}) :
    Type (max (u + 1) (v + 1)) where
  /-- One existing source-object primitive query. -/
  | source (query : ObjectQuery parameter)
  /-- One existing target-object primitive query. -/
  | target (query : ObjectQuery parameter)
  /-- One existing primitive Hom query. -/
  | hom (query : HomQuery parameter)

/-- Dependent values of the common primitive query declaration. -/
def Value {parameter : Parameter.{u, v}} :
    Query parameter → Type (max (u + 1) (v + 1))
  | .source query => ObjectValue query
  | .target query => ObjectValue query
  | .hom _ => ULift Bool

/-- A common primitive table assigns one correctly typed value to every
tagged query. -/
abbrev Table (parameter : Parameter.{u, v}) :=
  (query : Query parameter) → Value query

/-- A finite common primitive fragment is the existing dependent fragment
specialized to one finite query set. -/
abbrev Fragment {parameter : Parameter.{u, v}}
    (support : Finset (Query parameter)) :=
  IndependentFiniteFragments.Fragment
    (fun query : Query parameter => Value query) support

/-- A family of all finite common primitive restrictions. -/
abbrev FragmentFamily (parameter : Parameter.{u, v}) :=
  IndependentFiniteFragments.FragmentFamily
    (fun query : Query parameter => Value query)

/-- Compatibility of common primitive fragments is the existing restriction
compatibility condition. -/
abbrev Compatible {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) :=
  IndependentFiniteFragments.Compatible family

/-- Restrict a common primitive table to all finite query sets. -/
def fragments {parameter : Parameter.{u, v}} (table : Table parameter) :
    FragmentFamily parameter :=
  IndependentFiniteFragments.fragments table

/-- Glue a compatible common primitive family from its singleton cells. -/
def glue {parameter : Parameter.{u, v}} (family : FragmentFamily parameter) :
    Table parameter :=
  IndependentFiniteFragments.glue family

/-- Restrictions of every common primitive table are compatible. -/
theorem fragments_compatible {parameter : Parameter.{u, v}}
    (table : Table parameter) : Compatible (fragments table) :=
  IndependentFiniteFragments.fragments_compatible table

/-- Gluing all finite restrictions recovers a common primitive table. -/
theorem glue_fragments {parameter : Parameter.{u, v}}
    (table : Table parameter) : glue (fragments table) = table :=
  IndependentFiniteFragments.glue_fragments table

/-- A compatible common primitive family is recovered after gluing. -/
theorem fragments_glue {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) (compatible : Compatible family) :
    fragments (glue family) = family :=
  IndependentFiniteFragments.fragments_glue family compatible

/-! ### Common reading and reconstruction -/

/-- The four existing primitive readers, with only the universe lifts needed
to give them one dependent codomain. -/
noncomputable def reading (parameter : Parameter.{u, v}) :
    NativeCategory parameter ⥤ LocalCategory parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C := GeomReadCategory.{u, v} carrier)) ⋙
            IndependentGeometryCategoryReconstruction.representativeReadingFunctor
              carrier ⋙
            (ULiftHom.up (C :=
              IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                carrier))
      | explicit =>
          exact (ULiftHom.down (C :=
              ExplicitExactGeomCategory.{u, v} carrier)) ⋙
            IndependentGeometryCategoryReconstruction.explicitReadingFunctor
              carrier ⋙
            (ULiftHom.up (C :=
              IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                carrier))
  | lens input =>
      exact (ULiftHom.down (C :=
          LensRealization input.View input.reference)) ⋙
        IndependentLensPrimitiveReconstruction.readingFunctor input ⋙
        (ULiftHom.up (C := IndependentLensPrimitiveReconstruction.Object input))
  | protocol input =>
      exact (ULiftHom.down (C :=
          ProtocolRealization input.schema input.observation)) ⋙
        IndependentProtocolPrimitiveReconstruction.readingFunctor input ⋙
        (ULiftHom.up (C := IndependentProtocolPrimitiveReconstruction.Object input))

/-- No-unfold evaluation of the representative geometry branch reader. -/
@[simp] theorem reading_geometry_representative
    (carrier : AtomCarrier.{u}) :
    reading (Parameter.geometry carrier Mode.representative : Parameter.{u, v}) =
      (ULiftHom.down (C := GeomReadCategory.{u, v} carrier)) ⋙
        IndependentGeometryCategoryReconstruction.representativeReadingFunctor
          carrier ⋙
        (ULiftHom.up (C :=
          IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
            carrier)) := rfl

/-- No-unfold evaluation of the explicit geometry branch reader. -/
@[simp] theorem reading_geometry_explicit (carrier : AtomCarrier.{u}) :
    reading (Parameter.geometry carrier Mode.explicit : Parameter.{u, v}) =
      (ULiftHom.down (C := ExplicitExactGeomCategory.{u, v} carrier)) ⋙
        IndependentGeometryCategoryReconstruction.explicitReadingFunctor
          carrier ⋙
        (ULiftHom.up (C :=
          IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
            carrier)) := rfl

/-- No-unfold evaluation of the lens branch reader. -/
@[simp] theorem reading_lens (input : LensFamilyInput.{max u v}) :
    reading (Parameter.lens input : Parameter.{u, v}) =
      (ULiftHom.down (C := LensRealization input.View input.reference)) ⋙
        IndependentLensPrimitiveReconstruction.readingFunctor input ⋙
        (ULiftHom.up (C := IndependentLensPrimitiveReconstruction.Object input)) := rfl

/-- No-unfold evaluation of the protocol branch reader. -/
@[simp] theorem reading_protocol (input : ProtocolFamilyInput.{max u v}) :
    reading (Parameter.protocol input : Parameter.{u, v}) =
      (ULiftHom.down (C :=
          ProtocolRealization input.schema input.observation)) ⋙
        IndependentProtocolPrimitiveReconstruction.readingFunctor input ⋙
        (ULiftHom.up (C := IndependentProtocolPrimitiveReconstruction.Object input)) := rfl

/-- No-unfold API for direct assembly of a common primitive Hom. -/
noncomputable def assembleHom (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter}
    (localMorphism : (reading parameter).obj source ⟶
      (reading parameter).obj target) : source ⟶ target := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          let data := IndependentGeometryCategoryReconstruction.representativeReconstructionData
            carrier
          exact ⟨data.homAssembly.assemble localMorphism.down⟩
      | explicit =>
          let data := IndependentGeometryCategoryReconstruction.explicitReconstructionData
            carrier
          exact ⟨data.homAssembly.assemble localMorphism.down⟩
  | lens input =>
      let data := IndependentLensPrimitiveReconstruction.reconstructionData input
      exact ⟨data.homAssembly.assemble localMorphism.down⟩
  | protocol input =>
      let data := IndependentProtocolPrimitiveReconstruction.reconstructionData input
      exact ⟨data.homAssembly.assemble localMorphism.down⟩

/-- Reading after common direct Hom assembly recovers every local Hom. -/
@[simp] theorem read_assembleHom (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter}
    (localMorphism : (reading parameter).obj source ⟶
      (reading parameter).obj target) :
    (reading parameter).map (assembleHom parameter localMorphism) =
      localMorphism := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          apply ULift.ext
          let data := IndependentGeometryCategoryReconstruction.representativeReconstructionData
            carrier
          exact data.homAssembly.map_assemble localMorphism.down
      | explicit =>
          apply ULift.ext
          let data := IndependentGeometryCategoryReconstruction.explicitReconstructionData
            carrier
          exact data.homAssembly.map_assemble localMorphism.down
  | lens input =>
      apply ULift.ext
      let data := IndependentLensPrimitiveReconstruction.reconstructionData input
      exact data.homAssembly.map_assemble localMorphism.down
  | protocol input =>
      apply ULift.ext
      let data := IndependentProtocolPrimitiveReconstruction.reconstructionData input
      exact data.homAssembly.map_assemble localMorphism.down

/-- Common direct Hom assembly after reading recovers every native Hom. -/
@[simp] theorem assembleHom_read (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} (morphism : source ⟶ target) :
    assembleHom parameter ((reading parameter).map morphism) = morphism := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          apply ULift.ext
          let data := IndependentGeometryCategoryReconstruction.representativeReconstructionData
            carrier
          exact data.assemble_map morphism.down
      | explicit =>
          apply ULift.ext
          let data := IndependentGeometryCategoryReconstruction.explicitReconstructionData
            carrier
          exact data.assemble_map morphism.down
  | lens input =>
      apply ULift.ext
      let data := IndependentLensPrimitiveReconstruction.reconstructionData input
      exact data.assemble_map morphism.down
  | protocol input =>
      apply ULift.ext
      let data := IndependentProtocolPrimitiveReconstruction.reconstructionData input
      exact data.assemble_map morphism.down

/-- No-unfold API for direct assembly of a common primitive object. -/
noncomputable def assembleObject (parameter : Parameter.{u, v})
    (localObject : LocalCategory parameter) : NativeCategory parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          let data := IndependentGeometryCategoryReconstruction.representativeReconstructionData
            carrier
          exact ULiftHom.objUp
            (data.objectAssembly.assembleObject (ULiftHom.objDown localObject))
      | explicit =>
          let data := IndependentGeometryCategoryReconstruction.explicitReconstructionData
            carrier
          exact ULiftHom.objUp
            (data.objectAssembly.assembleObject (ULiftHom.objDown localObject))
  | lens input =>
      let data := IndependentLensPrimitiveReconstruction.reconstructionData input
      exact ULiftHom.objUp
        (data.objectAssembly.assembleObject (ULiftHom.objDown localObject))
  | protocol input =>
      let data := IndependentProtocolPrimitiveReconstruction.reconstructionData input
      exact ULiftHom.objUp
        (data.objectAssembly.assembleObject (ULiftHom.objDown localObject))

/-- Reading a directly assembled common object recovers it up to isomorphism. -/
noncomputable def readAssembledObjectIso (parameter : Parameter.{u, v})
    (localObject : LocalCategory parameter) :
    (reading parameter).obj (assembleObject parameter localObject) ≅ localObject := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          let data := IndependentGeometryCategoryReconstruction.representativeReconstructionData
            carrier
          exact ULiftHom.up.mapIso
            (data.objectAssembly.readAssembledIso (ULiftHom.objDown localObject))
      | explicit =>
          let data := IndependentGeometryCategoryReconstruction.explicitReconstructionData
            carrier
          exact ULiftHom.up.mapIso
            (data.objectAssembly.readAssembledIso (ULiftHom.objDown localObject))
  | lens input =>
      let data := IndependentLensPrimitiveReconstruction.reconstructionData input
      exact ULiftHom.up.mapIso
        (data.objectAssembly.readAssembledIso (ULiftHom.objDown localObject))
  | protocol input =>
      let data := IndependentProtocolPrimitiveReconstruction.reconstructionData input
      exact ULiftHom.up.mapIso
        (data.objectAssembly.readAssembledIso (ULiftHom.objDown localObject))

/-! ### Common total tables and finite restrictions -/

/-- The complete object table selected by one common parameter. -/
abbrev ObjectTable (parameter : Parameter.{u, v}) :=
  (query : ObjectQuery parameter) → ObjectValue query

/-- The complete Boolean Hom table selected by one common parameter. -/
abbrev HomTable (parameter : Parameter.{u, v}) :=
  HomQuery parameter → Bool

/-- Read the object table retained by an existing primitive local object. -/
def localObjectTable (parameter : Parameter.{u, v}) :
    LocalCategory parameter → ObjectTable parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact fun object => IndependentGeometryPrimitive.glue
            (ULiftHom.objDown object).localObject.val
      | explicit =>
          exact fun object => IndependentGeometryPrimitive.glue
            (ULiftHom.objDown object).localObject.val
  | lens input =>
      exact fun object => IndependentLensPrimitiveReconstruction.Object.table
        (ULiftHom.objDown object)
  | protocol input =>
      exact fun object => IndependentProtocolPrimitiveReconstruction.Object.table
        (ULiftHom.objDown object)

/-- Read the existing primitive object table directly from a native object. -/
def nativeObjectTable (parameter : Parameter.{u, v}) :
    NativeCategory parameter → ObjectTable parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact fun object => IndependentGeometryPrimitive.read
            (ULiftHom.objDown object)
      | explicit =>
          exact fun object => IndependentGeometryPrimitive.read
            (ULiftHom.objDown object).toGeometryPackage
  | lens input =>
      exact fun object => IndependentLensPrimitiveReconstruction.readDataTable
        (ULiftHom.objDown object).toLensData
  | protocol input =>
      exact fun object => IndependentProtocolPrimitiveReconstruction.readDataTable
        (ULiftHom.objDown object)

/-- Read the Boolean point table retained by an existing primitive local Hom. -/
def localHomTable (parameter : Parameter.{u, v})
    {source target : LocalCategory parameter} :
    (source ⟶ target) → HomTable parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact fun morphism query => InvariantWitness.point _ _
            morphism.down.val query
      | explicit =>
          exact fun morphism query => InvariantWitness.point _ _
            morphism.down.val query
  | lens input =>
      exact fun morphism => IndependentLensPrimitiveReconstruction.Hom.table
        morphism.down
  | protocol input =>
      exact fun morphism => IndependentProtocolPrimitiveReconstruction.Hom.table
        morphism.down

/-- Read the existing Boolean point table directly from a native Hom. -/
def nativeHomTable (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} :
    (source ⟶ target) → HomTable parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact fun morphism =>
            IndependentGeometryHomPrimitive.NativeReader.readRepresentative
              morphism.down
      | explicit =>
          exact fun morphism =>
            IndependentGeometryHomPrimitive.NativeReader.readExplicit morphism.down
  | lens input =>
      exact fun morphism => IndependentCarrierGraph.read _ _ morphism.down.toFun
  | protocol input =>
      exact fun morphism query => match query with
        | .map vertex graphQuery =>
            IndependentCarrierGraph.read _ _
              ((ProtocolRealization.res morphism.down).component vertex) graphQuery

/-- Combine source, target, and Hom tables into the common tagged table. -/
def packTable {parameter : Parameter.{u, v}}
    (source target : ObjectTable parameter) (hom : HomTable parameter) :
    Table parameter
  | .source query => source query
  | .target query => target query
  | .hom query => ULift.up (hom query)

/-- Restrict a common table to its source-object role. -/
def sourceTable {parameter : Parameter.{u, v}} (table : Table parameter) :
    ObjectTable parameter := fun query => table (.source query)

/-- Restrict a common table to its target-object role. -/
def targetTable {parameter : Parameter.{u, v}} (table : Table parameter) :
    ObjectTable parameter := fun query => table (.target query)

/-- Restrict a common table to its Boolean Hom role. -/
def homTable {parameter : Parameter.{u, v}} (table : Table parameter) :
    HomTable parameter := fun query => (table (.hom query)).down

/-- The common table read from one existing primitive local Hom. -/
def localTable (parameter : Parameter.{u, v})
    {source target : LocalCategory parameter} (morphism : source ⟶ target) :
    Table parameter :=
  packTable (localObjectTable parameter source) (localObjectTable parameter target)
    (localHomTable parameter morphism)

/-- The common table read directly from one native Hom. -/
def nativeTable (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} (morphism : source ⟶ target) :
    Table parameter :=
  packTable (nativeObjectTable parameter source) (nativeObjectTable parameter target)
    (nativeHomTable parameter morphism)

/-- Packing and then selecting the source role restores the source table. -/
@[simp] theorem sourceTable_packTable {parameter : Parameter.{u, v}}
    (source target : ObjectTable parameter) (hom : HomTable parameter) :
    sourceTable (packTable source target hom) = source := rfl

/-- Packing and then selecting the target role restores the target table. -/
@[simp] theorem targetTable_packTable {parameter : Parameter.{u, v}}
    (source target : ObjectTable parameter) (hom : HomTable parameter) :
    targetTable (packTable source target hom) = target := rfl

/-- Packing and then selecting the Hom role restores the Boolean Hom table. -/
@[simp] theorem homTable_packTable {parameter : Parameter.{u, v}}
    (source target : ObjectTable parameter) (hom : HomTable parameter) :
    homTable (packTable source target hom) = hom := rfl

/-- Local object-table reading after semantic reading is the direct native
object table. -/
theorem localObjectTable_read (parameter : Parameter.{u, v})
    (object : NativeCategory parameter) :
    localObjectTable parameter ((reading parameter).obj object) =
      nativeObjectTable parameter object := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          change IndependentGeometryPrimitive.glue
              (IndependentGeometryPrimitive.fragments
                (IndependentGeometryPrimitive.read
                  (ULiftHom.objDown
                    (C := GeomReadCategory.{u, v} carrier) object))) =
            IndependentGeometryPrimitive.read
              (ULiftHom.objDown
                (C := GeomReadCategory.{u, v} carrier) object)
          exact IndependentGeometryPrimitive.glue_fragments _
      | explicit =>
          change IndependentGeometryPrimitive.glue
              (IndependentGeometryPrimitive.fragments
                (IndependentGeometryPrimitive.read
                  (ULiftHom.objDown
                    (C := ExplicitExactGeomCategory.{u, v} carrier)
                    object).toGeometryPackage)) =
            IndependentGeometryPrimitive.read
              (ULiftHom.objDown
                (C := ExplicitExactGeomCategory.{u, v} carrier)
                object).toGeometryPackage
          exact IndependentGeometryPrimitive.glue_fragments _
  | lens input =>
      change IndependentLensPrimitiveReconstruction.objectGlue
          (IndependentLensPrimitiveReconstruction.objectFragments
            (IndependentLensPrimitiveReconstruction.readDataTable
              (ULiftHom.objDown
                (C := LensRealization input.View input.reference)
                object).toLensData)) =
        IndependentLensPrimitiveReconstruction.readDataTable
          (ULiftHom.objDown
            (C := LensRealization input.View input.reference) object).toLensData
      exact IndependentLensPrimitiveReconstruction.objectGlue_fragments _
  | protocol input =>
      change IndependentProtocolPrimitiveReconstruction.objectGlue
          (IndependentProtocolPrimitiveReconstruction.objectFragments
            (IndependentProtocolPrimitiveReconstruction.readDataTable
              (ULiftHom.objDown
                (C := ProtocolRealization input.schema input.observation)
                object))) =
        IndependentProtocolPrimitiveReconstruction.readDataTable
          (ULiftHom.objDown
            (C := ProtocolRealization input.schema input.observation) object)
      exact IndependentProtocolPrimitiveReconstruction.objectGlue_fragments _

/-- Representative geometry local-table reading agrees with the direct
native table. -/
theorem localTable_read_geometry_representative (carrier : AtomCarrier.{u})
    {source target : NativeCategory
      (Parameter.geometry carrier Mode.representative : Parameter.{u, v})}
    (morphism : source ⟶ target) :
    localTable (Parameter.geometry carrier Mode.representative)
        ((reading (Parameter.geometry carrier Mode.representative)).map morphism) =
      nativeTable (Parameter.geometry carrier Mode.representative) morphism := by
  funext query
  cases query with
  | source query =>
      exact congrFun
        (localObjectTable_read
          (Parameter.geometry carrier Mode.representative) source) query
  | target query =>
      exact congrFun
        (localObjectTable_read
          (Parameter.geometry carrier Mode.representative) target) query
  | hom query =>
      exact congrArg ULift.up
        (IndependentGeometryCategoryReconstruction.representativeReadingHomEquiv_point
          morphism.down query)

/-- Explicit geometry local-table reading agrees with the direct native
table. -/
theorem localTable_read_geometry_explicit (carrier : AtomCarrier.{u})
    {source target : NativeCategory
      (Parameter.geometry carrier Mode.explicit : Parameter.{u, v})}
    (morphism : source ⟶ target) :
    localTable (Parameter.geometry carrier Mode.explicit)
        ((reading (Parameter.geometry carrier Mode.explicit)).map morphism) =
      nativeTable (Parameter.geometry carrier Mode.explicit) morphism := by
  funext query
  cases query with
  | source query =>
      exact congrFun
        (localObjectTable_read
          (Parameter.geometry carrier Mode.explicit) source) query
  | target query =>
      exact congrFun
        (localObjectTable_read
          (Parameter.geometry carrier Mode.explicit) target) query
  | hom query =>
      exact congrArg ULift.up
        (IndependentGeometryCategoryReconstruction.explicitReadingHomEquiv_point
          morphism.down query)

/-- Lens local-table reading agrees with the direct native graph table. -/
theorem localTable_read_lens (input : LensFamilyInput.{max u v})
    {source target : NativeCategory (Parameter.lens input : Parameter.{u, v})}
    (morphism : source ⟶ target) :
    localTable (Parameter.lens input)
        ((reading (Parameter.lens input)).map morphism) =
      nativeTable (Parameter.lens input) morphism := by
  funext query
  cases query with
  | source query =>
      exact congrFun
        (localObjectTable_read (Parameter.lens input) source) query
  | target query =>
      exact congrFun
        (localObjectTable_read (Parameter.lens input) target) query
  | hom query =>
      exact congrArg ULift.up
        (IndependentLensPrimitiveReconstruction.readingFunctor_map_table
          input morphism.down query)

/-- Protocol local-table reading agrees with the direct native vertex-map
table. -/
theorem localTable_read_protocol (input : ProtocolFamilyInput.{max u v})
    {source target : NativeCategory (Parameter.protocol input : Parameter.{u, v})}
    (morphism : source ⟶ target) :
    localTable (Parameter.protocol input)
        ((reading (Parameter.protocol input)).map morphism) =
      nativeTable (Parameter.protocol input) morphism := by
  funext query
  cases query with
  | source query =>
      exact congrFun
        (localObjectTable_read (Parameter.protocol input) source) query
  | target query =>
      exact congrFun
        (localObjectTable_read (Parameter.protocol input) target) query
  | hom query =>
      exact congrArg ULift.up
        (IndependentProtocolPrimitiveReconstruction.table_readHom
          morphism.down query)

/-- Common local-table reading after the semantic reader is the direct native
source, target, and Hom table. -/
theorem localTable_read (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} (morphism : source ⟶ target) :
    localTable parameter ((reading parameter).map morphism) =
      nativeTable parameter morphism := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact localTable_read_geometry_representative carrier morphism
      | explicit => exact localTable_read_geometry_explicit carrier morphism
  | lens input => exact localTable_read_lens input morphism
  | protocol input => exact localTable_read_protocol input morphism

/-- Restricting the common table to finite supports and gluing it again
commutes with all three tagged roles. -/
theorem roleTables_glue_fragments {parameter : Parameter.{u, v}}
    (table : Table parameter) :
    sourceTable (glue (fragments table)) = sourceTable table ∧
      targetTable (glue (fragments table)) = targetTable table ∧
      homTable (glue (fragments table)) = homTable table := by
  rw [glue_fragments]
  exact ⟨rfl, rfl, rfl⟩

/-! ### Role embeddings and finite support -/

/-- Embed an object query into the source role of the common declaration. -/
def sourceQueryEmbedding (parameter : Parameter.{u, v}) :
    ObjectQuery parameter ↪ Query parameter where
  toFun := Query.source
  inj' := by intro first second equality; cases equality; rfl

/-- Embed an object query into the target role of the common declaration. -/
def targetQueryEmbedding (parameter : Parameter.{u, v}) :
    ObjectQuery parameter ↪ Query parameter where
  toFun := Query.target
  inj' := by intro first second equality; cases equality; rfl

/-- Embed a Hom query into the Hom role of the common declaration. -/
def homQueryEmbedding (parameter : Parameter.{u, v}) :
    HomQuery parameter ↪ Query parameter where
  toFun := Query.hom
  inj' := by intro first second equality; cases equality; rfl

/-- Restrict a common finite family to its source-object queries. -/
def sourceFamily {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) :
    IndependentFiniteFragments.FragmentFamily
      (fun query : ObjectQuery parameter => ObjectValue query) :=
  fun support query =>
    family (support.map (sourceQueryEmbedding parameter))
      ⟨.source query.val, Finset.mem_map.mpr
        ⟨query.val, query.property, rfl⟩⟩

/-- Restrict a common finite family to its target-object queries. -/
def targetFamily {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) :
    IndependentFiniteFragments.FragmentFamily
      (fun query : ObjectQuery parameter => ObjectValue query) :=
  fun support query =>
    family (support.map (targetQueryEmbedding parameter))
      ⟨.target query.val, Finset.mem_map.mpr
        ⟨query.val, query.property, rfl⟩⟩

/-- Finite Boolean fragment families over the existing Hom queries. -/
abbrev HomFragmentFamily (parameter : Parameter.{u, v}) :=
  IndependentFiniteFragments.FragmentFamily
    (fun _ : HomQuery parameter => Bool)

/-- Restrict a common finite family to its Boolean Hom queries. -/
def homFamily {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) : HomFragmentFamily parameter :=
  fun support query =>
    (family (support.map (homQueryEmbedding parameter))
      ⟨.hom query.val, Finset.mem_map.mpr
        ⟨query.val, query.property, rfl⟩⟩).down

/-- Source-role restriction commutes with restricting a complete table. -/
theorem sourceFamily_fragments {parameter : Parameter.{u, v}}
    (table : Table parameter) :
    sourceFamily (fragments table) =
      IndependentFiniteFragments.fragments (sourceTable table) := rfl

/-- Target-role restriction commutes with restricting a complete table. -/
theorem targetFamily_fragments {parameter : Parameter.{u, v}}
    (table : Table parameter) :
    targetFamily (fragments table) =
      IndependentFiniteFragments.fragments (targetTable table) := rfl

/-- Hom-role restriction commutes with restricting a complete table. -/
theorem homFamily_fragments {parameter : Parameter.{u, v}}
    (table : Table parameter) :
    homFamily (fragments table) =
      IndependentFiniteFragments.fragments (homTable table) := rfl

/-- Source-role gluing agrees with selecting the source of the common glue. -/
theorem objectGlue_sourceFamily {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) (compatible : Compatible family) :
    IndependentFiniteFragments.glue (sourceFamily family) =
      sourceTable (glue family) := by
  calc
    IndependentFiniteFragments.glue (sourceFamily family) =
        IndependentFiniteFragments.glue
          (sourceFamily (fragments (glue family))) :=
      congrArg IndependentFiniteFragments.glue
        (congrArg sourceFamily (fragments_glue family compatible).symm)
    _ = IndependentFiniteFragments.glue
          (IndependentFiniteFragments.fragments (sourceTable (glue family))) :=
      congrArg IndependentFiniteFragments.glue
        (sourceFamily_fragments (glue family))
    _ = sourceTable (glue family) :=
      IndependentFiniteFragments.glue_fragments _

/-- Target-role gluing agrees with selecting the target of the common glue. -/
theorem objectGlue_targetFamily {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) (compatible : Compatible family) :
    IndependentFiniteFragments.glue (targetFamily family) =
      targetTable (glue family) := by
  calc
    IndependentFiniteFragments.glue (targetFamily family) =
        IndependentFiniteFragments.glue
          (targetFamily (fragments (glue family))) :=
      congrArg IndependentFiniteFragments.glue
        (congrArg targetFamily (fragments_glue family compatible).symm)
    _ = IndependentFiniteFragments.glue
          (IndependentFiniteFragments.fragments (targetTable (glue family))) :=
      congrArg IndependentFiniteFragments.glue
        (targetFamily_fragments (glue family))
    _ = targetTable (glue family) :=
      IndependentFiniteFragments.glue_fragments _

/-- Hom-role gluing agrees with selecting the Hom part of the common glue. -/
theorem homGlue_homFamily {parameter : Parameter.{u, v}}
    (family : FragmentFamily parameter) (compatible : Compatible family) :
    IndependentFiniteFragments.glue (homFamily family) = homTable (glue family) := by
  calc
    IndependentFiniteFragments.glue (homFamily family) =
        IndependentFiniteFragments.glue
          (homFamily (fragments (glue family))) :=
      congrArg IndependentFiniteFragments.glue
        (congrArg homFamily (fragments_glue family compatible).symm)
    _ = IndependentFiniteFragments.glue
          (IndependentFiniteFragments.fragments (homTable (glue family))) :=
      congrArg IndependentFiniteFragments.glue
        (homFamily_fragments (glue family))
    _ = homTable (glue family) :=
      IndependentFiniteFragments.glue_fragments _

/-- The three-role image of one existing geometry formula support. -/
def geometryFormulaCommonSupport {carrier : AtomCarrier.{u}} {mode : Mode}
    (formula : IndependentFiniteLawFormula.Formula.{u, v, w} carrier mode) :
    Finset (Query
      (Parameter.geometry carrier mode : Parameter.{u, v})) := by
  classical
  exact formula.support.1.map
      (sourceQueryEmbedding (Parameter.geometry carrier mode)) ∪
    formula.support.2.1.map
      (targetQueryEmbedding (Parameter.geometry carrier mode)) ∪
    formula.support.2.2.map
      (homQueryEmbedding (Parameter.geometry carrier mode))

/-- Agreement on the common three-role support preserves evaluation of an
existing geometry formula. -/
theorem geometryFormula_evaluate_iff_of_commonSupport
    {carrier : AtomCarrier.{u}} {mode : Mode}
    (formula : IndependentFiniteLawFormula.Formula.{u, v, w} carrier mode)
    (first second : Table
      (Parameter.geometry carrier mode : Parameter.{u, v}))
    (agree : ∀ query ∈ geometryFormulaCommonSupport formula,
      first query = second query) :
    formula.evaluate (sourceTable first) (targetTable first) (homTable first) ↔
      formula.evaluate (sourceTable second) (targetTable second) (homTable second) := by
  classical
  apply IndependentFiniteLawFormula.Formula.evaluate_iff_of_support
  · intro query member
    apply agree (.source query)
    exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_map.mpr ⟨query, member, rfl⟩
  · intro query member
    apply agree (.target query)
    exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_map.mpr ⟨query, member, rfl⟩
  · intro query member
    apply congrArg ULift.down
    apply agree (.hom query)
    exact Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_map.mpr ⟨query, member, rfl⟩

/-- Embed a lens primitive Hom query into the matching common role. -/
def lensHomPrimitiveQueryEmbedding (input : LensFamilyInput.{u}) :
    IndependentLensPrimitiveReconstruction.HomPrimitiveQuery input ↪
      Query (Parameter.lens input : Parameter.{u, u}) where
  toFun
    | .source query => .source query
    | .target query => .target query
    | .map query => .hom query
  inj' := by
    intro first second equality
    cases first <;> cases second <;> cases equality <;> rfl

/-- Embed a protocol primitive Hom query into the matching common role. -/
def protocolHomPrimitiveQueryEmbedding (input : ProtocolFamilyInput.{u}) :
    IndependentProtocolPrimitiveReconstruction.HomPrimitiveQuery input ↪
      Query (Parameter.protocol input : Parameter.{u, u}) where
  toFun
    | .source query => .source query
    | .target query => .target query
    | .map vertex query => .hom (.map vertex query)
  inj' := by
    intro first second equality
    cases first <;> cases second <;> cases equality <;> rfl

/-- Common support of one existing lens object formula. -/
def lensObjectFormulaCommonSupport (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentLensPrimitiveReconstruction.ObjectLawQuery input)) :
    Finset (Query (Parameter.lens input : Parameter.{u, u})) :=
  (IndependentLensPrimitiveReconstruction.objectFormulaBaseSupport input formula).map
    (sourceQueryEmbedding (Parameter.lens input))

/-- Common support of one existing lens Hom formula. -/
def lensHomFormulaCommonSupport (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentLensPrimitiveReconstruction.HomQuery input)) :
    Finset (Query (Parameter.lens input : Parameter.{u, u})) :=
  (IndependentLensPrimitiveReconstruction.homFormulaBaseSupport input formula).map
    (lensHomPrimitiveQueryEmbedding input)

/-- Restrict a common lens table to the existing primitive Hom declaration. -/
def lensCommonHomPrimitiveTable (input : LensFamilyInput.{u})
    (table : Table (Parameter.lens input : Parameter.{u, u})) :
    IndependentLensPrimitiveReconstruction.HomPrimitiveTable input
  | .source query => table (.source query)
  | .target query => table (.target query)
  | .map query => table (.hom query)

/-- Common-support agreement preserves evaluation of a lens object formula. -/
theorem lensObjectFormula_evaluate_iff_of_commonSupport
    (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentLensPrimitiveReconstruction.ObjectLawQuery input))
    (first second : Table (Parameter.lens input : Parameter.{u, u}))
    (agree : ∀ query ∈ lensObjectFormulaCommonSupport input formula,
      first query = second query) :
    formula.evaluate
        (IndependentLensPrimitiveReconstruction.objectLawTable
          (sourceTable first)) ↔
      formula.evaluate
        (IndependentLensPrimitiveReconstruction.objectLawTable
          (sourceTable second)) := by
  apply IndependentLensPrimitiveReconstruction.objectFormula_evaluate_iff_of_base_support
  intro query member
  exact agree (.source query) (by
    classical
    exact Finset.mem_map.mpr ⟨query, member, rfl⟩)

/-- Common-support agreement preserves evaluation of a lens Hom formula. -/
theorem lensHomFormula_evaluate_iff_of_commonSupport
    (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentLensPrimitiveReconstruction.HomQuery input))
    (first second : Table (Parameter.lens input : Parameter.{u, u}))
    (agree : ∀ query ∈ lensHomFormulaCommonSupport input formula,
      first query = second query) :
    formula.evaluate
        (IndependentLensPrimitiveReconstruction.homPrimitiveLawTable
          (lensCommonHomPrimitiveTable input first)) ↔
      formula.evaluate
        (IndependentLensPrimitiveReconstruction.homPrimitiveLawTable
          (lensCommonHomPrimitiveTable input second)) := by
  apply IndependentLensPrimitiveReconstruction.homFormula_evaluate_iff_of_base_support
  intro query member
  cases query with
  | source query =>
      exact agree (.source query) (by
        classical
        exact Finset.mem_map.mpr ⟨.source query, member, rfl⟩)
  | target query =>
      exact agree (.target query) (by
        classical
        exact Finset.mem_map.mpr ⟨.target query, member, rfl⟩)
  | map query =>
      exact agree (.hom query) (by
        classical
        exact Finset.mem_map.mpr ⟨.map query, member, rfl⟩)

/-- Common support of one existing protocol object formula. -/
def protocolObjectFormulaCommonSupport (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentProtocolPrimitiveReconstruction.ObjectLawQuery input)) :
    Finset (Query (Parameter.protocol input : Parameter.{u, u})) :=
  (IndependentProtocolPrimitiveReconstruction.objectFormulaBaseSupport input formula).map
    (sourceQueryEmbedding (Parameter.protocol input))

/-- Common support of one existing protocol Hom formula. -/
def protocolHomFormulaCommonSupport (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentProtocolPrimitiveReconstruction.HomLawQuery input)) :
    Finset (Query (Parameter.protocol input : Parameter.{u, u})) :=
  (IndependentProtocolPrimitiveReconstruction.homFormulaBaseSupport input formula).map
    (protocolHomPrimitiveQueryEmbedding input)

/-- Restrict a common protocol table to the existing primitive Hom declaration. -/
def protocolCommonHomPrimitiveTable (input : ProtocolFamilyInput.{u})
    (table : Table (Parameter.protocol input : Parameter.{u, u})) :
    IndependentProtocolPrimitiveReconstruction.HomPrimitiveTable input
  | .source query => table (.source query)
  | .target query => table (.target query)
  | .map vertex query => table (.hom (.map vertex query))

/-- Common-support agreement preserves evaluation of a protocol object formula. -/
theorem protocolObjectFormula_evaluate_iff_of_commonSupport
    (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentProtocolPrimitiveReconstruction.ObjectLawQuery input))
    (first second : Table (Parameter.protocol input : Parameter.{u, u}))
    (agree : ∀ query ∈ protocolObjectFormulaCommonSupport input formula,
      first query = second query) :
    formula.evaluate
        (IndependentProtocolPrimitiveReconstruction.objectLawTable
          (sourceTable first)) ↔
      formula.evaluate
        (IndependentProtocolPrimitiveReconstruction.objectLawTable
          (sourceTable second)) := by
  apply IndependentProtocolPrimitiveReconstruction.objectFormula_evaluate_iff_of_base_support
  intro query member
  exact agree (.source query) (by
    classical
    exact Finset.mem_map.mpr ⟨query, member, rfl⟩)

/-- Common-support agreement preserves evaluation of a protocol Hom formula. -/
theorem protocolHomFormula_evaluate_iff_of_commonSupport
    (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (IndependentProtocolPrimitiveReconstruction.HomLawQuery input))
    (first second : Table (Parameter.protocol input : Parameter.{u, u}))
    (agree : ∀ query ∈ protocolHomFormulaCommonSupport input formula,
      first query = second query) :
    formula.evaluate
        (IndependentProtocolPrimitiveReconstruction.homPrimitiveLawTable
          (protocolCommonHomPrimitiveTable input first)) ↔
      formula.evaluate
        (IndependentProtocolPrimitiveReconstruction.homPrimitiveLawTable
          (protocolCommonHomPrimitiveTable input second)) := by
  apply IndependentProtocolPrimitiveReconstruction.homFormula_evaluate_iff_of_base_support
  intro query member
  cases query with
  | source query =>
      exact agree (.source query) (by
        classical
        exact Finset.mem_map.mpr ⟨.source query, member, rfl⟩)
  | target query =>
      exact agree (.target query) (by
        classical
        exact Finset.mem_map.mpr ⟨.target query, member, rfl⟩)
  | map vertex query =>
      exact agree (.hom (.map vertex query)) (by
        classical
        exact Finset.mem_map.mpr ⟨.map vertex query, member, rfl⟩)

/-! ### Independent laws on common finite families -/

/-- Finite fragments of a common object table, before selecting a local
object. -/
abbrev ObjectFragmentFamily (parameter : Parameter.{u, v}) :=
  IndependentFiniteFragments.FragmentFamily
    (fun query : ObjectQuery parameter => ObjectValue query)

/-- Compatibility for finite fragments of a common object table. -/
abbrev ObjectCompatible {parameter : Parameter.{u, v}}
    (family : ObjectFragmentFamily parameter) :=
  IndependentFiniteFragments.Compatible family

/-- Restrict a common object table to all finite supports. -/
def objectFragments {parameter : Parameter.{u, v}}
    (table : ObjectTable parameter) : ObjectFragmentFamily parameter :=
  IndependentFiniteFragments.fragments table

/-- Glue common object fragments from singleton cells. -/
def objectGlue {parameter : Parameter.{u, v}}
    (family : ObjectFragmentFamily parameter) : ObjectTable parameter :=
  IndependentFiniteFragments.glue family

/-- The existing independent protocol object laws, bundled without adding
completed semantic data to the common table. -/
structure ProtocolObjectTableLaws (input : ProtocolFamilyInput.{w})
    (table : IndependentProtocolPrimitiveReconstruction.ObjectTable input) : Prop where
  /-- Every named-edge graph has one output at each source state. -/
  edge_instances : ∀ {source target}
      (edge : input.schema.Edge source target),
    IndependentFiniteGraphLawFormula.CarrierRows.Instances
      (IndependentProtocolPrimitiveReconstruction.edgeTable table edge) id
      (IndependentProtocolPrimitiveReconstruction.State table source)
      (IndependentProtocolPrimitiveReconstruction.State table target)
  /-- Every observation graph has one output at each state. -/
  observe_instances : ∀ vertex,
    IndependentFiniteGraphLawFormula.CarrierRows.Instances
      (IndependentProtocolPrimitiveReconstruction.observeTable table vertex) id
      (IndependentProtocolPrimitiveReconstruction.State table vertex)
      (input.observation.obj (input.schema.vertexObject vertex))
  /-- Every named path relation is satisfied by the primitive table. -/
  relation_formula : ∀ relation state,
    (IndependentProtocolPrimitiveReconstruction.relationFormula input table
      (fun edge =>
        (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
          (IndependentProtocolPrimitiveReconstruction.edgeTable table edge)
          id _ _).mpr (edge_instances edge)) relation state).evaluate
      (IndependentProtocolPrimitiveReconstruction.objectLawTable table)
  /-- Every generating edge satisfies its observation square. -/
  observation_formula : ∀ {source target}
      (edge : input.schema.Edge source target) state,
    (IndependentProtocolPrimitiveReconstruction.observationFormula input table
      (fun edge =>
        (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
          (IndependentProtocolPrimitiveReconstruction.edgeTable table edge)
          id _ _).mpr (edge_instances edge))
      (fun vertex =>
        (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
          (IndependentProtocolPrimitiveReconstruction.observeTable table vertex)
          id _ _).mpr (observe_instances vertex)) edge state).evaluate
      (IndependentProtocolPrimitiveReconstruction.objectLawTable table)
  /-- Each vertex carrier is covered by a finite list. -/
  state_cover : ∀ vertex,
    IndependentProtocolPrimitiveReconstruction.StateCover table vertex

/-- Independent object laws selected by the common parameter.  Every branch
uses its existing graph rows, finite formulas, and finite-cover predicate. -/
def ObjectTableLaws (parameter : Parameter.{u, v})
    (table : ObjectTable parameter) : Prop := by
  cases parameter with
  | geometry carrier mode =>
      exact IndependentGeometryPrimitive.IsLawful table
  | lens input =>
      exact
        IndependentFiniteGraphLawFormula.CarrierRows.Instances
            (IndependentLensPrimitiveReconstruction.getTable table) id
            (table .stateCarrier) input.View ∧
        (∀ view, IndependentFiniteGraphLawFormula.CarrierRows.Instances
            (IndependentLensPrimitiveReconstruction.putTable table view) id
            (table .stateCarrier) (table .stateCarrier)) ∧
        (∀ state view,
          (IndependentLensPrimitiveReconstruction.putGetFormula input
            (table .stateCarrier) state view).evaluate
              (IndependentLensPrimitiveReconstruction.objectLawTable table)) ∧
        (∀ state target view,
          (IndependentLensPrimitiveReconstruction.getPutFormula input
            (table .stateCarrier) state target view).evaluate
              (IndependentLensPrimitiveReconstruction.objectLawTable table)) ∧
        (∀ state middle target first second,
          (IndependentLensPrimitiveReconstruction.putPutFormula input
            (table .stateCarrier) state middle target first second).evaluate
              (IndependentLensPrimitiveReconstruction.objectLawTable table)) ∧
        IndependentLensPrimitiveReconstruction.FiberCover input
          (table .stateCarrier) table
  | protocol input =>
      exact ProtocolObjectTableLaws input table

/-- A lawful common object family consists only of compatible finite cells and
the existing independent laws on their glued table. -/
abbrev LawfulObjectFamily (parameter : Parameter.{u, v}) :=
  {family : ObjectFragmentFamily parameter //
    ObjectCompatible family ∧ ObjectTableLaws parameter (objectGlue family)}

/-- Existing geometry point laws selected by the common mode. -/
def GeometryHomPointLaws {carrier : AtomCarrier.{u}}
    (mode : Mode)
    (source target : IndependentGeometryPrimitive.LocalObject.{u, v} carrier)
    (presentation : InvariantWitness.Presentation
      (IndependentGeometryTableAssembly.assemble
        (IndependentGeometryCategoryReconstruction.objectData source)).core.reading.invariantReading
      (IndependentGeometryTableAssembly.assemble
        (IndependentGeometryCategoryReconstruction.objectData target)).core.reading.invariantReading
      mode) : Prop :=
  match mode with
  | .representative =>
      FullRepresentative.PointLaws
        (IndependentGeometryCategoryReconstruction.objectData source)
        (IndependentGeometryCategoryReconstruction.objectData target)
        (Quotient.mk _ presentation)
  | .explicit =>
      FullExplicit.PointLaws
        (IndependentGeometryCategoryReconstruction.objectData source)
        (IndependentGeometryCategoryReconstruction.objectData target)
        (Quotient.mk _ presentation)

/-- Geometry Hom certificate retaining the completed presentation as data,
its whole original point table, and the existing branch point laws.  The
canonicality field removes only the auxiliary representative choice already
erased by `InvariantWitness.Local`. -/
structure GeometryHomTableCertificate {carrier : AtomCarrier.{u}}
    (mode : Mode)
    (source target : IndependentGeometryPrimitive.LocalObject.{u, v} carrier)
    (table : IndependentGeometryHomPrimitive.Table.{u, v} carrier mode) :
    Type (max (u + 1) (v + 1)) where
  /-- The completed coherent geometry presentation. -/
  presentation : InvariantWitness.Presentation
    (IndependentGeometryTableAssembly.assemble
      (IndependentGeometryCategoryReconstruction.objectData source)).core.reading.invariantReading
    (IndependentGeometryTableAssembly.assemble
      (IndependentGeometryCategoryReconstruction.objectData target)).core.reading.invariantReading
    mode
  /-- The retained presentation table is exactly the selected common table. -/
  retained_table : presentation.retained.table = table
  /-- All existing point laws for the selected geometry branch. -/
  point_laws : GeometryHomPointLaws mode source target presentation
  /-- The stored representative is the canonical readback of its assembly. -/
  canonical : presentation =
    InvariantWitness.readPresentation _ _
      (InvariantWitness.assemblePresentation _ _ presentation)

/-- Two geometry certificates over one table store the same canonical
presentation. -/
theorem GeometryHomTableCertificate.presentation_eq
    {carrier : AtomCarrier.{u}} {mode : Mode}
    {source target : IndependentGeometryPrimitive.LocalObject.{u, v} carrier}
    {table : IndependentGeometryHomPrimitive.Table.{u, v} carrier mode}
    (first second : GeometryHomTableCertificate mode source target table) :
    first.presentation = second.presentation := by
  have retainedEquality :
      first.presentation.retained = second.presentation.retained := by
    apply InvariantWitness.Retained.ext
    have tableEquality : first.presentation.retained.table =
        second.presentation.retained.table :=
      first.retained_table.trans second.retained_table.symm
    have familyEquality := congrArg TagChange.read tableEquality
    simpa only [InvariantWitness.Retained.table, TagChange.read_assemble] using
      familyEquality
  calc
    first.presentation =
        InvariantWitness.readPresentation _ _
          (InvariantWitness.assemblePresentation _ _ first.presentation) :=
      first.canonical
    _ = InvariantWitness.readPresentation _ _
          (InvariantWitness.assemblePresentation _ _ second.presentation) :=
      congrArg (InvariantWitness.readPresentation _ _)
        (InvariantWitness.assemblePresentation_congr _ _ _ _ retainedEquality)
    _ = second.presentation := second.canonical.symm

/-- Geometry certificates have no residual auxiliary choice once their table
is fixed. -/
instance geometryHomTableCertificateSubsingleton
    {carrier : AtomCarrier.{u}} {mode : Mode}
    {source target : IndependentGeometryPrimitive.LocalObject.{u, v} carrier}
    {table : IndependentGeometryHomPrimitive.Table.{u, v} carrier mode} :
    Subsingleton (GeometryHomTableCertificate mode source target table) where
  allEq first second := by
    have presentationEquality :=
      GeometryHomTableCertificate.presentation_eq first second
    cases first
    cases second
    cases presentationEquality
    rfl

/-- Independent Hom certificates for one common local source and target.  The
geometry branches retain their presentation data; the two CS branches retain
their existing proof packages through `PLift`. -/
def HomTableCertificate (parameter : Parameter.{u, v})
    (source target : LocalCategory parameter) (table : HomTable parameter) :
    Type (max (u + 1) (v + 1)) := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact GeometryHomTableCertificate .representative
            (ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                carrier) source).localObject
            (ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                carrier) target).localObject table
      | explicit =>
          exact GeometryHomTableCertificate .explicit
            (ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                carrier) source).localObject
            (ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                carrier) target).localObject table
  | lens input =>
      let sourceObject : IndependentLensPrimitiveReconstruction.Object input :=
        ULiftHom.objDown
          (C := IndependentLensPrimitiveReconstruction.Object input) source
      let targetObject : IndependentLensPrimitiveReconstruction.Object input :=
        ULiftHom.objDown
          (C := IndependentLensPrimitiveReconstruction.Object input) target
      exact ULift.{max (u + 1) (v + 1)} (PLift (
        IndependentFiniteGraphLawFormula.CarrierRows.Instances table id
          sourceObject.Carrier targetObject.Carrier ∧
        (∀ sourceState targetState view,
          (IndependentLensPrimitiveReconstruction.getPreservationFormula input
            sourceObject.Carrier targetObject.Carrier sourceState targetState view).evaluate
              (IndependentLensPrimitiveReconstruction.homLawTable
                sourceObject targetObject table)) ∧
        (∀ sourceState sourceState' targetState targetState' view,
          (IndependentLensPrimitiveReconstruction.putPreservationFormula input
            sourceObject.Carrier targetObject.Carrier sourceState sourceState'
              targetState targetState' view).evaluate
                (IndependentLensPrimitiveReconstruction.homLawTable
                  sourceObject targetObject table))))
  | protocol input =>
      let sourceObject : IndependentProtocolPrimitiveReconstruction.Object input :=
        ULiftHom.objDown
          (C := IndependentProtocolPrimitiveReconstruction.Object input) source
      let targetObject : IndependentProtocolPrimitiveReconstruction.Object input :=
        ULiftHom.objDown
          (C := IndependentProtocolPrimitiveReconstruction.Object input) target
      exact ULift.{max (u + 1) (v + 1)} (PLift (
        (∀ vertex, IndependentFiniteGraphLawFormula.CarrierRows.Instances
          (IndependentProtocolPrimitiveReconstruction.vertexMapTable table vertex) id
          (sourceObject.State vertex) (targetObject.State vertex)) ∧
        (∀ {a b} (edge : input.schema.Edge a b)
            (state : sourceObject.State a) (image : targetObject.State a)
            (sourceNext : sourceObject.State b) (targetNext : targetObject.State b),
          (IndependentProtocolPrimitiveReconstruction.edgePreservationFormula input
            sourceObject.table targetObject.table edge state image sourceNext targetNext).evaluate
              (IndependentProtocolPrimitiveReconstruction.homLawTable
                sourceObject.table targetObject.table table)) ∧
        (∀ vertex (state : sourceObject.State vertex)
            (image : targetObject.State vertex)
            (value : input.observation.obj (input.schema.vertexObject vertex)),
          (IndependentProtocolPrimitiveReconstruction.observationPreservationFormula input
            sourceObject.table targetObject.table vertex state image value).evaluate
              (IndependentProtocolPrimitiveReconstruction.homLawTable
                sourceObject.table targetObject.table table))))

/-- Every branch certificate is proof-irrelevant once its endpoint tables and
Hom table are fixed. -/
instance homTableCertificateSubsingleton (parameter : Parameter.{u, v})
    (source target : LocalCategory parameter) (table : HomTable parameter) :
    Subsingleton (HomTableCertificate parameter source target table) := by
  cases parameter with
  | geometry carrier mode =>
      cases mode <;> simp only [HomTableCertificate] <;> infer_instance
  | lens input =>
      simp only [HomTableCertificate]
      infer_instance
  | protocol input =>
      simp only [HomTableCertificate]
      infer_instance

/-- A lawful common Hom family includes both endpoint tables and one Hom table,
all as compatible finite common fragments. -/
structure LawfulHomFamily {parameter : Parameter.{u, v}}
    (source target : LocalCategory parameter) :
    Type (max (u + 1) (v + 1)) where
  /-- Compatible finite cells for the source, target, and Hom roles. -/
  family : FragmentFamily parameter
  /-- The common finite cells agree under restriction. -/
  compatible : Compatible family
  /-- The glued source role is the selected local source table. -/
  source_table : sourceTable (glue family) = localObjectTable parameter source
  /-- The glued target role is the selected local target table. -/
  target_table : targetTable (glue family) = localObjectTable parameter target
  /-- Branch-specific data certifying the glued Hom table. -/
  certificate : HomTableCertificate parameter source target
    (homTable (glue family))

/-- Lawful Hom families are equal when their finite common cells are equal. -/
@[ext]
theorem LawfulHomFamily.ext {parameter : Parameter.{u, v}}
    {source target : LocalCategory parameter}
    {first second : LawfulHomFamily source target}
    (equality : first.family = second.family) : first = second := by
  cases first with
  | mk firstFamily firstCompatible firstSource firstTarget firstCertificate =>
      cases second with
      | mk secondFamily secondCompatible secondSource secondTarget secondCertificate =>
          cases equality
          cases Subsingleton.elim firstCertificate secondCertificate
          rfl

/-- Restrict one primitive local object to its lawful common object family. -/
def localObjectFamily (parameter : Parameter.{u, v})
    (object : LocalCategory parameter) : LawfulObjectFamily parameter := by
  refine ⟨objectFragments (localObjectTable parameter object),
    IndependentFiniteFragments.fragments_compatible _, ?_⟩
  rw [show objectGlue (objectFragments (localObjectTable parameter object)) =
      localObjectTable parameter object from
    IndependentFiniteFragments.glue_fragments _]
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          simpa only [ObjectTableLaws, localObjectTable] using
            (ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                carrier) object).localObject.property.2
      | explicit =>
          simpa only [ObjectTableLaws, localObjectTable] using
            (ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                carrier) object).localObject.property.2
  | lens input =>
      let primitive := ULiftHom.objDown object
      exact ⟨primitive.get_instances, primitive.put_instances,
        primitive.put_get_formula, primitive.get_put_formula,
        primitive.put_put_formula, primitive.fiber_cover⟩
  | protocol input =>
      let primitive := ULiftHom.objDown object
      exact ⟨primitive.edge_instances, primitive.observe_instances,
        primitive.relation_formula, primitive.observation_formula,
        primitive.state_cover⟩

/-- Construct the existing primitive local object from one lawful common
object family. -/
noncomputable def localObjectOfFamily (parameter : Parameter.{u, v}) :
    LawfulObjectFamily parameter → LocalCategory parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact fun family => ULiftHom.objUp
            ⟨⟨family.val, family.property.1, by
              simpa only [ObjectTableLaws, objectGlue] using family.property.2⟩⟩
      | explicit =>
          exact fun family => ULiftHom.objUp
            ⟨⟨family.val, family.property.1, by
              simpa only [ObjectTableLaws, objectGlue] using family.property.2⟩⟩
  | lens input =>
      exact fun family => ULiftHom.objUp
        { family := family.val
          compatible := family.property.1
          get_instances := family.property.2.1
          put_instances := family.property.2.2.1
          put_get_formula := family.property.2.2.2.1
          get_put_formula := family.property.2.2.2.2.1
          put_put_formula := family.property.2.2.2.2.2.1
          fiber_cover := family.property.2.2.2.2.2.2 }
  | protocol input =>
      exact fun family => ULiftHom.objUp
        { family := family.val
          compatible := family.property.1
          edge_instances := family.property.2.edge_instances
          observe_instances := family.property.2.observe_instances
          relation_formula := family.property.2.relation_formula
          observation_formula := family.property.2.observation_formula
          state_cover := family.property.2.state_cover }

/-- Existing primitive local objects are equivalent to independently lawful
common finite object families. -/
noncomputable def localObjectFamilyEquiv (parameter : Parameter.{u, v}) :
    LocalCategory parameter ≃ LawfulObjectFamily parameter where
  toFun := localObjectFamily parameter
  invFun := localObjectOfFamily parameter
  left_inv object := by
    cases parameter with
    | geometry carrier mode =>
      cases mode with
      | representative =>
            change _ = ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                carrier) object
            apply IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.ext
            apply IndependentGeometryPrimitive.localObject_ext
            change IndependentGeometryPrimitive.glue
                (IndependentGeometryPrimitive.fragments
                  (IndependentGeometryPrimitive.glue
                    (ULiftHom.objDown (C :=
                      IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                        carrier) object).localObject.val)) =
              IndependentGeometryPrimitive.glue
                (ULiftHom.objDown (C :=
                  IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v}
                    carrier) object).localObject.val
            exact IndependentGeometryPrimitive.glue_fragments _
      | explicit =>
            change _ = ULiftHom.objDown (C :=
              IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                carrier) object
            apply IndependentGeometryCategoryReconstruction.ExplicitLocalObject.ext
            apply IndependentGeometryPrimitive.localObject_ext
            change IndependentGeometryPrimitive.glue
                (IndependentGeometryPrimitive.fragments
                  (IndependentGeometryPrimitive.glue
                    (ULiftHom.objDown (C :=
                      IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                        carrier) object).localObject.val)) =
              IndependentGeometryPrimitive.glue
                (ULiftHom.objDown (C :=
                  IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v}
                    carrier) object).localObject.val
            exact IndependentGeometryPrimitive.glue_fragments _
    | lens input =>
        change _ = ULiftHom.objDown
          (C := IndependentLensPrimitiveReconstruction.Object input) object
        apply IndependentLensPrimitiveReconstruction.Object.ext
        change IndependentLensPrimitiveReconstruction.objectFragments
            (IndependentLensPrimitiveReconstruction.objectGlue
              (ULiftHom.objDown
                (C := IndependentLensPrimitiveReconstruction.Object input)
                object).family) =
          (ULiftHom.objDown
            (C := IndependentLensPrimitiveReconstruction.Object input)
            object).family
        exact IndependentLensPrimitiveReconstruction.objectFragments_glue _
          (ULiftHom.objDown
            (C := IndependentLensPrimitiveReconstruction.Object input)
            object).compatible
    | protocol input =>
        change _ = ULiftHom.objDown
          (C := IndependentProtocolPrimitiveReconstruction.Object input) object
        apply IndependentProtocolPrimitiveReconstruction.Object.ext
        change IndependentProtocolPrimitiveReconstruction.objectFragments
            (IndependentProtocolPrimitiveReconstruction.objectGlue
              (ULiftHom.objDown
                (C := IndependentProtocolPrimitiveReconstruction.Object input)
                object).family) =
          (ULiftHom.objDown
            (C := IndependentProtocolPrimitiveReconstruction.Object input)
            object).family
        exact IndependentProtocolPrimitiveReconstruction.objectFragments_glue _
          (ULiftHom.objDown
            (C := IndependentProtocolPrimitiveReconstruction.Object input)
            object).compatible
  right_inv family := by
    apply Subtype.ext
    cases parameter with
    | geometry carrier mode =>
        cases mode with
        | representative =>
            change IndependentGeometryPrimitive.fragments
                (IndependentGeometryPrimitive.glue family.val) = family.val
            exact IndependentGeometryPrimitive.fragments_glue
              family.val family.property.1
        | explicit =>
            change IndependentGeometryPrimitive.fragments
                (IndependentGeometryPrimitive.glue family.val) = family.val
            exact IndependentGeometryPrimitive.fragments_glue
              family.val family.property.1
    | lens input =>
        change IndependentLensPrimitiveReconstruction.objectFragments
            (IndependentLensPrimitiveReconstruction.objectGlue family.val) =
          family.val
        exact IndependentLensPrimitiveReconstruction.objectFragments_glue
          family.val family.property.1
    | protocol input =>
        change IndependentProtocolPrimitiveReconstruction.objectFragments
            (IndependentProtocolPrimitiveReconstruction.objectGlue family.val) =
          family.val
        exact IndependentProtocolPrimitiveReconstruction.objectFragments_glue
          family.val family.property.1

/-- Gluing the common finite family of a local object recovers its complete
object table. -/
theorem objectGlue_localObjectFamily (parameter : Parameter.{u, v})
    (object : LocalCategory parameter) :
    objectGlue (localObjectFamily parameter object).val =
      localObjectTable parameter object :=
  IndependentFiniteFragments.glue_fragments _

/-- Restrict one existing primitive local Hom, including both endpoint
tables, to a lawful common finite Hom family. -/
def localHomFamily (parameter : Parameter.{u, v})
    {source target : LocalCategory parameter} (morphism : source ⟶ target) :
    LawfulHomFamily source target := by
  refine
    { family := fragments (localTable parameter morphism)
      compatible := IndependentFiniteFragments.fragments_compatible _
      source_table := ?_
      target_table := ?_
      certificate := ?_ }
  · calc
      sourceTable (glue (fragments (localTable parameter morphism))) =
          sourceTable (localTable parameter morphism) :=
        congrArg sourceTable (glue_fragments _)
      _ = localObjectTable parameter source := sourceTable_packTable _ _ _
  · calc
      targetTable (glue (fragments (localTable parameter morphism))) =
          targetTable (localTable parameter morphism) :=
        congrArg targetTable (glue_fragments _)
      _ = localObjectTable parameter target := targetTable_packTable _ _ _
  · rw [show glue (fragments (localTable parameter morphism)) =
        localTable parameter morphism from glue_fragments _]
    change HomTableCertificate parameter source target
      (localHomTable parameter morphism)
    cases parameter with
    | geometry carrier mode =>
        cases mode with
        | representative =>
            rcases morphism with ⟨morphism⟩
            rcases morphism with ⟨pointLocal, pointLaws⟩
            let native := InvariantWitness.assemble _ _ pointLocal
            let presentation :=
              InvariantWitness.readPresentation _ _ native
            refine
              { presentation := presentation
                retained_table := ?_
                point_laws := ?_
                canonical := ?_ }
            · funext query
              change InvariantWitness.point _ _
                  (InvariantWitness.read _ _
                    (InvariantWitness.assemble _ _ pointLocal)) query =
                InvariantWitness.point _ _ pointLocal query
              exact congrArg
                (fun localValue => InvariantWitness.point _ _ localValue query)
                (InvariantWitness.read_assemble _ _ pointLocal)
            · change FullRepresentative.PointLaws _ _
                (InvariantWitness.read _ _
                  (InvariantWitness.assemble _ _ pointLocal))
              rw [InvariantWitness.read_assemble]
              exact pointLaws
            · dsimp [presentation, native]
              exact
                (congrArg (InvariantWitness.readPresentation _ _)
                  (InvariantWitness.assemble_readPresentation _ _
                    (InvariantWitness.assemble _ _ pointLocal))).symm
        | explicit =>
            rcases morphism with ⟨morphism⟩
            rcases morphism with ⟨pointLocal, pointLaws⟩
            let native := InvariantWitness.assemble _ _ pointLocal
            let presentation :=
              InvariantWitness.readPresentation _ _ native
            refine
              { presentation := presentation
                retained_table := ?_
                point_laws := ?_
                canonical := ?_ }
            · funext query
              change InvariantWitness.point _ _
                  (InvariantWitness.read _ _
                    (InvariantWitness.assemble _ _ pointLocal)) query =
                InvariantWitness.point _ _ pointLocal query
              exact congrArg
                (fun localValue => InvariantWitness.point _ _ localValue query)
                (InvariantWitness.read_assemble _ _ pointLocal)
            · change FullExplicit.PointLaws _ _
                (InvariantWitness.read _ _
                  (InvariantWitness.assemble _ _ pointLocal))
              rw [InvariantWitness.read_assemble]
              exact pointLaws
            · dsimp [presentation, native]
              exact
                (congrArg (InvariantWitness.readPresentation _ _)
                  (InvariantWitness.assemble_readPresentation _ _
                    (InvariantWitness.assemble _ _ pointLocal))).symm
    | lens input =>
        let primitive := morphism.down
        exact ULift.up (PLift.up ⟨primitive.map_instances, primitive.get_formula,
          primitive.put_formula⟩)
    | protocol input =>
        let primitive := morphism.down
        exact ULift.up (PLift.up ⟨primitive.map_instances, primitive.edge_formula,
          primitive.observation_formula⟩)

/-- Gluing the lawful common family of a local Hom recovers its complete
tagged table. -/
theorem glue_localHomFamily (parameter : Parameter.{u, v})
    {source target : LocalCategory parameter} (morphism : source ⟶ target) :
    glue (localHomFamily parameter morphism).family =
      localTable parameter morphism := by
  change glue (fragments (localTable parameter morphism)) =
    localTable parameter morphism
  exact glue_fragments _

/-- Construct the existing primitive local Hom from a lawful common finite
Hom family. -/
noncomputable def localHomOfFamily (parameter : Parameter.{u, v})
    {source target : LocalCategory parameter} :
    LawfulHomFamily source target → (source ⟶ target) := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact fun family =>
            ULift.up
              ⟨Quotient.mk _ family.certificate.presentation,
                family.certificate.point_laws⟩
      | explicit =>
          exact fun family =>
            ULift.up
              ⟨Quotient.mk _ family.certificate.presentation,
                family.certificate.point_laws⟩
  | lens input =>
      exact fun family => by
        let table := homTable (glue family.family)
        let laws := family.certificate.down.down
        exact ULift.up
          { family := IndependentLensPrimitiveReconstruction.homFragments table
            compatible :=
              IndependentLensPrimitiveReconstruction.homFragments_compatible table
            map_instances := laws.1
            get_formula := laws.2.1
            put_formula := laws.2.2 }
  | protocol input =>
      exact fun family => by
        let table := homTable (glue family.family)
        let laws := family.certificate.down.down
        exact ULift.up
          { family := IndependentProtocolPrimitiveReconstruction.homFragments table
            compatible :=
              IndependentProtocolPrimitiveReconstruction.homFragments_compatible table
            map_instances := laws.1
            edge_formula := laws.2.1
            observation_formula := laws.2.2 }

/-- The representative Hom assembled from a lawful common family has exactly
the glued Hom table selected by that family. -/
theorem localHomOfFamily_representative_point {carrier : AtomCarrier.{u}}
    {source target : LocalCategory
      (Parameter.geometry carrier Mode.representative : Parameter.{u, v})}
    (family : LawfulHomFamily source target)
    (query : HomQuery
      (Parameter.geometry carrier Mode.representative : Parameter.{u, v})) :
    InvariantWitness.point _ _
        (localHomOfFamily
          (Parameter.geometry carrier Mode.representative) family).down.val query =
      homTable (glue family.family) query := by
  exact congrFun family.certificate.retained_table query

/-- The explicit Hom assembled from a lawful common family has exactly the
glued Hom table selected by that family. -/
theorem localHomOfFamily_explicit_point {carrier : AtomCarrier.{u}}
    {source target : LocalCategory
      (Parameter.geometry carrier Mode.explicit : Parameter.{u, v})}
    (family : LawfulHomFamily source target)
    (query : HomQuery
      (Parameter.geometry carrier Mode.explicit : Parameter.{u, v})) :
    InvariantWitness.point _ _
        (localHomOfFamily
          (Parameter.geometry carrier Mode.explicit) family).down.val query =
      homTable (glue family.family) query := by
  exact congrFun family.certificate.retained_table query

/-- Existing primitive local Homs are equivalent to independently lawful
common finite Hom families with fixed endpoint tables. -/
noncomputable def localHomFamilyEquiv (parameter : Parameter.{u, v})
    (source target : LocalCategory parameter) :
    (source ⟶ target) ≃ LawfulHomFamily source target where
  toFun := localHomFamily parameter
  invFun := localHomOfFamily parameter
  left_inv morphism := by
    cases parameter with
    | geometry carrier mode =>
        cases mode with
        | representative =>
            apply ULift.ext
            apply Subtype.ext
            apply InvariantWitness.point_ext
            intro query
            calc
              InvariantWitness.point _ _
                  (localHomOfFamily
                    (Parameter.geometry carrier Mode.representative)
                    (localHomFamily
                      (Parameter.geometry carrier Mode.representative)
                      morphism)).down.val query =
                  homTable
                    (glue
                      (localHomFamily
                        (Parameter.geometry carrier Mode.representative)
                        morphism).family) query :=
                localHomOfFamily_representative_point _ query
              _ = homTable (localTable
                    (Parameter.geometry carrier Mode.representative) morphism) query :=
                congrFun
                  (congrArg
                    (homTable (parameter :=
                      Parameter.geometry carrier Mode.representative))
                    (glue_localHomFamily
                      (Parameter.geometry carrier Mode.representative)
                      morphism)) query
              _ = InvariantWitness.point _ _ morphism.down.val query := rfl
        | explicit =>
            apply ULift.ext
            apply Subtype.ext
            apply InvariantWitness.point_ext
            intro query
            calc
              InvariantWitness.point _ _
                  (localHomOfFamily
                    (Parameter.geometry carrier Mode.explicit)
                    (localHomFamily
                      (Parameter.geometry carrier Mode.explicit)
                      morphism)).down.val query =
                  homTable
                    (glue
                      (localHomFamily
                        (Parameter.geometry carrier Mode.explicit)
                        morphism).family) query :=
                localHomOfFamily_explicit_point _ query
              _ = homTable (localTable
                    (Parameter.geometry carrier Mode.explicit) morphism) query :=
                congrFun
                  (congrArg
                    (homTable (parameter :=
                      Parameter.geometry carrier Mode.explicit))
                    (glue_localHomFamily
                      (Parameter.geometry carrier Mode.explicit)
                      morphism)) query
              _ = InvariantWitness.point _ _ morphism.down.val query := rfl
    | lens input =>
        apply ULift.ext
        apply IndependentLensPrimitiveReconstruction.Hom.ext
        change IndependentLensPrimitiveReconstruction.homFragments
            (IndependentLensPrimitiveReconstruction.homGlue morphism.down.family) =
          morphism.down.family
        exact IndependentLensPrimitiveReconstruction.homFragments_glue _
          morphism.down.compatible
    | protocol input =>
        apply ULift.ext
        apply IndependentProtocolPrimitiveReconstruction.Hom.ext
        change IndependentProtocolPrimitiveReconstruction.homFragments
            (IndependentProtocolPrimitiveReconstruction.homGlue
              morphism.down.family) = morphism.down.family
        exact IndependentProtocolPrimitiveReconstruction.homFragments_glue _
          morphism.down.compatible
  right_inv family := by
    apply LawfulHomFamily.ext
    have tableEquality :
        localTable parameter (localHomOfFamily parameter family) =
          glue family.family := by
      funext query
      cases query with
      | source query =>
          exact congrFun family.source_table.symm query
      | target query =>
          exact congrFun family.target_table.symm query
      | hom query =>
          cases parameter with
          | geometry carrier mode =>
              cases mode with
              | representative =>
                  exact congrArg ULift.up
                    (localHomOfFamily_representative_point family query)
              | explicit =>
                  exact congrArg ULift.up
                    (localHomOfFamily_explicit_point family query)
          | lens input =>
              exact congrArg ULift.up (congrFun
                (IndependentLensPrimitiveReconstruction.homGlue_fragments
                  (homTable (glue family.family))) query)
          | protocol input =>
              exact congrArg ULift.up (congrFun
                (IndependentProtocolPrimitiveReconstruction.homGlue_fragments
                  (homTable (glue family.family))) query)
    change fragments
        (localTable parameter (localHomOfFamily parameter family)) = family.family
    rw [tableEquality]
    exact fragments_glue family.family family.compatible

/-- Assemble a lawful common object family through the existing branch object
assembler. -/
noncomputable def assembleObjectFamily (parameter : Parameter.{u, v})
    (family : LawfulObjectFamily parameter) : NativeCategory parameter :=
  assembleObject parameter ((localObjectFamilyEquiv parameter).symm family)

/-- Assemble a lawful common Hom family through the existing branch Hom
assembler. -/
noncomputable def assembleHomFamily (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter}
    (family : LawfulHomFamily ((reading parameter).obj source)
      ((reading parameter).obj target)) : source ⟶ target :=
  assembleHom parameter ((localHomFamilyEquiv parameter _ _).symm family)

/-- Reading a Hom assembled from a lawful common family restores that family. -/
theorem localHomFamily_read_assemble (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter}
    (family : LawfulHomFamily ((reading parameter).obj source)
      ((reading parameter).obj target)) :
    localHomFamily parameter
        ((reading parameter).map (assembleHomFamily parameter family)) = family := by
  change localHomFamily parameter
      ((reading parameter).map
        (assembleHom parameter
          ((localHomFamilyEquiv parameter _ _).symm family))) = family
  calc
    localHomFamily parameter
        ((reading parameter).map
          (assembleHom parameter
            ((localHomFamilyEquiv parameter _ _).symm family))) =
        localHomFamily parameter
          ((localHomFamilyEquiv parameter _ _).symm family) :=
      congrArg (localHomFamily parameter)
        (read_assembleHom parameter
          ((localHomFamilyEquiv parameter _ _).symm family))
    _ = family := (localHomFamilyEquiv parameter _ _).apply_symm_apply family

/-- Assembling the common family read from a native Hom restores the native
Hom. -/
theorem assembleHomFamily_read (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} (morphism : source ⟶ target) :
    assembleHomFamily parameter
        (localHomFamily parameter ((reading parameter).map morphism)) = morphism := by
  change assembleHom parameter
      ((localHomFamilyEquiv parameter _ _).symm
        (localHomFamily parameter ((reading parameter).map morphism))) = morphism
  calc
    assembleHom parameter
        ((localHomFamilyEquiv parameter _ _).symm
          (localHomFamily parameter ((reading parameter).map morphism))) =
        assembleHom parameter ((reading parameter).map morphism) :=
      congrArg (assembleHom parameter)
        ((localHomFamilyEquiv parameter _ _).symm_apply_apply _)
    _ = morphism := assembleHom_read parameter morphism

/-- Equality of common finite families separates native Homs. -/
theorem nativeHom_eq_of_commonFamily_eq (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} {first second : source ⟶ target}
    (equality : localHomFamily parameter ((reading parameter).map first) =
      localHomFamily parameter ((reading parameter).map second)) :
    first = second := by
  rw [← assembleHomFamily_read parameter first,
    equality, assembleHomFamily_read parameter second]

/-- Every independently lawful common Hom family has one unique native
preimage under common finite-family reading. -/
theorem lawfulHomFamily_existsUnique_preimage (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter}
    (family : LawfulHomFamily ((reading parameter).obj source)
      ((reading parameter).obj target)) :
    ∃! morphism : source ⟶ target,
      localHomFamily parameter ((reading parameter).map morphism) = family := by
  refine ⟨assembleHomFamily parameter family,
    localHomFamily_read_assemble parameter family, ?_⟩
  intro morphism equality
  apply nativeHom_eq_of_commonFamily_eq parameter
  rw [equality, localHomFamily_read_assemble]

/-- Common reconstruction data whose separation and Hom assembly pass through
the independently lawful finite-family equivalence. -/
noncomputable def reconstructionData (parameter : Parameter.{u, v}) :
    ReconstructionData (reading parameter) where
  separation := ⟨fun _ _ => ⟨fun first second equality => by
    apply nativeHom_eq_of_commonFamily_eq parameter
    exact congrArg (localHomFamily parameter) equality⟩⟩
  homAssembly :=
    { assemble := fun localMorphism =>
        assembleHomFamily parameter (localHomFamily parameter localMorphism)
      map_assemble := fun localMorphism => by
        change (reading parameter).map
            (assembleHom parameter
              ((localHomFamilyEquiv parameter _ _).symm
                (localHomFamily parameter localMorphism))) = localMorphism
        rw [show (localHomFamilyEquiv parameter _ _).symm
              (localHomFamily parameter localMorphism) = localMorphism from
            (localHomFamilyEquiv parameter _ _).symm_apply_apply localMorphism]
        exact read_assembleHom parameter localMorphism }
  objectAssembly :=
    { assembleObject := fun localObject =>
        assembleObjectFamily parameter
          (localObjectFamily parameter localObject)
      readAssembledIso := fun localObject =>
        (readAssembledObjectIso parameter
          ((localObjectFamilyEquiv parameter).symm
            (localObjectFamily parameter localObject))).trans
          (eqToIso
            ((localObjectFamilyEquiv parameter).symm_apply_apply localObject)) }

/-- The common primitive reader separates every native Hom through finite
family equality. -/
theorem homSeparation (parameter : Parameter.{u, v}) :
    HomSeparation (reading parameter) :=
  (reconstructionData parameter).separation

/-- Every common primitive local Hom has one unique native preimage. -/
theorem existsUnique_preimage (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter}
    (localMorphism : (reading parameter).obj source ⟶
      (reading parameter).obj target) :
    ∃! morphism : source ⟶ target,
      (reading parameter).map morphism = localMorphism :=
  (reconstructionData parameter).existsUnique_preimage localMorphism

/-- The main common equivalence, obtained once from the finite-family-backed
common reconstruction data. -/
noncomputable def equivalence (parameter : Parameter.{u, v}) :
    NativeCategory parameter ≌ LocalCategory parameter :=
  (reconstructionData parameter).equivalence

/-- The forward functor of the common equivalence is the primitive reader. -/
@[simp] theorem equivalence_functor (parameter : Parameter.{u, v}) :
    (equivalence parameter).functor = reading parameter := rfl

/-- Reading and finite-family-backed assembly give the common Hom-set
equivalence. -/
def homEquiv (parameter : Parameter.{u, v})
    (source target : NativeCategory parameter) :
    (source ⟶ target) ≃
      ((reading parameter).obj source ⟶ (reading parameter).obj target) :=
  (reconstructionData parameter).homEquiv source target

/-! ### Evaluations on the existing primitive readers -/

/-- A semantic lens object reads to its existing primitive graph object. -/
@[simp] theorem lens_read_object (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    ULiftHom.objDown
        ((reading (Parameter.lens input : Parameter.{u, u})).obj
          (ULiftHom.objUp lens)) =
      IndependentLensPrimitiveReconstruction.readObject lens := rfl

/-- A semantic lens Hom reads to its existing primitive state-map graph. -/
@[simp] theorem lens_read_map (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) :
    (reading (Parameter.lens input : Parameter.{u, u})).map
        (ULift.up morphism) =
      ULift.up (IndependentLensPrimitiveReconstruction.readHom morphism) := rfl

/-- A semantic protocol object reads to its existing primitive protocol
table. -/
@[simp] theorem protocol_read_object (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation) :
    ULiftHom.objDown
        ((reading (Parameter.protocol input : Parameter.{u, u})).obj
          (ULiftHom.objUp realization)) =
        IndependentProtocolPrimitiveReconstruction.readObject realization := rfl

/-- A semantic protocol Hom reads to its existing primitive vertex-map
graphs. -/
@[simp] theorem protocol_read_map (input : ProtocolFamilyInput.{u})
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : source ⟶ target) :
    (reading (Parameter.protocol input : Parameter.{u, u})).map
        (ULift.up morphism) =
      ULift.up (IndependentProtocolPrimitiveReconstruction.readHom morphism) := rfl

/-- The common protocol reader retains the accepted observed path evaluation. -/
theorem protocol_observedRestriction_path
    (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation)
    {source target} (path : Quiver.Path source target)
    (state : realization.State source) :
    input.schema.evaluatePath
        (IndependentProtocolPrimitiveReconstruction.assembleEdge
          (ULiftHom.objDown
            ((reading (Parameter.protocol input : Parameter.{u, u})).obj
              (ULiftHom.objUp realization)))) path state =
      (protocolObservedRestrictionObject input realization).stateDiagram.map
        (input.schema.pathMorphism path).op.op state := by
  exact IndependentProtocolPrimitiveReconstruction.observedRestriction_path
    input realization path state

/-! ### Existing rejection fixtures in the common tables -/

/-- The ignored-update lens table placed in the source role of a common
table. -/
def lensIgnoredUpdateCommonTable :
    Table (Parameter.lens
      ({ View := Bool, reference := false } : LensFamilyInput) :
        Parameter.{0, 0}) :=
  packTable IndependentLensPrimitiveReconstruction.ignoredUpdateTable
    IndependentLensPrimitiveReconstruction.ignoredUpdateTable (fun _ => false)

/-- The common source role retains the existing ignored-update rejection. -/
theorem lensIgnoredUpdateCommonTable_rejected :
    ¬ (IndependentLensPrimitiveReconstruction.getPutFormula
      ({ View := Bool, reference := false } : LensFamilyInput)
      Bool false false true).evaluate
        (IndependentLensPrimitiveReconstruction.objectLawTable
          (sourceTable lensIgnoredUpdateCommonTable)) := by
  simpa only [sourceTable_packTable] using
    IndependentLensPrimitiveReconstruction.ignoredUpdateTable_rejected

/-- The visible-flipping lens Hom table placed in all three common roles. -/
def lensFlipVisibleCommonTable :
    Table (Parameter.lens
      ({ View := Bool, reference := false } : LensFamilyInput) :
        Parameter.{0, 0}) :=
  packTable
    (IndependentLensPrimitiveReconstruction.readDataTable
      IndependentLensPrimitiveReconstruction.booleanViewUnitLens.toLensData)
    (IndependentLensPrimitiveReconstruction.readDataTable
      IndependentLensPrimitiveReconstruction.booleanViewUnitLens.toLensData)
    IndependentLensPrimitiveReconstruction.flipVisibleTable

/-- The common Hom role retains the existing lens get-preservation rejection. -/
theorem lensFlipVisibleCommonTable_rejected :
    ¬ (IndependentLensPrimitiveReconstruction.getPreservationFormula
      ({ View := Bool, reference := false } : LensFamilyInput)
      (Bool × PUnit) (Bool × PUnit)
      (false, PUnit.unit) (true, PUnit.unit) false).evaluate
        (IndependentLensPrimitiveReconstruction.homLawTable
          (IndependentLensPrimitiveReconstruction.readObject
            IndependentLensPrimitiveReconstruction.booleanViewUnitLens)
          (IndependentLensPrimitiveReconstruction.readObject
            IndependentLensPrimitiveReconstruction.booleanViewUnitLens)
          (homTable lensFlipVisibleCommonTable)) := by
  simpa only [homTable_packTable] using
    IndependentLensPrimitiveReconstruction.flipVisibleTable_getPreservation_rejected

/-- A rejected candidate carrier graph cannot carry a common lens Hom-table
certificate. -/
theorem lensHomTableCertificate_not_of_not_lawful
    (input : LensFamilyInput.{u})
    (source target : IndependentLensPrimitiveReconstruction.Object input)
    (table : HomTable (Parameter.lens input : Parameter.{u, u}))
    (rejected : ¬ IndependentCarrierGraph.IsLawful
      source.Carrier target.Carrier table) :
    ¬ Nonempty
      (HomTableCertificate
        (Parameter.lens input : Parameter.{u, u})
        (ULiftHom.objUp source) (ULiftHom.objUp target) table) := by
  rintro ⟨certificate⟩
  apply rejected
  apply (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    table id source.Carrier target.Carrier).mpr
  simpa only [CategoryTheory.objDown_objUp] using certificate.down.down.1

/-- A true point on mismatched carriers cannot carry a common lens Hom-table
certificate. -/
theorem lensHomTableCertificate_mismatched_carrier_rejected
    (input : LensFamilyInput.{u})
    (source target : IndependentLensPrimitiveReconstruction.Object input)
    (table : HomTable (Parameter.lens input : Parameter.{u, u}))
    (S T : Type u) (x : S) (y : T)
    (carrierMismatch : S ≠ source.Carrier ∨ T ≠ target.Carrier)
    (edge : table (.edge S T x y) = true) :
    ¬ Nonempty
      (HomTableCertificate
        (Parameter.lens input : Parameter.{u, u})
        (ULiftHom.objUp source) (ULiftHom.objUp target) table) :=
  lensHomTableCertificate_not_of_not_lawful input source target table
    (IndependentCarrierGraph.mismatched_carrier_rejected
      (α := source.Carrier) (β := target.Carrier)
      table S T x y carrierMismatch edge)

/-- An all-false candidate graph cannot carry a common lens Hom-table
certificate when the source carrier is inhabited by a supplied point. -/
theorem lensHomTableCertificate_false_table_rejected
    (input : LensFamilyInput.{u})
    (source target : IndependentLensPrimitiveReconstruction.Object input)
    (point : source.Carrier) :
    ¬ Nonempty
      (HomTableCertificate
        (Parameter.lens input : Parameter.{u, u})
        (ULiftHom.objUp source) (ULiftHom.objUp target)
        (fun _ => false)) :=
  lensHomTableCertificate_not_of_not_lawful input source target
    (fun _ => false)
    (IndependentCarrierGraph.false_table_rejected
      (α := source.Carrier) (β := target.Carrier) point)

/-- Two different true outputs in one selected row cannot carry a common lens
Hom-table certificate. -/
theorem lensHomTableCertificate_duplicate_outputs_rejected
    (input : LensFamilyInput.{u})
    (source target : IndependentLensPrimitiveReconstruction.Object input)
    (table : HomTable (Parameter.lens input : Parameter.{u, u}))
    (x : source.Carrier) (y z : target.Carrier) (different : y ≠ z)
    (firstEdge : table (.edge source.Carrier target.Carrier x y) = true)
    (secondEdge : table (.edge source.Carrier target.Carrier x z) = true) :
    ¬ Nonempty
      (HomTableCertificate
        (Parameter.lens input : Parameter.{u, u})
        (ULiftHom.objUp source) (ULiftHom.objUp target) table) :=
  lensHomTableCertificate_not_of_not_lawful input source target table
    (IndependentCarrierGraph.duplicate_outputs_rejected
      (α := source.Carrier) (β := target.Carrier)
      table x y z different firstEdge secondEdge)

/-- The infinite-fiber lens table placed in the source role of a common
table. -/
def lensInfiniteFiberCommonTable :
    Table (Parameter.lens
      IndependentLensPrimitiveReconstruction.booleanFiberInput :
        Parameter.{0, 0}) :=
  packTable IndependentLensPrimitiveReconstruction.infiniteFiberTable
    IndependentLensPrimitiveReconstruction.infiniteFiberTable (fun _ => false)

/-- The common source role retains the existing infinite-fiber rejection. -/
theorem lensInfiniteFiberCommonTable_not_fiberCover :
    ¬ IndependentLensPrimitiveReconstruction.FiberCover
      IndependentLensPrimitiveReconstruction.booleanFiberInput Nat
      (sourceTable lensInfiniteFiberCommonTable) := by
  simpa only [sourceTable_packTable] using
    IndependentLensPrimitiveReconstruction.infiniteFiberTable_not_fiberCover

/-- The toggling protocol table placed in the source role of a common table. -/
def protocolTogglingCommonTable :
    Table (Parameter.protocol
      togglingProtocolInput :
        Parameter.{0, 0}) :=
  packTable IndependentProtocolPrimitiveReconstruction.togglingObjectTable
    IndependentProtocolPrimitiveReconstruction.togglingObjectTable
    (fun _ => false)

/-- The common source role retains the existing path-relation rejection. -/
theorem protocolTogglingCommonTable_relation_rejected :
    ¬ (IndependentProtocolPrimitiveReconstruction.relationFormula
      togglingProtocolInput
      (sourceTable protocolTogglingCommonTable)
      (fun edge => IndependentProtocolPrimitiveReconstruction.togglingEdgeLawful edge)
      PUnit.unit false).evaluate
        (IndependentProtocolPrimitiveReconstruction.objectLawTable
          (sourceTable protocolTogglingCommonTable)) := by
  simpa only [sourceTable_packTable] using
    IndependentProtocolPrimitiveReconstruction.togglingRelationFormula_rejected

/-- The finite Boolean protocol table that fails its observation square,
placed in the common source role. -/
def protocolObservationFailureCommonTable :
    Table (Parameter.protocol
      IndependentProtocolPrimitiveReconstruction.booleanProtocolInput :
        Parameter.{0, 0}) :=
  packTable
    IndependentProtocolPrimitiveReconstruction.booleanFlipEdgeObjectTable
    IndependentProtocolPrimitiveReconstruction.booleanFlipEdgeObjectTable
    (fun _ => false)

/-- The common source role retains the concrete protocol observation-square
rejection. -/
theorem protocolObservationFailureCommonTable_rejected :
    ¬ (IndependentProtocolPrimitiveReconstruction.observationFormula
      IndependentProtocolPrimitiveReconstruction.booleanProtocolInput
      (sourceTable protocolObservationFailureCommonTable)
      (fun edge =>
        IndependentProtocolPrimitiveReconstruction.booleanProtocolEdgeLawful
          (fun state => !state) id edge)
      (IndependentProtocolPrimitiveReconstruction.booleanProtocolObserveLawful
        (fun state => !state) id)
      IndependentProtocolPrimitiveReconstruction.booleanProtocolLoop false).evaluate
        (IndependentProtocolPrimitiveReconstruction.objectLawTable
          (sourceTable protocolObservationFailureCommonTable)) := by
  simpa only [sourceTable_packTable] using
    IndependentProtocolPrimitiveReconstruction.booleanFlipEdge_observationFormula_rejected

/-- The protocol observation-preservation failure placed in a common Hom
table. -/
def protocolObservationHomFailureCommonTable :
    Table (Parameter.protocol
      IndependentProtocolPrimitiveReconstruction.booleanProtocolInput :
        Parameter.{0, 0}) :=
  packTable
    IndependentProtocolPrimitiveReconstruction.booleanIdentityObjectTable
    IndependentProtocolPrimitiveReconstruction.booleanFlipObservationObjectTable
    IndependentProtocolPrimitiveReconstruction.booleanIdentityMapTable

/-- The common Hom role retains the concrete protocol observation-preservation
rejection. -/
theorem protocolObservationHomFailureCommonTable_rejected :
    ¬ (IndependentProtocolPrimitiveReconstruction.observationPreservationFormula
      IndependentProtocolPrimitiveReconstruction.booleanProtocolInput
      (sourceTable protocolObservationHomFailureCommonTable)
      (targetTable protocolObservationHomFailureCommonTable)
      TogglingProtocolVertex.point false false false).evaluate
        (IndependentProtocolPrimitiveReconstruction.homLawTable
          (sourceTable protocolObservationHomFailureCommonTable)
          (targetTable protocolObservationHomFailureCommonTable)
          (homTable protocolObservationHomFailureCommonTable)) := by
  simpa only [sourceTable_packTable, targetTable_packTable, homTable_packTable] using
    IndependentProtocolPrimitiveReconstruction.booleanIdentityMap_observationPreservation_rejected

/-- The protocol edge-preservation failure placed in a common Hom table. -/
def protocolEdgeHomFailureCommonTable :
    Table (Parameter.protocol
      IndependentProtocolPrimitiveReconstruction.booleanProtocolInput :
        Parameter.{0, 0}) :=
  packTable
    IndependentProtocolPrimitiveReconstruction.booleanFlipEdgeObjectTable
    IndependentProtocolPrimitiveReconstruction.booleanIdentityObjectTable
    IndependentProtocolPrimitiveReconstruction.booleanIdentityMapTable

/-- The common Hom role retains the concrete protocol edge-preservation
rejection. -/
theorem protocolEdgeHomFailureCommonTable_rejected :
    ¬ (IndependentProtocolPrimitiveReconstruction.edgePreservationFormula
      IndependentProtocolPrimitiveReconstruction.booleanProtocolInput
      (sourceTable protocolEdgeHomFailureCommonTable)
      (targetTable protocolEdgeHomFailureCommonTable)
      IndependentProtocolPrimitiveReconstruction.booleanProtocolLoop
      false false true false).evaluate
        (IndependentProtocolPrimitiveReconstruction.homLawTable
          (sourceTable protocolEdgeHomFailureCommonTable)
          (targetTable protocolEdgeHomFailureCommonTable)
          (homTable protocolEdgeHomFailureCommonTable)) := by
  simpa only [sourceTable_packTable, targetTable_packTable, homTable_packTable] using
    IndependentProtocolPrimitiveReconstruction.booleanIdentityMap_edgePreservation_rejected

/-- The infinite-state protocol table placed in the source role of a common
table. -/
def protocolInfiniteStateCommonTable :
    Table (Parameter.protocol
      togglingProtocolInput :
        Parameter.{0, 0}) :=
  packTable IndependentProtocolPrimitiveReconstruction.infiniteProtocolTable
    IndependentProtocolPrimitiveReconstruction.infiniteProtocolTable
    (fun _ => false)

/-- The common source role retains the existing infinite-state rejection. -/
theorem protocolInfiniteStateCommonTable_not_stateCover :
    ¬ IndependentProtocolPrimitiveReconstruction.StateCover
      (sourceTable protocolInfiniteStateCommonTable)
      TogglingProtocolVertex.point := by
  simpa only [sourceTable_packTable] using
    IndependentProtocolPrimitiveReconstruction.infiniteProtocol_not_stateCover

/-- The accepted noninvertible lens Hom as a Hom of the common native
category. -/
def lensBooleanToUnitNativeHom :
    ULiftHom.objUp
        LensSemanticFiniteDetermination.booleanFiberLens ⟶
      ULiftHom.objUp IndependentLensPrimitiveReconstruction.unitFiberLens :=
  ULift.up IndependentLensPrimitiveReconstruction.booleanToUnitHom

/-- Reading the noninvertible lens Hom to a common lawful family and assembling
it again recovers the original native Hom. -/
theorem lensBooleanToUnitNativeHom_family_recovery :
    assembleHomFamily
        (Parameter.lens IndependentLensPrimitiveReconstruction.booleanFiberInput :
          Parameter.{0, 0})
        (localHomFamily
          (Parameter.lens IndependentLensPrimitiveReconstruction.booleanFiberInput)
          ((reading
            (Parameter.lens IndependentLensPrimitiveReconstruction.booleanFiberInput)).map
              lensBooleanToUnitNativeHom)) =
      lensBooleanToUnitNativeHom :=
  assembleHomFamily_read _ _

/-- The common native lens fixture retains the accepted noninjective state
map. -/
theorem lensBooleanToUnitNativeHom_not_injective :
    ¬ Function.Injective
      (((reading
        (Parameter.lens IndependentLensPrimitiveReconstruction.booleanFiberInput :
          Parameter.{0, 0})).map lensBooleanToUnitNativeHom).down.toFun) :=
  IndependentLensPrimitiveReconstruction.booleanToUnitHom_not_injective

/-- The accepted noninvertible constant-false lens Hom as a Hom of the common
native lens category. -/
def lensConstantFalseNativeHom :
    ULiftHom.objUp
        LensSemanticFiniteDetermination.booleanFiberLens ⟶
      ULiftHom.objUp
        LensSemanticFiniteDetermination.booleanFiberLens :=
  ULift.up LensSemanticFiniteDetermination.constantFalseHom

/-- Reading the constant-false lens Hom to a common lawful family and
assembling it again recovers the original native Hom. -/
theorem lensConstantFalseNativeHom_family_recovery :
    assembleHomFamily
        (Parameter.lens
          IndependentLensPrimitiveReconstruction.booleanFiberInput :
            Parameter.{0, 0})
        (localHomFamily
          (Parameter.lens
            IndependentLensPrimitiveReconstruction.booleanFiberInput)
          ((reading
            (Parameter.lens
              IndependentLensPrimitiveReconstruction.booleanFiberInput)).map
                lensConstantFalseNativeHom)) =
      lensConstantFalseNativeHom :=
  assembleHomFamily_read _ _

/-- The common primitive reading of the constant-false lens Hom retains its
noninjective reference-fiber action. -/
theorem lensConstantFalseNativeHom_fiber_not_injective :
    ¬ Function.Injective
      (IndependentLensPrimitiveReconstruction.primitiveFiberMap
        ((reading
          (Parameter.lens
            IndependentLensPrimitiveReconstruction.booleanFiberInput :
              Parameter.{0, 0})).map lensConstantFalseNativeHom).down) := by
  change ¬ Function.Injective
    (IndependentLensPrimitiveReconstruction.primitiveFiberMap
      IndependentLensPrimitiveReconstruction.constantFalsePrimitiveHom)
  exact
    IndependentLensPrimitiveReconstruction.constantFalsePrimitiveHom_fiber_not_injective

/-- The accepted two-to-one protocol Hom as a Hom of the common native
category. -/
def protocolTwoToOneNativeHom :
    ULiftHom.objUp
        (ProtocolPresentation.decoderObject
          IndependentProtocolPrimitiveReconstruction.twoStateProtocolPresentation) ⟶
      ULiftHom.objUp
        (ProtocolPresentation.decoderObject
          IndependentProtocolPrimitiveReconstruction.oneStateProtocolPresentation) :=
  ULift.up IndependentProtocolPrimitiveReconstruction.twoToOneProtocolHom

/-- Reading the two-to-one protocol Hom to a common lawful family and
assembling it again recovers the original native Hom. -/
theorem protocolTwoToOneNativeHom_family_recovery :
    assembleHomFamily
        (Parameter.protocol
          togglingProtocolInput :
            Parameter.{0, 0})
        (localHomFamily
          (Parameter.protocol
            togglingProtocolInput)
          ((reading
            (Parameter.protocol
              togglingProtocolInput)).map
                protocolTwoToOneNativeHom)) =
      protocolTwoToOneNativeHom :=
  assembleHomFamily_read _ _

/-- The common native protocol fixture retains the accepted noninjective
vertex component. -/
theorem protocolTwoToOneNativeHom_not_injective :
    ¬ Function.Injective
      (((reading
        (Parameter.protocol
          togglingProtocolInput :
            Parameter.{0, 0})).map protocolTwoToOneNativeHom).down.component
              TogglingProtocolVertex.point) :=
  IndependentProtocolPrimitiveReconstruction.twoToOnePrimitiveHom_not_injective

/-- The common representative geometry reader evaluates every Hom query by
the accepted Part I point reader. -/
theorem representative_read_point (carrier : AtomCarrier.{u})
    {source target : GeomReadCategory.{u, v} carrier}
    (morphism : source ⟶ target)
    (query : IndependentGeometryHomPrimitive.Query.{u, v}
      carrier Mode.representative) :
    InvariantWitness.point _ _
        (((reading (Parameter.geometry carrier Mode.representative)).map
          (ULift.up morphism)).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        morphism query := by
  exact IndependentGeometryCategoryReconstruction.representativeReadingHomEquiv_point
    morphism query

/-- The common explicit geometry reader evaluates every Hom query by the
accepted Part I point reader. -/
theorem explicit_read_point (carrier : AtomCarrier.{u})
    {source target : ExplicitExactGeomCategory.{u, v} carrier}
    (morphism : source ⟶ target)
    (query : IndependentGeometryHomPrimitive.Query.{u, v}
      carrier Mode.explicit) :
    InvariantWitness.point _ _
        (((reading (Parameter.geometry carrier Mode.explicit)).map
          (ULift.up morphism)).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readExplicit morphism query := by
  exact IndependentGeometryCategoryReconstruction.explicitReadingHomEquiv_point
    morphism query

/-- The first coefficient projection regarded as a Hom between the two
canonical explicit object readings. -/
def explicitFirstProjectionOnRead
    {carrier : AtomCarrier.{u}} (package : AATCorePackage carrier)
    (geometry : Site.SelectedGeometryReading package) :
    ExplicitExactGeometryHom
      (IndependentGeometryTableAssembly.assemble
        (IndependentGeometryTableAssembly.read
          (IndependentHomRefutations.unitPackage package geometry (ℤ × ℤ))))
      (IndependentGeometryTableAssembly.assemble
        (IndependentGeometryTableAssembly.read
          (IndependentHomRefutations.unitPackage package geometry ℤ))) :=
  IndependentHomRefutations.explicitCoefficientHomOnRead package geometry
    IndependentHomRefutations.projection

/-- The second coefficient projection regarded as a Hom between the same two
canonical explicit object readings. -/
def explicitSecondProjectionOnRead
    {carrier : AtomCarrier.{u}} (package : AATCorePackage carrier)
    (geometry : Site.SelectedGeometryReading package) :
    ExplicitExactGeometryHom
      (IndependentGeometryTableAssembly.assemble
        (IndependentGeometryTableAssembly.read
          (IndependentHomRefutations.unitPackage package geometry (ℤ × ℤ))))
      (IndependentGeometryTableAssembly.assemble
        (IndependentGeometryTableAssembly.read
          (IndependentHomRefutations.unitPackage package geometry ℤ))) :=
  IndependentHomRefutations.explicitCoefficientHomOnRead package geometry
    IndependentHomRefutations.secondProjection

/-- The two coefficient projections have the same base object action, while
their Homs remain distinct after the common explicit primitive reading. -/
theorem explicitCoefficientProjection_commonReading_distinct
    {carrier : AtomCarrier.{u}} (package : AATCorePackage carrier)
    (geometry : Site.SelectedGeometryReading package) :
    (IndependentHomRefutations.explicitCoefficientHom package geometry
          IndependentHomRefutations.projection).base =
        (IndependentHomRefutations.explicitCoefficientHom package geometry
          IndependentHomRefutations.secondProjection).base ∧
      (reading
        (Parameter.geometry carrier Mode.explicit : Parameter.{u, 0})).map
          (ULift.up (explicitFirstProjectionOnRead package geometry)) ≠
        (reading
          (Parameter.geometry carrier Mode.explicit : Parameter.{u, 0})).map
            (ULift.up (explicitSecondProjectionOnRead package geometry)) := by
  constructor
  · rfl
  · obtain ⟨query, different⟩ :=
      IndependentHomRefutations.explicit_projection_homs_distinct_query
        package geometry
    intro equality
    have liftedEquality :=
      ((homSeparation
        (Parameter.geometry carrier Mode.explicit : Parameter.{u, 0})).hom
          _ _).injective equality
    have nativeEquality := congrArg ULift.down liftedEquality
    have pointEquality := congrArg
      (fun morphism =>
        IndependentGeometryHomPrimitive.NativeReader.readExplicit
          morphism query)
      nativeEquality
    apply different
    simpa only [explicitFirstProjectionOnRead,
      explicitSecondProjectionOnRead] using pointEquality

/-! ### Comparisons with existing readings -/

/-- Compare the common equivalence with any existing reading from the same
native category. -/
noncomputable def comparisonIso
    {R : Type u₁} [Category.{v₁} R]
    {M : Type u₂} [Category.{v₂} M]
    {L : Type w} [Category L]
    (equivalence : R ≌ M) (reader : R ⥤ L) :
    equivalence.functor ⋙ equivalence.inverse ⋙ reader ≅ reader :=
  equivalence.funInvIdAssoc reader

/-- Existing lens package objects and all package Homs enter the common lens
native category through the full and faithful semantic functor. -/
noncomputable def lensPackageInclusion (input : LensFamilyInput.{u}) :
    LensAATIndependentPackageObject input ⥤
      NativeCategory (Parameter.lens input : Parameter.{u, u}) :=
  lensAATIndependentPackageSemanticFunctor input ⋙
    (ULiftHom.up (C := LensRealization input.View input.reference))

/-- The lens package inclusion retains the existing full and faithful Hom
correspondence. -/
noncomputable def lensPackageInclusionFullyFaithful
    (input : LensFamilyInput.{u}) :
    (lensPackageInclusion input).FullyFaithful :=
  (lensAATIndependentPackageSemanticFullyFaithful input).comp
    (ULiftHom.equiv
      (C := LensRealization input.View input.reference)).fullyFaithfulFunctor

/-- Existing protocol package objects and all package Homs enter the common
protocol native category through the full and faithful semantic functor. -/
noncomputable def protocolPackageInclusion
    (input : ProtocolFamilyInput.{u}) :
    ProtocolAATIndependentPackageObject input ⥤
      NativeCategory (Parameter.protocol input : Parameter.{u, u}) :=
  protocolAATIndependentPackageSemanticFunctor input ⋙
    (ULiftHom.up (C := ProtocolRealization input.schema input.observation))

/-- The protocol package inclusion retains the existing full and faithful Hom
correspondence. -/
noncomputable def protocolPackageInclusionFullyFaithful
    (input : ProtocolFamilyInput.{u}) :
    (protocolPackageInclusion input).FullyFaithful :=
  (protocolAATIndependentPackageSemanticFullyFaithful input).comp
    (ULiftHom.equiv
      (C := ProtocolRealization input.schema input.observation)).fullyFaithfulFunctor

/-- Existing finite-fiber lens reading, with domain aligned to the common
native lens category. -/
noncomputable def lensFiberReader (input : LensFamilyInput.{u}) :
    NativeCategory (Parameter.lens input : Parameter.{u, u}) ⥤ FintypeCat.{u} :=
  (ULiftHom.down (C := LensRealization input.View input.reference)) ⋙
    lensSemanticFiberReading input

/-- Send a primitive lens local object through the new inverse and then the
accepted finite-fiber reader. -/
noncomputable def lensLocalToFiber (input : LensFamilyInput.{u}) :
    LocalCategory (Parameter.lens input : Parameter.{u, u}) ⥤ FintypeCat.{u} :=
  (equivalence (Parameter.lens input : Parameter.{u, u})).inverse ⋙
    lensFiberReader input

/-- The common lens equivalence compares canonically with the existing
finite-fiber reader. -/
noncomputable def lensFiberComparisonIso
    (input : LensFamilyInput.{u}) :
    (equivalence (Parameter.lens input : Parameter.{u, u})).functor ⋙
      lensLocalToFiber input ≅
      lensFiberReader input :=
  comparisonIso
    (equivalence (Parameter.lens input : Parameter.{u, u}))
    (lensFiberReader input)

/-- The forward lens comparison component is the accepted fiber reader applied
to the inverse unit component. -/
theorem lensFiberComparisonIso_hom_app (input : LensFamilyInput.{u})
    (object : NativeCategory (Parameter.lens input : Parameter.{u, u})) :
    (lensFiberComparisonIso input).hom.app object =
      (lensFiberReader input).map
        ((equivalence (Parameter.lens input : Parameter.{u, u})).unitInv.app object) :=
  Equivalence.funInvIdAssoc_hom_app _ _ _

/-- The inverse lens comparison component is the accepted fiber reader applied
to the unit component. -/
theorem lensFiberComparisonIso_inv_app (input : LensFamilyInput.{u})
    (object : NativeCategory (Parameter.lens input : Parameter.{u, u})) :
    (lensFiberComparisonIso input).inv.app object =
      (lensFiberReader input).map
        ((equivalence (Parameter.lens input : Parameter.{u, u})).unit.app object) :=
  Equivalence.funInvIdAssoc_inv_app _ _ _

/-- The lens comparison component acts on a reference-fiber state by the
accepted semantic restriction of the common equivalence unit. -/
theorem lensFiberComparisonIso_hom_app_apply
    (input : LensFamilyInput.{u})
    (object : NativeCategory (Parameter.lens input : Parameter.{u, u}))
    (state : (((equivalence
      (Parameter.lens input : Parameter.{u, u})).functor ⋙
        lensLocalToFiber input).obj object)) :
    (lensFiberComparisonIso input).hom.app object state =
      LensRealization.res
        ((equivalence
          (Parameter.lens input : Parameter.{u, u})).unitInv.app object).down
        state := by
  rw [lensFiberComparisonIso_hom_app]
  exact lensSemanticFiberReading_map_apply input _ state

/-- Existing observed protocol reading, with domain aligned to the common
native protocol category. -/
noncomputable def protocolObservedReader
    (input : ProtocolFamilyInput.{u}) :
    NativeCategory (Parameter.protocol input : Parameter.{u, u}) ⥤
      ProtocolObservedRestrictionModel input :=
  (ULiftHom.down (C :=
      ProtocolRealization input.schema input.observation)) ⋙
    protocolSemanticClosedFamilyFunctor input ⋙
    protocolObservedRestrictionReading input

/-- Send a primitive protocol local object through the new inverse and then
the accepted observed reader. -/
noncomputable def protocolLocalToObserved (input : ProtocolFamilyInput.{u}) :
    LocalCategory (Parameter.protocol input : Parameter.{u, u}) ⥤
      ProtocolObservedRestrictionModel input :=
  (equivalence (Parameter.protocol input : Parameter.{u, u})).inverse ⋙
    protocolObservedReader input

/-- The common protocol equivalence compares canonically with the existing
observed restriction reader. -/
noncomputable def protocolObservedComparisonIso
    (input : ProtocolFamilyInput.{u}) :
    (equivalence (Parameter.protocol input : Parameter.{u, u})).functor ⋙
        protocolLocalToObserved input ≅
      protocolObservedReader input :=
  comparisonIso
    (equivalence (Parameter.protocol input : Parameter.{u, u}))
    (protocolObservedReader input)

/-- The forward protocol comparison component is the observed reader applied
to the inverse unit component. -/
theorem protocolObservedComparisonIso_hom_app
    (input : ProtocolFamilyInput.{u})
    (object : NativeCategory (Parameter.protocol input : Parameter.{u, u})) :
    (protocolObservedComparisonIso input).hom.app object =
      (protocolObservedReader input).map
        ((equivalence (Parameter.protocol input : Parameter.{u, u})).unitInv.app object) :=
  Equivalence.funInvIdAssoc_hom_app _ _ _

/-- The inverse protocol comparison component is the observed reader applied
to the unit component. -/
theorem protocolObservedComparisonIso_inv_app
    (input : ProtocolFamilyInput.{u})
    (object : NativeCategory (Parameter.protocol input : Parameter.{u, u})) :
    (protocolObservedComparisonIso input).inv.app object =
      (protocolObservedReader input).map
        ((equivalence (Parameter.protocol input : Parameter.{u, u})).unit.app object) :=
  Equivalence.funInvIdAssoc_inv_app _ _ _

/-- The protocol comparison component acts at each vertex by the accepted
semantic state restriction of the common equivalence unit. -/
theorem protocolObservedComparisonIso_hom_app_vertex
    (input : ProtocolFamilyInput.{u})
    (object : NativeCategory (Parameter.protocol input : Parameter.{u, u}))
    (vertex : input.schema.Vertex)
    (state : ((((equivalence
      (Parameter.protocol input : Parameter.{u, u})).functor ⋙
        protocolLocalToObserved input).obj object).stateDiagram.obj
          (Opposite.op (Opposite.op
            (input.schema.vertexObject vertex))))) :
    ((protocolObservedComparisonIso input).hom.app object).stateMap.app
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) state =
      ((ProtocolRealization.res
        ((equivalence
          (Parameter.protocol input : Parameter.{u, u})).unitInv.app object).down).component
            vertex) state := by
  rw [protocolObservedComparisonIso_hom_app]
  rfl

/-- The semantic lens category is equivalent to the new primitive local
category. -/
noncomputable def lensSemanticPrimitiveEquivalence
    (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ≌
      LocalCategory (Parameter.lens input : Parameter.{u, u}) :=
  (ULiftHom.equiv (C := LensRealization input.View input.reference)).trans
    (equivalence (Parameter.lens input : Parameter.{u, u}))

/-- The semantic protocol category is equivalent to the new primitive local
category. -/
noncomputable def protocolSemanticPrimitiveEquivalence
    (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ≌
      LocalCategory (Parameter.protocol input : Parameter.{u, u}) :=
  (ULiftHom.equiv
    (C := ProtocolRealization input.schema input.observation)).trans
      (equivalence (Parameter.protocol input : Parameter.{u, u}))

/-- The semantic lens-to-primitive equivalence followed by the common local
fiber reader is the accepted semantic fiber reading. -/
noncomputable def lensSemanticPrimitiveFiberComparisonIso
    (input : LensFamilyInput.{u}) :
    (lensSemanticPrimitiveEquivalence input).functor ⋙
        lensLocalToFiber input ≅
      lensSemanticFiberReading input := by
  change (lensSemanticPrimitiveEquivalence input).functor ⋙
      (lensSemanticPrimitiveEquivalence input).inverse ⋙
        lensSemanticFiberReading input ≅
    lensSemanticFiberReading input
  exact (lensSemanticPrimitiveEquivalence input).funInvIdAssoc
    (lensSemanticFiberReading input)

/-- The semantic protocol-to-primitive equivalence followed by the common
observed reader is the accepted semantic observed-restriction reading. -/
noncomputable def protocolSemanticPrimitiveObservedComparisonIso
    (input : ProtocolFamilyInput.{u}) :
    (protocolSemanticPrimitiveEquivalence input).functor ⋙
        protocolLocalToObserved input ≅
      (protocolSemanticObservedRestrictionEquivalence input).functor := by
  change (protocolSemanticPrimitiveEquivalence input).functor ⋙
      (protocolSemanticPrimitiveEquivalence input).inverse ⋙
        (protocolSemanticObservedRestrictionEquivalence input).functor ≅
    (protocolSemanticObservedRestrictionEquivalence input).functor
  exact (protocolSemanticPrimitiveEquivalence input).funInvIdAssoc
    (protocolSemanticObservedRestrictionEquivalence input).functor

/-- Decode a finite lens presentation directly into the new primitive local
category. -/
noncomputable def lensFiniteDecoder (input : LensFamilyInput.{u}) :
    LensPresentation ⥤
      LocalCategory (Parameter.lens input : Parameter.{u, u}) :=
  LensRealization.lensDecoder input.View input.reference ⋙
    (lensSemanticPrimitiveEquivalence input).functor

/-- Decode a finite protocol presentation directly into the new primitive
local category. -/
noncomputable def protocolFiniteDecoder (input : ProtocolFamilyInput.{u}) :
    ProtocolPresentation input.schema input.observation ⥤
      LocalCategory (Parameter.protocol input : Parameter.{u, u}) :=
  ProtocolPresentation.decoder input.schema input.observation ⋙
    (protocolSemanticPrimitiveEquivalence input).functor

/-- Retract generation is preserved when the codomain is transported along
an equivalence. -/
theorem retractGeneratedBy_comp_equivalence
    {P : Type u₁} {R : Type u₂} {M : Type u₃}
    [Category.{v₁} P] [Category.{v₂} R] [Category.{v₃} M]
    (decoder : P ⥤ R) (equivalence : R ≌ M)
    (generated : RetractGeneratedBy decoder) :
    RetractGeneratedBy (decoder ⋙ equivalence.functor) := by
  intro localObject
  let semanticObject := equivalence.inverse.obj localObject
  rcases generated semanticObject with
    ⟨presentation, insertion, retraction, retract⟩
  let localIso := equivalence.counitIso.app localObject
  have mappedRetract :
      equivalence.functor.map insertion ≫
          equivalence.functor.map retraction =
        𝟙 (equivalence.functor.obj semanticObject) := by
    rw [← equivalence.functor.map_comp, retract,
      equivalence.functor.map_id]
  refine ⟨presentation,
    localIso.inv ≫ equivalence.functor.map insertion,
    equivalence.functor.map retraction ≫ localIso.hom, ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc
    (equivalence.functor.map insertion)
    (equivalence.functor.map retraction) localIso.hom]
  rw [mappedRetract]
  simpa only [Category.id_comp] using localIso.inv_hom_id

/-- Every primitive lens local object is a retract of the new finite decoder.
The witness is the accepted semantic retract transported through the new
semantic-to-primitive equivalence. -/
theorem lensFiniteDecoder_retractGeneratedBy (input : LensFamilyInput.{u}) :
    RetractGeneratedBy (lensFiniteDecoder input) := by
  exact retractGeneratedBy_comp_equivalence
    (LensRealization.lensDecoder input.View input.reference)
    (lensSemanticPrimitiveEquivalence input)
    LensRealization.lensRetractGeneratedBy

/-- Every primitive protocol local object is a retract of the new finite
decoder, by transport of the accepted semantic retract. -/
theorem protocolFiniteDecoder_retractGeneratedBy
    (input : ProtocolFamilyInput.{u}) :
    RetractGeneratedBy (protocolFiniteDecoder input) := by
  exact retractGeneratedBy_comp_equivalence
    (ProtocolPresentation.decoder input.schema input.observation)
    (protocolSemanticPrimitiveEquivalence input)
    ProtocolPresentation.protocolRetractGeneratedBy

/-- The accepted lens Karoubi equivalence followed by the new semantic to
primitive equivalence. -/
noncomputable def lensKaroubiEquivalence (input : LensFamilyInput.{u}) :
    Karoubi LensPresentation ≌
      LocalCategory (Parameter.lens input : Parameter.{u, u}) :=
  LensRealization.lensKaroubiReconstructionEquivalence.trans
    (lensSemanticPrimitiveEquivalence input)

/-- The accepted protocol Karoubi equivalence followed by the new semantic to
primitive equivalence. -/
noncomputable def protocolKaroubiEquivalence
    (input : ProtocolFamilyInput.{u}) :
    Karoubi (ProtocolPresentation input.schema input.observation) ≌
      LocalCategory (Parameter.protocol input : Parameter.{u, u}) :=
  ProtocolPresentation.protocolKaroubiReconstructionEquivalence.trans
    (protocolSemanticPrimitiveEquivalence input)

/-- Restricting the new lens Karoubi equivalence to presentations recovers
the new primitive finite decoder. -/
noncomputable def lensKaroubiRestrictionIso (input : LensFamilyInput.{u}) :
    toKaroubi LensPresentation ⋙
        (lensKaroubiEquivalence input).functor ≅
      lensFiniteDecoder input :=
  (Functor.associator
      (toKaroubi LensPresentation)
      LensRealization.lensKaroubiReconstructionEquivalence.functor
      (lensSemanticPrimitiveEquivalence input).functor).symm.trans
    (Functor.isoWhiskerRight
      LensRealization.lensKaroubiReconstructionRestrictionIso
      (lensSemanticPrimitiveEquivalence input).functor)

/-- Restricting the new protocol Karoubi equivalence to presentations
recovers the new primitive finite decoder. -/
noncomputable def protocolKaroubiRestrictionIso
    (input : ProtocolFamilyInput.{u}) :
    toKaroubi (ProtocolPresentation input.schema input.observation) ⋙
        (protocolKaroubiEquivalence input).functor ≅
      protocolFiniteDecoder input :=
  (Functor.associator
      (toKaroubi (ProtocolPresentation input.schema input.observation))
      ProtocolPresentation.protocolKaroubiReconstructionEquivalence.functor
      (protocolSemanticPrimitiveEquivalence input).functor).symm.trans
    (Functor.isoWhiskerRight
      ProtocolPresentation.protocolKaroubiReconstructionRestrictionIso
      (protocolSemanticPrimitiveEquivalence input).functor)

/-- The accepted lens Arrow reconstruction followed by the new primitive
Arrow equivalence. -/
noncomputable def lensKaroubiArrowEquivalence
    (input : LensFamilyInput.{u}) :
    Karoubi (Arrow LensPresentation) ≌
      Arrow (LocalCategory (Parameter.lens input : Parameter.{u, u})) :=
  LensRealization.lensKaroubiArrowReconstructionEquivalence.trans
    (Functor.mapArrowEquivalence (lensSemanticPrimitiveEquivalence input))

/-- The accepted protocol Arrow reconstruction followed by the new primitive
Arrow equivalence. -/
noncomputable def protocolKaroubiArrowEquivalence
    (input : ProtocolFamilyInput.{u}) :
    Karoubi (Arrow (ProtocolPresentation input.schema input.observation)) ≌
      Arrow (LocalCategory (Parameter.protocol input : Parameter.{u, u})) :=
  ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence.trans
    (Functor.mapArrowEquivalence (protocolSemanticPrimitiveEquivalence input))

/-- The new lens Karoubi route agrees with the accepted finite-fiber Karoubi
route after the common local-to-fiber comparison. -/
noncomputable def lensKaroubiFiberComparisonIso
    (input : LensFamilyInput.{u}) :
    (lensKaroubiEquivalence input).functor ⋙ lensLocalToFiber input ≅
      (lensKaroubiFiberEquivalence input).functor :=
  Functor.isoWhiskerLeft
    LensRealization.lensKaroubiReconstructionEquivalence.functor
    (lensSemanticPrimitiveFiberComparisonIso input)

/-- The new protocol Karoubi route agrees with the accepted observed Karoubi
route after the common local-to-observed comparison. -/
noncomputable def protocolKaroubiObservedComparisonIso
    (input : ProtocolFamilyInput.{u}) :
    (protocolKaroubiEquivalence input).functor ⋙
        protocolLocalToObserved input ≅
      (protocolKaroubiObservedRestrictionEquivalence input).functor :=
  Functor.isoWhiskerLeft
    ProtocolPresentation.protocolKaroubiReconstructionEquivalence.functor
    (protocolSemanticPrimitiveObservedComparisonIso input)

/-- The new lens Karoubi Arrow route agrees with the accepted finite-fiber
Arrow route after applying the common comparison at both endpoints. -/
noncomputable def lensKaroubiArrowFiberComparisonIso
    (input : LensFamilyInput.{u}) :
    (lensKaroubiArrowEquivalence input).functor ⋙
        Functor.mapArrow (lensLocalToFiber input) ≅
      (lensKaroubiFiberArrowEquivalence input).functor := by
  exact Functor.isoWhiskerLeft
    LensRealization.lensKaroubiArrowReconstructionEquivalence.functor
    (Functor.mapIso (Functor.mapArrowFunctor _ _)
      (lensSemanticPrimitiveFiberComparisonIso input))

/-- The new protocol Karoubi Arrow route agrees with the accepted observed
Arrow route after applying the common comparison at both endpoints. -/
noncomputable def protocolKaroubiArrowObservedComparisonIso
    (input : ProtocolFamilyInput.{u}) :
    (protocolKaroubiArrowEquivalence input).functor ⋙
        Functor.mapArrow (protocolLocalToObserved input) ≅
      (protocolKaroubiObservedRestrictionArrowEquivalence input).functor := by
  exact Functor.isoWhiskerLeft
    ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence.functor
    (Functor.mapIso (Functor.mapArrowFunctor _ _)
      (protocolSemanticPrimitiveObservedComparisonIso input))

/-! ### Mandatory explicit geometry inputs -/

/-- The tagged complete geometry as an object of the common explicit native
category. -/
noncomputable def taggedNativeObject :
    NativeCategory
      (Parameter.geometry FiniteModel.carrier Mode.explicit : Parameter.{0, 0}) :=
  taggedOperationExplicitExactGeometryObject

/-- Every tagged source choice as a Hom of the common explicit native
category. -/
noncomputable def taggedSourceChoiceNativeHom
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    taggedNativeObject ⟶ taggedNativeObject :=
  ULift.up (taggedSourceChoiceExplicitExactGeometryMorphism choice)

/-- The tagged normalization projector as a Hom of the common explicit native
category. -/
noncomputable def taggedNormalizationNativeHom :
    taggedNativeObject ⟶ taggedNativeObject :=
  ULift.up
    TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom

/-- Common primitive evaluation of every tagged source choice is the accepted
explicit Part I evaluation. -/
theorem taggedSourceChoice_read_point
    (choice : ArchitectureObject FiniteModel.carrier → Bool)
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.explicit) :
    InvariantWitness.point _ _
        (((reading (Parameter.geometry FiniteModel.carrier Mode.explicit)).map
          (taggedSourceChoiceNativeHom choice)).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readExplicit
        (taggedSourceChoiceExplicitExactGeometryMorphism choice) query :=
  explicit_read_point FiniteModel.carrier
    (taggedSourceChoiceExplicitExactGeometryMorphism choice) query

/-- Common primitive evaluation of the tagged normalization projector is the
accepted explicit Part I evaluation. -/
theorem taggedNormalization_read_point
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.explicit) :
    InvariantWitness.point _ _
        (((reading (Parameter.geometry FiniteModel.carrier Mode.explicit)).map
          taggedNormalizationNativeHom).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readExplicit
        TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom
          query :=
  explicit_read_point FiniteModel.carrier
    TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom
      query

/-- The common tagged source-choice map remains injective. -/
theorem taggedSourceChoiceNativeHom_injective :
    Function.Injective taggedSourceChoiceNativeHom := by
  intro first second equality
  apply taggedSourceChoiceExplicitExactGeometryMorphism_injective
  exact congrArg ULift.down equality

/-- The constant-true source choice is the accepted uniform flip in the
common explicit native category. -/
theorem taggedUniformFlipNativeHom_base :
    (taggedSourceChoiceNativeHom (fun _ => true)).down.base =
      taggedUniformFlipTotal :=
  taggedSourceChoiceExplicitExactGeometryHom_uniformFlip_base

/-- The tagged normalization remains idempotent in the common native
category. -/
@[simp] theorem taggedNormalizationNativeHom_idempotent :
    taggedNormalizationNativeHom ≫ taggedNormalizationNativeHom =
      taggedNormalizationNativeHom := by
  apply ULift.ext
  exact congrArg ULift.down
    TagChangeCanonicalNormalizationGeometryLaws.closedFamilyTaggedNormalization_idempotent

/-- Include the old represented tagged category in the common explicit native
category by its actual exact morphisms. -/
noncomputable def taggedRepresentedInclusion :
    TagChangeExactGeometryLocalModel.GlobalCategory ⥤
      NativeCategory
        (Parameter.geometry FiniteModel.carrier Mode.explicit : Parameter.{0, 0}) where
  obj _ := taggedNativeObject
  map morphism := morphism.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Transport the old tagged local category through its accepted inverse and
then into the common explicit primitive reader. -/
noncomputable def taggedLocalComparison :
    TagChangeExactGeometryLocalModel.LocalCategory ⥤
      LocalCategory
        (Parameter.geometry FiniteModel.carrier Mode.explicit : Parameter.{0, 0}) :=
  TagChangeExactGeometryLocalModel.equivalence.inverse ⋙
    taggedRepresentedInclusion ⋙
    reading
      (Parameter.geometry FiniteModel.carrier Mode.explicit : Parameter.{0, 0})

/-- The accepted tagged reader followed by the old inverse agrees with the
common explicit primitive reading of the represented inclusion. -/
noncomputable def taggedRepresentedReadingIso :
    TagChangeExactGeometryLocalModel.reading ⋙ taggedLocalComparison ≅
      taggedRepresentedInclusion ⋙
        reading
          (Parameter.geometry FiniteModel.carrier Mode.explicit :
            Parameter.{0, 0}) := by
  rw [← TagChangeExactGeometryLocalModel.equivalence_functor]
  exact TagChangeExactGeometryLocalModel.equivalence.funInvIdAssoc
    (taggedRepresentedInclusion ⋙
      reading
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0}))

/-- Every old tagged local section is evaluated by the common table of the
represented exact morphism selected by the accepted inverse. -/
theorem taggedLocalComparison_map_table
    (localSection : TagChangeGeneratedLocalModel.LocalSection) :
    localTable
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})
        (taggedLocalComparison.map
          (X := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
          (Y := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
          localSection) =
      nativeTable
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})
        (taggedRepresentedInclusion.map
          (X := SingleObj.star
            TagChangeExactGeometryLocalModel.ExactRepresentedSubmonoid)
          (Y := SingleObj.star
            TagChangeExactGeometryLocalModel.ExactRepresentedSubmonoid)
          (TagChangeExactGeometryLocalModel.equivalence.inverse.map
            (X := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
            (Y := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
            localSection)) := by
  change localTable
      (Parameter.geometry FiniteModel.carrier Mode.explicit :
        Parameter.{0, 0})
      ((reading
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})).map
        (taggedRepresentedInclusion.map
          (X := SingleObj.star
            TagChangeExactGeometryLocalModel.ExactRepresentedSubmonoid)
          (Y := SingleObj.star
            TagChangeExactGeometryLocalModel.ExactRepresentedSubmonoid)
          (TagChangeExactGeometryLocalModel.equivalence.inverse.map
            (X := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
            (Y := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
            localSection))) = _
  exact localTable_read _ _

/-- The accepted inverse sends the local reading of a normal form back to its
represented exact morphism. -/
theorem taggedInverse_read_normalForm
    (form : TagChangeGeneratedNormalForm.NormalForm) :
    TagChangeExactGeometryLocalModel.equivalence.inverse.map
        (X := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
        (Y := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
        (TagChangeGeneratedLocalModel.read form) =
      TagChangeExactGeometryNormalForm.normalFormMulEquivRepresented form := by
  change TagChangeExactGeometryLocalModel.representedMulEquivLocalSection.symm
      (TagChangeGeneratedLocalModel.read form) = _
  rw [← TagChangeExactGeometryLocalModel.representedMulEquivLocalSection_on_normalForm,
    MulEquiv.symm_apply_apply]

/-- The table evaluation of an accepted tagged normal form is the same
specialization of the represented comparison. -/
theorem taggedLocalComparison_normalForm_table
    (form : TagChangeGeneratedNormalForm.NormalForm) :
    localTable
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})
        (taggedLocalComparison.map
          (X := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
          (Y := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
          (TagChangeGeneratedLocalModel.read form)) =
      nativeTable
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})
        (taggedRepresentedInclusion.map
          (X := SingleObj.star
            TagChangeExactGeometryLocalModel.ExactRepresentedSubmonoid)
          (Y := SingleObj.star
            TagChangeExactGeometryLocalModel.ExactRepresentedSubmonoid)
          (TagChangeExactGeometryNormalForm.normalFormMulEquivRepresented form)) := by
  rw [← taggedInverse_read_normalForm]
  exact taggedLocalComparison_map_table
    (TagChangeGeneratedLocalModel.read form)

/-! ### Mandatory finite-axis-fold G-122 inputs -/

/-- The representative common parameter containing the fixed G-122 geometry
objects and all complete geometry Homs between them. -/
abbrev finiteAxisFoldGeometryParameter : Parameter.{0, 0} :=
  .geometry FiniteModel.carrier Mode.representative

/-- The fixed G-122 original endpoint in the common representative native
category. -/
noncomputable def finiteAxisFoldOriginalNativeObject :
    NativeCategory finiteAxisFoldGeometryParameter :=
  (G122GeneratedGeometryObject.original finiteAxisFoldG122CellInput).package
    finiteAxisFoldG122FamilyInput

/-- The fixed G-122 direct endpoint in the common representative native
category. -/
noncomputable def finiteAxisFoldDirectNativeObject :
    NativeCategory finiteAxisFoldGeometryParameter :=
  (G122GeneratedGeometryObject.direct finiteAxisFoldG122CellInput).package
    finiteAxisFoldG122FamilyInput

/-- The fixed G-122 via-base endpoint in the common representative native
category. -/
noncomputable def finiteAxisFoldViaBaseNativeObject :
    NativeCategory finiteAxisFoldGeometryParameter :=
  (G122GeneratedGeometryObject.viaBase finiteAxisFoldG122CellInput).package
    finiteAxisFoldG122FamilyInput

/-- The fixed G-122 comparison isomorphism map in the common representative
native category. -/
noncomputable def finiteAxisFoldBarAlphaNativeHom :
    finiteAxisFoldDirectNativeObject ⟶ finiteAxisFoldViaBaseNativeObject :=
  ULift.up (G122GeneratedGeometryObject.barAlpha
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput)

/-- The fixed G-122 comparison remains an isomorphism in the common
representative native category. -/
noncomputable def finiteAxisFoldBarAlphaNativeIso :
    finiteAxisFoldDirectNativeObject ≅ finiteAxisFoldViaBaseNativeObject where
  hom := finiteAxisFoldBarAlphaNativeHom
  inv := ULift.up (G122GeneratedGeometryObject.barAlphaIso
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput).inv
  hom_inv_id := by
    apply ULift.ext
    exact (G122GeneratedGeometryObject.barAlphaIso
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput).hom_inv_id
  inv_hom_id := by
    apply ULift.ext
    exact (G122GeneratedGeometryObject.barAlphaIso
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput).inv_hom_id

/-- The cochain-selected G-122 comparison in the common representative native
category. -/
noncomputable def finiteAxisFoldBarBetaNativeHom :
    finiteAxisFoldDirectNativeObject ⟶ finiteAxisFoldViaBaseNativeObject :=
  ULift.up (G122GeneratedGeometryObject.barBeta
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput)

/-- The G-122 source projector in the common representative native category. -/
noncomputable def finiteAxisFoldBarENativeHom :
    finiteAxisFoldDirectNativeObject ⟶ finiteAxisFoldDirectNativeObject :=
  ULift.up (G122GeneratedGeometryObject.barE
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput)

/-- The G-122 target projector in the common representative native category. -/
noncomputable def finiteAxisFoldBarDNativeHom :
    finiteAxisFoldViaBaseNativeObject ⟶ finiteAxisFoldViaBaseNativeObject :=
  ULift.up (G122GeneratedGeometryObject.barD
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput)

/-- The accepted G-122 comparison factorization is preserved by the common
native inclusion. -/
theorem finiteAxisFoldBarBetaNativeHom_factor :
    finiteAxisFoldBarBetaNativeHom =
      finiteAxisFoldBarAlphaNativeHom ≫ finiteAxisFoldBarDNativeHom := by
  apply ULift.ext
  exact G122GeneratedGeometryObject.barBeta_factor
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput

/-- The accepted G-122 comparison is fixed by its source projector in the
common native category. -/
@[simp] theorem finiteAxisFoldBarBetaNativeHom_source_factorization :
    finiteAxisFoldBarENativeHom ≫ finiteAxisFoldBarBetaNativeHom =
      finiteAxisFoldBarBetaNativeHom := by
  apply ULift.ext
  exact G122GeneratedGeometryObject.barBeta_source_factorization
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput

/-- The accepted G-122 comparison is fixed by its target projector in the
common native category. -/
@[simp] theorem finiteAxisFoldBarBetaNativeHom_target_factorization :
    finiteAxisFoldBarBetaNativeHom ≫ finiteAxisFoldBarDNativeHom =
      finiteAxisFoldBarBetaNativeHom := by
  apply ULift.ext
  exact G122GeneratedGeometryObject.barBeta_target_factorization
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput

/-- The accepted G-122 source projector remains idempotent in the common
native category. -/
@[simp] theorem finiteAxisFoldBarENativeHom_idempotent :
    finiteAxisFoldBarENativeHom ≫ finiteAxisFoldBarENativeHom =
      finiteAxisFoldBarENativeHom := by
  apply ULift.ext
  exact G122GeneratedGeometryObject.barE_idem
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput

/-- The accepted G-122 target projector remains idempotent in the common
native category. -/
@[simp] theorem finiteAxisFoldBarDNativeHom_idempotent :
    finiteAxisFoldBarDNativeHom ≫ finiteAxisFoldBarDNativeHom =
      finiteAxisFoldBarDNativeHom := by
  apply ULift.ext
  exact G122GeneratedGeometryObject.barD_idem
    finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput

/-- Common primitive evaluation of the fixed G-122 `barAlpha` is the accepted
representative Part I evaluation. -/
theorem finiteAxisFoldBarAlpha_read_point
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.representative) :
    InvariantWitness.point _ _
        (((reading finiteAxisFoldGeometryParameter).map
          finiteAxisFoldBarAlphaNativeHom).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (G122GeneratedGeometryObject.barAlpha
          finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query :=
  representative_read_point FiniteModel.carrier
    (G122GeneratedGeometryObject.barAlpha
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query

/-- Common primitive evaluation of the fixed G-122 `barBeta` is the accepted
representative Part I evaluation. -/
theorem finiteAxisFoldBarBeta_read_point
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.representative) :
    InvariantWitness.point _ _
        (((reading finiteAxisFoldGeometryParameter).map
          finiteAxisFoldBarBetaNativeHom).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (G122GeneratedGeometryObject.barBeta
          finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query :=
  representative_read_point FiniteModel.carrier
    (G122GeneratedGeometryObject.barBeta
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query

/-- Common primitive evaluation of the fixed G-122 source projector is the
accepted representative Part I evaluation. -/
theorem finiteAxisFoldBarE_read_point
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.representative) :
    InvariantWitness.point _ _
        (((reading finiteAxisFoldGeometryParameter).map
          finiteAxisFoldBarENativeHom).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (G122GeneratedGeometryObject.barE
          finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query :=
  representative_read_point FiniteModel.carrier
    (G122GeneratedGeometryObject.barE
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query

/-- Common primitive evaluation of the fixed G-122 target projector is the
accepted representative Part I evaluation. -/
theorem finiteAxisFoldBarD_read_point
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.representative) :
    InvariantWitness.point _ _
        (((reading finiteAxisFoldGeometryParameter).map
          finiteAxisFoldBarDNativeHom).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (G122GeneratedGeometryObject.barD
          finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query :=
  representative_read_point FiniteModel.carrier
    (G122GeneratedGeometryObject.barD
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput) query

/-- The constant-one cochain comparison is also a Hom of the same common
representative native category. -/
noncomputable def finiteAxisFoldIdentityCochainBarBetaNativeHom :
    finiteAxisFoldDirectNativeObject ⟶ finiteAxisFoldViaBaseNativeObject :=
  ULift.up (G122GeneratedGeometryObject.barBeta
    finiteAxisFoldG122FamilyInput finiteAxisFoldIdentityCochainG122CellInput)

/-- The constant-one G-122 input is retained and its selected comparison
equals the accepted `barAlpha` in the common native category. -/
theorem finiteAxisFoldIdentityCochain_barBeta_eq_barAlpha_common :
    finiteAxisFoldIdentityCochainBarBetaNativeHom =
      finiteAxisFoldBarAlphaNativeHom := by
  apply ULift.ext
  exact finiteAxisFold_identityCochain_barBeta_eq_barAlpha.trans
    finiteAxisFold_barAlpha_identityCochain.symm

/-- Common primitive evaluation of the constant-one cochain comparison is
the accepted representative Part I evaluation. -/
theorem finiteAxisFoldIdentityCochainBarBeta_read_point
    (query : IndependentGeometryHomPrimitive.Query.{0, 0}
      FiniteModel.carrier Mode.representative) :
    InvariantWitness.point _ _
        (((reading finiteAxisFoldGeometryParameter).map
          finiteAxisFoldIdentityCochainBarBetaNativeHom).down).val query =
      IndependentGeometryHomPrimitive.NativeReader.readRepresentative
        (G122GeneratedGeometryObject.barBeta
          finiteAxisFoldG122FamilyInput
          finiteAxisFoldIdentityCochainG122CellInput) query :=
  representative_read_point FiniteModel.carrier
    (G122GeneratedGeometryObject.barBeta
      finiteAxisFoldG122FamilyInput
      finiteAxisFoldIdentityCochainG122CellInput) query

/-! ### The G-122 projectors in the common Karoubi envelope -/

/-- The source projector of the fixed G-122 comparison as a Karoubi object in
the common representative native category. -/
noncomputable def finiteAxisFoldBarESourceKaroubi :
    Karoubi (NativeCategory finiteAxisFoldGeometryParameter) where
  X := finiteAxisFoldDirectNativeObject
  p := finiteAxisFoldBarENativeHom
  idem := finiteAxisFoldBarENativeHom_idempotent

/-- The target projector of the fixed G-122 comparison as a Karoubi object in
the common representative native category. -/
noncomputable def finiteAxisFoldBarDTargetKaroubi :
    Karoubi (NativeCategory finiteAxisFoldGeometryParameter) where
  X := finiteAxisFoldViaBaseNativeObject
  p := finiteAxisFoldBarDNativeHom
  idem := finiteAxisFoldBarDNativeHom_idempotent

/-- The fixed `barBeta` comparison as a Hom between its two common Karoubi
objects. -/
noncomputable def finiteAxisFoldBarBetaKaroubiHom :
    finiteAxisFoldBarESourceKaroubi ⟶ finiteAxisFoldBarDTargetKaroubi where
  f := finiteAxisFoldBarBetaNativeHom
  comm := by
    change finiteAxisFoldBarENativeHom ≫ finiteAxisFoldBarBetaNativeHom ≫
        finiteAxisFoldBarDNativeHom = finiteAxisFoldBarBetaNativeHom
    rw [finiteAxisFoldBarBetaNativeHom_target_factorization,
      finiteAxisFoldBarBetaNativeHom_source_factorization]

/-- Extend the common primitive reader to the Karoubi envelopes using
mathlib's standard extension. -/
noncomputable def primitiveKaroubiReading :
    Karoubi (NativeCategory finiteAxisFoldGeometryParameter) ⥤
      Karoubi (LocalCategory finiteAxisFoldGeometryParameter) :=
  (functorExtension₂ _ _).obj (reading finiteAxisFoldGeometryParameter)

/-- The extended reader sends the G-122 source carrier to the common reading
of the direct endpoint. -/
@[simp] theorem primitiveKaroubiReading_source_X :
    (primitiveKaroubiReading.obj finiteAxisFoldBarESourceKaroubi).X =
      (reading finiteAxisFoldGeometryParameter).obj
        finiteAxisFoldDirectNativeObject := rfl

/-- The extended reader sends the G-122 source projector to its common
primitive reading. -/
@[simp] theorem primitiveKaroubiReading_source_p :
    (primitiveKaroubiReading.obj finiteAxisFoldBarESourceKaroubi).p =
      (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldBarENativeHom := rfl

/-- The extended reader sends the G-122 target carrier to the common reading
of the via-base endpoint. -/
@[simp] theorem primitiveKaroubiReading_target_X :
    (primitiveKaroubiReading.obj finiteAxisFoldBarDTargetKaroubi).X =
      (reading finiteAxisFoldGeometryParameter).obj
        finiteAxisFoldViaBaseNativeObject := rfl

/-- The extended reader sends the G-122 target projector to its common
primitive reading. -/
@[simp] theorem primitiveKaroubiReading_target_p :
    (primitiveKaroubiReading.obj finiteAxisFoldBarDTargetKaroubi).p =
      (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldBarDNativeHom := rfl

/-- The underlying map of the extended `barBeta` Hom is its common primitive
reading. -/
@[simp] theorem primitiveKaroubiReading_barBeta_f :
    (primitiveKaroubiReading.map finiteAxisFoldBarBetaKaroubiHom).f =
      (reading finiteAxisFoldGeometryParameter).map
        finiteAxisFoldBarBetaNativeHom := rfl

/-! ### The G-122 comparison square in the common Arrow category -/

/-- The fixed `barAlpha` as an object of the Arrow category over the common
representative native category. -/
noncomputable def finiteAxisFoldBarAlphaArrow :
    Arrow (NativeCategory finiteAxisFoldGeometryParameter) :=
  Arrow.mk finiteAxisFoldBarAlphaNativeHom

/-- A raw G-122 comparison acts on both endpoints of the fixed common
`barAlpha` arrow. -/
noncomputable def finiteAxisFoldRawComparisonArrowHom
    (raw : FiniteAxisFoldComparisonRestrictionKernel.RawComparison) :
    finiteAxisFoldBarAlphaArrow ⟶ finiteAxisFoldBarAlphaArrow where
  left := ULift.up raw.1.1.hom.1
  right := ULift.up raw.1.2.hom.1
  w := by
    apply ULift.ext
    exact congrArg (fun morphism => morphism.hom)
      (FullGeometryNormalization.mem_rawGeometryNormalizationComparisonSubgroup.mp
        raw.property)

/-- Raw comparison multiplication is the endomorphism multiplication on the
common `barAlpha` arrow. -/
noncomputable def finiteAxisFoldRawComparisonArrowEndHom :
    FiniteAxisFoldComparisonRestrictionKernel.RawComparison →*
      End finiteAxisFoldBarAlphaArrow where
  toFun := finiteAxisFoldRawComparisonArrowHom
  map_one' := by
    apply Arrow.hom_ext <;> apply ULift.ext <;> rfl
  map_mul' first second := by
    apply Arrow.hom_ext <;> apply ULift.ext <;> rfl

/-- Include the old one-object G-122 comparison category in the Arrow
category of the common representative native category. -/
noncomputable def finiteAxisFoldRawComparisonInclusion :
    G122FullComparisonTwistedGroup.GlobalCategory ⥤
      Arrow (NativeCategory finiteAxisFoldGeometryParameter) where
  obj _ := finiteAxisFoldBarAlphaArrow
  map raw := finiteAxisFoldRawComparisonArrowEndHom raw
  map_id _ := finiteAxisFoldRawComparisonArrowEndHom.map_one
  map_comp first second :=
    finiteAxisFoldRawComparisonArrowEndHom.map_mul second first

/-- The left component of the Arrow inclusion is the source automorphism of
the raw comparison. -/
@[simp] theorem finiteAxisFoldRawComparisonInclusion_left
    (raw : FiniteAxisFoldComparisonRestrictionKernel.RawComparison) :
    ((finiteAxisFoldRawComparisonInclusion.map
      (X := SingleObj.star
        FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
      (Y := SingleObj.star
        FiniteAxisFoldComparisonRestrictionKernel.RawComparison) raw).left).down =
      raw.1.1.hom.1 := rfl

/-- The right component of the Arrow inclusion is the target automorphism of
the raw comparison. -/
@[simp] theorem finiteAxisFoldRawComparisonInclusion_right
    (raw : FiniteAxisFoldComparisonRestrictionKernel.RawComparison) :
    ((finiteAxisFoldRawComparisonInclusion.map
      (X := SingleObj.star
        FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
      (Y := SingleObj.star
        FiniteAxisFoldComparisonRestrictionKernel.RawComparison) raw).right).down =
      raw.1.2.hom.1 := rfl

/-- The accepted G-122 equivalence has the established twisted-coordinate
reader as its forward functor. -/
@[simp] theorem finiteAxisFoldTwistedEquivalence_functor :
    G122FullComparisonTwistedGroup.equivalence.functor =
      G122FullComparisonTwistedGroup.reading := rfl

/-- Transport twisted G-122 coordinates through the accepted inverse, retain
both Arrow endpoints, and apply the new primitive reading. -/
noncomputable def finiteAxisFoldTwistedComparison :
    G122FullComparisonTwistedGroup.LocalCategory ⥤
      Arrow (LocalCategory finiteAxisFoldGeometryParameter) :=
  G122FullComparisonTwistedGroup.equivalence.inverse ⋙
    finiteAxisFoldRawComparisonInclusion ⋙
    Functor.mapArrow (reading finiteAxisFoldGeometryParameter)

/-- The old twisted-coordinate reader followed by its accepted inverse agrees
with the new common Arrow reading of raw comparisons. -/
noncomputable def finiteAxisFoldRawComparisonReadingIso :
    G122FullComparisonTwistedGroup.reading ⋙
        finiteAxisFoldTwistedComparison ≅
      finiteAxisFoldRawComparisonInclusion ⋙
        Functor.mapArrow (reading finiteAxisFoldGeometryParameter) := by
  rw [← finiteAxisFoldTwistedEquivalence_functor]
  exact G122FullComparisonTwistedGroup.equivalence.funInvIdAssoc
    (finiteAxisFoldRawComparisonInclusion ⋙
      Functor.mapArrow (reading finiteAxisFoldGeometryParameter))

/-- The left component read from arbitrary twisted coordinates is the common
primitive reading of the assembled source endpoint map. -/
theorem finiteAxisFoldTwistedComparison_left
    (code : G122FullComparisonTwistedGroup.TwistedCode) :
    (finiteAxisFoldTwistedComparison.map
      (X := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
      (Y := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
      code).left =
      (reading finiteAxisFoldGeometryParameter).map
        (X := finiteAxisFoldDirectNativeObject)
        (Y := finiteAxisFoldDirectNativeObject)
        (ULift.up (G122FullComparisonTwistedGroup.assemble code).1.1.hom.1) := rfl

/-- The right component read from arbitrary twisted coordinates is the common
primitive reading of the assembled target endpoint map. -/
theorem finiteAxisFoldTwistedComparison_right
    (code : G122FullComparisonTwistedGroup.TwistedCode) :
    (finiteAxisFoldTwistedComparison.map
      (X := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
      (Y := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
      code).right =
      (reading finiteAxisFoldGeometryParameter).map
        (X := finiteAxisFoldViaBaseNativeObject)
        (Y := finiteAxisFoldViaBaseNativeObject)
        (ULift.up (G122FullComparisonTwistedGroup.assemble code).1.2.hom.1) := rfl

/-- Reading a raw comparison to twisted coordinates and applying the common
Arrow comparison recovers the direct common reading of that raw comparison. -/
theorem finiteAxisFoldTwistedComparison_read_raw
    (raw : FiniteAxisFoldComparisonRestrictionKernel.RawComparison) :
    finiteAxisFoldTwistedComparison.map
        (X := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
        (Y := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
        (G122FullComparisonTwistedGroup.read raw) =
      (Functor.mapArrow (reading finiteAxisFoldGeometryParameter)).map
        (finiteAxisFoldRawComparisonInclusion.map
          (X := SingleObj.star
            FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
          (Y := SingleObj.star
            FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
          raw) := by
  change (Functor.mapArrow (reading finiteAxisFoldGeometryParameter)).map
      (finiteAxisFoldRawComparisonInclusion.map
        (X := SingleObj.star
          FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
        (Y := SingleObj.star
          FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
        (G122FullComparisonTwistedGroup.assemble
          (G122FullComparisonTwistedGroup.read raw))) = _
  rw [G122FullComparisonTwistedGroup.assemble_read]

/-- The common Arrow comparison preserves the accepted twisted
multiplication. -/
theorem finiteAxisFoldTwistedComparison_multiply
    (first second : G122FullComparisonTwistedGroup.TwistedCode) :
    finiteAxisFoldTwistedComparison.map
        (X := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
        (Y := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
        (G122FullComparisonTwistedGroup.multiply first second) =
      finiteAxisFoldTwistedComparison.map
          (X := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
          (Y := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
          second ≫
        finiteAxisFoldTwistedComparison.map
          (X := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
          (Y := SingleObj.star G122FullComparisonTwistedGroup.TwistedCode)
          first := by
  exact finiteAxisFoldTwistedComparison.map_comp second first

/-! ### Cycle 79 compatibility -/

/-- Lift the represented tagged global category into Cycle 79's tagged
global branch through the accepted package-generated equivalence. -/
noncomputable def taggedCycle79GlobalLift :
    TagChangeExactGeometryLocalModel.GlobalCategory ⥤
      AATBranchGlobal .tagged :=
  TagChangeExactGeometryNormalForm.representedMulEquivPackageGenerated.toSingleObjEquiv.functor ⋙
    (ULiftHomULiftCategory.equiv.{1, 1}
      TagChangeGeneratedCategoryEquivalence.GlobalCategory).functor

/-- Lift the represented tagged local category into Cycle 79's tagged local
branch. -/
noncomputable def taggedCycle79LocalLift :
    TagChangeExactGeometryLocalModel.LocalCategory ⥤
      AATBranchLocal .tagged :=
  (ULiftHomULiftCategory.equiv.{1, 1}
    TagChangeGeneratedCategoryEquivalence.LocalCategory).functor

/-- Lift the raw G-122 comparison category into Cycle 79's G-122 global
branch. -/
noncomputable def g122Cycle79GlobalLift :
    G122FullComparisonTwistedGroup.GlobalCategory ⥤
      AATBranchGlobal .g122 :=
  (ULiftHomULiftCategory.equiv.{1, 1}
    G122FullComparisonTwistedGroup.GlobalCategory).functor

/-- Lift the twisted G-122 comparison category into Cycle 79's G-122 local
branch. -/
noncomputable def g122Cycle79LocalLift :
    G122FullComparisonTwistedGroup.LocalCategory ⥤
      AATBranchLocal .g122 :=
  (ULiftHomULiftCategory.equiv.{1, 1}
    G122FullComparisonTwistedGroup.LocalCategory).functor

/-- The represented tagged reader is the tagged Cycle 79 branch reader after
the canonical global and local lifts. -/
noncomputable def taggedCycle79BranchReadingIso :
    taggedCycle79GlobalLift ⋙ aatBranchReading .tagged ≅
      TagChangeExactGeometryLocalModel.reading ⋙
        taggedCycle79LocalLift :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro source target morphism
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply ULift.ext
    change TagChangeGeneratedCategoryEquivalence.reading.map
        (TagChangeExactGeometryNormalForm.representedMulEquivPackageGenerated
          morphism) =
      TagChangeExactGeometryLocalModel.reading.map morphism
    rfl)

/-- The raw-to-twisted G-122 reader is the G-122 Cycle 79 branch reader after
the canonical global and local lifts. -/
noncomputable def g122Cycle79BranchReadingIso :
    g122Cycle79GlobalLift ⋙ aatBranchReading .g122 ≅
      G122FullComparisonTwistedGroup.reading ⋙
        g122Cycle79LocalLift :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro source target morphism
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply ULift.ext
    change G122FullComparisonTwistedGroup.reading.map morphism =
      G122FullComparisonTwistedGroup.reading.map morphism
    rfl)

/-- The represented tagged reader reaches the Cycle 79 total reader through
the tagged global and local fibers. -/
noncomputable def cycle79TaggedRepresentedTotalReadingIso :
    taggedCycle79GlobalLift ⋙ aatGlobalFiberInclusion .tagged ⋙
        aatTotalReading ≅
      TagChangeExactGeometryLocalModel.reading ⋙
        taggedCycle79LocalLift ⋙ aatLocalFiberInclusion .tagged :=
  (Functor.isoWhiskerLeft taggedCycle79GlobalLift
      (aatFiberReadingIso .tagged)).trans
    (Functor.isoWhiskerRight taggedCycle79BranchReadingIso
      (aatLocalFiberInclusion .tagged))

/-- The raw G-122 reader reaches the Cycle 79 total reader through the G-122
global and local fibers. -/
noncomputable def cycle79G122RawTotalReadingIso :
    g122Cycle79GlobalLift ⋙ aatGlobalFiberInclusion .g122 ⋙
        aatTotalReading ≅
      G122FullComparisonTwistedGroup.reading ⋙
        g122Cycle79LocalLift ⋙ aatLocalFiberInclusion .g122 :=
  (Functor.isoWhiskerLeft g122Cycle79GlobalLift
      (aatFiberReadingIso .g122)).trans
    (Functor.isoWhiskerRight g122Cycle79BranchReadingIso
      (aatLocalFiberInclusion .g122))

/-- Reading a represented tagged Hom and applying the common local comparison
recovers the direct common reading of that represented Hom. -/
theorem taggedLocalComparison_read_represented
    {source target : TagChangeExactGeometryLocalModel.GlobalCategory}
    (morphism : source ⟶ target) :
    taggedLocalComparison.map
        (TagChangeExactGeometryLocalModel.reading.map morphism) =
      (reading
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})).map
        (taggedRepresentedInclusion.map morphism) := by
  change (reading
      (Parameter.geometry FiniteModel.carrier Mode.explicit :
        Parameter.{0, 0})).map
      (taggedRepresentedInclusion.map
        (TagChangeExactGeometryLocalModel.representedMulEquivLocalSection.symm
          (TagChangeExactGeometryLocalModel.representedMulEquivLocalSection
            morphism))) = _
  rw [TagChangeExactGeometryLocalModel.representedMulEquivLocalSection.symm_apply_apply]

/-- Cycle 79 total reading of a represented tagged Hom agrees with its direct
common explicit primitive reading. -/
theorem cycle79TaggedTotalReading_common
    {source target : TagChangeExactGeometryLocalModel.GlobalCategory}
    (morphism : source ⟶ target) :
    taggedLocalComparison.map
        (aatTotalFiberReadingMap .tagged
          (taggedCycle79GlobalLift.map morphism)).down =
      (reading
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})).map
        (taggedRepresentedInclusion.map morphism) := by
  rw [aatTotalFiberReadingMap_eq]
  change taggedLocalComparison.map
      (TagChangeExactGeometryLocalModel.reading.map morphism) = _
  exact taggedLocalComparison_read_represented morphism

/-- Cycle 79 total reading of a raw G-122 comparison agrees with its direct
common representative Arrow reading. -/
theorem cycle79G122TotalReading_common
    (raw : FiniteAxisFoldComparisonRestrictionKernel.RawComparison) :
    finiteAxisFoldTwistedComparison.map
        (aatTotalFiberReadingMap .g122
          (g122Cycle79GlobalLift.map
            (X := SingleObj.star
              FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
            (Y := SingleObj.star
              FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
            raw)).down =
      (Functor.mapArrow (reading finiteAxisFoldGeometryParameter)).map
        (finiteAxisFoldRawComparisonInclusion.map
          (X := SingleObj.star
            FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
          (Y := SingleObj.star
            FiniteAxisFoldComparisonRestrictionKernel.RawComparison)
          raw) := by
  rw [aatTotalFiberReadingMap_eq]
  change finiteAxisFoldTwistedComparison.map
      (G122FullComparisonTwistedGroup.read raw) = _
  exact finiteAxisFoldTwistedComparison_read_raw raw

/-- The new primitive lens decoder agrees with the accepted finite-fiber
decoder after applying the common local-to-fiber comparison. -/
noncomputable def lensFiniteDecoderFiberIso (input : LensFamilyInput.{0}) :
    lensFiniteDecoder input ⋙ lensLocalToFiber input ≅
      lensFiberFiniteDecoder input :=
  Functor.isoWhiskerLeft
    (LensRealization.lensDecoder input.View input.reference)
    (lensSemanticPrimitiveFiberComparisonIso input)

/-- The new primitive protocol decoder agrees with the accepted observed
decoder after applying the common local-to-observed comparison. -/
noncomputable def protocolFiniteDecoderObservedIso
    (input : ProtocolFamilyInput.{0}) :
    protocolFiniteDecoder input ⋙ protocolLocalToObserved input ≅
      protocolObservedFiniteDecoder input :=
  Functor.isoWhiskerLeft
    (ProtocolPresentation.decoder input.schema input.observation)
    (protocolSemanticPrimitiveObservedComparisonIso input)

/-- The tail that places a common lens local object in Cycle 79's total local
lens fiber. -/
noncomputable def lensCommonLocalToTotal (input : LensFamilyInput.{0}) :
    LocalCategory (Parameter.lens input : Parameter.{0, 0}) ⥤ AATTotalLocal :=
  lensLocalToFiber input ⋙
    (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
    aatLocalFiberInclusion (.lens input)

/-- The tail that places a common protocol local object in Cycle 79's total
local protocol fiber. -/
noncomputable def protocolCommonLocalToTotal
    (input : ProtocolFamilyInput.{0}) :
    LocalCategory (Parameter.protocol input : Parameter.{0, 0}) ⥤ AATTotalLocal :=
  protocolLocalToObserved input ⋙
    (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
    aatLocalFiberInclusion (.protocol input)

/-- The new lens finite decoder reaches the existing Cycle 79 total reading
through the common primitive local category. -/
noncomputable def cycle79LensPrimitiveFiniteDecoderReadingIso
    (input : LensFamilyInput.{0}) :
    (lensFiniteDecoder input ⋙ lensLocalToFiber input) ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        aatLocalFiberInclusion (.lens input) ≅
      aatTotalLensFiniteDecoder input ⋙ aatTotalReading :=
  (Functor.isoWhiskerRight (lensFiniteDecoderFiberIso input)
      ((ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        aatLocalFiberInclusion (.lens input))).trans
    (aatTotalLensFiniteDecoderReadingIso input).symm

/-- The new protocol finite decoder reaches the existing Cycle 79 total
reading through the common primitive local category. -/
noncomputable def cycle79ProtocolPrimitiveFiniteDecoderReadingIso
    (input : ProtocolFamilyInput.{0}) :
    (protocolFiniteDecoder input ⋙ protocolLocalToObserved input) ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        aatLocalFiberInclusion (.protocol input) ≅
      aatTotalProtocolFiniteDecoder input ⋙ aatTotalReading :=
  (Functor.isoWhiskerRight (protocolFiniteDecoderObservedIso input)
      ((ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        aatLocalFiberInclusion (.protocol input))).trans
    (aatTotalProtocolFiniteDecoderReadingIso input).symm

/-- Reading the existing Cycle 79 lens Karoubi route is the accepted
finite-fiber Karoubi functor in the total local lens fiber. -/
noncomputable def cycle79LensKaroubiFiberReadingIso
    (input : LensFamilyInput.{0}) :
    aatTotalLensKaroubiRoute input ⋙ aatTotalReading ≅
      (lensKaroubiFiberEquivalence input).functor ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        aatLocalFiberInclusion (.lens input) :=
  (Functor.isoWhiskerLeft
      (aatBranchLensKaroubiEquivalence input).functor
      (aatFiberReadingIso (.lens input))).trans
    (Functor.isoWhiskerLeft
      ((lensKaroubiFiberEquivalence input).functor ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input))))
      ((aatBranchReconstructionEquivalence (.lens input)).invFunIdAssoc
        (aatLocalFiberInclusion (.lens input))))

/-- Reading the existing Cycle 79 protocol Karoubi route is the accepted
observed Karoubi functor in the total local protocol fiber. -/
noncomputable def cycle79ProtocolKaroubiObservedReadingIso
    (input : ProtocolFamilyInput.{0}) :
    aatTotalProtocolKaroubiRoute input ⋙ aatTotalReading ≅
      (protocolKaroubiObservedRestrictionEquivalence input).functor ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        aatLocalFiberInclusion (.protocol input) :=
  (Functor.isoWhiskerLeft
      (aatBranchProtocolKaroubiEquivalence input).functor
      (aatFiberReadingIso (.protocol input))).trans
    (Functor.isoWhiskerLeft
      ((protocolKaroubiObservedRestrictionEquivalence input).functor ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input))))
      ((aatBranchReconstructionEquivalence (.protocol input)).invFunIdAssoc
        (aatLocalFiberInclusion (.protocol input))))

/-- The new lens Karoubi route reaches the existing Cycle 79 total reading
through the common primitive local category. -/
noncomputable def cycle79LensPrimitiveKaroubiReadingIso
    (input : LensFamilyInput.{0}) :
    ((lensKaroubiEquivalence input).functor ⋙ lensLocalToFiber input) ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        aatLocalFiberInclusion (.lens input) ≅
      aatTotalLensKaroubiRoute input ⋙ aatTotalReading :=
  (Functor.isoWhiskerRight (lensKaroubiFiberComparisonIso input)
      ((ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        aatLocalFiberInclusion (.lens input))).trans
    (cycle79LensKaroubiFiberReadingIso input).symm

/-- The new protocol Karoubi route reaches the existing Cycle 79 total
reading through the common primitive local category. -/
noncomputable def cycle79ProtocolPrimitiveKaroubiReadingIso
    (input : ProtocolFamilyInput.{0}) :
    ((protocolKaroubiEquivalence input).functor ⋙
        protocolLocalToObserved input) ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        aatLocalFiberInclusion (.protocol input) ≅
      aatTotalProtocolKaroubiRoute input ⋙ aatTotalReading :=
  (Functor.isoWhiskerRight (protocolKaroubiObservedComparisonIso input)
      ((ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        aatLocalFiberInclusion (.protocol input))).trans
    (cycle79ProtocolKaroubiObservedReadingIso input).symm

/-- Cycle 79's fiber reading square lifted to Arrow categories. -/
noncomputable def cycle79FiberArrowReadingIso
    (parameter : AATBranchParameter) :
    (aatGlobalFiberInclusion parameter).mapArrow ⋙
        Functor.mapArrow aatTotalReading ≅
      Functor.mapArrow (aatBranchReading parameter) ⋙
        (aatLocalFiberInclusion parameter).mapArrow := by
  change Functor.mapArrow
      (aatGlobalFiberInclusion parameter ⋙ aatTotalReading) ≅
    Functor.mapArrow
      (aatBranchReading parameter ⋙ aatLocalFiberInclusion parameter)
  exact Functor.mapIso (Functor.mapArrowFunctor _ _)
    (aatFiberReadingIso parameter)

/-- The branch Arrow equivalence evaluates to the Arrow lift of the accepted
branch reading. -/
@[simp] theorem aatBranchArrowReconstructionEquivalence_functor
    (parameter : AATBranchParameter) :
    (aatBranchArrowReconstructionEquivalence parameter).functor =
      Functor.mapArrow (aatBranchReading parameter) := rfl

/-- The lens Karoubi Arrow equivalence evaluates through the accepted
finite-fiber and branch equivalences. -/
@[simp] theorem aatBranchLensKaroubiArrowEquivalence_functor
    (input : LensFamilyInput) :
    (aatBranchLensKaroubiArrowEquivalence input).functor =
      (lensKaroubiFiberArrowEquivalence input).functor ⋙
        Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        (aatBranchArrowReconstructionEquivalence (.lens input)).inverse := rfl

/-- The protocol Karoubi Arrow equivalence evaluates through the accepted
observed and branch equivalences. -/
@[simp] theorem aatBranchProtocolKaroubiArrowEquivalence_functor
    (input : ProtocolFamilyInput) :
    (aatBranchProtocolKaroubiArrowEquivalence input).functor =
      (protocolKaroubiObservedRestrictionArrowEquivalence input).functor ⋙
        Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        (aatBranchArrowReconstructionEquivalence (.protocol input)).inverse := rfl

/-- Two left whiskers preserve the cancellation of the inverse and forward
functors of an equivalence. -/
private noncomputable def equivalenceCancellationAfterTwoIso
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type v₁}
    {E : Type w}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (first : Functor A B) (second : Functor B D)
    (equivalence : C ≌ D) (right : Functor D E) :
    first ⋙ second ⋙ equivalence.inverse ⋙
        equivalence.functor ⋙ right ≅
      first ⋙ second ⋙ right :=
  Functor.isoWhiskerLeft first
    (Functor.isoWhiskerLeft second (equivalence.invFunIdAssoc right))

/-- Reading the existing Cycle 79 lens Karoubi Arrow route is the accepted
finite-fiber Arrow functor in the total local lens fiber. -/
noncomputable def cycle79LensKaroubiArrowFiberReadingIso
    (input : LensFamilyInput.{0}) :
    aatTotalLensKaroubiArrowRoute input ⋙
        Functor.mapArrow aatTotalReading ≅
      (lensKaroubiFiberArrowEquivalence input).functor ⋙
        Functor.mapArrow (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        (aatLocalFiberInclusion (.lens input)).mapArrow := by
  refine (Functor.isoWhiskerLeft
    (aatBranchLensKaroubiArrowEquivalence input).functor
    (cycle79FiberArrowReadingIso (.lens input))).trans ?_
  rw [aatBranchLensKaroubiArrowEquivalence_functor]
  rw [← aatBranchArrowReconstructionEquivalence_functor]
  exact equivalenceCancellationAfterTwoIso
    (lensKaroubiFiberArrowEquivalence input).functor
    (Functor.mapArrow
      (ULiftHom.up (C := CSBranchLocal (.lens input))))
    (aatBranchArrowReconstructionEquivalence (.lens input))
    (aatLocalFiberInclusion (.lens input)).mapArrow

/-- Reading the existing Cycle 79 protocol Karoubi Arrow route is the accepted
observed Arrow functor in the total local protocol fiber. -/
noncomputable def cycle79ProtocolKaroubiArrowObservedReadingIso
    (input : ProtocolFamilyInput.{0}) :
    aatTotalProtocolKaroubiArrowRoute input ⋙
        Functor.mapArrow aatTotalReading ≅
      (protocolKaroubiObservedRestrictionArrowEquivalence input).functor ⋙
        Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        (aatLocalFiberInclusion (.protocol input)).mapArrow := by
  refine (Functor.isoWhiskerLeft
    (aatBranchProtocolKaroubiArrowEquivalence input).functor
    (cycle79FiberArrowReadingIso (.protocol input))).trans ?_
  rw [aatBranchProtocolKaroubiArrowEquivalence_functor]
  rw [← aatBranchArrowReconstructionEquivalence_functor]
  exact equivalenceCancellationAfterTwoIso
    (protocolKaroubiObservedRestrictionArrowEquivalence input).functor
    (Functor.mapArrow
      (ULiftHom.up (C := CSBranchLocal (.protocol input))))
    (aatBranchArrowReconstructionEquivalence (.protocol input))
    (aatLocalFiberInclusion (.protocol input)).mapArrow

/-- The new lens Karoubi Arrow route reaches the existing Cycle 79 total
Arrow reading through the common primitive local category. -/
noncomputable def cycle79LensPrimitiveKaroubiArrowReadingIso
    (input : LensFamilyInput.{0}) :
    ((lensKaroubiArrowEquivalence input).functor ⋙
        Functor.mapArrow (lensLocalToFiber input)) ⋙
        Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        (aatLocalFiberInclusion (.lens input)).mapArrow ≅
      aatTotalLensKaroubiArrowRoute input ⋙
        Functor.mapArrow aatTotalReading :=
  (Functor.isoWhiskerRight (lensKaroubiArrowFiberComparisonIso input)
      (Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.lens input))) ⋙
        (aatLocalFiberInclusion (.lens input)).mapArrow)).trans
    (cycle79LensKaroubiArrowFiberReadingIso input).symm

/-- The new protocol Karoubi Arrow route reaches the existing Cycle 79 total
Arrow reading through the common primitive local category. -/
noncomputable def cycle79ProtocolPrimitiveKaroubiArrowReadingIso
    (input : ProtocolFamilyInput.{0}) :
    ((protocolKaroubiArrowEquivalence input).functor ⋙
        Functor.mapArrow (protocolLocalToObserved input)) ⋙
        Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        (aatLocalFiberInclusion (.protocol input)).mapArrow ≅
      aatTotalProtocolKaroubiArrowRoute input ⋙
        Functor.mapArrow aatTotalReading :=
  (Functor.isoWhiskerRight (protocolKaroubiArrowObservedComparisonIso input)
      (Functor.mapArrow
          (ULiftHom.up (C := CSBranchLocal (.protocol input))) ⋙
        (aatLocalFiberInclusion (.protocol input)).mapArrow)).trans
    (cycle79ProtocolKaroubiArrowObservedReadingIso input).symm

/-- Cycle 79's global fiber inclusion remains available downstream of the
common primitive reconstruction. -/
noncomputable def cycle79GlobalFiberInclusion
    (parameter : AATBranchParameter) :
    AATBranchGlobal parameter ⥤ AATTotalGlobal :=
  aatGlobalFiberInclusion parameter

/-- Cycle 79's local fiber inclusion remains available downstream of the
common primitive reconstruction. -/
noncomputable def cycle79LocalFiberInclusion
    (parameter : AATBranchParameter) :
    AATBranchLocal parameter ⥤ AATTotalLocal :=
  aatLocalFiberInclusion parameter

/-- Cycle 79's fiber reading square is retained without reconstructing its
decoder, Karoubi, or Arrow arguments. -/
noncomputable def cycle79FiberReadingIso (parameter : AATBranchParameter) :
    cycle79GlobalFiberInclusion parameter ⋙ aatTotalReading ≅
      aatBranchReading parameter ⋙ cycle79LocalFiberInclusion parameter :=
  aatFiberReadingIso parameter

/-- The existing tagged explicit route is the tagged specialization of the
Cycle 79 fiber reading square. -/
noncomputable def cycle79TaggedFiberReadingIso :
    cycle79GlobalFiberInclusion .tagged ⋙ aatTotalReading ≅
      aatBranchReading .tagged ⋙ cycle79LocalFiberInclusion .tagged :=
  cycle79FiberReadingIso .tagged

/-- The existing G-122 route is the representative specialization of the
Cycle 79 fiber reading square. -/
noncomputable def cycle79G122FiberReadingIso :
    cycle79GlobalFiberInclusion .g122 ⋙ aatTotalReading ≅
      aatBranchReading .g122 ⋙ cycle79LocalFiberInclusion .g122 :=
  cycle79FiberReadingIso .g122

/-- The existing lens route is the lens specialization of the Cycle 79 fiber
reading square. -/
noncomputable def cycle79LensFiberReadingIso (input : LensFamilyInput.{0}) :
    cycle79GlobalFiberInclusion (.lens input) ⋙ aatTotalReading ≅
      aatBranchReading (.lens input) ⋙ cycle79LocalFiberInclusion (.lens input) :=
  cycle79FiberReadingIso (.lens input)

/-- The existing protocol route is the protocol specialization of the Cycle
79 fiber reading square. -/
noncomputable def cycle79ProtocolFiberReadingIso
    (input : ProtocolFamilyInput.{0}) :
    cycle79GlobalFiberInclusion (.protocol input) ⋙ aatTotalReading ≅
      aatBranchReading (.protocol input) ⋙
        cycle79LocalFiberInclusion (.protocol input) :=
  cycle79FiberReadingIso (.protocol input)

/-- Cycle 79's exact global Hom inclusion is retained. -/
def cycle79GlobalFiberHomEquiv (parameter : AATBranchParameter)
    (source target : AATBranchGlobal parameter) :
    (source ⟶ target) ≃
      ((cycle79GlobalFiberInclusion parameter).obj source ⟶
        (cycle79GlobalFiberInclusion parameter).obj target) :=
  aatGlobalFiberHomEquiv parameter source target

/-- Cycle 79's exact local Hom inclusion is retained. -/
def cycle79LocalFiberHomEquiv (parameter : AATBranchParameter)
    (source target : AATBranchLocal parameter) :
    (source ⟶ target) ≃
      ((cycle79LocalFiberInclusion parameter).obj source ⟶
        (cycle79LocalFiberInclusion parameter).obj target) :=
  aatLocalFiberHomEquiv parameter source target

end IndependentAATPrimitiveReconstruction

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
