import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryCategoryReconstruction
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
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport
open AAT.AG.RealizationReconstruction
open LocalReconstructionEquivalence
open IndependentGeometryHomPrimitive

noncomputable section

namespace IndependentAATPrimitiveReconstruction

universe u v u₁ u₂ v₁ v₂ w

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

/-- One common reconstruction datum built from direct branch assembly. -/
noncomputable def reconstructionData (parameter : Parameter.{u, v}) :
    ReconstructionData (reading parameter) where
  separation := ⟨fun _ _ => ⟨fun first second equality => by
    rw [← assembleHom_read parameter first, equality,
      assembleHom_read parameter second]⟩⟩
  homAssembly :=
    { assemble := assembleHom parameter
      map_assemble := read_assembleHom parameter }
  objectAssembly :=
    { assembleObject := assembleObject parameter
      readAssembledIso := readAssembledObjectIso parameter }

/-- The common primitive reader separates every native Hom. -/
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

/-- The main common equivalence, obtained by applying the general
reconstruction theorem once to the common concrete data. -/
noncomputable def equivalence (parameter : Parameter.{u, v}) :
    NativeCategory parameter ≌ LocalCategory parameter :=
  (reconstructionData parameter).equivalence

/-- No-unfold API: the forward functor of the common equivalence is the
common primitive reader. -/
@[simp] theorem equivalence_functor (parameter : Parameter.{u, v}) :
    (equivalence parameter).functor = reading parameter := rfl

/-- Reading and assembly give the common Hom-set equivalence. -/
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

/-! ### Comparisons with existing readings -/

/-- Compare the common equivalence with any existing reading from the same
native category. -/
noncomputable def comparisonIso
    {R : Type u₁} [Category.{v₁} R]
    {M : Type u₂} [Category.{v₂} M]
    {L : Type w} [Category L]
    (equivalence : R ≌ M) (reader : R ⥤ L) :
    equivalence.functor ⋙ (equivalence.inverse ⋙ reader) ≅ reader :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight equivalence.unitIso.symm reader ≪≫ reader.leftUnitor

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

/-- The common lens equivalence compares canonically with the existing
finite-fiber reader. -/
noncomputable def lensFiberComparisonIso
    (input : LensFamilyInput.{u}) :
    (equivalence (Parameter.lens input : Parameter.{u, u})).functor ⋙
        ((equivalence (Parameter.lens input : Parameter.{u, u})).inverse ⋙
          lensFiberReader input) ≅
      lensFiberReader input :=
  comparisonIso (equivalence (Parameter.lens input : Parameter.{u, u}))
    (lensFiberReader input)

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

/-- The common protocol equivalence compares canonically with the existing
observed restriction reader. -/
noncomputable def protocolObservedComparisonIso
    (input : ProtocolFamilyInput.{u}) :
    (equivalence (Parameter.protocol input : Parameter.{u, u})).functor ⋙
        ((equivalence (Parameter.protocol input : Parameter.{u, u})).inverse ⋙
          protocolObservedReader input) ≅
      protocolObservedReader input :=
  comparisonIso (equivalence (Parameter.protocol input : Parameter.{u, u}))
    (protocolObservedReader input)

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

/-- The old represented tagged route agrees with the common explicit
primitive reading after reconstruction. -/
noncomputable def taggedRepresentedReadingIso :
    taggedRepresentedInclusion ⋙
        ((equivalence
          (Parameter.geometry FiniteModel.carrier Mode.explicit :
            Parameter.{0, 0})).functor ⋙
          ((equivalence
            (Parameter.geometry FiniteModel.carrier Mode.explicit :
              Parameter.{0, 0})).inverse ⋙
            reading
              (Parameter.geometry FiniteModel.carrier Mode.explicit :
                Parameter.{0, 0}))) ≅
      taggedRepresentedInclusion ⋙
        reading
          (Parameter.geometry FiniteModel.carrier Mode.explicit :
            Parameter.{0, 0}) :=
  Functor.isoWhiskerLeft taggedRepresentedInclusion
    (comparisonIso
      (equivalence
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0}))
      (reading
        (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})))

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

/-- The common representative equivalence induces the Arrow equivalence used
to compare the old G-122 category with the primitive reading. -/
noncomputable def finiteAxisFoldArrowEquivalence :
    Arrow (NativeCategory finiteAxisFoldGeometryParameter) ≌
      Arrow (LocalCategory finiteAxisFoldGeometryParameter) :=
  Functor.mapArrowEquivalence (equivalence finiteAxisFoldGeometryParameter)

/-- After the old G-122 category enters through both endpoint maps, the
common Arrow reading agrees with its reconstruction comparison. -/
noncomputable def finiteAxisFoldRawComparisonReadingIso :
    finiteAxisFoldRawComparisonInclusion ⋙
        (finiteAxisFoldArrowEquivalence.functor ⋙
          (finiteAxisFoldArrowEquivalence.inverse ⋙
            Functor.mapArrow (reading finiteAxisFoldGeometryParameter))) ≅
      finiteAxisFoldRawComparisonInclusion ⋙
        Functor.mapArrow (reading finiteAxisFoldGeometryParameter) :=
  Functor.isoWhiskerLeft finiteAxisFoldRawComparisonInclusion
    (comparisonIso finiteAxisFoldArrowEquivalence
      (Functor.mapArrow (reading finiteAxisFoldGeometryParameter)))

/-! ### Cycle 79 compatibility -/

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
