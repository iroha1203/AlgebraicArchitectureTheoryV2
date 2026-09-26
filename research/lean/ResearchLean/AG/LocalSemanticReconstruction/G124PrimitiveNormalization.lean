import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionGroupSquare
import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalization
import Formal.Util.AssertStandardAxioms

/-! Canonical-normalization admissibility read from the independent primitive
geometry object, and its unrestricted local idempotent. -/

namespace AAT.AG.LocalSemanticReconstruction.G124PrimitiveNormalization

open CategoryTheory CategoryTheory.Idempotents AtomFoundation DoctrineFiberProduct
open IndependentGeometryCategoryReconstruction IndependentGeometryTableAssembly
open IndependentAATPrimitiveReconstruction
open FullGeometryNormalization
open IndependentGeometryHomPrimitive

universe u v

/-- The core formed directly from the local object's finite primitive
package rows.  The completed geometry is not part of this definition. -/
noncomputable abbrev primitiveCore {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) : AATCorePackage U :=
  G124ProjectionBottom.coreObject data

/-- The five existing canonical admissibility laws, evaluated on the core
formed by the primitive package rows.  This predicate is an object condition
only; morphisms in its full subcategory remain all lawful local morphisms. -/
structure PrimitiveAdmissible {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) : Prop where
  equationResidual_eq : ∀ W object index atom,
    (primitiveCore data).algebra.equationSystem.equationResidual W object index atom =
      (primitiveCore data).algebra.equationSystem.equationResidual W
        (canonicalObjectNormalization (primitiveCore data) object) index atom
  operation_type_eq : ∀ first second,
    (primitiveCore data).reading.operationReading.Op first second =
      (primitiveCore data).reading.operationReading.Op
        (canonicalObjectNormalization (primitiveCore data) first)
        (canonicalObjectNormalization (primitiveCore data) second)
  operation_naturality : ∀ first second
      (operation : (primitiveCore data).reading.operationReading.Op first second),
    ConfigurationHom.comp
        ((primitiveCore data).reading.operationReading.configurationMap
          (cast (operation_type_eq first second) operation))
        (canonicalObjectNormalizationConfigurationHom (primitiveCore data) first) =
      ConfigurationHom.comp
        (canonicalObjectNormalizationConfigurationHom (primitiveCore data) second)
        ((primitiveCore data).reading.operationReading.configurationMap operation)
  invariant_transport : ∀ index,
    Invariant.TransportedAlong
      ((primitiveCore data).reading.invariantReading.invariant index)
      ((primitiveCore data).reading.invariantReading.invariant index)
      _root_.id (canonicalObjectNormalization (primitiveCore data))
  coordinate_eq : ∀ object axis,
    (primitiveCore data).reading.signatureReading.coordinate object axis =
      (primitiveCore data).reading.signatureReading.coordinate
        (canonicalObjectNormalization (primitiveCore data) object) axis

/-- No new axiom is hidden in the expanded predicate: its five primitive
conditions are precisely the accepted native admissibility conditions. -/
theorem admissible_iff_native {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) :
    PrimitiveAdmissible data ↔
      CanonicalObjectNormalizationAdmissible (primitiveCore data) := by
  constructor
  · intro h
    exact ⟨h.equationResidual_eq, h.operation_type_eq,
      h.operation_naturality, h.invariant_transport, h.coordinate_eq⟩
  · intro h
    exact ⟨h.equationResidual_eq, h.operation_type_eq,
      h.operation_naturality, h.invariant_transport, h.coordinate_eq⟩

/-- The two native geometry presentations use the same primitive object
condition, because their difference is in their Hom context action. -/
def representativeAdmissible {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U) : Prop :=
  PrimitiveAdmissible (objectData object.localObject)

def explicitAdmissible {U : AtomCarrier.{u}}
    (object : ExplicitLocalObject.{u, v} U) : Prop :=
  PrimitiveAdmissible (objectData object.localObject)

/-- Ordinary full subcategories: admissibility constrains objects and does
not add a condition to any allowed geometry morphism. -/
abbrev representativeAdmissibleProperty (U : AtomCarrier.{u}) :
    ObjectProperty (RepresentativeLocalObject.{u, v} U) :=
  fun object => representativeAdmissible object

abbrev explicitAdmissibleProperty (U : AtomCarrier.{u}) :
    ObjectProperty (ExplicitLocalObject.{u, v} U) :=
  fun object => explicitAdmissible object

abbrev RepresentativeAdmissibleLocal (U : AtomCarrier.{u}) :=
  (representativeAdmissibleProperty.{u, v} U).FullSubcategory

abbrev ExplicitAdmissibleLocal (U : AtomCarrier.{u}) :=
  (explicitAdmissibleProperty.{u, v} U).FullSubcategory

theorem representative_read_admissible_iff {U : AtomCarrier.{u}}
    (G : GeometryTransport.GeomReadCategory.{u, v} U) :
    representativeAdmissible (representativeReadObject G) ↔
      CanonicalObjectNormalizationAdmissible G.core := by
  rw [representativeAdmissible, admissible_iff_native]
  change CanonicalObjectNormalizationAdmissible
    (assemble (objectData (representativeReadObject G).localObject)).core ↔ _
  have recovered :
      assemble (objectData (representativeReadObject G).localObject) = G :=
    assemble_objectData_readFragments G
  simp only [recovered]

theorem explicit_read_admissible_iff {U : AtomCarrier.{u}}
    (G : RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U) :
    explicitAdmissible (explicitReadObject G) ↔
      CanonicalObjectNormalizationAdmissible G.toGeometryPackage.core := by
  rw [explicitAdmissible, admissible_iff_native]
  change CanonicalObjectNormalizationAdmissible
    (assemble (objectData (explicitReadObject G).localObject)).core ↔ _
  rw [show assemble (objectData (explicitReadObject G).localObject) =
      G.toGeometryPackage from by
        cases G with
        | mk package => exact assemble_objectData_readFragments package]

/-- The explicit native full subcategory has exactly the same five object
conditions; the underlying explicit Homs retain raw and actual-context data. -/
abbrev explicitNativeAdmissibleProperty (U : AtomCarrier.{u}) :
    ObjectProperty (RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U) :=
  fun G => CanonicalObjectNormalizationAdmissible G.toGeometryPackage.core

abbrev ExplicitAdmissibleNative (U : AtomCarrier.{u}) :=
  (explicitNativeAdmissibleProperty.{u, v} U).FullSubcategory

noncomputable def explicitAdmissibleReading (U : AtomCarrier.{u}) :
    ExplicitAdmissibleNative.{u, v} U ⥤ ExplicitAdmissibleLocal.{u, v} U where
  obj G := ⟨explicitReadObject G.obj,
    (explicit_read_admissible_iff G.obj).mpr G.property⟩
  map f := ObjectProperty.homMk ((explicitReadingFunctor U).map f.hom)
  map_id G := by
    apply ObjectProperty.hom_ext
    exact (explicitReadingFunctor U).map_id G.obj
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact (explicitReadingFunctor U).map_comp first.hom second.hom

noncomputable def explicitAdmissibleAssembly (U : AtomCarrier.{u}) :
    ExplicitAdmissibleLocal.{u, v} U ⥤ ExplicitAdmissibleNative.{u, v} U where
  obj object := ⟨⟨assemble (objectData object.obj.localObject)⟩,
    (admissible_iff_native _).mp object.property⟩
  map f := ObjectProperty.homMk ((explicitAssemblyFunctor U).map f.hom)
  map_id object := by
    apply ObjectProperty.hom_ext
    exact (explicitAssemblyFunctor U).map_id object.obj
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact (explicitAssemblyFunctor U).map_comp first.hom second.hom

/-- Restrict the accepted representative reader to precisely the native and
primitive full subcategories satisfying the same five admissibility laws. -/
noncomputable def representativeAdmissibleReading (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U ⥤
      RepresentativeAdmissibleLocal.{u, v} U where
  obj G := ⟨representativeReadObject G.obj,
    (representative_read_admissible_iff G.obj).mpr G.property⟩
  map f := ObjectProperty.homMk
    ((representativeReadingFunctor U).map f.hom)
  map_id G := by
    apply ObjectProperty.hom_ext
    exact (representativeReadingFunctor U).map_id G.obj
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact (representativeReadingFunctor U).map_comp first.hom second.hom

/-- Assemble the primitive admissible full subcategory back to the accepted
native full subcategory, retaining every local Hom. -/
noncomputable def representativeAdmissibleAssembly (U : AtomCarrier.{u}) :
    RepresentativeAdmissibleLocal.{u, v} U ⥤
      CanonicalNormalizationAdmissibleGeometry.{u, v} U where
  obj object := ⟨assemble (objectData object.obj.localObject),
    (admissible_iff_native _).mp object.property⟩
  map f := ObjectProperty.homMk
    ((representativeAssemblyFunctor U).map f.hom)
  map_id object := by
    apply ObjectProperty.hom_ext
    exact (representativeAssemblyFunctor U).map_id object.obj
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact (representativeAssemblyFunctor U).map_comp first.hom second.hom

/-- The primitive representative projector reads the independently
constructed canonical object-normalization map on the geometry assembled
from this primitive object.  Its source and target are the original local
object; no native Hom or comparison certificate is supplied as input. -/
noncomputable def representativeProjector {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) : object ⟶ object := by
  let data := objectData object.localObject
  let nativeAdmissible : CanonicalObjectNormalizationAdmissible (assemble data).core :=
    (admissible_iff_native data).mp admissible
  let native := canonicalGeometryNormalization (assemble data) nativeAdmissible
  exact ⟨NativeReader.localRepresentative native,
    NativeReader.localRepresentative_points data data native⟩

/-- Reading and then assembling the primitive projector gives precisely the
canonical normalization constructed from that same primitive object. -/
theorem representativeProjector_assemble {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) :
    FullRepresentative.assembleHom
        (objectData object.localObject) (objectData object.localObject)
        (representativeProjector object admissible).val
        (representativeProjector object admissible).property =
      canonicalGeometryNormalization
        (assemble (objectData object.localObject))
        ((admissible_iff_native _).mp admissible) := by
  exact NativeReader.localRepresentative_assemble _ _ _

/-- Every primitive query of the local projector is the value computed by
canonical normalization of the primitive object's own assembled geometry. -/
theorem representativeProjector_point {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U .representative) :
    InvariantWitness.point _ _ (representativeProjector object admissible).val query =
      NativeReader.readRepresentative
        (canonicalGeometryNormalization
          (assemble (objectData object.localObject))
          ((admissible_iff_native _).mp admissible)) query := rfl

/-- The lower source graph of the local projector is the point reading of
canonical object normalization on the primitive core. -/
theorem representativeProjector_source_point {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object)
    (query : IndependentCarrierGraph.Query.{u, u}) :
    InvariantWitness.point _ _ (representativeProjector object admissible).val
        (.source query) =
      IndependentCarrierGraph.read _ _
        (canonicalObjectNormalizationTotal
          (primitiveCore (objectData object.localObject))
          ((admissible_iff_native _).mp admissible)).base.doctrineHom.sourceMap
        query := by
  rw [representativeProjector_point]
  rfl

/-- Operation cells use the canonical normalized core map and the identity
coefficient map, at every candidate source and target pair. -/
theorem representativeProjector_operation_point {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object)
    (A B A' B' : ArchitectureObject U)
    (query : IndependentCarrierGraph.Query.{u, u}) :
    InvariantWitness.point _ _ (representativeProjector object admissible).val
        (.operation A B A' B' query) =
      NativeReader.operationRows .representative
        (canonicalObjectNormalizationTotal
          (primitiveCore (objectData object.localObject))
          ((admissible_iff_native _).mp admissible))
        (RingHom.id (assemble (objectData object.localObject)).Coefficient)
        (.edge (A, B) (A', B') query) := by
  rw [representativeProjector_point]
  rfl

/-- The directed coefficient cell is the graph of the identity ring map. -/
theorem representativeProjector_coefficient_point {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object)
    (query : IndependentCarrierGraph.Query.{v, v}) :
    InvariantWitness.point _ _ (representativeProjector object admissible).val
        (.coefficient query) =
      IndependentCarrierGraph.read _ _
        (RingHom.id (assemble (objectData object.localObject)).Coefficient) query := by
  rw [representativeProjector_point]
  rfl

/-- The projector's object graph is exactly canonical object normalization
of the primitive core, for every candidate source and target object. -/
theorem representativeProjector_object_point {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object)
    (A B : ArchitectureObject U) :
    InvariantWitness.point _ _ (representativeProjector object admissible).val
        (.object A B) = true ↔
      canonicalObjectNormalization
        (primitiveCore (objectData object.localObject)) A = B := by
  rw [representativeProjector_point]
  exact NativeReader.readWith_object_iff .representative
    (canonicalGeometryNormalization
      (assemble (objectData object.localObject))
      ((admissible_iff_native _).mp admissible)).base
    _ _ _ A B

/-- The accepted reader carries the native projector to the local projector. -/
private theorem canonical_read_eq {U : AtomCarrier.{u}}
    {G H : GeometryTransport.GeomReadCategory.{u, v} U}
    (equality : G = H)
    (gAdmissible : CanonicalObjectNormalizationAdmissible G.core)
    (hAdmissible : CanonicalObjectNormalizationAdmissible H.core)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U .representative) :
    NativeReader.readRepresentative
        (canonicalGeometryNormalization G gAdmissible) query =
      NativeReader.readRepresentative
        (canonicalGeometryNormalization H hAdmissible) query := by
  cases equality
  rfl

theorem representative_read_projector {U : AtomCarrier.{u}}
    (G : GeometryTransport.GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (representativeReadingFunctor U).map
        (canonicalGeometryNormalization G admissible) =
      representativeProjector (representativeReadObject G)
        ((representative_read_admissible_iff G).mpr admissible) := by
  apply Subtype.ext
  apply InvariantWitness.point_ext
  intro query
  change InvariantWitness.point _ _
      (representativeReadingHomEquiv G G
        (canonicalGeometryNormalization G admissible)).val query =
    InvariantWitness.point _ _
      (representativeProjector (representativeReadObject G)
        ((representative_read_admissible_iff G).mpr admissible)).val query
  rw [representativeReadingHomEquiv_point, representativeProjector_point]
  have recovered :
      assemble (objectData (representativeReadObject G).localObject) = G :=
    assemble_objectData_readFragments G
  exact (canonical_read_eq recovered
    ((admissible_iff_native _).mp
      ((representative_read_admissible_iff G).mpr admissible))
    admissible query).symm

/-- The projector equality in the four-branch main reader's exact category
presentation, rather than only in the underlying geometry branch. -/
theorem main_read_projector {U : AtomCarrier.{u}}
    (G : GeometryTransport.GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (reading (Parameter.geometry U .representative)).map
        (ULift.up (canonicalGeometryNormalization G admissible)) =
      ULift.up (representativeProjector (representativeReadObject G)
        ((representative_read_admissible_iff G).mpr admissible)) := by
  exact congrArg ULift.up (representative_read_projector G admissible)

/-- Native canonical normalization as an actual idempotent in the same
four-branch category used by the main reader. -/
noncomputable def nativeCanonicalKaroubi {U : AtomCarrier.{u}}
    (G : GeometryTransport.GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    Karoubi (NativeCategory (Parameter.geometry U .representative)) where
  X := (ULiftHom.up (C := GeometryTransport.GeomReadCategory.{u, v} U)).obj G
  p := ULift.up (canonicalGeometryNormalization G admissible)
  idem := congrArg ULift.up (canonicalGeometryNormalization_idem G admissible)

/-- `Kar(N)` sends the native normalization idempotent to the actual local
projector, so its Hom equivalence applies to normalized comparisons. -/
theorem main_canonicalKaroubi_projector {U : AtomCarrier.{u}}
    (G : GeometryTransport.GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    ((G124KaroubiProjection.karoubiReading
        (Parameter.geometry U .representative)).obj
        (nativeCanonicalKaroubi G admissible)).p =
      ULift.up (representativeProjector (representativeReadObject G)
        ((representative_read_admissible_iff G).mpr admissible)) := by
  exact main_read_projector G admissible

/-- Idempotence is equality of complete local Homs, including all retained
primitive graph components and the invariant quotient. -/
theorem representativeProjector_idem {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) :
    representativeProjector object admissible ≫
        representativeProjector object admissible =
      representativeProjector object admissible := by
  let d := objectData object.localObject
  let hn : CanonicalObjectNormalizationAdmissible (assemble d).core :=
    (admissible_iff_native d).mp admissible
  let n := canonicalGeometryNormalization (assemble d) hn
  apply Subtype.ext
  change Composition.representativeLocal d d d
      (NativeReader.localRepresentative n)
      (NativeReader.localRepresentative_points d d n)
      (NativeReader.localRepresentative n)
      (NativeReader.localRepresentative_points d d n) =
    NativeReader.localRepresentative n
  rw [Composition.representativeLocal_read_comp]
  exact congrArg NativeReader.localRepresentative
    (canonicalGeometryNormalization_idem (assemble d) hn)

/-- The direct primitive bottom projection sends the local projector to the
identity on the exact pointed extraction doctrine. -/
theorem representativeProjector_bottom {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) :
    (G124ProjectionBottom.localRepresentative U).map
        (representativeProjector object admissible) = 𝟙 _ := by
  change G124ProjectionBottom.representativeMap
      (representativeProjector object admissible) = 𝟙 _
  rw [G124ProjectionBottom.representativeMap_eq_native]
  change (G124ProjectionBottom.nativeRepresentative U).map
      (FullRepresentative.assembleHom _ _
        (representativeProjector object admissible).val
        (representativeProjector object admissible).property) = 𝟙 _
  rw [representativeProjector_assemble]
  rfl

/-- The intermediate core projection is the original total canonical map,
including its dependent operation and equation components. -/
theorem representativeProjector_core {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) :
    (G124ProjectionBottom.localRepresentativeCore U).map
        (representativeProjector object admissible) =
      canonicalObjectNormalizationTotal
        (primitiveCore (objectData object.localObject))
        ((admissible_iff_native _).mp admissible) := by
  change G124ProjectionBottom.representativeCoreMap
      (representativeProjector object admissible) = _
  rw [G124ProjectionBottom.representativeCoreMap_eq_native]
  change (GeometryTransport.geometryProjection U).map
      (FullRepresentative.assembleHom _ _
        (representativeProjector object admissible).val
        (representativeProjector object admissible).property) = _
  rw [representativeProjector_assemble]
  rfl

theorem representativeProjector_coefficient {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) :
    (G124ProjectionCoefficient.localRepresentative U).map
        (representativeProjector object admissible) = 𝟙 _ := by
  change G124ProjectionCoefficient.representativeMap
      (representativeProjector object admissible) = 𝟙 _
  rw [G124ProjectionCoefficient.representativeMap_eq_native]
  change (G124ProjectionCoefficient.nativeRepresentative U).map
      (FullRepresentative.assembleHom _ _
        (representativeProjector object admissible).val
        (representativeProjector object admissible).property) = 𝟙 _
  rw [representativeProjector_assemble]
  rfl

theorem representativeProjector_observation {U : AtomCarrier.{u}}
    (object : RepresentativeLocalObject.{u, v} U)
    (admissible : representativeAdmissible object) :
    (G124ProjectionObservationComponents.localRepresentative U).map
        (representativeProjector object admissible) = 𝟙 _ := by
  change G124ProjectionObservationComponents.localRepresentativeMap
      (representativeProjector object admissible) =
        G124ProjectionObservationComponents.RepresentativeHom.id _
  rw [G124ProjectionObservationComponents.localRepresentativeMap_eq_native]
  change (G124ProjectionObservationComponents.nativeRepresentative U).map
      (FullRepresentative.assembleHom _ _
        (representativeProjector object admissible).val
        (representativeProjector object admissible).property) =
      G124ProjectionObservationComponents.RepresentativeHom.id _
  rw [representativeProjector_assemble]
  rfl

/-- The complete assembly functor reflects equality of local primitive Homs
because the original local quotient is recovered after assembly. -/
theorem representativeAssembly_injective {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U} :
    Function.Injective
      ((representativeAssemblyFunctor U).map :
        (source ⟶ target) →
          ((representativeAssemblyFunctor U).obj source ⟶
            (representativeAssemblyFunctor U).obj target)) := by
  intro first second equality
  apply Subtype.ext
  have readEquality := congrArg NativeReader.localRepresentative equality
  change NativeReader.localRepresentative
      (FullRepresentative.assembleHom _ _ first.val first.property) =
    NativeReader.localRepresentative
      (FullRepresentative.assembleHom _ _ second.val second.property) at readEquality
  simpa only [NativeReader.localRepresentative_read_assemble] using readEquality

noncomputable def admissibleRepresentativeProjector {U : AtomCarrier.{u}}
    (object : RepresentativeAdmissibleLocal.{u, v} U) : object ⟶ object :=
  ObjectProperty.homMk (representativeProjector object.obj object.property)

theorem admissibleRepresentativeProjector_idem {U : AtomCarrier.{u}}
    (object : RepresentativeAdmissibleLocal.{u, v} U) :
    admissibleRepresentativeProjector object ≫
        admissibleRepresentativeProjector object =
      admissibleRepresentativeProjector object := by
  apply ObjectProperty.hom_ext
  exact representativeProjector_idem object.obj object.property

@[simp] theorem representativeAdmissibleAssembly_map_projector
    {U : AtomCarrier.{u}}
    (object : RepresentativeAdmissibleLocal.{u, v} U) :
    (representativeAdmissibleAssembly U).map
        (admissibleRepresentativeProjector object) =
      canonicalAdmissibleGeometryNormalization
        ((representativeAdmissibleAssembly U).obj object) := by
  apply ObjectProperty.hom_ext
  exact representativeProjector_assemble object.obj object.property

/-- One-sided absorption for every lawful local Hom between admissible
primitive objects.  The Hom carries no extra normalization certificate. -/
theorem representativeProjector_absorption {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (sourceAdmissible : representativeAdmissible source)
    (targetAdmissible : representativeAdmissible target)
    (f : source ⟶ target) :
    representativeProjector source sourceAdmissible ≫ f ≫
        representativeProjector target targetAdmissible =
      representativeProjector source sourceAdmissible ≫ f := by
  apply representativeAssembly_injective
  let sourceNative : CanonicalNormalizationAdmissibleGeometry.{u, v} U :=
    ⟨assemble (objectData source.localObject),
      (admissible_iff_native _).mp sourceAdmissible⟩
  let targetNative : CanonicalNormalizationAdmissibleGeometry.{u, v} U :=
    ⟨assemble (objectData target.localObject),
      (admissible_iff_native _).mp targetAdmissible⟩
  let native : sourceNative ⟶ targetNative :=
    ObjectProperty.homMk ((representativeAssemblyFunctor U).map f)
  have absorption := canonicalAdmissibleGeometryNormalization_absorption native
  have underlying := congrArg (fun morphism => morphism.hom) absorption
  change canonicalGeometryNormalization sourceNative.obj sourceNative.property ≫
      native.hom ≫
        canonicalGeometryNormalization targetNative.obj targetNative.property =
    canonicalGeometryNormalization sourceNative.obj sourceNative.property ≫ native.hom
      at underlying
  have sourceMap := representativeProjector_assemble source sourceAdmissible
  change (representativeAssemblyFunctor U).map
      (representativeProjector source sourceAdmissible) =
    canonicalGeometryNormalization sourceNative.obj sourceNative.property at sourceMap
  have targetMap := representativeProjector_assemble target targetAdmissible
  change (representativeAssemblyFunctor U).map
      (representativeProjector target targetAdmissible) =
    canonicalGeometryNormalization targetNative.obj targetNative.property at targetMap
  simp only [Functor.map_comp]
  rw [sourceMap, targetMap]
  exact underlying

theorem admissibleRepresentativeProjector_absorption {U : AtomCarrier.{u}}
    {source target : RepresentativeAdmissibleLocal.{u, v} U}
    (f : source ⟶ target) :
    admissibleRepresentativeProjector source ≫ f ≫
        admissibleRepresentativeProjector target =
      admissibleRepresentativeProjector source ≫ f := by
  apply ObjectProperty.hom_ext
  exact representativeProjector_absorption
    source.property target.property f.hom

/-- The normalized local object retains its admissible primitive object as a
label; its identity will be the actual local projector. -/
structure NormalizedRepresentativeObject (U : AtomCarrier.{u}) where
  obj : RepresentativeAdmissibleLocal.{u, v} U

noncomputable def normalizedRepresentativeKaroubiObject {U : AtomCarrier.{u}}
    (object : RepresentativeAdmissibleLocal.{u, v} U) :
    Karoubi (RepresentativeAdmissibleLocal.{u, v} U) where
  X := object
  p := admissibleRepresentativeProjector object
  idem := admissibleRepresentativeProjector_idem object

/-- Morphisms are precisely the ordinary sandwich Homs, with no two-sided
naturality premise on arbitrary raw local Homs. -/
noncomputable instance normalizedRepresentativeCategory {U : AtomCarrier.{u}} :
    Category (NormalizedRepresentativeObject.{u, v} U) where
  Hom source target :=
    normalizedRepresentativeKaroubiObject source.obj ⟶
      normalizedRepresentativeKaroubiObject target.obj
  id _ := 𝟙 _
  comp first second := first ≫ second
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

noncomputable def localNormalizationFunctor (U : AtomCarrier.{u}) :
    RepresentativeAdmissibleLocal.{u, v} U ⥤
      NormalizedRepresentativeObject.{u, v} U where
  obj object := ⟨object⟩
  map := fun {source target} f =>
    { f := admissibleRepresentativeProjector source ≫ f
      comm := by
        change admissibleRepresentativeProjector source ≫
            (admissibleRepresentativeProjector source ≫ f) ≫
              admissibleRepresentativeProjector target =
          admissibleRepresentativeProjector source ≫ f
        rw [← Category.assoc]
        rw [← Category.assoc
          (admissibleRepresentativeProjector source)
          (admissibleRepresentativeProjector source) f,
          admissibleRepresentativeProjector_idem]
        simpa only [Category.assoc] using
          admissibleRepresentativeProjector_absorption f }
  map_id object := by
    apply Karoubi.Hom.ext
    exact Category.comp_id _
  map_comp first second := by
    apply Karoubi.Hom.ext
    change admissibleRepresentativeProjector _ ≫ (first ≫ second) =
      (admissibleRepresentativeProjector _ ≫ first) ≫
        (admissibleRepresentativeProjector _ ≫ second)
    simpa only [Category.assoc] using congrArg
      (fun h => h ≫ second)
      (admissibleRepresentativeProjector_absorption first).symm

/-- Assemble normalized local sandwich Homs into the accepted normalized
geometry category.  The native sandwich law is the image of the proved local
law; it is not a supplied compatibility certificate. -/
noncomputable def normalizedRepresentativeAssembly (U : AtomCarrier.{u}) :
    NormalizedRepresentativeObject.{u, v} U ⥤
      NormalizedGeometryObject.{u, v} U where
  obj object := ⟨(representativeAdmissibleAssembly U).obj object.obj⟩
  map := fun {source target} f =>
    { f := (representativeAdmissibleAssembly U).map f.f
      comm := by
        have h := congrArg
          (fun morphism => (representativeAdmissibleAssembly U).map morphism)
          f.comm
        simpa only [normalizedRepresentativeKaroubiObject,
          normalizedGeometryKaroubiObject, Functor.map_comp,
          representativeAdmissibleAssembly_map_projector] using h }
  map_id object := by
    apply Karoubi.Hom.ext
    exact representativeAdmissibleAssembly_map_projector object.obj
  map_comp first second := by
    apply Karoubi.Hom.ext
    exact (representativeAdmissibleAssembly U).map_comp first.f second.f

/-- The two normalization routes retain the same complete geometry label. -/
theorem normalization_assembly_object (U : AtomCarrier.{u})
    (object : RepresentativeAdmissibleLocal.{u, v} U) :
    (normalizedRepresentativeAssembly U).obj
        ((localNormalizationFunctor U).obj object) =
      (geometryNormalizationFunctor U).obj
        ((representativeAdmissibleAssembly U).obj object) := rfl

/-- The local sandwich `f e_X` is sent to the accepted native sandwich by
ordinary functoriality and the primitive projector evaluation. -/
theorem normalization_assembly_map (U : AtomCarrier.{u})
    {source target : RepresentativeAdmissibleLocal.{u, v} U}
    (f : source ⟶ target) :
    ((normalizedRepresentativeAssembly U).map
        ((localNormalizationFunctor U).map f)).f =
      ((geometryNormalizationFunctor U).map
        ((representativeAdmissibleAssembly U).map f)).f := by
  change (representativeAdmissibleAssembly U).map
      (admissibleRepresentativeProjector source ≫ f) =
    canonicalAdmissibleGeometryNormalization
        ((representativeAdmissibleAssembly U).obj source) ≫
      (representativeAdmissibleAssembly U).map f
  rw [Functor.map_comp, representativeAdmissibleAssembly_map_projector]

@[simp] theorem localNormalizationFunctor_map_f {U : AtomCarrier.{u}}
    {source target : RepresentativeAdmissibleLocal.{u, v} U}
    (f : source ⟶ target) :
    ((localNormalizationFunctor U).map f).f =
      admissibleRepresentativeProjector source ≫ f := rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124PrimitiveNormalization

end AAT.AG.LocalSemanticReconstruction.G124PrimitiveNormalization
