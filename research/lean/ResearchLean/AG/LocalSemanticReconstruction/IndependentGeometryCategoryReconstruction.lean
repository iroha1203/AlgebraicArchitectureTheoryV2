import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryFiniteFragments
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalCategoryLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalCompositionLaws
import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import ResearchLean.AG.RealizationReconstruction.CSAATExplicitExactGeometryCategory
import Mathlib.CategoryTheory.HomCongr
import Formal.Util.AssertStandardAxioms

/-!
# Geometry reconstruction from the independent finite reading

The finite primitive objects and lawful local Hom quotients constructed in
Part I form categories in both geometry modes.  Reading first replaces each
native endpoint by its recovered primitive object and then applies the existing
complete Hom-reading equivalence.  The resulting functors have explicit Hom
separation, Hom assembly, and object assembly, so the general reconstruction
theorem supplies the two category equivalences.

## Implementation notes

Each category wrapper stores only the existing `LocalObject`.  Its Hom type is
the existing invariant quotient together with the existing point laws; it does
not retain a completed native Hom.  Identity and composition use the direct
Part I constructors.  Native Homs occur only in reading and assembly maps.

The endpoint equalities are exposed as `eqToIso` values and combined with
`Iso.homCongr`.  A new dependent transport layer was rejected because these
equalities already give the exact typed conversion needed by both modes.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction
open LocalReconstructionEquivalence IndependentGeometryTableAssembly
open IndependentGeometryHomPrimitive

noncomputable section

namespace IndependentGeometryCategoryReconstruction

universe u v

variable {U : AtomCarrier.{u}}

/-- The Part I finite primitive object, retained as the sole object datum of
both local geometry categories. -/
abbrev PrimitiveLocalObject (U : AtomCarrier.{u}) :=
  IndependentGeometryPrimitive.LocalObject.{u, v} U

/-- Recover the verified dependent stages used to index all Part I local Hom
queries and laws. -/
def objectData (object : PrimitiveLocalObject.{u, v} U) : ObjectData.{u, v} U :=
  IndependentGeometryPrimitive.stages
    (IndependentGeometryPrimitive.glue object.val) object.property.2

/-- Stage assembly is definitionally the Part I finite-fragment assembly. -/
theorem assemble_objectData (object : PrimitiveLocalObject.{u, v} U) :
    assemble (objectData object) =
      IndependentGeometryPrimitive.assembleFragments object := rfl

/-- A local object read from a native geometry assembles back to that geometry. -/
theorem assemble_objectData_readFragments (G : GeometryPackage.{u, v} U) :
    assemble (objectData (IndependentGeometryPrimitive.readFragments G)) = G := by
  rw [assemble_objectData,
    IndependentGeometryPrimitive.assembleFragments_readFragments]

/-- The representative local category stores one Part I primitive object. -/
structure RepresentativeLocalObject (U : AtomCarrier.{u}) where
  /-- The independent finite primitive object. -/
  localObject : PrimitiveLocalObject.{u, v} U

/-- The explicit local category stores the same Part I primitive object. -/
structure ExplicitLocalObject (U : AtomCarrier.{u}) where
  /-- The independent finite primitive object. -/
  localObject : PrimitiveLocalObject.{u, v} U

namespace RepresentativeLocalObject

/-- Representative local objects are equal when their primitive objects are
equal. -/
@[ext]
theorem ext {first second : RepresentativeLocalObject.{u, v} U}
    (h : first.localObject = second.localObject) : first = second := by
  cases first
  cases second
  cases h
  rfl

end RepresentativeLocalObject

namespace ExplicitLocalObject

/-- Explicit local objects are equal when their primitive objects are equal. -/
@[ext]
theorem ext {first second : ExplicitLocalObject.{u, v} U}
    (h : first.localObject = second.localObject) : first = second := by
  cases first
  cases second
  cases h
  rfl

end ExplicitLocalObject

/-- Lawful representative local Homs use the Part I invariant quotient and
all representative point laws. -/
abbrev RepresentativeHom
    (source target : RepresentativeLocalObject.{u, v} U) :=
  {p : InvariantWitness.Local.{u, v}
      (assemble (objectData source.localObject)).core.reading.invariantReading
      (assemble (objectData target.localObject)).core.reading.invariantReading
      .representative //
    FullRepresentative.PointLaws
      (objectData source.localObject) (objectData target.localObject) p}

/-- Lawful explicit local Homs use the same quotient and all explicit point
laws, including the actual context action. -/
abbrev ExplicitHom
    (source target : ExplicitLocalObject.{u, v} U) :=
  {p : InvariantWitness.Local.{u, v}
      (assemble (objectData source.localObject)).core.reading.invariantReading
      (assemble (objectData target.localObject)).core.reading.invariantReading
      .explicit //
    FullExplicit.PointLaws
      (objectData source.localObject) (objectData target.localObject) p}

/-- Direct representative identity on one primitive local object. -/
def representativeIdentity (object : RepresentativeLocalObject.{u, v} U) :
    RepresentativeHom object object :=
  ⟨IdentityLocal.representativeIdentity (objectData object.localObject),
    IdentityLocal.representativeIdentity_points (objectData object.localObject)⟩

/-- Direct representative composition on primitive local Hom classes. -/
def representativeComp
    {source middle target : RepresentativeLocalObject.{u, v} U}
    (first : RepresentativeHom source middle)
    (second : RepresentativeHom middle target) :
    RepresentativeHom source target :=
  ⟨Composition.representativeLocal
      (objectData source.localObject) (objectData middle.localObject)
      (objectData target.localObject)
      first.val first.property second.val second.property,
    Composition.representativeLocal_points
      (objectData source.localObject) (objectData middle.localObject)
      (objectData target.localObject)
      first.val first.property second.val second.property⟩

/-- Direct explicit identity on one primitive local object. -/
def explicitIdentity (object : ExplicitLocalObject.{u, v} U) :
    ExplicitHom object object :=
  ⟨IdentityLocal.explicitIdentity (objectData object.localObject),
    IdentityLocal.explicitIdentity_points (objectData object.localObject)⟩

/-- Direct explicit composition on primitive local Hom classes. -/
def explicitComp {source middle target : ExplicitLocalObject.{u, v} U}
    (first : ExplicitHom source middle) (second : ExplicitHom middle target) :
    ExplicitHom source target :=
  ⟨Composition.explicitLocal
      (objectData source.localObject) (objectData middle.localObject)
      (objectData target.localObject)
      first.val first.property second.val second.property,
    Composition.explicitLocal_points
      (objectData source.localObject) (objectData middle.localObject)
      (objectData target.localObject)
      first.val first.property second.val second.property⟩

/-- Direct Part I representative identities and composites make primitive
local objects a category. -/
noncomputable instance representativeLocalCategory :
    Category (RepresentativeLocalObject.{u, v} U) where
  Hom := RepresentativeHom
  id := representativeIdentity
  comp := representativeComp
  id_comp morphism := by
    apply Subtype.ext
    exact CategoryLaws.representative_id_comp
      (objectData _) (objectData _) morphism.val morphism.property
  comp_id morphism := by
    apply Subtype.ext
    exact CategoryLaws.representative_comp_id
      (objectData _) (objectData _) morphism.val morphism.property
  assoc first second third := by
    apply Subtype.ext
    exact Composition.representativeLocal_assoc
      (objectData _) (objectData _) (objectData _) (objectData _)
      first.val first.property second.val second.property third.val third.property

/-- Direct Part I explicit identities and composites make the same primitive
objects an explicit local category. -/
noncomputable instance explicitLocalCategory :
    Category (ExplicitLocalObject.{u, v} U) where
  Hom := ExplicitHom
  id := explicitIdentity
  comp := explicitComp
  id_comp morphism := by
    apply Subtype.ext
    exact CategoryLaws.explicit_id_comp
      (objectData _) (objectData _) morphism.val morphism.property
  comp_id morphism := by
    apply Subtype.ext
    exact CategoryLaws.explicit_comp_id
      (objectData _) (objectData _) morphism.val morphism.property
  assoc first second third := by
    apply Subtype.ext
    exact Composition.explicitLocal_assoc
      (objectData _) (objectData _) (objectData _) (objectData _)
      first.val first.property second.val second.property third.val third.property

/-- Read one representative native object into the finite primitive category. -/
def representativeReadObject (G : GeomReadCategory.{u, v} U) :
    RepresentativeLocalObject.{u, v} U :=
  ⟨IndependentGeometryPrimitive.readFragments G⟩

/-- Read one explicit native object into the same finite primitive object
presentation. -/
def explicitReadObject (G : ExplicitExactGeomCategory.{u, v} U) :
    ExplicitLocalObject.{u, v} U :=
  ⟨IndependentGeometryPrimitive.readFragments G.toGeometryPackage⟩

/-- API lemma for the fixed GOAL B geometry branch: the Part I finite
fragment reader separates representative native objects after they are wrapped
as objects of the new local category. -/
theorem representativeReadObject_injective :
    Function.Injective (representativeReadObject.{u, v} (U := U)) := by
  intro G H equality
  apply IndependentGeometryPrimitive.readFragments_injective
  exact congrArg (fun object => object.localObject) equality

/-- API lemma for the fixed GOAL B geometry branch: the same Part I finite
fragment reader separates explicit native objects after they are wrapped as
objects of the new local category. -/
theorem explicitReadObject_injective :
    Function.Injective (explicitReadObject.{u, v} (U := U)) := by
  intro G H equality
  cases G with
  | mk G =>
      cases H with
      | mk H =>
          have fragmentEquality :
              IndependentGeometryPrimitive.readFragments G =
                IndependentGeometryPrimitive.readFragments H :=
            congrArg (fun object => object.localObject) equality
          have packageEquality : G = H :=
            IndependentGeometryPrimitive.readFragments_injective fragmentEquality
          cases packageEquality
          rfl

/-- The assembled representative reading is canonically isomorphic to its
native source object. -/
def representativeObjectIso (G : GeomReadCategory.{u, v} U) :
    assemble (objectData (representativeReadObject G).localObject) ≅ G :=
  eqToIso (assemble_objectData_readFragments G)

/-- Part I object recovery lifted through the explicit native-category wrapper;
this is the object equality used by the Issue #4711 §3 endpoint conversion. -/
theorem explicit_assemble_objectData_readFragments
    (G : ExplicitExactGeomCategory.{u, v} U) :
    ExplicitExactGeomCategory.ofGeometryPackage
        (assemble (objectData (explicitReadObject G).localObject)) = G := by
  cases G with
  | mk package =>
      exact congrArg ExplicitExactGeomCategory.ofGeometryPackage
        (assemble_objectData_readFragments package)

/-- The assembled explicit reading is canonically isomorphic to its native
source object. -/
def explicitObjectIso (G : ExplicitExactGeomCategory.{u, v} U) :
    ExplicitExactGeomCategory.ofGeometryPackage
        (assemble (objectData (explicitReadObject G).localObject)) ≅ G :=
  eqToIso (explicit_assemble_objectData_readFragments G)

/-- Convert representative native Hom endpoints to the independently
assembled primitive endpoints. -/
def representativeEndpointHomEquiv (G H : GeomReadCategory.{u, v} U) :
    (G ⟶ H) ≃
      (assemble (objectData (representativeReadObject G).localObject) ⟶
        assemble (objectData (representativeReadObject H).localObject)) :=
  (representativeObjectIso G).symm.homCongr (representativeObjectIso H).symm

/-- Convert explicit native Hom endpoints to the independently assembled
primitive endpoints. -/
def explicitEndpointHomEquiv (G H : ExplicitExactGeomCategory.{u, v} U) :
    (G ⟶ H) ≃
      (ExplicitExactGeomCategory.ofGeometryPackage
          (assemble (objectData (explicitReadObject G).localObject)) ⟶
        ExplicitExactGeomCategory.ofGeometryPackage
          (assemble (objectData (explicitReadObject H).localObject))) :=
  (explicitObjectIso G).symm.homCongr (explicitObjectIso H).symm

/-- Transporting the endpoints of a representative Hom along equality
isomorphisms leaves its Part I primitive table unchanged.  This helper exposes
the proof principle used by the Issue #4711 §3 API theorem below. -/
private theorem readRepresentative_eqToIso_homCongr
    {G H G' H' : GeomReadCategory.{u, v} U}
    (source : G' = G) (target : H' = H) (morphism : G ⟶ H) :
    NativeReader.readRepresentative
        (((eqToIso source).symm.homCongr (eqToIso target).symm) morphism) =
      NativeReader.readRepresentative morphism := by
  subst G
  subst H
  simp

/-- Transporting the endpoints of an explicit Hom along equality isomorphisms
leaves its Part I primitive table unchanged.  This is the explicit counterpart
of the helper used by the Issue #4711 §3 API theorem below. -/
private theorem readExplicit_eqToIso_homCongr
    {G H G' H' : ExplicitExactGeomCategory.{u, v} U}
    (source : G' = G) (target : H' = H) (morphism : G ⟶ H) :
    NativeReader.readExplicit
        (((eqToIso source).symm.homCongr (eqToIso target).symm) morphism) =
      NativeReader.readExplicit morphism := by
  subst G
  subst H
  simp

/-- Issue #4711 §3 representative endpoint conversion preserves the complete
Part I primitive table.  Its only equalities are supplied by the Part I object
round trip. -/
theorem representativeEndpointHomEquiv_read
    (G H : GeomReadCategory.{u, v} U) (morphism : G ⟶ H) :
    NativeReader.readRepresentative
        (representativeEndpointHomEquiv G H morphism) =
      NativeReader.readRepresentative morphism := by
  simpa [representativeEndpointHomEquiv, representativeObjectIso] using
    readRepresentative_eqToIso_homCongr
      (assemble_objectData_readFragments G)
      (assemble_objectData_readFragments H) morphism

/-- Issue #4711 §3 explicit endpoint conversion preserves the complete Part I
primitive table.  Its only equalities are supplied by the lifted Part I object
round trip. -/
theorem explicitEndpointHomEquiv_read
    (G H : ExplicitExactGeomCategory.{u, v} U) (morphism : G ⟶ H) :
    NativeReader.readExplicit (explicitEndpointHomEquiv G H morphism) =
      NativeReader.readExplicit morphism := by
  simpa [explicitEndpointHomEquiv, explicitObjectIso] using
    readExplicit_eqToIso_homCongr
      (explicit_assemble_objectData_readFragments G)
      (explicit_assemble_objectData_readFragments H) morphism

/-- Endpoint conversion followed by the Part I representative Hom reading is
an equivalence for every native object pair. -/
def representativeReadingHomEquiv (G H : GeomReadCategory.{u, v} U) :
    (G ⟶ H) ≃
      RepresentativeHom (representativeReadObject G) (representativeReadObject H) :=
  (representativeEndpointHomEquiv G H).trans
    (NativeReader.representativeHomReadingEquiv
      (objectData (representativeReadObject G).localObject)
      (objectData (representativeReadObject H).localObject))

/-- Endpoint conversion followed by the Part I explicit Hom reading is an
equivalence for every native object pair. -/
def explicitReadingHomEquiv
    (G H : ExplicitExactGeomCategory.{u, v} U) :
    (G ⟶ H) ≃ ExplicitHom (explicitReadObject G) (explicitReadObject H) :=
  (explicitEndpointHomEquiv G H).trans
    (NativeReader.explicitHomReadingEquiv
      (objectData (explicitReadObject G).localObject)
      (objectData (explicitReadObject H).localObject))

/-- Issue #4711 §3 point API: every representative local query agrees with
the original native Hom before endpoint conversion. -/
theorem representativeReadingHomEquiv_point
    {G H : GeomReadCategory.{u, v} U} (morphism : G ⟶ H)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U .representative) :
    InvariantWitness.point _ _ (representativeReadingHomEquiv G H morphism).val query =
      NativeReader.readRepresentative morphism query := by
  calc
    InvariantWitness.point _ _
        (representativeReadingHomEquiv G H morphism).val query =
      NativeReader.readRepresentative
        (representativeEndpointHomEquiv G H morphism) query :=
      NativeReader.point_localRepresentative _ query
    _ = NativeReader.readRepresentative morphism query :=
      congrFun (representativeEndpointHomEquiv_read G H morphism) query

/-- Issue #4711 §3 point API: every explicit local query agrees with the
original native Hom before endpoint conversion. -/
theorem explicitReadingHomEquiv_point
    {G H : ExplicitExactGeomCategory.{u, v} U} (morphism : G ⟶ H)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U .explicit) :
    InvariantWitness.point _ _ (explicitReadingHomEquiv G H morphism).val query =
      NativeReader.readExplicit morphism query := by
  calc
    InvariantWitness.point _ _
        (explicitReadingHomEquiv G H morphism).val query =
      NativeReader.readExplicit (explicitEndpointHomEquiv G H morphism) query :=
      NativeReader.point_localExplicit _ query
    _ = NativeReader.readExplicit morphism query :=
      congrFun (explicitEndpointHomEquiv_read G H morphism) query

/-- Reading a representative identity gives the direct primitive local
identity. -/
theorem representativeReadingHomEquiv_id (G : GeomReadCategory.{u, v} U) :
    representativeReadingHomEquiv G G (𝟙 G) =
      representativeIdentity (representativeReadObject G) := by
  apply Subtype.ext
  change NativeReader.localRepresentative
      (((representativeObjectIso G).symm.homCongr
        (representativeObjectIso G).symm) (𝟙 G)) =
    IdentityLocal.representativeIdentity
      (objectData (representativeReadObject G).localObject)
  rw [show ((representativeObjectIso G).symm.homCongr
      (representativeObjectIso G).symm) (𝟙 G) =
      𝟙 (assemble (objectData (representativeReadObject G).localObject)) by simp]
  exact (IdentityLocal.representativeLocalIdentity_eq_native _).symm

/-- Representative reading sends native composition to the direct primitive
local composite. -/
theorem representativeReadingHomEquiv_comp
    {G H K : GeomReadCategory.{u, v} U} (first : G ⟶ H) (second : H ⟶ K) :
    representativeReadingHomEquiv G K (first ≫ second) =
      representativeComp (representativeReadingHomEquiv G H first)
        (representativeReadingHomEquiv H K second) := by
  apply Subtype.ext
  change NativeReader.localRepresentative
      (((representativeObjectIso G).symm.homCongr
        (representativeObjectIso K).symm) (first ≫ second)) = _
  rw [Iso.homCongr_comp]
  exact (Composition.representativeLocal_read_comp
    (objectData (representativeReadObject G).localObject)
    (objectData (representativeReadObject H).localObject)
    (objectData (representativeReadObject K).localObject) _ _).symm

/-- Reading an explicit identity gives the direct primitive local identity. -/
theorem explicitReadingHomEquiv_id (G : ExplicitExactGeomCategory.{u, v} U) :
    explicitReadingHomEquiv G G (𝟙 G) =
      explicitIdentity (explicitReadObject G) := by
  apply Subtype.ext
  change NativeReader.localExplicit
      (((explicitObjectIso G).symm.homCongr
        (explicitObjectIso G).symm) (𝟙 G)) =
    IdentityLocal.explicitIdentity (objectData (explicitReadObject G).localObject)
  rw [show ((explicitObjectIso G).symm.homCongr
      (explicitObjectIso G).symm) (𝟙 G) =
      𝟙 (ExplicitExactGeomCategory.ofGeometryPackage
        (assemble (objectData (explicitReadObject G).localObject))) by simp]
  exact (IdentityLocal.explicitLocalIdentity_eq_native _).symm

/-- Explicit reading sends native composition to the direct primitive local
composite. -/
theorem explicitReadingHomEquiv_comp
    {G H K : ExplicitExactGeomCategory.{u, v} U}
    (first : G ⟶ H) (second : H ⟶ K) :
    explicitReadingHomEquiv G K (first ≫ second) =
      explicitComp (explicitReadingHomEquiv G H first)
        (explicitReadingHomEquiv H K second) := by
  apply Subtype.ext
  change NativeReader.localExplicit
      (((explicitObjectIso G).symm.homCongr
        (explicitObjectIso K).symm) (first ≫ second)) = _
  rw [Iso.homCongr_comp]
  exact (Composition.explicitLocal_read_comp
    (objectData (explicitReadObject G).localObject)
    (objectData (explicitReadObject H).localObject)
    (objectData (explicitReadObject K).localObject) _ _).symm

/-- Read every representative object and Hom into the independent primitive
local category. -/
def representativeReadingFunctor (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ RepresentativeLocalObject.{u, v} U where
  obj := representativeReadObject
  map {G H} morphism := representativeReadingHomEquiv G H morphism
  map_id G := by
    change representativeReadingHomEquiv G G (𝟙 G) =
      representativeIdentity (representativeReadObject G)
    exact representativeReadingHomEquiv_id G
  map_comp first second := by
    change representativeReadingHomEquiv _ _ (first ≫ second) =
      representativeComp (representativeReadingHomEquiv _ _ first)
        (representativeReadingHomEquiv _ _ second)
    exact representativeReadingHomEquiv_comp first second

/-- Read every explicit object and Hom into the independent primitive local
category. -/
def explicitReadingFunctor (U : AtomCarrier.{u}) :
    ExplicitExactGeomCategory.{u, v} U ⥤ ExplicitLocalObject.{u, v} U where
  obj := explicitReadObject
  map {G H} morphism := explicitReadingHomEquiv G H morphism
  map_id G := by
    change explicitReadingHomEquiv G G (𝟙 G) = explicitIdentity (explicitReadObject G)
    exact explicitReadingHomEquiv_id G
  map_comp first second := by
    change explicitReadingHomEquiv _ _ (first ≫ second) =
      explicitComp (explicitReadingHomEquiv _ _ first)
        (explicitReadingHomEquiv _ _ second)
    exact explicitReadingHomEquiv_comp first second

/-- Assemble representative local objects and Homs with the Part I primitive
assemblers. -/
def representativeAssemblyFunctor (U : AtomCarrier.{u}) :
    RepresentativeLocalObject.{u, v} U ⥤ GeomReadCategory.{u, v} U where
  obj object := assemble (objectData object.localObject)
  map morphism := FullRepresentative.assembleHom
    (objectData _) (objectData _) morphism.val morphism.property
  map_id object := IdentityLocal.representativeIdentity_assemble
    (objectData object.localObject)
  map_comp first second := Composition.representativeLocal_assemble
    (objectData _) (objectData _) (objectData _)
    first.val first.property second.val second.property

/-- Assemble explicit local objects and Homs with the same primitive object
assembler and the Part I explicit Hom assembler. -/
def explicitAssemblyFunctor (U : AtomCarrier.{u}) :
    ExplicitLocalObject.{u, v} U ⥤ ExplicitExactGeomCategory.{u, v} U where
  obj object := ExplicitExactGeomCategory.ofGeometryPackage
    (assemble (objectData object.localObject))
  map morphism := FullExplicit.assembleHom
    (objectData _) (objectData _) morphism.val morphism.property
  map_id object := IdentityLocal.explicitIdentity_assemble
    (objectData object.localObject)
  map_comp first second := Composition.explicitLocal_assemble
    (objectData _) (objectData _) (objectData _)
    first.val first.property second.val second.property

/-- Representative reading is separating on every complete native Hom type. -/
theorem representativeHomSeparation (U : AtomCarrier.{u}) :
    HomSeparation (representativeReadingFunctor.{u, v} U) where
  hom G H := ⟨by
    intro first second equality
    apply (representativeReadingHomEquiv G H).injective
    change representativeReadingHomEquiv G H first =
      representativeReadingHomEquiv G H second at equality
    exact equality⟩

/-- Every lawful representative local Hom assembles, and reading recovers it. -/
def representativeHomAssembly (U : AtomCarrier.{u}) :
    HomAssembly (representativeReadingFunctor.{u, v} U) where
  assemble {G H} morphism := by
    change RepresentativeHom (representativeReadObject G) (representativeReadObject H) at morphism
    exact (representativeReadingHomEquiv G H).symm morphism
  map_assemble {G H} morphism := by
    change RepresentativeHom (representativeReadObject G) (representativeReadObject H) at morphism
    change representativeReadingHomEquiv G H
      ((representativeReadingHomEquiv G H).symm morphism) = morphism
    exact (representativeReadingHomEquiv G H).apply_symm_apply morphism

/-- Every representative primitive local object is the reading of its direct
finite-fragment assembly. -/
def representativeObjectAssembly (U : AtomCarrier.{u}) :
    ObjectAssembly (representativeReadingFunctor.{u, v} U) where
  assembleObject object :=
    IndependentGeometryPrimitive.assembleFragments object.localObject
  readAssembledIso object := eqToIso (by
    apply RepresentativeLocalObject.ext
    change IndependentGeometryPrimitive.readFragments
      (IndependentGeometryPrimitive.assembleFragments object.localObject) =
        object.localObject
    exact IndependentGeometryPrimitive.readFragments_assembleFragments
      object.localObject)

/-- Explicit reading is separating on every complete native Hom type. -/
theorem explicitHomSeparation (U : AtomCarrier.{u}) :
    HomSeparation (explicitReadingFunctor.{u, v} U) where
  hom G H := ⟨by
    intro first second equality
    apply (explicitReadingHomEquiv G H).injective
    change explicitReadingHomEquiv G H first =
      explicitReadingHomEquiv G H second at equality
    exact equality⟩

/-- Every lawful explicit local Hom assembles, and reading recovers it. -/
def explicitHomAssembly (U : AtomCarrier.{u}) :
    HomAssembly (explicitReadingFunctor.{u, v} U) where
  assemble {G H} morphism := by
    change ExplicitHom (explicitReadObject G) (explicitReadObject H) at morphism
    exact (explicitReadingHomEquiv G H).symm morphism
  map_assemble {G H} morphism := by
    change ExplicitHom (explicitReadObject G) (explicitReadObject H) at morphism
    change explicitReadingHomEquiv G H
      ((explicitReadingHomEquiv G H).symm morphism) = morphism
    exact (explicitReadingHomEquiv G H).apply_symm_apply morphism

/-- Every explicit primitive local object is the reading of its direct
finite-fragment assembly. -/
def explicitObjectAssembly (U : AtomCarrier.{u}) :
    ObjectAssembly (explicitReadingFunctor.{u, v} U) where
  assembleObject object := ExplicitExactGeomCategory.ofGeometryPackage
    (IndependentGeometryPrimitive.assembleFragments object.localObject)
  readAssembledIso object := eqToIso (by
    apply ExplicitLocalObject.ext
    change IndependentGeometryPrimitive.readFragments
      (IndependentGeometryPrimitive.assembleFragments object.localObject) =
        object.localObject
    exact IndependentGeometryPrimitive.readFragments_assembleFragments
      object.localObject)

/-- Fixed GOAL B representative reconstruction data.  Part I supplies Hom
separation, Hom assembly, and finite-object assembly; this value packages
those three inputs for the Cycle 65 reconstruction theorem. -/
def representativeReconstructionData (U : AtomCarrier.{u}) :
    ReconstructionData (representativeReadingFunctor.{u, v} U) where
  separation := representativeHomSeparation U
  homAssembly := representativeHomAssembly U
  objectAssembly := representativeObjectAssembly U

/-- Fixed GOAL B explicit reconstruction data.  Part I supplies Hom
separation, Hom assembly, and finite-object assembly; this value packages
those three inputs for the Cycle 65 reconstruction theorem. -/
def explicitReconstructionData (U : AtomCarrier.{u}) :
    ReconstructionData (explicitReadingFunctor.{u, v} U) where
  separation := explicitHomSeparation U
  homAssembly := explicitHomAssembly U
  objectAssembly := explicitObjectAssembly U

/-- Every representative Hom is recovered after local reading and assembly.
As a simp rule, it removes this round trip in favor of the original Hom. -/
@[simp]
theorem representative_assemble_read {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U} (morphism : G ⟶ H) :
    (representativeReadingHomEquiv G H).symm
      (representativeReadingHomEquiv G H morphism) = morphism :=
  (representativeReadingHomEquiv G H).symm_apply_apply morphism

/-- Every representative local Hom is recovered after assembly and reading.
As a simp rule, it removes this round trip in favor of the original local Hom. -/
@[simp]
theorem representative_read_assemble {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U}
    (morphism : (representativeReadingFunctor.{u, v} U).obj G ⟶
      (representativeReadingFunctor.{u, v} U).obj H) :
    representativeReadingHomEquiv G H
      ((representativeReadingHomEquiv G H).symm morphism) = morphism :=
  (representativeReadingHomEquiv G H).apply_symm_apply morphism

/-- Every explicit Hom is recovered after local reading and assembly.  As a
simp rule, it removes this round trip in favor of the original Hom. -/
@[simp]
theorem explicit_assemble_read {U : AtomCarrier.{u}}
    {G H : ExplicitExactGeomCategory.{u, v} U} (morphism : G ⟶ H) :
    (explicitReadingHomEquiv G H).symm
      (explicitReadingHomEquiv G H morphism) = morphism :=
  (explicitReadingHomEquiv G H).symm_apply_apply morphism

/-- Every explicit local Hom is recovered after assembly and reading.  As a
simp rule, it removes this round trip in favor of the original local Hom. -/
@[simp]
theorem explicit_read_assemble {U : AtomCarrier.{u}}
    {G H : ExplicitExactGeomCategory.{u, v} U}
    (morphism : (explicitReadingFunctor.{u, v} U).obj G ⟶
      (explicitReadingFunctor.{u, v} U).obj H) :
    explicitReadingHomEquiv G H
      ((explicitReadingHomEquiv G H).symm morphism) = morphism :=
  (explicitReadingHomEquiv G H).apply_symm_apply morphism

/-- Representative local Homs have one and only one native preimage. -/
theorem representative_existsUnique_preimage {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U}
    (morphism : (representativeReadingFunctor.{u, v} U).obj G ⟶
      (representativeReadingFunctor.{u, v} U).obj H) :
    ∃! global : G ⟶ H,
      (representativeReadingFunctor.{u, v} U).map global = morphism :=
  (representativeReconstructionData U).existsUnique_preimage morphism

/-- Explicit local Homs have one and only one native preimage. -/
theorem explicit_existsUnique_preimage {U : AtomCarrier.{u}}
    {G H : ExplicitExactGeomCategory.{u, v} U}
    (morphism : (explicitReadingFunctor.{u, v} U).obj G ⟶
      (explicitReadingFunctor.{u, v} U).obj H) :
    ∃! global : G ⟶ H,
      (explicitReadingFunctor.{u, v} U).map global = morphism :=
  (explicitReconstructionData U).existsUnique_preimage morphism

/-- Main theorem for the fixed GOAL B representative geometry branch.  It
applies the Cycle 65 theorem to the concrete Part I reconstruction data, with
no additional premise. -/
def representativeEquivalence (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ≌ RepresentativeLocalObject.{u, v} U :=
  (representativeReconstructionData U).equivalence

/-- Main theorem for the fixed GOAL B explicit geometry branch.  It applies
the Cycle 65 theorem to the concrete Part I reconstruction data, with no
additional premise. -/
def explicitEquivalence (U : AtomCarrier.{u}) :
    ExplicitExactGeomCategory.{u, v} U ≌ ExplicitLocalObject.{u, v} U :=
  (explicitReconstructionData U).equivalence

end IndependentGeometryCategoryReconstruction

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryCategoryReconstruction
