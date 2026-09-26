import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import ResearchLean.AG.CrossStageCoherence.Basic
import Formal.Util.AssertStandardAxioms

/-! G-124(III-1): the geometry bottom projection selects the pointed
extraction doctrine from primitive tables and the lower pointed map from
the local Hom's source, Atom, and normalization points. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionBottom

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction
open IndependentCoreTableAssembly IndependentGeometryTableAssembly
open IndependentGeometryCategoryReconstruction
open IndependentGeometryHomPrimitive

universe u v

/-- Geometry's established two-stage bottom projection. -/
noncomputable def nativeRepresentative (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ ExtractionInstance U :=
  CrossStageCoherence.crossStageProjection U

/-- Explicit geometry has the same extraction object and lower map. -/
noncomputable def nativeExplicit (U : AtomCarrier.{u}) :
    ExplicitExactGeomCategory.{u, v} U ⥤ ExtractionInstance U where
  obj geometry := packagePoint geometry.toGeometryPackage.core
  map morphism := morphism.base.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The pointed extraction doctrine selected by the primitive extraction
table, before complete core or geometry assembly. -/
noncomputable def object {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) : ExtractionInstance U := by
  let pointed := finiteExtractionEquiv.symm data.1.val.1.1
  exact ⟨pointed.1.1, pointed.1.2⟩

theorem object_eq_native {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) :
    object data = packagePoint (assemblePackage data.1) := rfl

/-- Select only the lower pointed doctrine map from a representative local
Hom's retained primitive points. -/
noncomputable def representativeMap
    {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    object (objectData source.localObject) ⟶
      object (objectData target.localObject) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  exact PackageAssembly.lower s.1 t.1
    (PackageAssembly.retained s.1 t.1 morphism.1).table
    morphism.2.package

/-- The explicit local Hom has the same direct lower pointed map. -/
noncomputable def explicitMap
    {U : AtomCarrier.{u}}
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    object (objectData source.localObject) ⟶
      object (objectData target.localObject) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  exact PackageAssembly.lower s.1 t.1
    (PackageAssembly.retained s.1 t.1 morphism.1).table
    morphism.2.package

theorem representativeMap_eq_native
    {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    representativeMap morphism =
      (nativeRepresentative U).map
        ((representativeAssemblyFunctor U).map morphism) := rfl

theorem explicitMap_eq_native
    {U : AtomCarrier.{u}}
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    explicitMap morphism =
      (nativeExplicit U).map
        ((explicitAssemblyFunctor U).map morphism) := rfl

/-- The intermediate core stage is assembled from primitive package rows,
without constructing any geometry-stage fields. -/
noncomputable def coreObject {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) : AATCorePackage U :=
  assemblePackage data.1

noncomputable def representativeCoreMap
    {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    coreObject (objectData source.localObject) ⟶
      coreObject (objectData target.localObject) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  exact PackageAssembly.assemble s.1 t.1 morphism.1 morphism.2.package

noncomputable def explicitCoreMap
    {U : AtomCarrier.{u}}
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    coreObject (objectData source.localObject) ⟶
      coreObject (objectData target.localObject) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  exact PackageAssembly.assemble s.1 t.1 morphism.1 morphism.2.package

theorem representativeCoreMap_eq_native
    {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    representativeCoreMap morphism =
      (geometryProjection U).map
        ((representativeAssemblyFunctor U).map morphism) := rfl

theorem explicitCoreMap_eq_native
    {U : AtomCarrier.{u}}
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    explicitCoreMap morphism =
      ((explicitAssemblyFunctor U).map morphism).base := rfl

noncomputable def nativeExplicitCore (U : AtomCarrier.{u}) :
    ExplicitExactGeomCategory.{u, v} U ⥤ AATCorePackage U where
  obj geometry := geometry.toGeometryPackage.core
  map morphism := morphism.base
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def localRepresentativeCore (U : AtomCarrier.{u}) :
    RepresentativeLocalObject.{u, v} U ⥤ AATCorePackage U where
  obj source := coreObject (objectData source.localObject)
  map morphism := representativeCoreMap morphism
  map_id source := by
    rw [representativeCoreMap_eq_native]
    rw [(representativeAssemblyFunctor U).map_id,
      (geometryProjection U).map_id]
    rfl
  map_comp first second := by
    change representativeCoreMap (first ≫ second) =
      representativeCoreMap first ≫ representativeCoreMap second
    rw [representativeCoreMap_eq_native, representativeCoreMap_eq_native,
      representativeCoreMap_eq_native]
    rw [(representativeAssemblyFunctor U).map_comp,
      (geometryProjection U).map_comp]

noncomputable def localExplicitCore (U : AtomCarrier.{u}) :
    ExplicitLocalObject.{u, v} U ⥤ AATCorePackage U where
  obj source := coreObject (objectData source.localObject)
  map morphism := explicitCoreMap morphism
  map_id source := by
    rw [explicitCoreMap_eq_native]
    rw [(explicitAssemblyFunctor U).map_id]
    rfl
  map_comp first second := by
    change explicitCoreMap (first ≫ second) =
      explicitCoreMap first ≫ explicitCoreMap second
    rw [explicitCoreMap_eq_native, explicitCoreMap_eq_native,
      explicitCoreMap_eq_native]
    rw [(explicitAssemblyFunctor U).map_comp]
    rfl

theorem representativeCoreObject_read {U : AtomCarrier.{u}}
    (geometry : GeomReadCategory.{u, v} U) :
    coreObject (objectData (representativeReadObject geometry).localObject) =
      geometry.core := by
  exact congrArg (fun x : GeomReadCategory.{u, v} U => x.core)
    (by simpa [representativeReadObject] using
      assemble_objectData_readFragments geometry)

theorem explicitCoreObject_read {U : AtomCarrier.{u}}
    (geometry : ExplicitExactGeomCategory.{u, v} U) :
    coreObject (objectData (explicitReadObject geometry).localObject) =
      geometry.toGeometryPackage.core := by
  exact congrArg (fun x : ExplicitExactGeomCategory.{u, v} U =>
    x.toGeometryPackage.core)
      (explicit_assemble_objectData_readFragments geometry)

theorem localRepresentativeCore_eq_assembly (U : AtomCarrier.{u}) :
    localRepresentativeCore.{u, v} U =
      representativeAssemblyFunctor U ⋙ geometryProjection U := by
  refine CategoryTheory.Functor.ext (fun source => rfl) ?_
  intro source target morphism
  simpa using representativeCoreMap_eq_native morphism

theorem localExplicitCore_eq_assembly (U : AtomCarrier.{u}) :
    localExplicitCore.{u, v} U =
      explicitAssemblyFunctor U ⋙ nativeExplicitCore U := by
  refine CategoryTheory.Functor.ext (fun source => rfl) ?_
  intro source target morphism
  simpa [nativeExplicitCore] using explicitCoreMap_eq_native morphism

noncomputable def localRepresentative (U : AtomCarrier.{u}) :
    RepresentativeLocalObject.{u, v} U ⥤ ExtractionInstance U where
  obj source := object (objectData source.localObject)
  map morphism := representativeMap morphism
  map_id source := by
    rw [representativeMap_eq_native]
    rw [(representativeAssemblyFunctor U).map_id,
      (nativeRepresentative U).map_id]
    change 𝟙 ((nativeRepresentative U).obj (assemble (objectData source.localObject))) =
      𝟙 (object (objectData source.localObject))
    rfl
  map_comp first second := by
    change representativeMap (first ≫ second) =
      representativeMap first ≫ representativeMap second
    rw [representativeMap_eq_native, representativeMap_eq_native,
      representativeMap_eq_native]
    simp

noncomputable def localExplicit (U : AtomCarrier.{u}) :
    ExplicitLocalObject.{u, v} U ⥤ ExtractionInstance U where
  obj source := object (objectData source.localObject)
  map morphism := explicitMap morphism
  map_id source := by
    rw [explicitMap_eq_native]
    rw [(explicitAssemblyFunctor U).map_id,
      (nativeExplicit U).map_id]
    change 𝟙 ((nativeExplicit U).obj
      (ExplicitExactGeomCategory.ofGeometryPackage (assemble (objectData source.localObject)))) =
      𝟙 (object (objectData source.localObject))
    rfl
  map_comp first second := by
    change explicitMap (first ≫ second) =
      explicitMap first ≫ explicitMap second
    rw [explicitMap_eq_native, explicitMap_eq_native,
      explicitMap_eq_native]
    simp

theorem localRepresentative_eq_assembly (U : AtomCarrier.{u}) :
    localRepresentative.{u, v} U =
      representativeAssemblyFunctor U ⋙ nativeRepresentative U := by
  refine CategoryTheory.Functor.ext (fun source => rfl) ?_
  intro source target morphism
  simpa using representativeMap_eq_native morphism

theorem localExplicit_eq_assembly (U : AtomCarrier.{u}) :
    localExplicit.{u, v} U =
      explicitAssemblyFunctor U ⋙ nativeExplicit U := by
  refine CategoryTheory.Functor.ext (fun source => rfl) ?_
  intro source target morphism
  simpa using explicitMap_eq_native morphism

theorem representativeObject_read {U : AtomCarrier.{u}}
    (geometry : GeomReadCategory.{u, v} U) :
    object (objectData (representativeReadObject geometry).localObject) =
      (nativeRepresentative U).obj geometry := by
  rw [object_eq_native]
  exact congrArg (nativeRepresentative U).obj
    (by simpa [representativeReadObject] using
      assemble_objectData_readFragments geometry)

theorem explicitObject_read {U : AtomCarrier.{u}}
    (geometry : ExplicitExactGeomCategory.{u, v} U) :
    object (objectData (explicitReadObject geometry).localObject) =
      (nativeExplicit U).obj geometry := by
  change object (objectData (explicitReadObject geometry).localObject) =
    packagePoint geometry.toGeometryPackage.core
  rw [object_eq_native]
  exact congrArg (fun x : ExplicitExactGeomCategory.{u, v} U =>
    packagePoint x.toGeometryPackage.core)
      (explicit_assemble_objectData_readFragments geometry)

theorem representativeAssembly_read_map
    {U : AtomCarrier.{u}}
    {source target : GeomReadCategory.{u, v} U}
    (morphism : source ⟶ target) :
    (representativeAssemblyFunctor U).map
        ((representativeReadingFunctor U).map morphism) =
      representativeEndpointHomEquiv source target morphism := by
  let s := objectData (representativeReadObject source).localObject
  let t := objectData (representativeReadObject target).localObject
  change (NativeReader.representativeHomReadingEquiv s t).symm
      ((NativeReader.representativeHomReadingEquiv s t)
        (representativeEndpointHomEquiv source target morphism)) =
    representativeEndpointHomEquiv source target morphism
  exact (NativeReader.representativeHomReadingEquiv s t).symm_apply_apply _

theorem explicitAssembly_read_map
    {U : AtomCarrier.{u}}
    {source target : ExplicitExactGeomCategory.{u, v} U}
    (morphism : source ⟶ target) :
    (explicitAssemblyFunctor U).map
        ((explicitReadingFunctor U).map morphism) =
      explicitEndpointHomEquiv source target morphism := by
  let s := objectData (explicitReadObject source).localObject
  let t := objectData (explicitReadObject target).localObject
  change (NativeReader.explicitHomReadingEquiv s t).symm
      ((NativeReader.explicitHomReadingEquiv s t)
        (explicitEndpointHomEquiv source target morphism)) =
    explicitEndpointHomEquiv source target morphism
  exact (NativeReader.explicitHomReadingEquiv s t).symm_apply_apply _

noncomputable def representativeCoreReadingIso (U : AtomCarrier.{u}) :
    representativeReadingFunctor.{u, v} U ⋙ localRepresentativeCore U ≅
      geometryProjection U :=
  NatIso.ofComponents
    (fun geometry => eqToIso (representativeCoreObject_read geometry))
    (by
      intro source target morphism
      change (localRepresentativeCore U).map
          ((representativeReadingFunctor U).map morphism) ≫
          (eqToIso (representativeCoreObject_read target)).hom =
        (eqToIso (representativeCoreObject_read source)).hom ≫
          (geometryProjection U).map morphism
      rw [show (localRepresentativeCore U).map
          ((representativeReadingFunctor U).map morphism) =
            (geometryProjection U).map
              (representativeEndpointHomEquiv source target morphism) from by
            change representativeCoreMap
              ((representativeReadingFunctor U).map morphism) = _
            rw [representativeCoreMap_eq_native,
              representativeAssembly_read_map]]
      have h : representativeEndpointHomEquiv source target morphism ≫
          (representativeObjectIso target).hom =
          (representativeObjectIso source).hom ≫ morphism := by
        simp [representativeEndpointHomEquiv, Iso.homCongr,
          Category.assoc]
      have mapped := congrArg (geometryProjection U).map h
      have mappedObjectIso (geometry : GeomReadCategory.{u, v} U) :
          (geometryProjection U).map (representativeObjectIso geometry).hom =
            (eqToIso (representativeCoreObject_read geometry)).hom := by
        let h : assemble
            (objectData (representativeReadObject geometry).localObject) = geometry := by
          simpa [representativeReadObject] using
            assemble_objectData_readFragments geometry
        change (geometryProjection U).map (eqToHom h) =
          eqToHom (congrArg (geometryProjection U).obj h)
        exact eqToHom_map (geometryProjection U) h
      rw [← mappedObjectIso source, ← mappedObjectIso target]
      change (geometryProjection U).map
          (representativeEndpointHomEquiv source target morphism) ≫
          (geometryProjection U).map (representativeObjectIso target).hom =
        (geometryProjection U).map (representativeObjectIso source).hom ≫
          (geometryProjection U).map morphism
      rw [← (geometryProjection U).map_comp,
        ← (geometryProjection U).map_comp]
      exact mapped)

noncomputable def explicitCoreReadingIso (U : AtomCarrier.{u}) :
    explicitReadingFunctor.{u, v} U ⋙ localExplicitCore U ≅
      nativeExplicitCore U :=
  NatIso.ofComponents
    (fun geometry => eqToIso (explicitCoreObject_read geometry))
    (by
      intro source target morphism
      change (localExplicitCore U).map
          ((explicitReadingFunctor U).map morphism) ≫
          (eqToIso (explicitCoreObject_read target)).hom =
        (eqToIso (explicitCoreObject_read source)).hom ≫
          (nativeExplicitCore U).map morphism
      rw [show (localExplicitCore U).map
          ((explicitReadingFunctor U).map morphism) =
            (nativeExplicitCore U).map
              (explicitEndpointHomEquiv source target morphism) from by
            change explicitCoreMap ((explicitReadingFunctor U).map morphism) = _
            rw [explicitCoreMap_eq_native, explicitAssembly_read_map]
            rfl]
      simp [explicitEndpointHomEquiv, Iso.homCongr,
        explicitObjectIso, eqToHom_map, Category.assoc])

noncomputable def representativeReadingIso (U : AtomCarrier.{u}) :
    representativeReadingFunctor.{u, v} U ⋙ localRepresentative U ≅
      nativeRepresentative U :=
  NatIso.ofComponents
    (fun geometry => eqToIso (representativeObject_read geometry))
    (by
      intro source target morphism
      change (localRepresentative U).map
          ((representativeReadingFunctor U).map morphism) ≫
          (eqToIso (representativeObject_read target)).hom =
        (eqToIso (representativeObject_read source)).hom ≫
          (nativeRepresentative U).map morphism
      rw [show (localRepresentative U).map
          ((representativeReadingFunctor U).map morphism) =
            (nativeRepresentative U).map
              (representativeEndpointHomEquiv source target morphism) from by
            change representativeMap
              ((representativeReadingFunctor U).map morphism) = _
            rw [representativeMap_eq_native,
              representativeAssembly_read_map]]
      simp [representativeEndpointHomEquiv, Iso.homCongr,
        representativeObjectIso, eqToHom_map, Category.assoc])

noncomputable def explicitReadingIso (U : AtomCarrier.{u}) :
    explicitReadingFunctor.{u, v} U ⋙ localExplicit U ≅
      nativeExplicit U :=
  NatIso.ofComponents
    (fun geometry => eqToIso (explicitObject_read geometry))
    (by
      intro source target morphism
      change (localExplicit U).map
          ((explicitReadingFunctor U).map morphism) ≫
          (eqToIso (explicitObject_read target)).hom =
        (eqToIso (explicitObject_read source)).hom ≫
          (nativeExplicit U).map morphism
      rw [show (localExplicit U).map
          ((explicitReadingFunctor U).map morphism) =
            (nativeExplicit U).map
              (explicitEndpointHomEquiv source target morphism) from by
            change explicitMap ((explicitReadingFunctor U).map morphism) = _
            rw [explicitMap_eq_native, explicitAssembly_read_map]]
      simp [explicitEndpointHomEquiv, Iso.homCongr,
        explicitObjectIso, eqToHom_map, Category.assoc])

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionBottom

end AAT.AG.LocalSemanticReconstruction.G124ProjectionBottom
