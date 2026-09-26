import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import Formal.Util.AssertStandardAxioms

/-! G-124(III-1): the coefficient projection selects primitive carrier and
ring-operation data from local objects, and the directed coefficient graph
from local Homs. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionCoefficient

open CategoryTheory
open IndependentGeometryTableAssembly
open IndependentGeometryCategoryReconstruction
open IndependentGeometryHomPrimitive
open GeometryTransport
open RealizationReconstruction

universe u v

/-- Native representative geometry keeps its original coefficient ring and
directed coefficient map. -/
noncomputable def nativeRepresentative (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ CommRingCat.{v} where
  obj geometry := CommRingCat.of geometry.Coefficient
  map morphism := CommRingCat.ofHom morphism.geometry.coefficientHom
  map_id geometry := by
    apply CommRingCat.hom_ext
    rfl
  map_comp first second := by
    apply CommRingCat.hom_ext
    rfl

/-- Native explicit geometry retains the same directed coefficient map. -/
noncomputable def nativeExplicit (U : AtomCarrier.{u}) :
    ExplicitExactGeomCategory.{u, v} U ⥤ CommRingCat.{v} where
  obj geometry := CommRingCat.of geometry.toGeometryPackage.Coefficient
  map morphism := CommRingCat.ofHom morphism.coefficientHom
  map_id geometry := by
    apply CommRingCat.hom_ext
    rfl
  map_comp first second := by
    apply CommRingCat.hom_ext
    rfl

/-- The original coefficient ring assembled solely from the primitive
coefficient carrier and operation table. -/
noncomputable def object {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) : CommRingCat := by
  let ring := coefficient data.2.2.1
  letI : CommRing ring.1 := ring.2
  exact CommRingCat.of ring.1

theorem object_eq_native {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) :
    object data = (nativeRepresentative U).obj (assemble data) := rfl

theorem object_eq_native_explicit {U : AtomCarrier.{u}}
    (data : ObjectData.{u, v} U) :
    object data = (nativeExplicit U).obj
      (ExplicitExactGeomCategory.ofGeometryPackage (assemble data)) := rfl

/-- Reading and reassembling the primitive coefficient object table recovers
the original representative coefficient ring. -/
theorem representativeObject_read {U : AtomCarrier.{u}}
    (geometry : GeomReadCategory.{u, v} U) :
    object (objectData (representativeReadObject geometry).localObject) =
      (nativeRepresentative U).obj geometry := by
  rw [object_eq_native]
  exact congrArg (nativeRepresentative U).obj
    (by simpa [representativeReadObject] using
      assemble_objectData_readFragments geometry)

/-- The explicit mode has the same primitive coefficient object recovery. -/
theorem explicitObject_read {U : AtomCarrier.{u}}
    (geometry : ExplicitExactGeomCategory.{u, v} U) :
    object (objectData (explicitReadObject geometry).localObject) =
      (nativeExplicit U).obj geometry := by
  rw [object_eq_native_explicit,
    explicit_assemble_objectData_readFragments]

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

/-- A representative local Hom selects its directed coefficient graph and
ring-preservation laws, then assembles only the coefficient map. -/
noncomputable def representativeMap
    {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    object (objectData source.localObject) ⟶
      object (objectData target.localObject) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  letI : CommRing (coefficient s.2.2.1).1 := (coefficient s.2.2.1).2
  letI : CommRing (coefficient t.2.2.1).1 := (coefficient t.2.2.1).2
  exact CommRingCat.ofHom
    (GeometryComponents.coefficientMap s t morphism.1 morphism.2.coefficient)

/-- The explicit local category uses the same original directed coefficient
graph, with its own independently checked Hom laws. -/
noncomputable def explicitMap
    {U : AtomCarrier.{u}}
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    object (objectData source.localObject) ⟶
      object (objectData target.localObject) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  letI : CommRing (coefficient s.2.2.1).1 := (coefficient s.2.2.1).2
  letI : CommRing (coefficient t.2.2.1).1 := (coefficient t.2.2.1).2
  exact CommRingCat.ofHom
    (GeometryComponents.coefficientMap s t morphism.1 morphism.2.coefficient)

/-- The coefficient map selected from primitive local points agrees with the
coefficient field of the accepted full representative assembly. -/
theorem representativeMap_eq_native
    {U : AtomCarrier.{u}}
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    representativeMap morphism =
      (nativeRepresentative U).map
        ((representativeAssemblyFunctor U).map morphism) := rfl

/-- The explicit local coefficient selection has the same native evaluation. -/
theorem explicitMap_eq_native
    {U : AtomCarrier.{u}}
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    explicitMap morphism =
      (nativeExplicit U).map
        ((explicitAssemblyFunctor U).map morphism) := rfl

/-- The local representative coefficient projection is defined only by the
primitive coefficient object table and directed Hom graph. -/
noncomputable def localRepresentative (U : AtomCarrier.{u}) :
    RepresentativeLocalObject.{u, v} U ⥤ CommRingCat.{v} where
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

/-- The explicit local coefficient projection likewise selects only the
primitive coefficient components. -/
noncomputable def localExplicit (U : AtomCarrier.{u}) :
    ExplicitLocalObject.{u, v} U ⥤ CommRingCat.{v} where
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

/-- The direct local coefficient projection commutes with the accepted
representative assembly on every object and Hom. -/
theorem localRepresentative_eq_assembly (U : AtomCarrier.{u}) :
    localRepresentative.{u, v} U =
      representativeAssemblyFunctor U ⋙ nativeRepresentative U := by
  refine CategoryTheory.Functor.ext (fun source => rfl) ?_
  intro source target morphism
  simpa using representativeMap_eq_native morphism

/-- The same equality holds for explicit local context actions. -/
theorem localExplicit_eq_assembly (U : AtomCarrier.{u}) :
    localExplicit.{u, v} U =
      explicitAssemblyFunctor U ⋙ nativeExplicit U := by
  refine CategoryTheory.Functor.ext (fun source => rfl) ?_
  intro source target morphism
  simpa using explicitMap_eq_native morphism

/-- The direct local representative coefficient projection agrees naturally
with the native coefficient projection after reading. -/
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

/-- The explicit local coefficient projection has the corresponding natural
comparison, including morphisms with actual context action. -/
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

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionCoefficient

end AAT.AG.LocalSemanticReconstruction.G124ProjectionCoefficient
