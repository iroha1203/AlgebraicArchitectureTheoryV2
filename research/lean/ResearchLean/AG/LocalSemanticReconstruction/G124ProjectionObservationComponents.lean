import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Observation components selected from the G-124 primitive tables

The observation object retains the generated architecture object, selected
context preorder, and observable equation family.  Its local constructor
selects the context and equation primitive stages directly.  A local Hom
selects the independently assembled context equivalence and observable ring
family from the retained common Hom table.
-/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionObservationComponents

open CategoryTheory GeometryTransport
open IndependentGeometryHomPrimitive
open IndependentCoreTableAssembly
open IndependentGeometryTableAssembly
open IndependentGeometryCategoryReconstruction

noncomputable section

universe u v

variable {U : AtomCarrier.{u}}

/-- The dependent object required to type selected contexts and observable rings. -/
structure Object (U : AtomCarrier.{u}) where
  architecture : ArchitectureObject U
  context : Site.ContextPreorderCategory architecture
  equation : ArchitecturalEquationSystem context

/-- Read the native observation object from a representative geometry. -/
def nativeObject (geometry : GeometryPackage.{u, v} U) : Object U where
  architecture := geometry.core.object
  context := geometry.core.contextPreorder
  equation := geometry.core.algebra.equationSystem

/-- Assemble only the context and equation stages of a primitive object table. -/
def localObject (data : ObjectData.{u, v} U) : Object U where
  architecture := generatedObject data.1.val.1
  context := context data.1.val.2.1
  equation := equation data.1.val.2.2.1

/-- The local observation object reads the same dependent components as the
native geometry assembled from the primitive table. -/
theorem localObject_eq_native (data : ObjectData.{u, v} U) :
    localObject data = nativeObject (assemble data) := by
  rfl

/-- Primitive representative reading preserves the observation object. -/
theorem representativeObject_read (geometry : GeomReadCategory.{u, v} U) :
    localObject (objectData (representativeReadObject geometry).localObject) =
      nativeObject geometry := by
  rw [localObject_eq_native]
  change nativeObject (assemble
    (objectData (IndependentGeometryPrimitive.readFragments geometry))) = nativeObject geometry
  rw [assemble_objectData_readFragments]

/-- Primitive explicit reading preserves the same observation object. -/
theorem explicitObject_read
    (geometry : RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U) :
    localObject (objectData (explicitReadObject geometry).localObject) =
      nativeObject geometry.toGeometryPackage := by
  rw [localObject_eq_native]
  change nativeObject (assemble
    (objectData (IndependentGeometryPrimitive.readFragments geometry.toGeometryPackage))) =
    nativeObject geometry.toGeometryPackage
  rw [assemble_objectData_readFragments]

/-- Mode-specific wrappers keep the two observation Hom meanings separate. -/
structure RepresentativeObject (U : AtomCarrier.{u}) where
  data : Object U

/-- Explicit observation retains actual context action in its Hom type. -/
structure ExplicitObject (U : AtomCarrier.{u}) where
  data : Object U

/-- Representative data recovery lifted to its target category object. -/
theorem representativeWrappedObject_read (geometry : GeomReadCategory.{u, v} U) :
    (⟨localObject (objectData (representativeReadObject geometry).localObject)⟩ :
      RepresentativeObject U) = ⟨nativeObject geometry⟩ :=
  congrArg RepresentativeObject.mk (representativeObject_read geometry)

/-- Explicit data recovery lifted to its own target category object. -/
theorem explicitWrappedObject_read
    (geometry : RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U) :
    (⟨localObject (objectData (explicitReadObject geometry).localObject)⟩ :
      ExplicitObject U) = ⟨nativeObject geometry.toGeometryPackage⟩ :=
  congrArg ExplicitObject.mk (explicitObject_read geometry)

/-- Selected primitive context points of a representative local Hom. -/
def representativeContext
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    (Site.ContextCategoryObject
      (localObject (objectData source.localObject)).context) ≌
    (Site.ContextCategoryObject
      (localObject (objectData target.localObject)).context) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  exact Context.assemble
    (localObject s).context (localObject t).context
    (Context.points h (localObject s).architecture (localObject t).architecture)
    morphism.property.package.contextRows

/-- The representative context projection uses exactly the primitive
forward and backward point rows. -/
theorem representativeContext_read
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    Context.read
      (localObject (objectData source.localObject)).context
      (localObject (objectData target.localObject)).context
      (representativeContext morphism) =
    Context.points
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      (localObject (objectData source.localObject)).architecture
      (localObject (objectData target.localObject)).architecture := by
  exact Context.read_assemble _ _ _ _

/-- Observable ring equivalences assembled directly from the common Hom
graph, indexed by the context equivalence assembled above. -/
def representativeObservable
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    ∀ W : Site.ContextCategoryObject
      (localObject (objectData source.localObject)).context,
      (localObject (objectData source.localObject)).equation.Observable W ≃+*
        (localObject (objectData target.localObject)).equation.Observable
          ((representativeContext morphism).functor.obj W) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  let sr := s.1.val.2.2.1.val
  let tr := t.1.val.2.2.1.val
  letI := ObservableNatural.rings sr s.1.val.2.2.1.property.choose
    s.1.val.2.2.1.property.choose_spec
  letI := ObservableNatural.rings tr t.1.val.2.2.1.property.choose
    t.1.val.2.2.1.property.choose_spec
  exact Observable.assemble
    (localObject s).context (localObject t).context h
    morphism.property.package.contextRows _ _
    morphism.property.package.observableRows

/-- Explicit context equivalence is selected from the common context rows. -/
def explicitContext
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    (Site.ContextCategoryObject
      (localObject (objectData source.localObject)).context) ≌
    (Site.ContextCategoryObject
      (localObject (objectData target.localObject)).context) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  exact Context.assemble
    (localObject s).context (localObject t).context
    (Context.points h (localObject s).architecture (localObject t).architecture)
    morphism.property.package.contextRows

/-- Explicit context equivalence reads back to the same raw point pairs. -/
theorem explicitContext_read
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    Context.read
      (localObject (objectData source.localObject)).context
      (localObject (objectData target.localObject)).context
      (explicitContext morphism) =
    Context.points
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      (localObject (objectData source.localObject)).architecture
      (localObject (objectData target.localObject)).architecture := by
  exact Context.read_assemble _ _ _ _

/-- Explicit observable ring maps use the same inverse graph constructor;
the realization fiber action remains a separate component. -/
def explicitObservable
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    ∀ W : Site.ContextCategoryObject
      (localObject (objectData source.localObject)).context,
      (localObject (objectData source.localObject)).equation.Observable W ≃+*
        (localObject (objectData target.localObject)).equation.Observable
          ((explicitContext morphism).functor.obj W) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  let sr := s.1.val.2.2.1.val
  let tr := t.1.val.2.2.1.val
  letI := ObservableNatural.rings sr s.1.val.2.2.1.property.choose
    s.1.val.2.2.1.property.choose_spec
  letI := ObservableNatural.rings tr t.1.val.2.2.1.property.choose
    t.1.val.2.2.1.property.choose_spec
  exact Observable.assemble
    (localObject s).context (localObject t).context h
    morphism.property.package.contextRows _ _
    morphism.property.package.observableRows

/-- Restriction naturality is discharged by the original point-square law,
with the constructed context map and observable family. -/
theorem representativeObservable_naturality
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    ContextObservableGraphCoherence.IsRingFamilyRestrictionNatural
      (representativeContext morphism).functor
      (fun W => (localObject (objectData source.localObject)).equation.Observable W)
      (fun V => (localObject (objectData target.localObject)).equation.Observable V)
      (localObject (objectData source.localObject)).equation.restrict
      (localObject (objectData target.localObject)).equation.restrict
      (representativeObservable morphism) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  intro W V f value
  simpa only [ContextObservableGraphCoherence.IsRingFamilyRestrictionNatural,
    representativeContext, representativeObservable, localObject,
    IndependentCoreTableAssembly.equation,
    IndependentEquationPrimitive.assemble] using
    (((ObservableNatural.points_iff_nativeNaturality
    s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose
    s.1.val.2.2.1.property.choose_spec t.1.val.2.2.1.property.choose_spec
    h morphism.property.package.contextRows
    morphism.property.package.observableRows).1
    morphism.property.package.equationPoints.naturality)
    morphism.property.package.observableRows) f value

/-- The same point-square law applies to the explicit observation action. -/
theorem explicitObservable_naturality
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    ContextObservableGraphCoherence.IsRingFamilyRestrictionNatural
      (explicitContext morphism).functor
      (fun W => (localObject (objectData source.localObject)).equation.Observable W)
      (fun V => (localObject (objectData target.localObject)).equation.Observable V)
      (localObject (objectData source.localObject)).equation.restrict
      (localObject (objectData target.localObject)).equation.restrict
      (explicitObservable morphism) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  intro W V f value
  simpa only [ContextObservableGraphCoherence.IsRingFamilyRestrictionNatural,
    explicitContext, explicitObservable, localObject,
    IndependentCoreTableAssembly.equation,
    IndependentEquationPrimitive.assemble] using
    (((ObservableNatural.points_iff_nativeNaturality
    s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose
    s.1.val.2.2.1.property.choose_spec t.1.val.2.2.1.property.choose_spec
    h morphism.property.package.contextRows
    morphism.property.package.observableRows).1
    morphism.property.package.equationPoints.naturality)
    morphism.property.package.observableRows) f value

/-! ### Representative observation morphisms -/

/-- A morphism on the retained observation data.  Its context map acts on
selected restrictions; the three realization components are indexed by that
map and preserve the original reading predicates. -/
structure RepresentativeHom (source target : Object U) where
  atomMap : U.Atom → U.Atom
  contextFunctor : Site.ContextCategoryObject source.context ⥤
    Site.ContextCategoryObject target.context
  observableRing : ∀ W, source.equation.Observable W →+*
    target.equation.Observable (contextFunctor.obj W)
  observable_naturality : ∀ {W V} (f : W ⟶ V)
      (x : source.equation.Observable V),
    observableRing W (source.equation.restrict f x) =
      target.equation.restrict (contextFunctor.map f) (observableRing V x)
  supportMap : ∀ W, W.ctx.Support → (contextFunctor.obj W).ctx.Support
  axisMap : ∀ W, W.ctx.Axis → (contextFunctor.obj W).ctx.Axis
  observableMap : ∀ W, W.ctx.Observable → (contextFunctor.obj W).ctx.Observable
  supportReads : ∀ W x atom, W.ctx.minimal.supportReads x atom →
    (contextFunctor.obj W).ctx.minimal.supportReads (supportMap W x) (atomMap atom)
  axisReads : ∀ W x, W.ctx.minimal.axisReads x →
    (contextFunctor.obj W).ctx.minimal.axisReads (axisMap W x)
  observableReads : ∀ W x, W.ctx.minimal.observableReads x →
    (contextFunctor.obj W).ctx.minimal.observableReads (observableMap W x)
  support_naturality : ∀ {W V} (f : W ⟶ V) x,
    (target.context.morphism (leOfHom (contextFunctor.map f))).supportMap (supportMap W x) =
      supportMap V ((source.context.morphism (leOfHom f)).supportMap x)
  axis_naturality : ∀ {W V} (f : W ⟶ V) x,
    (target.context.morphism (leOfHom (contextFunctor.map f))).axisMap (axisMap W x) =
      axisMap V ((source.context.morphism (leOfHom f)).axisMap x)
  observable_naturality' : ∀ {W V} (f : W ⟶ V) x,
    (target.context.morphism (leOfHom (contextFunctor.map f))).observableRestrict
      (observableMap V x) =
      observableMap W ((source.context.morphism (leOfHom f)).observableRestrict x)

namespace RepresentativeHom

/-- Identity acts by identity on every retained observation component. -/
def id (object : Object U) : RepresentativeHom object object where
  atomMap := _root_.id
  contextFunctor := Functor.id _
  observableRing _ := RingHom.id _
  observable_naturality := by intros; rfl
  supportMap _ := _root_.id
  axisMap _ := _root_.id
  observableMap _ := _root_.id
  supportReads := by intro _ _ _ h; exact h
  axisReads := by intro _ _ h; exact h
  observableReads := by intro _ _ h; exact h
  support_naturality := by intros; rfl
  axis_naturality := by intros; rfl
  observable_naturality' := by intros; rfl

/-- Composition reindexes each fiber map by the first context action. -/
def comp {source middle target : Object U}
    (first : RepresentativeHom source middle)
    (second : RepresentativeHom middle target) :
    RepresentativeHom source target where
  atomMap := second.atomMap ∘ first.atomMap
  contextFunctor := first.contextFunctor ⋙ second.contextFunctor
  observableRing W := (second.observableRing (first.contextFunctor.obj W)).comp
    (first.observableRing W)
  observable_naturality := by
    intro W V f x
    change second.observableRing (first.contextFunctor.obj W)
        (first.observableRing W (source.equation.restrict f x)) =
      target.equation.restrict (second.contextFunctor.map (first.contextFunctor.map f))
        (second.observableRing (first.contextFunctor.obj V)
          (first.observableRing V x))
    rw [first.observable_naturality f x,
      second.observable_naturality (first.contextFunctor.map f)
        (first.observableRing V x)]
  supportMap W x := second.supportMap (first.contextFunctor.obj W) (first.supportMap W x)
  axisMap W x := second.axisMap (first.contextFunctor.obj W) (first.axisMap W x)
  observableMap W x := second.observableMap (first.contextFunctor.obj W)
    (first.observableMap W x)
  supportReads := by
    intro W x atom h
    exact second.supportReads _ _ _ (first.supportReads W x atom h)
  axisReads := by
    intro W x h
    exact second.axisReads _ _ (first.axisReads W x h)
  observableReads := by
    intro W x h
    exact second.observableReads _ _ (first.observableReads W x h)
  support_naturality := by
    intro W V f x
    change (target.context.morphism (leOfHom
        (second.contextFunctor.map (first.contextFunctor.map f)))).supportMap
        (second.supportMap _ (first.supportMap W x)) =
      second.supportMap _
        (first.supportMap V ((source.context.morphism (leOfHom f)).supportMap x))
    rw [second.support_naturality (first.contextFunctor.map f) (first.supportMap W x),
      first.support_naturality f x]
  axis_naturality := by
    intro W V f x
    change (target.context.morphism (leOfHom
        (second.contextFunctor.map (first.contextFunctor.map f)))).axisMap
        (second.axisMap _ (first.axisMap W x)) =
      second.axisMap _
        (first.axisMap V ((source.context.morphism (leOfHom f)).axisMap x))
    rw [second.axis_naturality (first.contextFunctor.map f) (first.axisMap W x),
      first.axis_naturality f x]
  observable_naturality' := by
    intro W V f x
    change (target.context.morphism (leOfHom
        (second.contextFunctor.map (first.contextFunctor.map f)))).observableRestrict
        (second.observableMap _ (first.observableMap V x)) =
      second.observableMap _
        (first.observableMap W
          ((source.context.morphism (leOfHom f)).observableRestrict x))
    rw [second.observable_naturality' (first.contextFunctor.map f)
      (first.observableMap V x), first.observable_naturality' f x]

/-- Computational components determine a representative observation Hom. -/
theorem ext {source target : Object U}
    {first second : RepresentativeHom source target}
    (hatom : first.atomMap = second.atomMap)
    (hcontext : first.contextFunctor = second.contextFunctor)
    (hring : HEq first.observableRing second.observableRing)
    (hsupport : HEq first.supportMap second.supportMap)
    (haxis : HEq first.axisMap second.axisMap)
    (hobservable : HEq first.observableMap second.observableMap) :
    first = second := by
  cases first
  cases second
  cases hatom
  cases hcontext
  cases hring
  cases hsupport
  cases haxis
  cases hobservable
  rfl

end RepresentativeHom

/-- The retained representative observation data form a category under
pointwise composition and context reindexing. -/
instance representativeObservationCategory : Category (RepresentativeObject U) where
  Hom source target := RepresentativeHom source.data target.data
  id object := RepresentativeHom.id object.data
  comp := RepresentativeHom.comp
  id_comp := by
    intro source target morphism
    apply RepresentativeHom.ext <;> rfl
  comp_id := by
    intro source target morphism
    apply RepresentativeHom.ext <;> rfl
  assoc := by
    intro first second third fourth f g h
    apply RepresentativeHom.ext <;> rfl

/-- Native representative geometry forgets exactly to its observation data. -/
def nativeRepresentativeMap {source target : GeometryPackage.{u, v} U}
    (morphism : GeometryTotalHom source target) :
    RepresentativeHom (nativeObject source) (nativeObject target) where
  atomMap := morphism.base.upper.atomEquiv
  contextFunctor := morphism.base.upper.equationTransport.contextEquivalence.functor
  observableRing W := (morphism.base.upper.equationTransport.observableEquiv W).toRingHom
  observable_naturality := by
    intro W V f x
    exact morphism.base.upper.equationTransport.observable_naturality f x
  supportMap := morphism.geometry.supportComp
  axisMap := morphism.geometry.axisComp
  observableMap := morphism.geometry.observableComp
  supportReads := morphism.geometry.supportReads
  axisReads := morphism.geometry.axisReads
  observableReads := morphism.geometry.observableReads
  support_naturality := morphism.geometry.support_naturality
  axis_naturality := morphism.geometry.axis_naturality
  observable_naturality' := morphism.geometry.observable_naturality

/-- Native representative projection to the observation category. -/
def nativeRepresentative (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ RepresentativeObject U where
  obj geometry := ⟨nativeObject geometry⟩
  map := nativeRepresentativeMap
  map_id _ := by
    apply RepresentativeHom.ext <;> rfl
  map_comp _ _ := by
    apply RepresentativeHom.ext <;> rfl

/-- The local representative observation map selects its context, ring, and
three realization components from the primitive Hom table. -/
def localRepresentativeMap
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    RepresentativeHom
      (localObject (objectData source.localObject))
      (localObject (objectData target.localObject)) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let realization := GeometryComponents.representativeRealization
    s t p morphism.property.package morphism.property.realization
  exact {
    atomMap := Atom.assemble (Atom.upper h) morphism.property.package.atom.upper
    contextFunctor := (representativeContext morphism).functor
    observableRing := fun W => (representativeObservable morphism W).toRingHom
    observable_naturality := by
      intro W V f x
      exact representativeObservable_naturality morphism f x
    supportMap := realization.supportComp
    axisMap := realization.axisComp
    observableMap := realization.observableComp
    supportReads := realization.supportReads
    axisReads := realization.axisReads
    observableReads := realization.observableReads
    support_naturality := realization.support_naturality
    axis_naturality := realization.axis_naturality
    observable_naturality' := realization.observable_naturality }

/-- Complete-Hom assembly verifies the direct local observation map without
occurring in its definition. -/
theorem localRepresentativeMap_eq_native
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    localRepresentativeMap morphism =
      nativeRepresentativeMap
        (FullRepresentative.assembleHom
          (objectData source.localObject) (objectData target.localObject)
          morphism.val morphism.property) := by
  rfl

/-- Direct local representative projection.  Its object and Hom maps select
observation components before any complete geometry assembly. -/
def localRepresentative (U : AtomCarrier.{u}) :
    RepresentativeLocalObject.{u, v} U ⥤ RepresentativeObject U where
  obj object := ⟨localObject (objectData object.localObject)⟩
  map := localRepresentativeMap
  map_id object := by
    change localRepresentativeMap (𝟙 object) = RepresentativeHom.id _
    rw [localRepresentativeMap_eq_native]
    change (nativeRepresentative U).map
      ((representativeAssemblyFunctor U).map (𝟙 object)) =
      𝟙 ((nativeRepresentative U).obj ((representativeAssemblyFunctor U).obj object))
    rw [(representativeAssemblyFunctor U).map_id,
      (nativeRepresentative U).map_id]
  map_comp first second := by
    change localRepresentativeMap (first ≫ second) =
      RepresentativeHom.comp (localRepresentativeMap first)
        (localRepresentativeMap second)
    rw [localRepresentativeMap_eq_native,
      localRepresentativeMap_eq_native first,
      localRepresentativeMap_eq_native second]
    change (nativeRepresentative U).map
      ((representativeAssemblyFunctor U).map (first ≫ second)) =
      (nativeRepresentative U).map
        ((representativeAssemblyFunctor U).map first) ≫
      (nativeRepresentative U).map
        ((representativeAssemblyFunctor U).map second)
    rw [(representativeAssemblyFunctor U).map_comp,
      (nativeRepresentative U).map_comp]

/-- Equality with assembly is used only to verify the independently defined
component projection and its functor laws. -/
theorem localRepresentative_eq_assembly (U : AtomCarrier.{u}) :
    localRepresentative.{u, v} U =
      representativeAssemblyFunctor U ⋙ nativeRepresentative U := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target morphism
  exact localRepresentativeMap_eq_native morphism

/-- Reading then assembling a representative Hom gives the endpoint-conjugated
native Hom used by the fixed reconstruction equivalence. -/
theorem representativeAssembly_read_map
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

/-- Observation extraction commutes naturally with the representative reader. -/
def representativeReadingIso (U : AtomCarrier.{u}) :
    representativeReadingFunctor.{u, v} U ⋙ localRepresentative U ≅
      nativeRepresentative U :=
  NatIso.ofComponents
    (fun geometry => eqToIso (representativeWrappedObject_read geometry))
    (by
      intro source target morphism
      change (localRepresentative U).map
          ((representativeReadingFunctor U).map morphism) ≫
          (eqToIso (representativeWrappedObject_read target)).hom =
        (eqToIso (representativeWrappedObject_read source)).hom ≫
          (nativeRepresentative U).map morphism
      rw [show (localRepresentative U).map
          ((representativeReadingFunctor U).map morphism) =
            (nativeRepresentative U).map
              (representativeEndpointHomEquiv source target morphism) from by
            change localRepresentativeMap
              ((representativeReadingFunctor U).map morphism) = _
            rw [localRepresentativeMap_eq_native]
            change (nativeRepresentative U).map
                ((representativeAssemblyFunctor U).map
                  ((representativeReadingFunctor U).map morphism)) = _
            rw [representativeAssembly_read_map]]
      simp [representativeEndpointHomEquiv, Iso.homCongr,
        representativeObjectIso, eqToHom_map, Category.assoc])

/-! ### Explicit observation morphisms -/

/-- The explicit observation Hom retains its action on actual context
morphisms, independently of the chosen thin-category representative. -/
structure ExplicitHom (source target : Object U) where
  atomEquiv : U.Atom ≃ U.Atom
  contextFunctor : Site.ContextCategoryObject source.context ⥤
    Site.ContextCategoryObject target.context
  observableRing : ∀ W, source.equation.Observable W ≃+*
    target.equation.Observable (contextFunctor.obj W)
  observable_naturality : ∀ {W V} (f : W ⟶ V)
      (x : source.equation.Observable V),
    observableRing W (source.equation.restrict f x) =
      target.equation.restrict (contextFunctor.map f) (observableRing V x)
  actualContext : ∀ {W V : Site.ContextCategoryObject source.context},
    Site.ContextMorphism W.ctx V.ctx →
      Site.ContextMorphism (contextFunctor.obj W).ctx (contextFunctor.obj V).ctx
  actualRestriction : ∀ {W V : Site.ContextCategoryObject source.context}
      (f : Site.ContextMorphism W.ctx V.ctx),
    f.IsRestriction → (actualContext f).IsRestriction
  supportEquiv : ∀ W, W.ctx.Support ≃ (contextFunctor.obj W).ctx.Support
  axisEquiv : ∀ W, W.ctx.Axis ≃ (contextFunctor.obj W).ctx.Axis
  observableEquiv : ∀ W, W.ctx.Observable ≃
    (contextFunctor.obj W).ctx.Observable
  supportReads_iff : ∀ W x atom, W.ctx.minimal.supportReads x atom ↔
    (contextFunctor.obj W).ctx.minimal.supportReads
      (supportEquiv W x) (atomEquiv atom)
  axisReads_iff : ∀ W x, W.ctx.minimal.axisReads x ↔
    (contextFunctor.obj W).ctx.minimal.axisReads (axisEquiv W x)
  observableReads_iff : ∀ W x, W.ctx.minimal.observableReads x ↔
    (contextFunctor.obj W).ctx.minimal.observableReads (observableEquiv W x)
  support_naturality : ∀ {W V : Site.ContextCategoryObject source.context}
      (f : Site.ContextMorphism W.ctx V.ctx) x,
    (actualContext f).supportMap (supportEquiv W x) =
      supportEquiv V (f.supportMap x)
  axis_naturality : ∀ {W V : Site.ContextCategoryObject source.context}
      (f : Site.ContextMorphism W.ctx V.ctx) x,
    (actualContext f).axisMap (axisEquiv W x) =
      axisEquiv V (f.axisMap x)
  observable_naturality' : ∀ {W V : Site.ContextCategoryObject source.context}
      (f : Site.ContextMorphism W.ctx V.ctx) x,
    (actualContext f).observableRestrict (observableEquiv V x) =
      observableEquiv W (f.observableRestrict x)

namespace ExplicitHom

/-- Identity on every retained explicit observation component. -/
def id (object : Object U) : ExplicitHom object object where
  atomEquiv := Equiv.refl _
  contextFunctor := Functor.id _
  observableRing _ := RingEquiv.refl _
  observable_naturality := by intros; rfl
  actualContext f := f
  actualRestriction _ hf := hf
  supportEquiv _ := Equiv.refl _
  axisEquiv _ := Equiv.refl _
  observableEquiv _ := Equiv.refl _
  supportReads_iff := by intros; exact Iff.rfl
  axisReads_iff := by intros; exact Iff.rfl
  observableReads_iff := by intros; exact Iff.rfl
  support_naturality := by intros; rfl
  axis_naturality := by intros; rfl
  observable_naturality' := by intros; rfl

/-- Explicit action composes on the actual context morphism, with each fiber
equivalence reindexed through the first context image. -/
def comp {source middle target : Object U}
    (first : ExplicitHom source middle)
    (second : ExplicitHom middle target) : ExplicitHom source target where
  atomEquiv := first.atomEquiv.trans second.atomEquiv
  contextFunctor := first.contextFunctor ⋙ second.contextFunctor
  observableRing W := (first.observableRing W).trans
    (second.observableRing (first.contextFunctor.obj W))
  observable_naturality := by
    intro W V f x
    change second.observableRing (first.contextFunctor.obj W)
        (first.observableRing W (source.equation.restrict f x)) =
      target.equation.restrict (second.contextFunctor.map (first.contextFunctor.map f))
        (second.observableRing (first.contextFunctor.obj V)
          (first.observableRing V x))
    rw [first.observable_naturality f x,
      second.observable_naturality (first.contextFunctor.map f)
        (first.observableRing V x)]
  actualContext f := second.actualContext (first.actualContext f)
  actualRestriction f hf :=
    second.actualRestriction _ (first.actualRestriction f hf)
  supportEquiv W := (first.supportEquiv W).trans
    (second.supportEquiv (first.contextFunctor.obj W))
  axisEquiv W := (first.axisEquiv W).trans
    (second.axisEquiv (first.contextFunctor.obj W))
  observableEquiv W := (first.observableEquiv W).trans
    (second.observableEquiv (first.contextFunctor.obj W))
  supportReads_iff := by
    intro W x atom
    exact (first.supportReads_iff W x atom).trans
      (second.supportReads_iff (first.contextFunctor.obj W)
        (first.supportEquiv W x) (first.atomEquiv atom))
  axisReads_iff := by
    intro W x
    exact (first.axisReads_iff W x).trans
      (second.axisReads_iff (first.contextFunctor.obj W) (first.axisEquiv W x))
  observableReads_iff := by
    intro W x
    exact (first.observableReads_iff W x).trans
      (second.observableReads_iff (first.contextFunctor.obj W)
        (first.observableEquiv W x))
  support_naturality := by
    intro W V f x
    change (second.actualContext (first.actualContext f)).supportMap
        (second.supportEquiv _ (first.supportEquiv W x)) =
      second.supportEquiv _ (first.supportEquiv V (f.supportMap x))
    rw [second.support_naturality (first.actualContext f) (first.supportEquiv W x),
      first.support_naturality f x]
  axis_naturality := by
    intro W V f x
    change (second.actualContext (first.actualContext f)).axisMap
        (second.axisEquiv _ (first.axisEquiv W x)) =
      second.axisEquiv _ (first.axisEquiv V (f.axisMap x))
    rw [second.axis_naturality (first.actualContext f) (first.axisEquiv W x),
      first.axis_naturality f x]
  observable_naturality' := by
    intro W V f x
    change (second.actualContext (first.actualContext f)).observableRestrict
        (second.observableEquiv _ (first.observableEquiv V x)) =
      second.observableEquiv _ (first.observableEquiv W (f.observableRestrict x))
    rw [second.observable_naturality' (first.actualContext f)
      (first.observableEquiv V x), first.observable_naturality' f x]

/-- Computational fields determine an explicit observation Hom. -/
theorem ext {source target : Object U}
    {first second : ExplicitHom source target}
    (hatom : first.atomEquiv = second.atomEquiv)
    (hcontext : first.contextFunctor = second.contextFunctor)
    (hring : HEq first.observableRing second.observableRing)
    (haction : HEq
      (@ExplicitHom.actualContext U source target first)
      (@ExplicitHom.actualContext U source target second))
    (hsupport : HEq first.supportEquiv second.supportEquiv)
    (haxis : HEq first.axisEquiv second.axisEquiv)
    (hobservable : HEq first.observableEquiv second.observableEquiv) :
    first = second := by
  cases first
  cases second
  cases hatom
  cases hcontext
  cases hring
  cases haction
  cases hsupport
  cases haxis
  cases hobservable
  rfl

end ExplicitHom

/-- Explicit observation Homs compose while retaining actual context action. -/
instance explicitObservationCategory : Category (ExplicitObject U) where
  Hom source target := ExplicitHom source.data target.data
  id object := ExplicitHom.id object.data
  comp := ExplicitHom.comp
  id_comp := by
    intro source target morphism
    apply ExplicitHom.ext <;> rfl
  comp_id := by
    intro source target morphism
    apply ExplicitHom.ext <;> rfl
  assoc := by
    intro first second third fourth f g h
    apply ExplicitHom.ext <;> rfl

/-- Native explicit geometry retains its actual context action and fiber
equivalences in the observation category. -/
def nativeExplicitMap
    {source target : RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U}
    (morphism : source ⟶ target) :
    ExplicitHom (nativeObject source.toGeometryPackage)
      (nativeObject target.toGeometryPackage) where
  atomEquiv := morphism.base.upper.atomEquiv
  contextFunctor := morphism.base.upper.equationTransport.contextEquivalence.functor
  observableRing := morphism.base.upper.equationTransport.observableEquiv
  observable_naturality := morphism.base.upper.equationTransport.observable_naturality
  actualContext := morphism.realization.contextMorphism
  actualRestriction := morphism.realization.contextMorphism_isRestriction
  supportEquiv := morphism.realization.supportEquiv
  axisEquiv := morphism.realization.axisEquiv
  observableEquiv := morphism.realization.observableEquiv
  supportReads_iff := morphism.realization.supportReads_iff
  axisReads_iff := morphism.realization.axisReads_iff
  observableReads_iff := morphism.realization.observableReads_iff
  support_naturality := morphism.realization.support_naturality
  axis_naturality := morphism.realization.axis_naturality
  observable_naturality' := morphism.realization.observable_naturality

/-- Native explicit projection to retained observation data. -/
def nativeExplicit (U : AtomCarrier.{u}) :
    RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U ⥤ ExplicitObject U where
  obj geometry := ⟨nativeObject geometry.toGeometryPackage⟩
  map := nativeExplicitMap
  map_id _ := by
    apply ExplicitHom.ext <;> rfl
  map_comp _ _ := by
    apply ExplicitHom.ext <;> rfl

/-- Local explicit observation uses only the primitive context, observable,
and actual realization component assemblers. -/
def localExplicitMap
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    ExplicitHom
      (localObject (objectData source.localObject))
      (localObject (objectData target.localObject)) := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let realization := GeometryComponents.explicitRealization
    s t p morphism.property.package morphism.property.realization
  exact {
    atomEquiv := Atom.assemble (Atom.upper h) morphism.property.package.atom.upper
    contextFunctor := (explicitContext morphism).functor
    observableRing := explicitObservable morphism
    observable_naturality := by
      intro W V f x
      exact explicitObservable_naturality morphism f x
    actualContext := realization.contextMorphism
    actualRestriction := realization.contextMorphism_isRestriction
    supportEquiv := realization.supportEquiv
    axisEquiv := realization.axisEquiv
    observableEquiv := realization.observableEquiv
    supportReads_iff := realization.supportReads_iff
    axisReads_iff := realization.axisReads_iff
    observableReads_iff := realization.observableReads_iff
    support_naturality := realization.support_naturality
    axis_naturality := realization.axis_naturality
    observable_naturality' := realization.observable_naturality }

/-- Complete explicit assembly verifies the direct local component selection. -/
theorem localExplicitMap_eq_native
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target) :
    localExplicitMap morphism =
      nativeExplicitMap
        (FullExplicit.assembleHom
          (objectData source.localObject) (objectData target.localObject)
          morphism.val morphism.property) := by
  rfl

/-- Direct explicit projection from the local primitive category. -/
def localExplicit (U : AtomCarrier.{u}) :
    ExplicitLocalObject.{u, v} U ⥤ ExplicitObject U where
  obj object := ⟨localObject (objectData object.localObject)⟩
  map := localExplicitMap
  map_id object := by
    change localExplicitMap (𝟙 object) = ExplicitHom.id _
    rw [localExplicitMap_eq_native]
    change (nativeExplicit U).map
      ((explicitAssemblyFunctor U).map (𝟙 object)) =
      𝟙 ((nativeExplicit U).obj ((explicitAssemblyFunctor U).obj object))
    rw [(explicitAssemblyFunctor U).map_id,
      (nativeExplicit U).map_id]
  map_comp first second := by
    change localExplicitMap (first ≫ second) =
      ExplicitHom.comp (localExplicitMap first) (localExplicitMap second)
    rw [localExplicitMap_eq_native,
      localExplicitMap_eq_native first,
      localExplicitMap_eq_native second]
    change (nativeExplicit U).map
      ((explicitAssemblyFunctor U).map (first ≫ second)) =
      (nativeExplicit U).map ((explicitAssemblyFunctor U).map first) ≫
      (nativeExplicit U).map ((explicitAssemblyFunctor U).map second)
    rw [(explicitAssemblyFunctor U).map_comp,
      (nativeExplicit U).map_comp]

/-- The explicit local component projection agrees with partial native
extraction after the accepted complete assembly. -/
theorem localExplicit_eq_assembly (U : AtomCarrier.{u}) :
    localExplicit.{u, v} U =
      explicitAssemblyFunctor U ⋙ nativeExplicit U := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target morphism
  exact localExplicitMap_eq_native morphism

/-- Reading and assembling an explicit Hom restores the endpoint-conjugated
native Hom. -/
theorem explicitAssembly_read_map
    {source target : RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U}
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

/-- Observation extraction commutes naturally with the explicit reader,
including actual context-morphism action. -/
def explicitReadingIso (U : AtomCarrier.{u}) :
    explicitReadingFunctor.{u, v} U ⋙ localExplicit U ≅
      nativeExplicit U :=
  NatIso.ofComponents
    (fun geometry => eqToIso (explicitWrappedObject_read geometry))
    (by
      intro source target morphism
      change (localExplicit U).map
          ((explicitReadingFunctor U).map morphism) ≫
          (eqToIso (explicitWrappedObject_read target)).hom =
        (eqToIso (explicitWrappedObject_read source)).hom ≫
          (nativeExplicit U).map morphism
      rw [show (localExplicit U).map
          ((explicitReadingFunctor U).map morphism) =
            (nativeExplicit U).map
              (explicitEndpointHomEquiv source target morphism) from by
            change localExplicitMap
              ((explicitReadingFunctor U).map morphism) = _
            rw [localExplicitMap_eq_native]
            change (nativeExplicit U).map
                ((explicitAssemblyFunctor U).map
                  ((explicitReadingFunctor U).map morphism)) = _
            rw [explicitAssembly_read_map]]
      simp [explicitEndpointHomEquiv, Iso.homCongr,
        explicitObjectIso, eqToHom_map, Category.assoc])

/-! ### Direct point evaluation -/

/-- A representative support graph cell is true precisely at the selected
local support image. -/
theorem representativeSupport_point
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ArchCtx (localObject (objectData source.localObject)).architecture)
    (x : W.Support)
    (y : ((localRepresentativeMap morphism).contextFunctor.obj ⟨W⟩).ctx.Support) :
    RepresentativeRealization.support
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      W ((localRepresentativeMap morphism).contextFunctor.obj ⟨W⟩).ctx x y = true ↔
      (localRepresentativeMap morphism).supportMap ⟨W⟩ x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let f := GeometryComponents.base s t p morphism.property.package
  let hm := GeometryComponents.representative_maps s t p morphism.property.package
  let hp := (GeometryComponents.representative_points_iff s t p).2
    morphism.property.realization
  exact IndependentFixedIndexedPointGraph.point_iff
    (RepresentativeRealization.forward f) hm.context
    (RepresentativeRealization.support h) hp.supportRows W x y

/-- Representative axis evaluation is the primitive directed axis graph. -/
theorem representativeAxis_point
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ArchCtx (localObject (objectData source.localObject)).architecture)
    (x : W.Axis)
    (y : ((localRepresentativeMap morphism).contextFunctor.obj ⟨W⟩).ctx.Axis) :
    RepresentativeRealization.axis
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      W ((localRepresentativeMap morphism).contextFunctor.obj ⟨W⟩).ctx x y = true ↔
      (localRepresentativeMap morphism).axisMap ⟨W⟩ x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let f := GeometryComponents.base s t p morphism.property.package
  let hm := GeometryComponents.representative_maps s t p morphism.property.package
  let hp := (GeometryComponents.representative_points_iff s t p).2
    morphism.property.realization
  exact IndependentFixedIndexedPointGraph.point_iff
    (RepresentativeRealization.forward f) hm.context
    (RepresentativeRealization.axis h) hp.axisRows W x y

/-- Representative observable fiber evaluation is the primitive directed
observable graph, separate from the observable ring component. -/
theorem representativeObservable_point
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ArchCtx (localObject (objectData source.localObject)).architecture)
    (x : W.Observable)
    (y : ((localRepresentativeMap morphism).contextFunctor.obj ⟨W⟩).ctx.Observable) :
    RepresentativeRealization.observable
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      W ((localRepresentativeMap morphism).contextFunctor.obj ⟨W⟩).ctx x y = true ↔
      (localRepresentativeMap morphism).observableMap ⟨W⟩ x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let f := GeometryComponents.base s t p morphism.property.package
  let hm := GeometryComponents.representative_maps s t p morphism.property.package
  let hp := (GeometryComponents.representative_points_iff s t p).2
    morphism.property.realization
  exact IndependentFixedIndexedPointGraph.point_iff
    (RepresentativeRealization.forward f) hm.context
    (RepresentativeRealization.observable h) hp.observableRows W x y

/-- An explicit support graph cell is true precisely at the forward fiber
equivalence selected by the local table. -/
theorem explicitSupport_point
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ArchCtx (localObject (objectData source.localObject)).architecture)
    (x : W.Support)
    (y : ((localExplicitMap morphism).contextFunctor.obj ⟨W⟩).ctx.Support) :
    ExplicitRealization.support
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      .forward W ((localExplicitMap morphism).contextFunctor.obj ⟨W⟩).ctx x y = true ↔
      (localExplicitMap morphism).supportEquiv ⟨W⟩ x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let f := GeometryComponents.base s t p morphism.property.package
  let hm := GeometryComponents.explicit_maps s t p morphism.property.package
  let hp := morphism.property.realization
  exact IndependentFixedIndexedPointGraph.point_iff
    (ExplicitRealization.forward f) hm.context
    (ExplicitRealization.support h .forward) hp.supportRows.forward W x y

/-- The explicit axis equivalence evaluates to its retained forward graph. -/
theorem explicitAxis_point
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ArchCtx (localObject (objectData source.localObject)).architecture)
    (x : W.Axis)
    (y : ((localExplicitMap morphism).contextFunctor.obj ⟨W⟩).ctx.Axis) :
    ExplicitRealization.axis
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      .forward W ((localExplicitMap morphism).contextFunctor.obj ⟨W⟩).ctx x y = true ↔
      (localExplicitMap morphism).axisEquiv ⟨W⟩ x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let f := GeometryComponents.base s t p morphism.property.package
  let hm := GeometryComponents.explicit_maps s t p morphism.property.package
  let hp := morphism.property.realization
  exact IndependentFixedIndexedPointGraph.point_iff
    (ExplicitRealization.forward f) hm.context
    (ExplicitRealization.axis h .forward) hp.axisRows.forward W x y

/-- The explicit observable fiber equivalence evaluates to its retained
forward graph; the ring observable remains the separate equation component. -/
theorem explicitObservable_point
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ArchCtx (localObject (objectData source.localObject)).architecture)
    (x : W.Observable)
    (y : ((localExplicitMap morphism).contextFunctor.obj ⟨W⟩).ctx.Observable) :
    ExplicitRealization.observable
      (PackageAssembly.retained
        (objectData source.localObject).1
        (objectData target.localObject).1 morphism.val).table
      .forward W ((localExplicitMap morphism).contextFunctor.obj ⟨W⟩).ctx x y = true ↔
      (localExplicitMap morphism).observableEquiv ⟨W⟩ x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let p := morphism.val
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let f := GeometryComponents.base s t p morphism.property.package
  let hm := GeometryComponents.explicit_maps s t p morphism.property.package
  let hp := morphism.property.realization
  exact IndependentFixedIndexedPointGraph.point_iff
    (ExplicitRealization.forward f) hm.context
    (ExplicitRealization.observable h .forward) hp.observableRows.forward W x y

/-- The representative local observable-ring map evaluates at the original
forward graph cell on the selected context pair. -/
theorem representativeObservableRing_point
    {source target : RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ContextCategoryObject
      (localObject (objectData source.localObject)).context)
    (x : (localObject (objectData source.localObject)).equation.Observable W)
    (y : (localObject (objectData target.localObject)).equation.Observable
      ((localRepresentativeMap morphism).contextFunctor.obj W)) :
    (PackageAssembly.retained
      (objectData source.localObject).1
      (objectData target.localObject).1 morphism.val).table
        (.atObjects
          (localObject (objectData source.localObject)).architecture
          (localObject (objectData target.localObject)).architecture
          (.observable .forward W.ctx
            ((localRepresentativeMap morphism).contextFunctor.obj W).ctx
            (.edge _ _ x y))) = true ↔
      (localRepresentativeMap morphism).observableRing W x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  letI := ObservableNatural.rings s.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose s.1.val.2.2.1.property.choose_spec
  letI := ObservableNatural.rings t.1.val.2.2.1.val
    t.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose_spec
  have hp := Observable.forward_point
    (localObject s).context (localObject t).context h
    morphism.property.package.contextRows W
  have he := Observable.atPair_forward_iff h _ _
    morphism.property.package.observableRows W.ctx
    ((representativeContext morphism).functor.obj W).ctx hp x y
  have hv : Observable.atPair h _ _
      morphism.property.package.observableRows W.ctx
      ((representativeContext morphism).functor.obj W).ctx hp =
      representativeObservable morphism W := by
    exact (Observable.assemble_eq_atPair
      (localObject s).context (localObject t).context h
      morphism.property.package.contextRows _ _
      morphism.property.package.observableRows W).symm
  rw [hv] at he
  exact he

/-- The explicit local observable-ring equivalence has the same direct
forward point evaluation on the retained common table. -/
theorem explicitObservableRing_point
    {source target : ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (W : Site.ContextCategoryObject
      (localObject (objectData source.localObject)).context)
    (x : (localObject (objectData source.localObject)).equation.Observable W)
    (y : (localObject (objectData target.localObject)).equation.Observable
      ((localExplicitMap morphism).contextFunctor.obj W)) :
    (PackageAssembly.retained
      (objectData source.localObject).1
      (objectData target.localObject).1 morphism.val).table
        (.atObjects
          (localObject (objectData source.localObject)).architecture
          (localObject (objectData target.localObject)).architecture
          (.observable .forward W.ctx
            ((localExplicitMap morphism).contextFunctor.obj W).ctx
            (.edge _ _ x y))) = true ↔
      (localExplicitMap morphism).observableRing W x = y := by
  let s := objectData source.localObject
  let t := objectData target.localObject
  let h := (PackageAssembly.retained s.1 t.1 morphism.val).table
  letI := ObservableNatural.rings s.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose s.1.val.2.2.1.property.choose_spec
  letI := ObservableNatural.rings t.1.val.2.2.1.val
    t.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose_spec
  have hp := Observable.forward_point
    (localObject s).context (localObject t).context h
    morphism.property.package.contextRows W
  have he := Observable.atPair_forward_iff h _ _
    morphism.property.package.observableRows W.ctx
    ((explicitContext morphism).functor.obj W).ctx hp x y
  have hv : Observable.atPair h _ _
      morphism.property.package.observableRows W.ctx
      ((explicitContext morphism).functor.obj W).ctx hp =
      explicitObservable morphism W := by
    exact (Observable.assemble_eq_atPair
      (localObject s).context (localObject t).context h
      morphism.property.package.contextRows _ _
      morphism.property.package.observableRows W).symm
  rw [hv] at he
  exact he

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.G124ProjectionObservationComponents

end

end AAT.AG.LocalSemanticReconstruction.G124ProjectionObservationComponents
