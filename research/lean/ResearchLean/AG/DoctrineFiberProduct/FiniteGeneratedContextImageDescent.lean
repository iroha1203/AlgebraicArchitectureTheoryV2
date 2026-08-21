import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectImageDescent

/-!
# Canonical finite-model context image descent

This module lifts every carrier of a finite-model architecture context through
`ULift` and reflects contexts whose four carrier types have the corresponding
canonical shape.  Reflection keeps the low carrier types supplied by a template,
while its predicates and extension value are read from the actual high context.

The same construction is applied to all three computational maps of a raw
`ContextMorphism`.  The resulting round trips and restriction laws provide the
primitive image API needed to reflect a generated high context equivalence in a
later module.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Context objects -/

/--
Lift all four carriers and the selected predicates of a finite-model context.
-/
def finiteModelLiftArchitectureContext
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) :
    Site.ArchitectureContext (finiteModelLiftArchitectureObject.{u} A) where
  minimal := {
    Support := ULift.{u} W.Support
    Axis := ULift.{u} W.Axis
    Observable := ULift.{u} W.Observable
    supportReads := fun support atom =>
      W.minimal.supportReads support.down
        (finiteModelLiftCarrierEquiv.{u}.atom.symm atom)
    supportReads_objectFamily := by
      intro support atom hread
      simpa [finiteModelLiftArchitectureObject,
        finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using
        W.supportReads_objectFamily hread
    axisReads := fun axis => W.minimal.axisReads axis.down
    observableReads := fun observable =>
      W.minimal.observableReads observable.down
  }
  Extension := ULift.{u} W.Extension
  extension := ULift.up W.extension

/-- Lifted support predicates agree with the source predicate on lifted data. -/
@[simp]
theorem finiteModelLiftArchitectureContext_supportReads
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) (support : W.Support)
    (atom : FiniteModel.carrier.Atom) :
    (finiteModelLiftArchitectureContext.{u} W).minimal.supportReads
        (ULift.up support) (finiteModelLiftCarrierEquiv.{u}.atom atom) ↔
      W.minimal.supportReads support atom := by
  simp [finiteModelLiftArchitectureContext]

/-- Lifted axis predicates agree with the source predicate on lifted axes. -/
@[simp]
theorem finiteModelLiftArchitectureContext_axisReads
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) (axis : W.Axis) :
    (finiteModelLiftArchitectureContext.{u} W).minimal.axisReads
        (ULift.up axis) ↔ W.minimal.axisReads axis :=
  Iff.rfl

/-- Lifted observable predicates agree with the source predicate on lifted values. -/
@[simp]
theorem finiteModelLiftArchitectureContext_observableReads
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) (observable : W.Observable) :
    (finiteModelLiftArchitectureContext.{u} W).minimal.observableReads
        (ULift.up observable) ↔ W.minimal.observableReads observable :=
  Iff.rfl

/-- The lifted extension value is the canonical lift of the source value. -/
@[simp]
theorem finiteModelLiftArchitectureContext_extension
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) :
    (finiteModelLiftArchitectureContext.{u} W).extension =
      ULift.up W.extension :=
  rfl

/--
Carrier-only alignment between a low template and an actual high context.

The fields contain no predicate, context map, image preimage, or generated
factor.  They are used only to type the casts through which reflection reads the
actual high fields.
-/
structure FiniteModelContextCarrierShape
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B)) where
  /-- The actual support carrier has the canonical lifted template shape. -/
  support_eq : ULift.{u} template.Support = actual.Support
  /-- The actual axis carrier has the canonical lifted template shape. -/
  axis_eq : ULift.{u} template.Axis = actual.Axis
  /-- The actual observable carrier has the canonical lifted template shape. -/
  observable_eq : ULift.{u} template.Observable = actual.Observable
  /-- The actual extension carrier has the canonical lifted template shape. -/
  extension_eq : ULift.{u} template.Extension = actual.Extension

/-- Lift a low value into a carrier identified with its canonical `ULift`. -/
def finiteModelContextShapeUp {X : Type} {Y : Type u}
    (h : ULift.{u} X = Y) (x : X) : Y :=
  _root_.cast h (ULift.up x)

/-- Lower a value from a carrier identified with a canonical `ULift`. -/
def finiteModelContextShapeDown {X : Type} {Y : Type u}
    (h : ULift.{u} X = Y) (y : Y) : X := by
  subst Y
  exact y.down

/-- Shape-guided lifting after lowering recovers every actual high value. -/
theorem finiteModelContextShape_up_down
    {X : Type} {Y : Type u} (h : ULift.{u} X = Y) (y : Y) :
    finiteModelContextShapeUp h (finiteModelContextShapeDown h y) = y := by
  cases h
  exact ULift.up_down y

/-- Shape-guided lowering after lifting recovers every low value. -/
theorem finiteModelContextShape_down_up
    {X : Type} {Y : Type u} (h : ULift.{u} X = Y) (x : X) :
    finiteModelContextShapeDown h (finiteModelContextShapeUp h x) = x := by
  cases h
  rfl

/--
Reflect an actual high context along its carrier shape.

The returned carriers come from `template`.  Its support, axis, and observable
predicates and its extension value are obtained by evaluating the corresponding
fields of `actual` after the shape casts.
-/
noncomputable def finiteModelReflectArchitectureContextAt
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B))
    (shape : FiniteModelContextCarrierShape template actual) :
    Site.ArchitectureContext B where
  minimal := {
    Support := template.Support
    Axis := template.Axis
    Observable := template.Observable
    supportReads := fun support atom =>
      actual.minimal.supportReads
        (finiteModelContextShapeUp shape.support_eq support)
        (finiteModelLiftCarrierEquiv.{u}.atom atom)
    supportReads_objectFamily := by
      intro support atom hread
      have hhigh := actual.supportReads_objectFamily hread
      simpa [finiteModelLiftArchitectureObject,
        finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using hhigh
    axisReads := fun axis =>
      actual.minimal.axisReads
        (finiteModelContextShapeUp shape.axis_eq axis)
    observableReads := fun observable =>
      actual.minimal.observableReads
        (finiteModelContextShapeUp shape.observable_eq observable)
  }
  Extension := template.Extension
  extension := finiteModelContextShapeDown shape.extension_eq actual.extension

/-- Reflected support predicates are evaluations of the actual high predicate. -/
theorem finiteModelReflectArchitectureContextAt_supportReads
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B))
    (shape : FiniteModelContextCarrierShape template actual)
    (support : template.Support) (atom : FiniteModel.carrier.Atom) :
    (finiteModelReflectArchitectureContextAt template actual shape).minimal.supportReads
        support atom ↔
      actual.minimal.supportReads
        (finiteModelContextShapeUp shape.support_eq support)
        (finiteModelLiftCarrierEquiv.{u}.atom atom) :=
  Iff.rfl

/-- Reflected axis predicates are evaluations of the actual high predicate. -/
theorem finiteModelReflectArchitectureContextAt_axisReads
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B))
    (shape : FiniteModelContextCarrierShape template actual)
    (axis : template.Axis) :
    (finiteModelReflectArchitectureContextAt template actual shape).minimal.axisReads
        axis ↔
      actual.minimal.axisReads
        (finiteModelContextShapeUp shape.axis_eq axis) :=
  Iff.rfl

/-- Reflected observable predicates are evaluations of the actual high predicate. -/
theorem finiteModelReflectArchitectureContextAt_observableReads
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B))
    (shape : FiniteModelContextCarrierShape template actual)
    (observable : template.Observable) :
    (finiteModelReflectArchitectureContextAt template actual shape).minimal.observableReads
        observable ↔
      actual.minimal.observableReads
        (finiteModelContextShapeUp shape.observable_eq observable) :=
  Iff.rfl

/-- Lifting the reflected extension value recovers the actual high value. -/
theorem finiteModelReflectArchitectureContextAt_extension_graph
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B))
    (shape : FiniteModelContextCarrierShape template actual) :
    finiteModelContextShapeUp shape.extension_eq
        (finiteModelReflectArchitectureContextAt template actual shape).extension =
      actual.extension :=
  finiteModelContextShape_up_down _ _

/-- A canonically lifted context has the canonical carrier shape. -/
def finiteModelLiftArchitectureContext_shape
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) :
    FiniteModelContextCarrierShape W
      (finiteModelLiftArchitectureContext.{u} W) where
  support_eq := rfl
  axis_eq := rfl
  observable_eq := rfl
  extension_eq := rfl

/-- Reflecting a canonically lifted context recovers the complete source context. -/
@[simp]
theorem finiteModelReflectArchitectureContextAt_lift
    {A : ArchitectureObject FiniteModel.carrier}
    (W : Site.ArchitectureContext A) :
    finiteModelReflectArchitectureContextAt W
        (finiteModelLiftArchitectureContext.{u} W)
        (finiteModelLiftArchitectureContext_shape.{u} W) = W := by
  rcases W with
    ⟨⟨Support, Axis, Observable, supportReads, supportReads_objectFamily,
      axisReads, observableReads⟩, Extension, extension⟩
  simp [finiteModelReflectArchitectureContextAt,
    finiteModelLiftArchitectureContext,
    finiteModelContextShapeUp, finiteModelContextShapeDown]
  exact ⟨rfl, rfl, rfl⟩

/--
Every shape-reflected context lifts back to the complete actual high context.
-/
theorem finiteModelLiftArchitectureContext_reflectAt
    {A B : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B))
    (shape : FiniteModelContextCarrierShape template actual) :
    finiteModelLiftArchitectureContext.{u}
        (finiteModelReflectArchitectureContextAt template actual shape) = actual := by
  rcases template with
    ⟨⟨Support, Axis, Observable, supportReads, supportReads_objectFamily,
      axisReads, observableReads⟩, Extension, extension⟩
  rcases actual with
    ⟨⟨SupportHigh, AxisHigh, ObservableHigh, supportReadsHigh,
      supportReadsObjectHigh, axisReadsHigh, observableReadsHigh⟩,
      ExtensionHigh, extensionHigh⟩
  rcases shape with ⟨hsupport, haxis, hobservable, hextension⟩
  cases hsupport
  cases haxis
  cases hobservable
  cases hextension
  simp [finiteModelLiftArchitectureContext,
    finiteModelReflectArchitectureContextAt,
    finiteModelContextShapeUp, finiteModelContextShapeDown]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · funext support atom
    rcases support with ⟨support⟩
    rcases atom with ⟨atom⟩
    rfl
  · funext axis
    rcases axis with ⟨axis⟩
    rfl
  · funext observable
    rcases observable with ⟨observable⟩
    rfl

/-! ## Raw context morphisms -/

/-- Lift all three maps of a raw context morphism by `ULift` conjugation. -/
def finiteModelLiftContextMorphism
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism W V) :
    Site.ContextMorphism
      (finiteModelLiftArchitectureContext.{u} W)
      (finiteModelLiftArchitectureContext.{u} V) where
  supportMap support := ULift.up (f.supportMap support.down)
  axisMap axis := ULift.up (f.axisMap axis.down)
  observableRestrict observable :=
    ULift.up (f.observableRestrict observable.down)

/-- The lifted support map is the lift of the actual source support map. -/
@[simp]
theorem finiteModelLiftContextMorphism_supportMap
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism W V) (support : W.Support) :
    (finiteModelLiftContextMorphism.{u} f).supportMap (ULift.up support) =
      ULift.up (f.supportMap support) :=
  rfl

/-- The lifted axis map is the lift of the actual source axis map. -/
@[simp]
theorem finiteModelLiftContextMorphism_axisMap
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism W V) (axis : W.Axis) :
    (finiteModelLiftContextMorphism.{u} f).axisMap (ULift.up axis) =
      ULift.up (f.axisMap axis) :=
  rfl

/-- The lifted observable restriction is the lift of the source restriction. -/
@[simp]
theorem finiteModelLiftContextMorphism_observableRestrict
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism W V) (observable : V.Observable) :
    (finiteModelLiftContextMorphism.{u} f).observableRestrict
        (ULift.up observable) =
      ULift.up (f.observableRestrict observable) :=
  rfl

/-- Canonical context-morphism lifting preserves the restriction role. -/
theorem finiteModelLiftContextMorphism_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {f : Site.ContextMorphism W V} (hf : f.IsRestriction) :
    (finiteModelLiftContextMorphism.{u} f).IsRestriction := by
  rcases hf with ⟨hsupport, haxis, hobservable, hnongenerating⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    exact hsupport hread
  · intro axis hread
    exact haxis hread
  · intro observable hread
    exact hobservable hread
  · intro support atom hread
    exact hnongenerating hread

/--
Reflect all three maps of an actual high context morphism through carrier shapes.
-/
noncomputable def finiteModelReflectContextMorphismAt
    {A B : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {X Y : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B)}
    (shapeX : FiniteModelContextCarrierShape W X)
    (shapeY : FiniteModelContextCarrierShape V Y)
    (f : Site.ContextMorphism X Y) :
    Site.ContextMorphism
      (finiteModelReflectArchitectureContextAt W X shapeX)
      (finiteModelReflectArchitectureContextAt V Y shapeY) where
  supportMap support := finiteModelContextShapeDown shapeY.support_eq
    (f.supportMap (finiteModelContextShapeUp shapeX.support_eq support))
  axisMap axis := finiteModelContextShapeDown shapeY.axis_eq
    (f.axisMap (finiteModelContextShapeUp shapeX.axis_eq axis))
  observableRestrict observable :=
    finiteModelContextShapeDown shapeX.observable_eq
      (f.observableRestrict
        (finiteModelContextShapeUp shapeY.observable_eq observable))

/-- Reflected support maps are the down-conjugates of the actual high maps. -/
theorem finiteModelReflectContextMorphismAt_supportMap
    {A B : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {X Y : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B)}
    (shapeX : FiniteModelContextCarrierShape W X)
    (shapeY : FiniteModelContextCarrierShape V Y)
    (f : Site.ContextMorphism X Y) (support : W.Support) :
    (finiteModelReflectContextMorphismAt shapeX shapeY f).supportMap support =
      finiteModelContextShapeDown shapeY.support_eq
        (f.supportMap (finiteModelContextShapeUp shapeX.support_eq support)) :=
  rfl

/-- Reflected axis maps are the down-conjugates of the actual high maps. -/
theorem finiteModelReflectContextMorphismAt_axisMap
    {A B : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {X Y : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B)}
    (shapeX : FiniteModelContextCarrierShape W X)
    (shapeY : FiniteModelContextCarrierShape V Y)
    (f : Site.ContextMorphism X Y) (axis : W.Axis) :
    (finiteModelReflectContextMorphismAt shapeX shapeY f).axisMap axis =
      finiteModelContextShapeDown shapeY.axis_eq
        (f.axisMap (finiteModelContextShapeUp shapeX.axis_eq axis)) :=
  rfl

/-- Reflected observable restrictions are the down-conjugates of the high maps. -/
theorem finiteModelReflectContextMorphismAt_observableRestrict
    {A B : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {X Y : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B)}
    (shapeX : FiniteModelContextCarrierShape W X)
    (shapeY : FiniteModelContextCarrierShape V Y)
    (f : Site.ContextMorphism X Y) (observable : V.Observable) :
    (finiteModelReflectContextMorphismAt shapeX shapeY f).observableRestrict
        observable =
      finiteModelContextShapeDown shapeX.observable_eq
        (f.observableRestrict
          (finiteModelContextShapeUp shapeY.observable_eq observable)) :=
  rfl

/-- Shape reflection preserves the restriction role of every actual high map. -/
theorem finiteModelReflectContextMorphismAt_isRestriction
    {A B : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {X Y : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u} B)}
    {shapeX : FiniteModelContextCarrierShape W X}
    {shapeY : FiniteModelContextCarrierShape V Y}
    {f : Site.ContextMorphism X Y} (hf : f.IsRestriction) :
    (finiteModelReflectContextMorphismAt shapeX shapeY f).IsRestriction := by
  rcases hf with ⟨hsupport, haxis, hobservable, hnongenerating⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    have hresult := hsupport hread
    simpa only [finiteModelReflectContextMorphismAt,
      finiteModelReflectArchitectureContextAt,
      finiteModelContextShape_up_down] using hresult
  · intro axis hread
    have hresult := haxis hread
    simpa only [finiteModelReflectContextMorphismAt,
      finiteModelReflectArchitectureContextAt,
      finiteModelContextShape_up_down] using hresult
  · intro observable hread
    have hresult := hobservable hread
    simpa only [finiteModelReflectContextMorphismAt,
      finiteModelReflectArchitectureContextAt,
      finiteModelContextShape_up_down] using hresult
  · intro support atom hread
    have hreadHigh :
        Y.minimal.supportReads
          (f.supportMap
            (finiteModelContextShapeUp shapeX.support_eq support))
          (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
      simpa only [finiteModelReflectContextMorphismAt,
        finiteModelReflectArchitectureContextAt,
        finiteModelContextShape_up_down] using hread
    have hhigh := hnongenerating hreadHigh
    simpa [finiteModelLiftArchitectureObject,
      finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using hhigh

/-- Reflect a high morphism whose endpoints are canonical lifted contexts. -/
noncomputable def finiteModelReflectLiftedContextMorphism
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism
      (finiteModelLiftArchitectureContext.{u} W)
      (finiteModelLiftArchitectureContext.{u} V)) :
    Site.ContextMorphism W V :=
  finiteModelReflectContextMorphismAt
    (finiteModelLiftArchitectureContext_shape.{u} W)
    (finiteModelLiftArchitectureContext_shape.{u} V) f

/-- Reflecting a lifted raw context morphism recovers all three source maps. -/
@[simp]
theorem finiteModelReflectLiftedContextMorphism_lift
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism W V) :
    finiteModelReflectLiftedContextMorphism
        (finiteModelLiftContextMorphism.{u} f) = f := by
  rcases f with ⟨supportMap, axisMap, observableRestrict⟩
  rfl

/-- Lifting the reflection of a lifted-endpoint map recovers the high map. -/
@[simp]
theorem finiteModelLiftContextMorphism_reflectLifted
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    (f : Site.ContextMorphism
      (finiteModelLiftArchitectureContext.{u} W)
      (finiteModelLiftArchitectureContext.{u} V)) :
    finiteModelLiftContextMorphism.{u}
        (finiteModelReflectLiftedContextMorphism f) = f := by
  rcases f with ⟨supportMap, axisMap, observableRestrict⟩
  simp [finiteModelReflectLiftedContextMorphism,
    finiteModelReflectContextMorphismAt,
    finiteModelLiftContextMorphism,
    finiteModelContextShapeUp, finiteModelContextShapeDown]
  refine ⟨?_, ?_, ?_⟩ <;> funext value <;> exact ULift.up_down _

/-- Restriction reflection is exact on canonical lifted endpoints. -/
theorem finiteModelReflectLiftedContextMorphism_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    {W V : Site.ArchitectureContext A}
    {f : Site.ContextMorphism
      (finiteModelLiftArchitectureContext.{u} W)
      (finiteModelLiftArchitectureContext.{u} V)}
    (hf : f.IsRestriction) :
    (finiteModelReflectLiftedContextMorphism f).IsRestriction :=
  finiteModelReflectContextMorphismAt_isRestriction hf

/-! ## Canonical context-category inclusion -/

/-- The finite-model context category over a low architecture object. -/
abbrev FiniteModelLowContextCategory
    (A : ArchitectureObject FiniteModel.carrier) :=
  Site.ContextCategoryObject (Site.contextMorphismPreorderCategory A)

/-- The high context category over the canonical lift of a low object. -/
abbrev FiniteModelHighContextCategory
    (A : ArchitectureObject FiniteModel.carrier) :=
  Site.ContextCategoryObject
    (Site.contextMorphismPreorderCategory
      (finiteModelLiftArchitectureObject.{u} A))

/--
Exact low context-equivalence output still required from an actual normalized
generated prefix.  This alias fixes the downstream type without accepting a
functor, image witness, or equivalence from the caller.
-/
abbrev FiniteGeneratedReflectedContextEquivalenceOutput
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :=
  Site.ContextCategoryObject
      (((finiteGeneratedOuterInput input base).lowGeneratedLift.domain).algebra.contextPreorder) ≌
    Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)

/-- Lift a wrapped object of the canonical finite-model context category. -/
def finiteModelLiftContextCategoryObject
    {A : ArchitectureObject FiniteModel.carrier}
    (W : FiniteModelLowContextCategory A) :
    FiniteModelHighContextCategory.{u} A where
  ctx := finiteModelLiftArchitectureContext.{u} W.ctx

/--
The canonical context lift is a functor between the low category and the full
high context category.  Its object image consists of canonically lifted
contexts, and its arrows are generated by lifting the selected readable maps.
-/
noncomputable def finiteModelLiftContextFunctor
    (A : ArchitectureObject FiniteModel.carrier) :
    FiniteModelLowContextCategory A ⥤ FiniteModelHighContextCategory.{u} A where
  obj := finiteModelLiftContextCategoryObject
  map {W V} f := by
    apply homOfLE
    change ∃ g : Site.ContextMorphism
        (finiteModelLiftArchitectureContext.{u} W.ctx)
        (finiteModelLiftArchitectureContext.{u} V.ctx), g.IsRestriction
    let C := Site.contextMorphismPreorderCategory A
    exact ⟨finiteModelLiftContextMorphism.{u} (C.morphism (leOfHom f)),
      finiteModelLiftContextMorphism_isRestriction
        (C.morphism_isRestriction (leOfHom f))⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The canonical context lift is faithful because both context categories are thin. -/
instance finiteModelLiftContextFunctor_faithful
    (A : ArchitectureObject FiniteModel.carrier) :
    (finiteModelLiftContextFunctor.{u} A).Faithful where
  map_injective _ := Subsingleton.elim _ _

/--
The canonical context lift is full: a high arrow between lifted endpoints
reflects to a low readable restriction.
-/
noncomputable instance finiteModelLiftContextFunctor_full
    (A : ArchitectureObject FiniteModel.carrier) :
    (finiteModelLiftContextFunctor.{u} A).Full where
  map_surjective {W V} f := by
    let D := Site.contextMorphismPreorderCategory
      (finiteModelLiftArchitectureObject.{u} A)
    let highMorphism := D.morphism (leOfHom f)
    have highRestriction : highMorphism.IsRestriction :=
      D.morphism_isRestriction (leOfHom f)
    let lowMorphism : Site.ContextMorphism W.ctx V.ctx :=
      finiteModelReflectLiftedContextMorphism highMorphism
    have lowRestriction : lowMorphism.IsRestriction :=
      finiteModelReflectLiftedContextMorphism_isRestriction highRestriction
    refine ⟨homOfLE ?_, Subsingleton.elim _ _⟩
    exact ⟨lowMorphism, lowRestriction⟩

/-!
## Next generated construction

For an actual normalized generated upper `H`, the next definition must produce
the following value without accepting shape data from its caller:

```lean
noncomputable def finiteGeneratedReflectedContextEquivalence
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    FiniteGeneratedReflectedContextEquivalenceOutput input base
```

Its forward and inverse object shapes are generated internally from
`H.upper.equationTransport.contextEquivalence` and the full architecture-object
image graph.  The forward and inverse maps are then lifted, mapped by the actual
high functors, and reflected by the definitions above; their unit and counit are
reflections of the actual high unit and counit.  This signature is recorded here
only as the downstream consumer of the primitive API.
-/

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
