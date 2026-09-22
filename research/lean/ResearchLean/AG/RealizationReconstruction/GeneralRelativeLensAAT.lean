import ResearchLean.AG.RealizationReconstruction.GeneralRelativeLensTyped
import ResearchLean.AG.RealizationReconstruction.CSAATArchitectureObjects
import Formal.Util.AssertStandardAxioms

/-!
The actual AAT typed construction of the four lens roles and the two named
operations. A selected reference view is used only for the selected quantity
of the constructed architecture objects, as in construction 1.39. Morphisms
need not preserve that selected reference: the typed category reads the role
carriers and named operation functions of the constructed objects.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace GeneralLens

/-- The four role names of construction 1.39. -/
inductive AATRole
  | state | view | read | write

/-- The parameter used by the existing finite-reference AAT Atom vocabulary. -/
def aatInput (L : GeneralLens.{u}) (v₀ : L.View) : LensFamilyInput.{u} where
  View := L.View
  reference := v₀

def AATRole.carrier (L : GeneralLens.{u}) : AATRole → Type u
  | .state => L.State
  | .view => L.View
  | .read => L.State
  | .write => L.State × L.View

def AATRole.atom (L : GeneralLens.{u}) (v₀ : L.View) :
    AATRole → LensAATAtom (aatInput L v₀)
  | .state => .state
  | .view => .view
  | .read => .read
  | .write => .write

/-- The actual ArchitectureObject of each role, with its exact semantic
carrier as structure data and the selected reference as quantity. -/
def aatRoleObject (L : GeneralLens.{u}) (v₀ : L.View) (role : AATRole) :
    ArchitectureObject (lensAATCarrier (aatInput L v₀)) where
  configuration := typedRoleConfiguration (role.atom L v₀)
  StructureMaps := Type u
  SelectedQuantities := ULift.{u + 1, u} L.View
  structureMaps := role.carrier L
  selectedQuantities := ULift.up v₀

@[simp] theorem aatRoleObject_carrier (L : GeneralLens.{u})
    (v₀ : L.View) (role : AATRole) :
    (aatRoleObject L v₀ role).structureMaps = role.carrier L := rfl

/-- The actual named AAT operation for the read arrow. -/
def aatGetOperation (L : GeneralLens.{u}) (v₀ : L.View) :
    Operation (lensAATCarrier (aatInput L v₀)) where
  source := aatRoleObject L v₀ .read
  target := aatRoleObject L v₀ .view
  configurationMap := lensNamedConfigurationHom .get .read .view (by simp)

/-- The actual named AAT operation for the update arrow. -/
def aatPutOperation (L : GeneralLens.{u}) (v₀ : L.View) :
    Operation (lensAATCarrier (aatInput L v₀)) where
  source := aatRoleObject L v₀ .write
  target := aatRoleObject L v₀ .state
  configurationMap := lensNamedConfigurationHom .put .write .state (by simp)

/-- The semantic function attached to the constructed AAT get operation. -/
def aatGetFunction (L : GeneralLens.{u}) (_v₀ : L.View) : L.State → L.View :=
  L.get

/-- The semantic function attached to the constructed AAT put operation. -/
def aatPutFunction (L : GeneralLens.{u}) (_v₀ : L.View) :
    L.State × L.View → L.State := fun x => L.put x.1 x.2

/-- The complete named operation produced by construction 1.39: its AAT
operation fixes the name and endpoints, while the semantic function is
carried together with it. This is constructed from a lens, not assumed of it. -/
structure AATSemanticOperation (L : GeneralLens.{u}) (v₀ : L.View) where
  source : AATRole
  target : AATRole
  name : LensAATAtom (aatInput L v₀)
  operation : Operation (lensAATCarrier (aatInput L v₀))
  operation_source : operation.source = aatRoleObject L v₀ source
  operation_target : operation.target = aatRoleObject L v₀ target
  operation_name : operation.configurationMap.atomMap .point = name
  semanticFunction : (aatRoleObject L v₀ source).structureMaps →
    (aatRoleObject L v₀ target).structureMaps

/-- The get name, AAT operation, and original semantic function in one value. -/
def aatGetSemanticOperation (L : GeneralLens.{u}) (v₀ : L.View) :
    AATSemanticOperation L v₀ where
  source := .read
  target := .view
  name := .get
  operation := aatGetOperation L v₀
  operation_source := rfl
  operation_target := rfl
  operation_name := rfl
  semanticFunction := aatGetFunction L v₀

/-- The put name, AAT operation, and original semantic function in one value. -/
def aatPutSemanticOperation (L : GeneralLens.{u}) (v₀ : L.View) :
    AATSemanticOperation L v₀ where
  source := .write
  target := .state
  name := .put
  operation := aatPutOperation L v₀
  operation_source := rfl
  operation_target := rfl
  operation_name := rfl
  semanticFunction := aatPutFunction L v₀

@[simp] theorem aatGetFunction_eq (L : GeneralLens.{u}) (v₀ : L.View) :
    aatGetFunction L v₀ = L.get := rfl

@[simp] theorem aatPutFunction_eq (L : GeneralLens.{u}) (v₀ : L.View) :
    aatPutFunction L v₀ = fun x => L.put x.1 x.2 := rfl

/-- Read exactly the four role carriers and the two named semantic operations
from the AAT construction above. -/
def aatTypedReadback (L : GeneralLens.{u}) (v₀ : L.View) : TypedLens.{u} where
  State := (aatRoleObject L v₀ .state).structureMaps
  View := (aatRoleObject L v₀ .view).structureMaps
  Read := (aatRoleObject L v₀ .read).structureMaps
  Write := (aatRoleObject L v₀ .write).structureMaps
  readState := Equiv.refl _
  writeStateView := Equiv.refl _
  getOp := (aatGetSemanticOperation L v₀).semanticFunction
  putOp := (aatPutSemanticOperation L v₀).semanticFunction
  put_get := L.put_get
  get_put := L.get_put
  put_put := L.put_put

/-- Construction 1.39's AAT objects and named operations read back to the
same typed object used by the fully faithful functor. -/
theorem aatTypedReadback_eq_toTyped (L : GeneralLens.{u}) (v₀ : L.View) :
    aatTypedReadback L v₀ = L.toTyped := rfl

/-- On a finite-reference lens, the generalized role object is precisely the
existing AAT role object, not a second abstract operation model. -/
theorem aatRoleObject_fixed_state {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatRoleObject (ofLensRealization X) input.reference .state =
      lensAATArchitectureObject
        (.state : LensPrimitiveObject input X) := rfl

theorem aatRoleObject_fixed_view {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatRoleObject (ofLensRealization X) input.reference .view =
      lensAATArchitectureObject
        (.view : LensPrimitiveObject input X) := rfl

theorem aatRoleObject_fixed_read {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatRoleObject (ofLensRealization X) input.reference .read =
      lensAATArchitectureObject
        (.read : LensPrimitiveObject input X) := rfl

theorem aatRoleObject_fixed_write {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatRoleObject (ofLensRealization X) input.reference .write =
      lensAATArchitectureObject
        (.write : LensPrimitiveObject input X) := rfl

theorem aatGetOperation_fixed {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatGetOperation (ofLensRealization X) input.reference =
      lensGetAATOperation X := rfl

theorem aatPutOperation_fixed {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatPutOperation (ofLensRealization X) input.reference =
      lensPutAATOperation X := rfl

theorem aatGetFunction_fixed {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatGetFunction (ofLensRealization X) input.reference =
      lensGetAATFunction X := rfl

theorem aatPutFunction_fixed {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    aatPutFunction (ofLensRealization X) input.reference =
      lensPutAATFunction X := rfl

/-- A reference view is carried with each object for construction 1.39. It
does not constrain relative morphisms or their visible maps. -/
structure Pointed where
  lens : GeneralLens.{u}
  reference : lens.View

instance : Category Pointed.{u} where
  Hom X Y := X.lens ⟶ Y.lens
  id X := 𝟙 X.lens
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

/-- An independently stored AAT typed object. Its carriers, selected reference,
lens laws, four architecture objects, and two named operations are target data;
no source `Pointed` object is retained. The equations identify the AAT data
with construction 1.39 on these carriers and semantic functions. -/
structure AATConstructed where
  State : Type u
  View : Type u
  reference : View
  get : State → View
  put : State → View → State
  put_get : ∀ c, put c (get c) = c
  get_put : ∀ c v, get (put c v) = v
  put_put : ∀ c v w, put (put c v) w = put c w
  stateObject : ArchitectureObject
    (lensAATCarrier (aatInput
      { State := State, View := View, get := get, put := put,
        put_get := put_get, get_put := get_put, put_put := put_put } reference))
  viewObject : ArchitectureObject
    (lensAATCarrier (aatInput
      { State := State, View := View, get := get, put := put,
        put_get := put_get, get_put := get_put, put_put := put_put } reference))
  readObject : ArchitectureObject
    (lensAATCarrier (aatInput
      { State := State, View := View, get := get, put := put,
        put_get := put_get, get_put := get_put, put_put := put_put } reference))
  writeObject : ArchitectureObject
    (lensAATCarrier (aatInput
      { State := State, View := View, get := get, put := put,
        put_get := put_get, get_put := get_put, put_put := put_put } reference))
  getOperation : AATSemanticOperation
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference
  putOperation : AATSemanticOperation
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference
  getSemantic : State → View
  putSemantic : State × View → State
  stateObject_eq : stateObject = aatRoleObject
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference .state
  viewObject_eq : viewObject = aatRoleObject
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference .view
  readObject_eq : readObject = aatRoleObject
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference .read
  writeObject_eq : writeObject = aatRoleObject
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference .write
  getOperation_eq : getOperation = aatGetSemanticOperation
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference
  putOperation_eq : putOperation = aatPutSemanticOperation
    { State := State, View := View, get := get, put := put,
      put_get := put_get, get_put := get_put, put_put := put_put } reference
  getSemantic_eq : getSemantic = get
  putSemantic_eq : putSemantic = fun x => put x.1 x.2

/-- Construction 1.39, with every AAT component installed as object data. -/
def toAATConstructed (X : Pointed.{u}) : AATConstructed.{u} where
  State := X.lens.State
  View := X.lens.View
  reference := X.reference
  get := X.lens.get
  put := X.lens.put
  put_get := X.lens.put_get
  get_put := X.lens.get_put
  put_put := X.lens.put_put
  stateObject := aatRoleObject X.lens X.reference .state
  viewObject := aatRoleObject X.lens X.reference .view
  readObject := aatRoleObject X.lens X.reference .read
  writeObject := aatRoleObject X.lens X.reference .write
  stateObject_eq := rfl
  viewObject_eq := rfl
  readObject_eq := rfl
  writeObject_eq := rfl
  getOperation := aatGetSemanticOperation X.lens X.reference
  putOperation := aatPutSemanticOperation X.lens X.reference
  getSemantic := X.lens.get
  putSemantic := fun x => X.lens.put x.1 x.2
  getOperation_eq := rfl
  putOperation_eq := rfl
  getSemantic_eq := rfl
  putSemantic_eq := rfl

namespace AATConstructed

/-- Definition 1.42 with a variable visible map. The equations preserve the
stored semantic readings certified by the two named AAT operation packages. -/
@[ext]
structure Hom (X Y : AATConstructed.{u}) where
  state : X.State → Y.State
  view : X.View → Y.View
  read : X.State → Y.State
  write : X.State × X.View → Y.State × Y.View
  read_coord : ∀ c, read c = state c
  write_coord : ∀ c,
    write c = (state c.1, view c.2)
  get_comm : ∀ c,
    Y.getSemantic (read c) = view (X.getSemantic c)
  put_comm : ∀ c,
    Y.putSemantic (write c) = state (X.putSemantic c)

instance : Category AATConstructed.{u} where
  Hom := Hom
  id X :=
    { state := id, view := id, read := id, write := id
      read_coord := fun _ => rfl
      write_coord := fun _ => rfl
      get_comm := fun _ => rfl
      put_comm := fun _ => rfl }
  comp f g :=
    { state := g.state ∘ f.state
      view := g.view ∘ f.view
      read := g.read ∘ f.read
      write := g.write ∘ f.write
      read_coord := fun c => by
        simp only [Function.comp_apply, g.read_coord, f.read_coord]
      write_coord := fun c => by
        simp only [Function.comp_apply, g.write_coord, f.write_coord]
      get_comm := fun c => by
        simp only [Function.comp_apply, g.get_comm, f.get_comm]
      put_comm := fun c => by
        simp only [Function.comp_apply, g.put_comm, f.put_comm] }
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; ext <;> rfl

end AATConstructed

/-- A relative lens morphism acts on all four constructed AAT role objects
and commutes with the semantic functions of the named get and put operations. -/
def toAATConstructedHom {X Y : Pointed.{u}} (f : X ⟶ Y) :
    toAATConstructed X ⟶ toAATConstructed Y where
  state := f.state
  view := f.view
  read := f.state
  write := Prod.map f.state f.view
  read_coord := fun _ => rfl
  write_coord := fun _ => rfl
  get_comm := f.get_comm
  put_comm := fun c => (f.put_comm c.1 c.2).symm

/-- The named AAT operations recover both relative preservation equations. -/
def fromAATConstructedHom {X Y : Pointed.{u}}
    (f : toAATConstructed X ⟶ toAATConstructed Y) : X ⟶ Y where
  state := f.state
  view := f.view
  get_comm c := by
    have hr := f.read_coord c
    have hg := f.get_comm c
    change f.read c = f.state c at hr
    change Y.lens.get (f.read c) = f.view (X.lens.get c) at hg
    rw [← hr]
    exact hg
  put_comm c v := by
    have hw := f.write_coord (c, v)
    have hp := f.put_comm (c, v)
    change f.write (c, v) = (f.state c, f.view v) at hw
    change Y.lens.put (f.write (c, v)).1 (f.write (c, v)).2 =
      f.state (X.lens.put c v) at hp
    rw [hw] at hp
    exact hp.symm

/-- Hom recovery is an actual equivalence for the named AAT construction. -/
def homEquivAATConstructed (X Y : Pointed.{u}) :
    (X ⟶ Y) ≃ (toAATConstructed X ⟶ toAATConstructed Y) where
  toFun := toAATConstructedHom
  invFun := fromAATConstructedHom
  left_inv f := by apply Hom.ext <;> rfl
  right_inv f := by
    apply AATConstructed.Hom.ext
    · rfl
    · rfl
    · funext c
      exact (f.read_coord c).symm
    · funext c
      exact (f.write_coord c).symm

/-- The construction 1.39 functor into actual named AAT typed objects. -/
def aatConstructedFunctor : Pointed.{u} ⥤ AATConstructed.{u} where
  obj := toAATConstructed
  map := toAATConstructedHom
  map_id X := by apply AATConstructed.Hom.ext <;> rfl
  map_comp f g := by apply AATConstructed.Hom.ext <;> rfl

/-- Relative morphisms, including visible changes, are exactly the maps of
the generated AAT objects that preserve their two named operations. -/
def aatConstructedFunctorFullyFaithful : aatConstructedFunctor.FullyFaithful where
  preimage := fromAATConstructedHom
  map_preimage f := (homEquivAATConstructed _ _).right_inv f
  preimage_map f := (homEquivAATConstructed _ _).left_inv f

/-- The object map uses the actual AAT role objects and named operations,
then reads their exact carriers and semantic functions. -/
def aatTypedFunctor : Pointed.{u} ⥤ TypedLens.{u} where
  obj X := aatTypedReadback X.lens X.reference
  map f := toTypedHom f
  map_id X := by
    apply TypedLens.Hom.ext <;> rfl
  map_comp f g := by
    apply TypedLens.Hom.ext <;> rfl

/-- Construction 1.39 with independently selected reference views is full and
faithful for all relative lens morphisms, including view changes. -/
def aatTypedFunctorFullyFaithful : aatTypedFunctor.FullyFaithful where
  preimage f := fromTypedHom f
  map_preimage f := (homEquivTypedHom _ _).right_inv f
  preimage_map f := (homEquivTypedHom _ _).left_inv f

end GeneralLens

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
