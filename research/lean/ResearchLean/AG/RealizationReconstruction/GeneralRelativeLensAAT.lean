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
  getOp := aatGetFunction L v₀
  putOp := aatPutFunction L v₀
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
