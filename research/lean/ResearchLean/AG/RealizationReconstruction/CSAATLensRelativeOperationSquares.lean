import ResearchLean.AG.RealizationReconstruction.CSAATForwardMorphisms
import ResearchLean.AG.RealizationReconstruction.FixedFLensConnection
import Formal.Util.AssertStandardAxioms

/-!
# Relative directed lens operation squares

This module retains one state map and one possibly nontrivial visible map in
both the named `get` and `put` squares.  It includes arbitrary directed maps,
the fixed-visible L2 interface, and the equivalence-valued L5 specialization;
it does not coerce a noninvertible map into the exact-equivalence geometry API.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- A lens change relative to a possibly nontrivial visible-carrier map.  The
same state map and visible map occur in both named-operation squares. -/
@[ext]
structure LensAATRelativeForwardMorphism {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) where
  stateMap : X.Carrier → Y.Carrier
  visibleMap : input.View → input.View
  get_naturality : ∀ state,
    Y.get (stateMap state) = visibleMap (X.get state)
  put_naturality : ∀ state requested,
    stateMap (X.put state requested) =
      Y.put (stateMap state) (visibleMap requested)

namespace LensAATRelativeForwardMorphism

/-- The typed map on each of the four exact lens object roles is respectively
`h`, `u`, `h`, and `h × u`. -/
def typedObjectMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (role : LensPrimitiveObject input X) :
    role.Carrier → (lensRoleTransport (Y := Y) role).Carrier := by
  cases role with
  | state => exact f.stateMap
  | view => exact f.visibleMap
  | read => exact f.stateMap
  | write => exact fun stateView =>
      (f.stateMap stateView.1, f.visibleMap stateView.2)

@[simp] theorem typedObjectMap_state {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) (state : X.Carrier) :
    f.typedObjectMap (.state : LensPrimitiveObject input X) state =
      f.stateMap state := rfl

@[simp] theorem typedObjectMap_view {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) (view : input.View) :
    f.typedObjectMap (.view : LensPrimitiveObject input X) view =
      f.visibleMap view := rfl

@[simp] theorem typedObjectMap_read {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) (state : X.Carrier) :
    f.typedObjectMap (.read : LensPrimitiveObject input X) state =
      f.stateMap state := rfl

@[simp] theorem typedObjectMap_write {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (state : X.Carrier) (view : input.View) :
    f.typedObjectMap (.write : LensPrimitiveObject input X) (state, view) =
      (f.stateMap state, f.visibleMap view) := rfl

/-- The relative typed maps commute with the actual named `get` operation. -/
theorem get_square {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) (state : X.Carrier) :
    f.typedObjectMap (.view : LensPrimitiveObject input X)
        (lensOperationFunction
          (PrimitiveOperation.lensGet (input := input) (X := X)) state) =
      lensOperationFunction
        (PrimitiveOperation.lensGet (input := input) (X := Y))
        (f.typedObjectMap (.read : LensPrimitiveObject input X) state) := by
  exact (f.get_naturality state).symm

/-- The relative typed maps commute with the actual named `put` operation. -/
theorem put_square {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (state : X.Carrier) (view : input.View) :
    f.typedObjectMap (.state : LensPrimitiveObject input X)
        (lensOperationFunction
          (PrimitiveOperation.lensPut (input := input) (X := X)) (state, view)) =
      lensOperationFunction
        (PrimitiveOperation.lensPut (input := input) (X := Y))
        (f.typedObjectMap (.write : LensPrimitiveObject input X) (state, view)) := by
  exact f.put_naturality state view

/-- Embed the pre-existing fixed-visible morphism by taking `u = id`. -/
def ofForwardMorphism {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATRelativeForwardMorphism X Y where
  stateMap := f.stateMap
  visibleMap := _root_.id
  get_naturality := f.get_naturality
  put_naturality := f.put_naturality

/-- A relative morphism whose visible map is extensionally the identity gives
the existing fixed-visible morphism. -/
def toForwardMorphism {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (visible_eq : f.visibleMap = _root_.id) :
    LensAATForwardMorphism X Y where
  stateMap := f.stateMap
  get_naturality state := by
    change Y.get (f.stateMap state) = X.get state
    calc
      Y.get (f.stateMap state) = f.visibleMap (X.get state) :=
        f.get_naturality state
      _ = X.get state := by rw [visible_eq]; rfl
  put_naturality state view := by
    change f.stateMap (X.put state view) = Y.put (f.stateMap state) view
    calc
      f.stateMap (X.put state view) =
          Y.put (f.stateMap state) (f.visibleMap view) :=
        f.put_naturality state view
      _ = Y.put (f.stateMap state) view := by rw [visible_eq]; rfl

/-- Fixed-visible morphisms are exactly the fiber of relative morphisms over
the identity visible map. -/
def identityVisibleEquiv {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) :
    LensAATForwardMorphism X Y ≃
      { f : LensAATRelativeForwardMorphism X Y //
        f.visibleMap = _root_.id } where
  toFun f := ⟨ofForwardMorphism f, rfl⟩
  invFun f := toForwardMorphism f.1 f.2
  left_inv f := by
    apply LensAATForwardMorphism.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply LensAATRelativeForwardMorphism.ext
    · rfl
    · exact f.2.symm

/-- Every independently defined invertible lens change supplies a relative
typed AAT morphism with exactly its state and visible maps. -/
def ofLensInvertibleChange {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    {visible : Equiv.Perm input.View}
    (change : FixedFLensConnection.LensInvertibleChange X Y visible) :
    LensAATRelativeForwardMorphism X Y where
  stateMap := change.h
  visibleMap := visible
  get_naturality := change.get_naturality
  put_naturality := change.put_naturality

/-- Conversely, equivalence-valued realizations of the two computational maps
recover the independent `LensInvertibleChange`; the equalities merely identify
the supplied equivalences with the already constructed relative actions. -/
def toLensInvertibleChange {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (h : X.Carrier ≃ Y.Carrier) (visible : Equiv.Perm input.View)
    (h_toFun : h.toFun = f.stateMap)
    (visible_toFun : visible.toFun = f.visibleMap) :
    FixedFLensConnection.LensInvertibleChange X Y visible where
  h := h
  get_naturality state := by
    change Y.get (h.toFun state) = visible.toFun (X.get state)
    rw [h_toFun, visible_toFun]
    exact f.get_naturality state
  put_naturality state requested := by
    change h.toFun (X.put state requested) =
      Y.put (h.toFun state) (visible.toFun requested)
    rw [h_toFun, visible_toFun]
    exact f.put_naturality state requested

@[simp] theorem ofLensInvertibleChange_stateMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    {visible : Equiv.Perm input.View}
    (change : FixedFLensConnection.LensInvertibleChange X Y visible) :
    (ofLensInvertibleChange change).stateMap = change.h := rfl

@[simp] theorem ofLensInvertibleChange_visibleMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    {visible : Equiv.Perm input.View}
    (change : FixedFLensConnection.LensInvertibleChange X Y visible) :
    (ofLensInvertibleChange change).visibleMap = visible := rfl

@[simp] theorem toLensInvertibleChange_ofLensInvertibleChange
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    {visible : Equiv.Perm input.View}
    (change : FixedFLensConnection.LensInvertibleChange X Y visible) :
    toLensInvertibleChange (ofLensInvertibleChange change)
      change.h visible rfl rfl = change := by
  apply FixedFLensConnection.LensInvertibleChange.ext
  rfl

theorem ofLensInvertibleChange_toLensInvertibleChange
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (h : X.Carrier ≃ Y.Carrier) (visible : Equiv.Perm input.View)
    (h_toFun : h.toFun = f.stateMap)
    (visible_toFun : visible.toFun = f.visibleMap) :
    ofLensInvertibleChange
        (toLensInvertibleChange f h visible h_toFun visible_toFun) = f := by
  apply LensAATRelativeForwardMorphism.ext
  · exact h_toFun
  · exact visible_toFun

end LensAATRelativeForwardMorphism

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
