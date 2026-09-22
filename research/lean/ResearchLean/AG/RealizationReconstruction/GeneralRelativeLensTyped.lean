import ResearchLean.AG.RealizationReconstruction.GeneralRelativeLens
import Formal.Util.AssertStandardAxioms

/-!
The four typed roles of a lens: state, view, read input, and write input.
The read and write input carriers may have independent presentations, with
specified coordinate equivalences to state and state × view.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- A typed presentation of the two lens operations. -/
structure TypedLens where
  State : Type u
  View : Type u
  Read : Type u
  Write : Type u
  readState : Read ≃ State
  writeStateView : Write ≃ State × View
  getOp : Read → View
  putOp : Write → State
  put_get : ∀ c, putOp (writeStateView.symm (c, getOp (readState.symm c))) = c
  get_put : ∀ c v,
    getOp (readState.symm (putOp (writeStateView.symm (c, v)))) = v
  put_put : ∀ c v w,
    putOp (writeStateView.symm
      (putOp (writeStateView.symm (c, v)), w)) =
      putOp (writeStateView.symm (c, w))

namespace TypedLens

/-- A typed morphism has a map on every role and commutes with the two
operations and with the structural input coordinates. -/
@[ext]
structure Hom (X Y : TypedLens.{u}) where
  state : X.State → Y.State
  view : X.View → Y.View
  read : X.Read → Y.Read
  write : X.Write → Y.Write
  read_coord : ∀ x, Y.readState (read x) = state (X.readState x)
  write_coord : ∀ x,
    Y.writeStateView (write x) =
      (state (X.writeStateView x).1, view (X.writeStateView x).2)
  get_comm : ∀ x, Y.getOp (read x) = view (X.getOp x)
  put_comm : ∀ x, Y.putOp (write x) = state (X.putOp x)

instance : Category TypedLens.{u} where
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
      read_coord := fun x => by
        simp only [Function.comp_apply, g.read_coord, f.read_coord]
      write_coord := fun x => by
        simp only [Function.comp_apply, g.write_coord, f.write_coord]
      get_comm := fun x => by
        simp only [Function.comp_apply, g.get_comm, f.get_comm]
      put_comm := fun x => by
        simp only [Function.comp_apply, g.put_comm, f.put_comm] }
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; ext <;> rfl

end TypedLens

namespace GeneralLens

/-- Construct the four actual typed roles from a semantic lens. -/
def toTyped (L : GeneralLens.{u}) : TypedLens.{u} where
  State := L.State
  View := L.View
  Read := L.State
  Write := L.State × L.View
  readState := Equiv.refl _
  writeStateView := Equiv.refl _
  getOp := L.get
  putOp := fun x => L.put x.1 x.2
  put_get := L.put_get
  get_put := L.get_put
  put_put := L.put_put

/-- A relative semantic map acts on every typed role. -/
def toTypedHom {L M : GeneralLens.{u}} (f : L ⟶ M) :
    L.toTyped ⟶ M.toTyped where
  state := f.state
  view := f.view
  read := f.state
  write := Prod.map f.state f.view
  read_coord := fun _ => rfl
  write_coord := fun _ => rfl
  get_comm := f.get_comm
  put_comm := fun x => (f.put_comm x.1 x.2).symm

/-- Read back the two semantic maps and their preservation laws from the
typed operations. -/
def fromTypedHom {L M : GeneralLens.{u}}
    (f : L.toTyped ⟶ M.toTyped) : L ⟶ M where
  state := f.state
  view := f.view
  get_comm c := by
    have hr := f.read_coord c
    have hg := f.get_comm c
    change f.read c = f.state c at hr
    change M.get (f.read c) = f.view (L.get c) at hg
    rw [← hr]
    exact hg
  put_comm c v := by
    have hw := f.write_coord (c, v)
    have hp := f.put_comm (c, v)
    change f.write (c, v) = (f.state c, f.view v) at hw
    change M.put (f.write (c, v)).1 (f.write (c, v)).2 =
      f.state (L.put c v) at hp
    rw [hw] at hp
    exact hp.symm

/-- Every typed map between generated objects is uniquely determined by its
state and view maps; the operations force the relative lens equations. -/
def homEquivTypedHom (L M : GeneralLens.{u}) :
    (L ⟶ M) ≃ (L.toTyped ⟶ M.toTyped) where
  toFun := toTypedHom
  invFun := fromTypedHom
  left_inv f := by
    apply Hom.ext <;> rfl
  right_inv f := by
    apply TypedLens.Hom.ext
    · rfl
    · rfl
    · funext x
      exact (f.read_coord x).symm
    · funext x
      exact (f.write_coord x).symm

/-- The generated typed construction is a functor on the general relative
lens category. -/
def typedFunctor : GeneralLens.{u} ⥤ TypedLens.{u} where
  obj := toTyped
  map := toTypedHom
  map_id X := by
    apply TypedLens.Hom.ext <;> rfl
  map_comp f g := by
    apply TypedLens.Hom.ext <;> rfl

/-- Both fullness and faithfulness hold with varying state and view types. -/
def typedFunctorFullyFaithful : typedFunctor.FullyFaithful where
  preimage := fromTypedHom
  map_preimage f := (homEquivTypedHom _ _).right_inv f
  preimage_map f := (homEquivTypedHom _ _).left_inv f

end GeneralLens

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
