import ResearchLean.AG.RealizationReconstruction.GeneralRelativeLensTyped
import ResearchLean.AG.RealizationReconstruction.CSAATLensRelativeOperationSquares
import Formal.Util.AssertStandardAxioms

/-!
Comparison with the existing finite-reference AAT lens API. The general
relative theory retains its arbitrary source and target views; this bridge
specializes only at the existing API's shared view and reference.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace GeneralLens

/-- Embed an existing relative AAT morphism in the general relative category,
retaining both maps and both preservation equations. -/
def ofAATRelative {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) :
    ofLensRealization X ⟶ ofLensRealization Y where
  state := f.stateMap
  view := f.visibleMap
  get_comm := f.get_naturality
  put_comm := f.put_naturality

/-- Read a general morphism on the existing objects back into the existing
relative typed-operation API. -/
def toAATRelative {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : ofLensRealization X ⟶ ofLensRealization Y) :
    LensAATRelativeForwardMorphism X Y where
  stateMap := f.state
  visibleMap := f.view
  get_naturality := f.get_comm
  put_naturality := f.put_comm

/-- The bridge is a bijection on every existing pair of lens objects. -/
def aatRelativeEquiv {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) :
    LensAATRelativeForwardMorphism X Y ≃
      (ofLensRealization X ⟶ ofLensRealization Y) where
  toFun := ofAATRelative
  invFun := toAATRelative
  left_inv f := by
    apply LensAATRelativeForwardMorphism.ext <;> rfl
  right_inv f := by
    apply Hom.ext <;> rfl

theorem ofAATRelative_state {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) :
    (ofAATRelative f).state = f.stateMap := rfl

theorem ofAATRelative_view {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y) :
    (ofAATRelative f).view = f.visibleMap := rfl

/-- On the existing finite-reference input, the relative AAT maps preserve
the assembled read/write operation with the same state map in both roles. -/
theorem ofAATRelative_operation_square {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATRelativeForwardMorphism X Y)
    (x : X.Carrier ⊕ (X.Carrier × input.View)) :
    Sum.map f.visibleMap f.stateMap ((ofLensRealization X).operation x) =
      (ofLensRealization Y).operation
        (Sum.map f.stateMap (Prod.map f.stateMap f.visibleMap) x) :=
  (ofAATRelative f).operation_square x

/-- The pre-existing fixed-view map agrees with the general relative bridge. -/
theorem ofAATRelative_fixed {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    ofAATRelative (LensAATRelativeForwardMorphism.ofForwardMorphism f) =
      ⟨f.stateMap, id, f.get_naturality, f.put_naturality⟩ := by
  apply Hom.ext <;> rfl

end GeneralLens

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
