import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardOverlapExtension
import Formal.Util.AssertStandardAxioms

/-!
# Generated identity and composition laws for forward CS geometry

The one-way geometry components are generated from the primitive named-operation
morphisms.  This file proves their identity and composition laws directly for
the primitive state action, every Law index, the full Law coordinate ring, and
every object and arrow of the context functor.  No aggregate geometry record is
accepted as input.

The raw quotient transformation is obtained later by conjugating the polynomial
map with endpoint-dependent presheaf isomorphisms.  Its identity and composition
laws require that conjugation cancellation and are not claimed here.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens generated components -/

namespace LensAATForwardMorphism

/-- The primitive lens identity fixes every state. -/
@[simp] theorem id_stateMap_apply {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) (state : X.Carrier) :
    (id X).stateMap state = state :=
  rfl

/-- Primitive lens composition acts successively on every state. -/
@[simp] theorem comp_stateMap_apply {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (state : X.Carrier) :
    (comp f g).stateMap state = g.stateMap (f.stateMap state) :=
  rfl

/-- The generated lens Law-index action fixes every index at identity. -/
@[simp] theorem lawIndexMap_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (index : LensLawIndex input.View X.Carrier) :
    (id X).lawIndexMap index = index := by
  cases index <;> rfl

/-- The generated lens Law-index action respects primitive composition on all
three fully quantified Law-index constructors. -/
@[simp] theorem lawIndexMap_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (index : LensLawIndex input.View X.Carrier) :
    (comp f g).lawIndexMap index = g.lawIndexMap (f.lawIndexMap index) := by
  cases index <;> rfl

/-- The complete generated lens coordinate-ring map is the identity, not only
on a selected family of variables. -/
@[simp] theorem lawCoordinateMap_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    (id X).lawCoordinateMap = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lawCoordinateMap, lensLawCoordinateMap]
  · rcases value with ⟨⟨index⟩, atom⟩
    simp [lawCoordinateMap, lensLawCoordinateMap]
    exact lawIndexMap_id X index

/-- The complete generated lens coordinate-ring map respects primitive
composition. -/
@[simp] theorem lawCoordinateMap_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    (comp f g).lawCoordinateMap =
      g.lawCoordinateMap.comp f.lawCoordinateMap := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lawCoordinateMap, lensLawCoordinateMap]
  · rcases value with ⟨⟨index⟩, atom⟩
    simp [lawCoordinateMap, lensLawCoordinateMap]
    exact lawIndexMap_comp f g index

/-- Direct and successive lens full-family rebasing agree on every context
object. -/
@[simp] theorem lawContextFunctor_comp_obj {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (lensLawObject input X.Carrier X.toLensData.toLawStructure))) :
    ((comp f g).lawContextFunctor).obj W =
      g.lawContextFunctor.obj (f.lawContextFunctor.obj W) :=
  rfl

/-- Direct and successive lens full-family rebasing agree on every selected
restriction arrow. -/
@[simp] theorem lawContextFunctor_comp_map {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (lensLawObject input X.Carrier X.toLensData.toLawStructure))}
    (h : W ⟶ V) :
    ((comp f g).lawContextFunctor).map h =
      g.lawContextFunctor.map (f.lawContextFunctor.map h) :=
  Subsingleton.elim _ _

end LensAATForwardMorphism

/-! ## Protocol generated components -/

namespace ProtocolAATForwardMorphism

/-- The primitive protocol identity fixes every state at every vertex. -/
@[simp] theorem id_stateMap_apply {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    (id X).stateMap vertex state = state :=
  rfl

/-- Primitive protocol composition acts successively at every vertex. -/
@[simp] theorem comp_stateMap_apply {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    (comp f g).stateMap vertex state =
      g.stateMap vertex (f.stateMap vertex state) :=
  rfl

/-- The generated protocol Law-index action fixes every relation and
observation index at identity. -/
@[simp] theorem lawIndexMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (index : ProtocolLawIndex X.State) :
    (id X).lawIndexMap index = index := by
  cases index <;> rfl

/-- The generated protocol Law-index action respects primitive composition for
every relation and observation instance. -/
@[simp] theorem lawIndexMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    (index : ProtocolLawIndex X.State) :
    (comp f g).lawIndexMap index = g.lawIndexMap (f.lawIndexMap index) := by
  cases index <;> rfl

/-- The complete generated protocol coordinate-ring map is the identity. -/
@[simp] theorem lawCoordinateMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    (id X).lawCoordinateMap = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lawCoordinateMap, protocolLawCoordinateMap]
  · rcases value with ⟨⟨index⟩, atom⟩
    simp [lawCoordinateMap, protocolLawCoordinateMap]
    exact lawIndexMap_id X index

/-- The complete generated protocol coordinate-ring map respects primitive
composition. -/
@[simp] theorem lawCoordinateMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z) :
    (comp f g).lawCoordinateMap =
      g.lawCoordinateMap.comp f.lawCoordinateMap := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lawCoordinateMap, protocolLawCoordinateMap]
  · rcases value with ⟨⟨index⟩, atom⟩
    simp [lawCoordinateMap, protocolLawCoordinateMap]
    exact lawIndexMap_comp f g index

/-- Direct and successive protocol full-family rebasing agree on every context
object. -/
@[simp] theorem lawContextFunctor_comp_obj {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input X.State X.toLawStructure))) :
    ((comp f g).lawContextFunctor).obj W =
      g.lawContextFunctor.obj (f.lawContextFunctor.obj W) :=
  rfl

/-- Direct and successive protocol full-family rebasing agree on every
selected restriction arrow. -/
@[simp] theorem lawContextFunctor_comp_map {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input X.State X.toLawStructure))}
    (h : W ⟶ V) :
    ((comp f g).lawContextFunctor).map h =
      g.lawContextFunctor.map (f.lawContextFunctor.map h) :=
  Subsingleton.elim _ _

end ProtocolAATForwardMorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
