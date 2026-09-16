import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardOverlapExtension
import Formal.Util.AssertStandardAxioms

/-!
# Generated identity and composition laws for forward CS geometry

The one-way geometry components are generated from the primitive named-operation
morphisms.  This file proves their identity and composition laws directly for
the primitive state action, every Law index, the full Law coordinate ring, and
every object of the context functor.  On arrows, the context categories are
thin, so the proved identity and composition statements are the corresponding
thin-category coherence equalities; they do not recover extra data from a
chosen representative of a preorder arrow.  No aggregate geometry record is
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

/-- Identity full-family rebasing retains every field of every lens context;
the only replaced field is a proof of membership in the already-full family. -/
@[simp] theorem lawContextFunctor_id_obj {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (lensLawObject input X.Carrier X.toLensData.toLawStructure))) :
    ((id X).lawContextFunctor).obj W = W := by
  rcases W with ⟨⟨⟨Support, Axis, Observable, supportReads,
    supportReads_objectFamily, axisReads, observableReads⟩, Extension, extension⟩⟩
  rfl

/-- On the thin lens context category, identity rebasing has the unique arrow
with the retained endpoints. -/
@[simp] theorem lawContextFunctor_id_map {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (lensLawObject input X.Carrier X.toLensData.toLawStructure))}
    (h : W ⟶ V) :
    ((id X).lawContextFunctor).map h = h :=
  Subsingleton.elim _ _

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

/-- Direct and successive lens full-family rebasing give the same arrow by
thin-category uniqueness, after their endpoint contexts agree. -/
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

/-- Identity full-family rebasing retains every field of every protocol
context; only the proof of membership in the full family is replaced. -/
@[simp] theorem lawContextFunctor_id_obj {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input X.State X.toLawStructure))) :
    ((id X).lawContextFunctor).obj W = W := by
  rcases W with ⟨⟨⟨Support, Axis, Observable, supportReads,
    supportReads_objectFamily, axisReads, observableReads⟩, Extension, extension⟩⟩
  rfl

/-- On the thin protocol context category, identity rebasing has the unique
arrow with the retained endpoints. -/
@[simp] theorem lawContextFunctor_id_map {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input X.State X.toLawStructure))}
    (h : W ⟶ V) :
    ((id X).lawContextFunctor).map h = h :=
  Subsingleton.elim _ _

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

/-- Direct and successive protocol full-family rebasing give the same arrow by
thin-category uniqueness, after their endpoint contexts agree. -/
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
