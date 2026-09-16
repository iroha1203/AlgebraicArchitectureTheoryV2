import ResearchLean.AG.RealizationReconstruction.AATClosedFamilySignature
import Formal.Util.AssertStandardAxioms

/-!
# Typed CS primitive operations in the closed AAT family

This module interprets the lens and protocol constructors of the closed
G-123 family signature in their independently specified semantic objects.
The interpretation is indexed by every semantic object and every semantic
morphism; it does not select decoder images or accept completed maps.

For lenses, the four object roles are interpreted by the exact state, view,
read-domain, and write-domain carriers.  For protocols, every named vertex
and fixed observation carrier is retained.  Primitive operation names are
interpreted by `get`, `put`, the named edge action, and the named observation
map.  Arbitrary, possibly noninvertible semantic morphisms give typed maps on
all roles, and the defining semantic naturality laws prove their operation
squares.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v

/-! ## Lens objects and primitive operations -/

/-- Interpret every closed lens object role in its exact semantic carrier. -/
def lensObjectCarrier {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    (object : PrimitiveObject (.lens input) (.lens X)) : Type u := by
  cases object with
  | lens role => exact role.Carrier

/-- Interpret a lens primitive operation by the exact `get` or `put`
function of the independently supplied semantic lens. -/
def lensOperationFunction {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    {source target : PrimitiveObject (.lens input) (.lens X)}
    (operation : PrimitiveOperation (.lens input) (.lens X) source target) :
    lensObjectCarrier source → lensObjectCarrier target := by
  cases operation with
  | lensGet => exact X.get
  | lensPut => exact fun stateView => X.put stateView.1 stateView.2

/-- The interpretation of the `lensGet` operation is definitionally the
original semantic `get` function. -/
@[simp] theorem lensOperationFunction_get {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference} :
    lensOperationFunction
        (PrimitiveOperation.lensGet (input := input) (X := X)) = X.get :=
  rfl

/-- The interpretation of the `lensPut` operation is definitionally the
original semantic `put` function on the exact write carrier `C x V`. -/
@[simp] theorem lensOperationFunction_put {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference} :
    lensOperationFunction
        (PrimitiveOperation.lensPut (input := input) (X := X)) =
      fun stateView => X.put stateView.1 stateView.2 :=
  rfl

/-- Transport a lens role name between semantic objects without changing the
role.  Only the dependent owner changes. -/
def lensRoleTransport {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} :
    LensPrimitiveObject input X → LensPrimitiveObject input Y
  | .state => .state
  | .view => .view
  | .read => .read
  | .write => .write

/-- An arbitrary lens morphism acts on every lens object role.  State and
read roles use the complete semantic state map, view uses the identity, and
write uses their product. -/
def lensObjectMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (role : LensPrimitiveObject input X) :
    role.Carrier → (lensRoleTransport (Y := Y) role).Carrier := by
  cases role with
  | state => exact f.toFun
  | view => exact id
  | read => exact f.toFun
  | write => exact fun stateView => (f.toFun stateView.1, stateView.2)

/-- Every arbitrary lens morphism commutes with the named `get` operation. -/
theorem lensGet_square {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (state : X.Carrier) :
    lensObjectMap f .view (X.get state) =
      Y.get (lensObjectMap f .read state) := by
  exact (f.get_naturality state).symm

/-- Every arbitrary lens morphism commutes with the named `put` operation. -/
theorem lensPut_square {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (state : X.Carrier) (view : input.View) :
    lensObjectMap f .state (X.put state view) =
      Y.put (lensObjectMap f .write (state, view)).1
        (lensObjectMap f .write (state, view)).2 := by
  exact f.put_naturality state view

/-- The state-role map preserves semantic identities. -/
@[simp] theorem lensObjectMap_id_state {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) (value : X.Carrier) :
    lensObjectMap (𝟙 X) (.state : LensPrimitiveObject input X) value = value := rfl

/-- The read-role map preserves semantic identities. -/
@[simp] theorem lensObjectMap_id_read {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) (value : X.Carrier) :
    lensObjectMap (𝟙 X) (.read : LensPrimitiveObject input X) value = value := rfl

/-- The view-role map preserves semantic identities. -/
@[simp] theorem lensObjectMap_id_view {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) (value : input.View) :
    lensObjectMap (𝟙 X) (.view : LensPrimitiveObject input X) value = value := rfl

/-- The write-role map preserves semantic identities. -/
@[simp] theorem lensObjectMap_id_write {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (value : X.Carrier × input.View) :
    lensObjectMap (𝟙 X) (.write : LensPrimitiveObject input X) value = value := rfl

/-- The state-role map preserves composition of arbitrary semantic lens morphisms. -/
@[simp] theorem lensObjectMap_comp_state {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) (value : X.Carrier) :
    lensObjectMap (f ≫ g) (.state : LensPrimitiveObject input X) value =
      lensObjectMap g (.state : LensPrimitiveObject input Y)
        (lensObjectMap f (.state : LensPrimitiveObject input X) value) := rfl

/-- The read-role map preserves composition of arbitrary semantic lens morphisms. -/
@[simp] theorem lensObjectMap_comp_read {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) (value : X.Carrier) :
    lensObjectMap (f ≫ g) (.read : LensPrimitiveObject input X) value =
      lensObjectMap g (.read : LensPrimitiveObject input Y)
        (lensObjectMap f (.read : LensPrimitiveObject input X) value) := rfl

/-- The view-role map preserves composition of arbitrary semantic lens morphisms. -/
@[simp] theorem lensObjectMap_comp_view {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) (value : input.View) :
    lensObjectMap (f ≫ g) (.view : LensPrimitiveObject input X) value =
      lensObjectMap g (.view : LensPrimitiveObject input Y)
        (lensObjectMap f (.view : LensPrimitiveObject input X) value) := rfl

/-- The write-role map preserves composition of arbitrary semantic lens morphisms. -/
@[simp] theorem lensObjectMap_comp_write {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) (value : X.Carrier × input.View) :
    lensObjectMap (f ≫ g) (.write : LensPrimitiveObject input X) value =
      lensObjectMap g (.write : LensPrimitiveObject input Y)
        (lensObjectMap f (.write : LensPrimitiveObject input X) value) := rfl

/-! ## Protocol objects and primitive operations -/

/-- Interpret every protocol object role by the exact state or fixed
observation carrier at its named vertex. -/
def protocolObjectCarrier {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    (object : PrimitiveObject (.protocol input) (.protocol X)) : Type u := by
  cases object with
  | protocolState vertex => exact X.State vertex
  | protocolObservation vertex =>
      exact input.observation.obj (input.schema.vertexObject vertex)

/-- Interpret every protocol primitive operation without changing its name:
an edge is interpreted by its exact edge action, and an observation name is
interpreted by the exact observation component at that vertex. -/
def protocolOperationFunction {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    {source target : PrimitiveObject (.protocol input) (.protocol X)}
    (operation : PrimitiveOperation (.protocol input) (.protocol X) source target) :
    protocolObjectCarrier source → protocolObjectCarrier target := by
  cases operation with
  | protocolEdge edge => exact X.edgeAction edge
  | protocolObservation vertex => exact X.observe vertex

/-- A named protocol edge evaluates to the original semantic edge action. -/
@[simp] theorem protocolOperationFunction_edge {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    protocolOperationFunction
        (PrimitiveOperation.protocolEdge (input := input) (X := X) edge) =
      X.edgeAction edge :=
  rfl

/-- A named observation evaluates to the original semantic observation. -/
@[simp] theorem protocolOperationFunction_observation
    {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    (vertex : input.schema.Vertex) :
    protocolOperationFunction
        (PrimitiveOperation.protocolObservation (input := input) (X := X) vertex) =
      X.observe vertex :=
  rfl

/-- An arbitrary protocol morphism acts on a named state carrier. -/
def protocolStateMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (vertex : input.schema.Vertex) : X.State vertex → Y.State vertex :=
  a.toNatTrans.app (input.schema.vertexObject vertex)

/-- The fixed observation carrier map of every protocol morphism is the
identity; observations belong to the fixed parameter `O`, not to a decoder. -/
def protocolObservationMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (_a : X ⟶ Y)
    (vertex : input.schema.Vertex) :
    input.observation.obj (input.schema.vertexObject vertex) →
      input.observation.obj (input.schema.vertexObject vertex) :=
  id

/-- Every arbitrary protocol morphism commutes with every named edge. -/
theorem protocolEdge_square {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target)
    (state : X.State source) :
    protocolStateMap a target (X.edgeAction edge state) =
      Y.edgeAction edge (protocolStateMap a source state) :=
  congrFun (ProtocolRealization.edge_naturality a edge) state

/-- Every arbitrary protocol morphism commutes with every named observation,
with the identity map on the fixed observation carrier. -/
theorem protocolObservation_square {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    protocolObservationMap a vertex (X.observe vertex state) =
      Y.observe vertex (protocolStateMap a vertex state) := by
  exact (congrFun (ProtocolRealization.observation_app a vertex) state).symm

/-- State maps of the protocol identity are pointwise identities. -/
@[simp] theorem protocolStateMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    protocolStateMap (𝟙 X) vertex state = state :=
  rfl

/-- State maps preserve composition of arbitrary protocol morphisms. -/
@[simp] theorem protocolStateMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : X ⟶ Y) (b : Y ⟶ Z) (vertex : input.schema.Vertex)
    (state : X.State vertex) :
    protocolStateMap (a ≫ b) vertex state =
      protocolStateMap b vertex (protocolStateMap a vertex state) :=
  rfl

/-- Observation maps of the protocol identity are pointwise identities. -/
@[simp] theorem protocolObservationMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex)
    (value : input.observation.obj (input.schema.vertexObject vertex)) :
    protocolObservationMap (𝟙 X) vertex value = value :=
  rfl

/-- Identity observation maps also preserve semantic composition. -/
@[simp] theorem protocolObservationMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : X ⟶ Y) (b : Y ⟶ Z) (vertex : input.schema.Vertex)
    (value : input.observation.obj (input.schema.vertexObject vertex)) :
    protocolObservationMap (a ≫ b) vertex value =
      protocolObservationMap b vertex (protocolObservationMap a vertex value) :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
