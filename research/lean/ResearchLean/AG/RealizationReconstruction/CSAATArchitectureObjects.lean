import ResearchLean.AG.RealizationReconstruction.CSAATTypedOperationTranslation
import ResearchLean.AG.AtomFoundation.Doctrine
import Formal.AG.Atom.ObjectAlgebra
import Formal.Util.AssertStandardAxioms

/-!
# AAT objects and sources for the two independent CS semantics

This module constructs actual `AtomCarrier`, `ArchitectureObject`, `Operation`,
`ExtractionDoctrine`, and `ExactDoctrineHom` values for the lens and protocol
families of G-123(E).  State values are kept in the source types fixed by
n1015 (A1), not promoted to primitive Atoms.  Consequently an arbitrary,
possibly noninjective, semantic morphism is retained by the doctrine source
map while the finite Atom vocabulary is transported by the identity
equivalence.

The architecture objects retain the exact carrier type of every typed role.
Lens objects also retain the independently fixed reference view as their
selected quantity.  Named primitive operations have actual AAT endpoints and
configuration maps, and constructed dependent packages join each such Formal
operation to its exact semantic function.  This module does not construct a
complete core, Law, geometry, or a readback from arbitrary AAT morphisms.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation

universe u

/-! ## Lens Atom carrier and architecture objects -/

/-- The finite lens Atom vocabulary.  Values of the state and view carriers
remain in `LensAATSource`; Atoms record only the typed roles and operation
names required by n1015. -/
inductive LensAATAtom (input : LensFamilyInput.{u}) : Type (u + 1)
  | point
  | state
  | view
  | read
  | write
  | get
  | put
  deriving DecidableEq

/-- The lens Atom carrier, lifted one universe so an architecture object's
structure-map value can be the exact role carrier `Type u`. -/
def lensAATCarrier (input : LensFamilyInput.{u}) : AtomCarrier.{u + 1} where
  AtomKind := LensAATAtom input
  Axis := LensAATAtom input
  Subject := LensAATAtom input
  Predicate := LensAATAtom input
  Payload := LensAATAtom input
  Atom := LensAATAtom input
  kind := id
  axis := id
  subject := id
  predicate := id
  payload := id

/-- A typed-role configuration containing the complete fixed Atom vocabulary.
Its relation points every vocabulary atom to the selected role, so operation
names transported by a configuration map remain inside the actual family and
are attached to the target role rather than hidden in an off-family value. -/
def typedRoleConfiguration {U : AtomCarrier.{u}} (selected : U.Atom) :
    AtomConfiguration U where
  family.mem _ := True
  relation _ target := target = selected
  identification _ _ := False

/-- Every Atom in the fixed vocabulary belongs to a typed-role configuration. -/
@[simp] theorem typedRoleConfiguration_mem {U : AtomCarrier.{u}}
    (selected atom : U.Atom) :
    (typedRoleConfiguration selected).family.mem atom :=
  trivial

/-- The Atom naming a closed lens object role. -/
def lensRoleAtom {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference} :
    LensPrimitiveObject input X → LensAATAtom input
  | .state => .state
  | .view => .view
  | .read => .read
  | .write => .write

/-- The actual AAT architecture object for a lens role.  Its structure-map
value is the exact semantic carrier type, including empty carriers, and its
selected quantity is the fixed reference view. -/
def lensAATArchitectureObject {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    (role : LensPrimitiveObject input X) : ArchitectureObject (lensAATCarrier input) where
  configuration := typedRoleConfiguration (lensRoleAtom role)
  StructureMaps := Type u
  SelectedQuantities := ULift.{u + 1, u} input.View
  structureMaps := role.Carrier
  selectedQuantities := ULift.up input.reference

/-- Reading a lens AAT role object recovers its exact semantic carrier type. -/
@[simp] theorem lensAATArchitectureObject_structureMaps
    {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    (role : LensPrimitiveObject input X) :
    (lensAATArchitectureObject role).structureMaps = role.Carrier :=
  rfl

/-- Every lens AAT role object retains the fixed reference view. -/
@[simp] theorem lensAATArchitectureObject_selectedQuantities
    {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    (role : LensPrimitiveObject input X) :
    (lensAATArchitectureObject role).selectedQuantities =
      (ULift.up input.reference : ULift.{u + 1, u} input.View) :=
  rfl

/-- A named lens operation map.  The selected source Atom is sent to the
selected target Atom, and the point Atom records the operation name so `get`
and `put` remain distinct AAT operations. -/
def lensNamedConfigurationHom {input : LensFamilyInput.{u}}
    (name source target : LensAATAtom input) (source_ne_point : source ≠ .point) :
    ConfigurationHom
      (typedRoleConfiguration (U := lensAATCarrier input) source)
      (typedRoleConfiguration (U := lensAATCarrier input) target) where
  atomMap atom := match atom with
    | .point => name
    | _ => target
  maps_family := by simp [typedRoleConfiguration]
  maps_relation := by
    intro left right hright
    subst right
    cases source <;> simp_all [typedRoleConfiguration]
  maps_identification := False.elim

/-- The point Atom records the exact authored lens operation name. -/
@[simp] theorem lensNamedConfigurationHom_point {input : LensFamilyInput.{u}}
    (name source target : LensAATAtom input) (source_ne_point : source ≠ .point) :
    (lensNamedConfigurationHom name source target source_ne_point).atomMap .point = name :=
  rfl

/-- A transported lens operation name is an actual member of the target
configuration and is related to its selected target role. -/
theorem lensNamedConfigurationHom_name_supported {input : LensFamilyInput.{u}}
    (name source target : LensAATAtom input) (source_ne_point : source ≠ .point) :
    (typedRoleConfiguration target).family.mem
        ((lensNamedConfigurationHom name source target source_ne_point).atomMap .point) ∧
      (typedRoleConfiguration target).relation
        ((lensNamedConfigurationHom name source target source_ne_point).atomMap .point) target := by
  simp [typedRoleConfiguration]

/-- The actual Formal AAT operation carrying the named lens `get` endpoint. -/
def lensGetAATOperation {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : Operation (lensAATCarrier input) where
  source := lensAATArchitectureObject (X := X) .read
  target := lensAATArchitectureObject (X := X) .view
  configurationMap := lensNamedConfigurationHom .get .read .view (by simp)

/-- The actual Formal AAT operation carrying the named lens `put` endpoint. -/
def lensPutAATOperation {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : Operation (lensAATCarrier input) where
  source := lensAATArchitectureObject (X := X) .write
  target := lensAATArchitectureObject (X := X) .state
  configurationMap := lensNamedConfigurationHom .put .write .state (by simp)

/-- The semantic function attached to the actual named AAT `get` operation. -/
def lensGetAATFunction {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : X.Carrier → input.View :=
  X.get

/-- The semantic function attached to the actual named AAT `put` operation. -/
def lensPutAATFunction {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    X.Carrier × input.View → X.Carrier :=
  fun stateView => X.put stateView.1 stateView.2

/-- The semantic function attached to the named AAT get operation is the original get. -/
@[simp] theorem lensGetAATFunction_eq {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensGetAATFunction X = X.get :=
  rfl

/-- The semantic function attached to the named AAT put operation is the original put. -/
@[simp] theorem lensPutAATFunction_eq {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensPutAATFunction X = fun stateView => X.put stateView.1 stateView.2 :=
  rfl

/-- A constructed bridge joining one endpoint-indexed primitive name, its
actual Formal AAT operation, and its exact semantic function.  This is output
of the translation, not an additional premise on a lens realization. -/
structure LensAATSemanticOperation {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) where
  source : LensPrimitiveObject input X
  target : LensPrimitiveObject input X
  primitive : PrimitiveOperation (.lens input) (.lens X) (.lens source) (.lens target)
  operation : Operation (lensAATCarrier input)
  operation_source : operation.source = lensAATArchitectureObject source
  operation_target : operation.target = lensAATArchitectureObject target
  semanticFunction : source.Carrier → target.Carrier

/-- The named get primitive, Formal operation, and original get function in
one constructed AAT translation value. -/
def lensGetAATSemanticOperation {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : LensAATSemanticOperation X where
  source := .read
  target := .view
  primitive := .lensGet
  operation := lensGetAATOperation X
  operation_source := rfl
  operation_target := rfl
  semanticFunction := X.get

/-- The named put primitive, Formal operation, and original put function in
one constructed AAT translation value. -/
def lensPutAATSemanticOperation {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : LensAATSemanticOperation X where
  source := .write
  target := .state
  primitive := .lensPut
  operation := lensPutAATOperation X
  operation_source := rfl
  operation_target := rfl
  semanticFunction := fun stateView => X.put stateView.1 stateView.2

/-- The constructed get package evaluates by the original semantic get. -/
@[simp] theorem lensGetAATSemanticOperation_function {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    (lensGetAATSemanticOperation X).semanticFunction = X.get :=
  rfl

/-- The constructed put package evaluates by the original semantic put. -/
@[simp] theorem lensPutAATSemanticOperation_function {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    (lensPutAATSemanticOperation X).semanticFunction =
      fun stateView => X.put stateView.1 stateView.2 :=
  rfl

/-! ## Lens n1015 (A1) source and exact doctrine morphisms -/

/-- The exact n1015 (A1) lens source `1 + C + V + (C x V)`. -/
inductive LensAATSource {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : Type (u + 1)
  | point
  | state (value : X.Carrier)
  | view (value : input.View)
  | write (state : X.Carrier) (view : input.View)

/-- An arbitrary semantic lens morphism acts on every A1 source summand. -/
def lensAATSourceMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    LensAATSource X → LensAATSource Y
  | .point => .point
  | .state value => .state (lensObjectMap f .state value)
  | .view value => .view (lensObjectMap f .view value)
  | .write state view =>
      .write (lensObjectMap f .write (state, view)).1
        (lensObjectMap f .write (state, view)).2

/-- Every lens semantic morphism fixes the distinguished A1 point. -/
@[simp] theorem lensAATSourceMap_point {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    lensAATSourceMap f (.point : LensAATSource X) = .point :=
  rfl

/-- The state summand of the lens A1 source is mapped by the original state map. -/
@[simp] theorem lensAATSourceMap_state {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (value : X.Carrier) :
    lensAATSourceMap f (.state value) = .state (f.toFun value) :=
  rfl

/-- The fixed view summand of the lens A1 source is mapped identically. -/
@[simp] theorem lensAATSourceMap_view {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (value : input.View) :
    lensAATSourceMap f (.view value) = .view value :=
  rfl

/-- The write summand uses the original state map and the identity view map. -/
@[simp] theorem lensAATSourceMap_write {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (state : X.Carrier) (view : input.View) :
    lensAATSourceMap f (.write state view) = .write (f.toFun state) view :=
  rfl

/-- The lens A1 source construction preserves semantic identities. -/
@[simp] theorem lensAATSourceMap_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensAATSourceMap (𝟙 X) = id := by
  funext source
  cases source <;> rfl

/-- The lens A1 source construction preserves composition. -/
@[simp] theorem lensAATSourceMap_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    lensAATSourceMap (f ≫ g) = lensAATSourceMap g ∘ lensAATSourceMap f := by
  funext source
  cases source <;> rfl

/-- Read the state summand of a lens A1 source. -/
def lensAATSourceState? {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference} :
    LensAATSource X → Option X.Carrier
  | .state value => some value
  | _ => none

/-- State readback after source transport is the original semantic state map. -/
@[simp] theorem lensAATSourceState_map {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (value : X.Carrier) :
    lensAATSourceState? (lensAATSourceMap f (.state value)) = some (f.toFun value) :=
  rfl

/-- Source-relative extraction for the finite lens vocabulary.  The selected
point sees the complete signature; the other summands expose precisely their
typed roles and operation names. -/
def lensAATExtracts {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    (source : LensAATSource X) (atom : LensAATAtom input) : Prop :=
  match source with
  | .point => True
  | .state _ => atom = .state ∨ atom = .read ∨ atom = .get
  | .view _ => atom = .view
  | .write _ _ => atom = .write ∨ atom = .put

/-- The distinguished lens source extracts every atom in the fixed finite vocabulary. -/
theorem lensAATExtracts_point {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference} (atom : LensAATAtom input) :
    lensAATExtracts (.point : LensAATSource X) atom :=
  trivial

/-- A state source does not extract the distinct view-role atom. -/
theorem lensAATExtracts_state_not_view {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference} (value : X.Carrier) :
    ¬ lensAATExtracts (.state value) (.view : LensAATAtom input) := by
  simp [lensAATExtracts]

/-- The AAT extraction doctrine whose source is exactly n1015 (A1). -/
def lensAATExtractionDoctrine {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    ExtractionDoctrine (lensAATCarrier input) where
  Source := LensAATSource X
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows _ _ := True
  semanticAllows _ source atom := lensAATExtracts source atom
  resolutionAllows _ _ _ := True
  sourceSemantics _ _ := True
  normalize := id

/-- Every semantic lens morphism gives an exact AAT doctrine morphism.  Its
Atom equivalence is identity; all possible noninjectivity remains visible in
the complete A1 source map. -/
def lensAATExactDoctrineHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    ExactDoctrineHom (lensAATExtractionDoctrine X) (lensAATExtractionDoctrine Y) where
  sourceMap := lensAATSourceMap f
  atomEquiv := Equiv.refl _
  normalize_eq _ := rfl
  extraction_iff source atom := by
    cases source <;> simp [ExtractionDoctrine.extracts, lensAATExtractionDoctrine,
      lensAATExtracts, lensAATSourceMap]

/-- The exact-doctrine translation preserves the lens identity morphism. -/
@[simp] theorem lensAATExactDoctrineHom_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensAATExactDoctrineHom (𝟙 X) = ExactDoctrineHom.id (lensAATExtractionDoctrine X) := by
  apply ExactDoctrineHom.ext
  · exact lensAATSourceMap_id X
  · rfl

/-- The exact-doctrine translation preserves composition of arbitrary lens morphisms. -/
@[simp] theorem lensAATExactDoctrineHom_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    lensAATExactDoctrineHom (f ≫ g) =
      ExactDoctrineHom.comp (lensAATExactDoctrineHom f) (lensAATExactDoctrineHom g) := by
  apply ExactDoctrineHom.ext
  · exact lensAATSourceMap_comp f g
  · rfl

/-- The doctrine translation exposes the original lens state map on sources. -/
@[simp] theorem lensAATExactDoctrineHom_sourceMap_state
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (value : X.Carrier) :
    (lensAATExactDoctrineHom f).sourceMap (.state value) = .state (f.toFun value) :=
  rfl

/-- The AAT doctrine translation retains every semantic lens morphism. -/
theorem lensAATExactDoctrineHom_injective {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} :
    Function.Injective
      (lensAATExactDoctrineHom : (X ⟶ Y) →
        ExactDoctrineHom (lensAATExtractionDoctrine X) (lensAATExtractionDoctrine Y)) := by
  intro f g equality
  apply LensRealization.Hom.ext
  funext value
  have sourceEquality := congrArg ExactDoctrineHom.sourceMap equality
  have stateEquality := congrFun sourceEquality (.state value)
  exact LensAATSource.state.inj stateEquality

/-! ## Protocol Atom carrier, architecture objects, and operations -/

/-- The finite protocol Atom vocabulary.  Named edges retain their dependent
source and target vertices even when two edges have equal semantic actions. -/
inductive ProtocolAATAtom (input : ProtocolFamilyInput.{u}) : Type (u + 1)
  | point
  | state (vertex : input.schema.Vertex)
  | observation (vertex : input.schema.Vertex)
  | edge {source target : input.schema.Vertex} (name : input.schema.Edge source target)
  | observe (vertex : input.schema.Vertex)

/-- The protocol Atom carrier for one fixed schema. -/
def protocolAATCarrier (input : ProtocolFamilyInput.{u}) : AtomCarrier.{u + 1} where
  AtomKind := ProtocolAATAtom input
  Axis := ProtocolAATAtom input
  Subject := ProtocolAATAtom input
  Predicate := ProtocolAATAtom input
  Payload := ProtocolAATAtom input
  Atom := ProtocolAATAtom input
  kind := id
  axis := id
  subject := id
  predicate := id
  payload := id

/-- The actual AAT state object at a named protocol vertex. -/
def protocolStateAATArchitectureObject {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) : ArchitectureObject (protocolAATCarrier input) where
  configuration := typedRoleConfiguration (.state vertex)
  StructureMaps := Type u
  SelectedQuantities := PUnit
  structureMaps := X.State vertex
  selectedQuantities := PUnit.unit

/-- The actual AAT observation object at a named protocol vertex. -/
def protocolObservationAATArchitectureObject {input : ProtocolFamilyInput.{u}}
    (_X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) : ArchitectureObject (protocolAATCarrier input) where
  configuration := typedRoleConfiguration (.observation vertex)
  StructureMaps := Type u
  SelectedQuantities := PUnit
  structureMaps := input.observation.obj (input.schema.vertexObject vertex)
  selectedQuantities := PUnit.unit

/-- Interpret either protocol primitive object role as its actual AAT object. -/
def protocolAATArchitectureObject {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    PrimitiveObject (.protocol input) (.protocol X) →
      ArchitectureObject (protocolAATCarrier input)
  | .protocolState vertex => protocolStateAATArchitectureObject X vertex
  | .protocolObservation vertex => protocolObservationAATArchitectureObject X vertex

/-- A protocol state AAT object stores the exact state carrier at its vertex. -/
@[simp] theorem protocolStateAATArchitectureObject_structureMaps
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolStateAATArchitectureObject X vertex).structureMaps = X.State vertex :=
  rfl

/-- A protocol observation AAT object stores the fixed observation carrier. -/
@[simp] theorem protocolObservationAATArchitectureObject_structureMaps
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolObservationAATArchitectureObject X vertex).structureMaps =
      input.observation.obj (input.schema.vertexObject vertex) :=
  rfl

/-- A protocol operation configuration map retaining its exact name in the
image of the point Atom. -/
def protocolNamedConfigurationHom {input : ProtocolFamilyInput.{u}}
    (name source target : ProtocolAATAtom input) (source_ne_point : source ≠ .point) :
    ConfigurationHom
      (typedRoleConfiguration (U := protocolAATCarrier input) source)
      (typedRoleConfiguration (U := protocolAATCarrier input) target) where
  atomMap atom := match atom with
    | .point => name
    | _ => target
  maps_family := by simp [typedRoleConfiguration]
  maps_relation := by
    intro left right hright
    subst right
    cases source <;> simp_all [typedRoleConfiguration]
  maps_identification := False.elim

/-- The point Atom records the exact named protocol edge or observation. -/
@[simp] theorem protocolNamedConfigurationHom_point {input : ProtocolFamilyInput.{u}}
    (name source target : ProtocolAATAtom input) (source_ne_point : source ≠ .point) :
    (protocolNamedConfigurationHom name source target source_ne_point).atomMap .point = name :=
  rfl

/-- A transported protocol operation name is an actual member of the target
configuration and is related to its selected target role. -/
theorem protocolNamedConfigurationHom_name_supported {input : ProtocolFamilyInput.{u}}
    (name source target : ProtocolAATAtom input) (source_ne_point : source ≠ .point) :
    (typedRoleConfiguration target).family.mem
        ((protocolNamedConfigurationHom name source target source_ne_point).atomMap .point) ∧
      (typedRoleConfiguration target).relation
        ((protocolNamedConfigurationHom name source target source_ne_point).atomMap .point) target := by
  simp [typedRoleConfiguration]

/-- The actual Formal AAT operation for a named protocol edge. -/
def protocolEdgeAATOperation {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    Operation (protocolAATCarrier input) where
  source := protocolStateAATArchitectureObject X source
  target := protocolStateAATArchitectureObject X target
  configurationMap :=
    protocolNamedConfigurationHom (.edge edge) (.state source) (.state target) (by simp)

/-- The actual Formal AAT observation operation at a named vertex. -/
def protocolObserveAATOperation {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) : Operation (protocolAATCarrier input) where
  source := protocolStateAATArchitectureObject X vertex
  target := protocolObservationAATArchitectureObject X vertex
  configurationMap :=
    protocolNamedConfigurationHom (.observe vertex) (.state vertex) (.observation vertex) (by simp)

/-- Exact semantic execution attached to a named AAT protocol operation. -/
def protocolEdgeAATFunction {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    X.State source → X.State target :=
  X.edgeAction edge

/-- Exact semantic observation attached to a named AAT protocol operation. -/
def protocolObserveAATFunction {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    X.State vertex → input.observation.obj (input.schema.vertexObject vertex) :=
  X.observe vertex

/-- A named protocol edge operation carries the original edge action. -/
@[simp] theorem protocolEdgeAATFunction_eq {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    protocolEdgeAATFunction X edge = X.edgeAction edge :=
  rfl

/-- A named protocol observation operation carries the original observation map. -/
@[simp] theorem protocolObserveAATFunction_eq {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    protocolObserveAATFunction X vertex = X.observe vertex :=
  rfl

/-- A constructed bridge joining one dependent protocol primitive name, its
actual Formal AAT operation, and its exact semantic function. -/
structure ProtocolAATSemanticOperation {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) where
  source : PrimitiveObject (.protocol input) (.protocol X)
  target : PrimitiveObject (.protocol input) (.protocol X)
  primitive : PrimitiveOperation (.protocol input) (.protocol X) source target
  operation : Operation (protocolAATCarrier input)
  operation_source : operation.source = protocolAATArchitectureObject X source
  operation_target : operation.target = protocolAATArchitectureObject X target
  semanticFunction : protocolObjectCarrier source → protocolObjectCarrier target

/-- Package one original named edge as a dependent AAT semantic operation. -/
def protocolEdgeAATSemanticOperation {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    ProtocolAATSemanticOperation X where
  source := .protocolState source
  target := .protocolState target
  primitive := .protocolEdge edge
  operation := protocolEdgeAATOperation X edge
  operation_source := rfl
  operation_target := rfl
  semanticFunction := X.edgeAction edge

/-- Package one original vertex observation as a dependent AAT semantic operation. -/
def protocolObserveAATSemanticOperation {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) : ProtocolAATSemanticOperation X where
  source := .protocolState vertex
  target := .protocolObservation vertex
  primitive := .protocolObservation vertex
  operation := protocolObserveAATOperation X vertex
  operation_source := rfl
  operation_target := rfl
  semanticFunction := X.observe vertex

/-- The constructed edge package evaluates by the original named edge action. -/
@[simp] theorem protocolEdgeAATSemanticOperation_function
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    (protocolEdgeAATSemanticOperation X edge).semanticFunction = X.edgeAction edge :=
  rfl

/-- The constructed observation package evaluates by the original observation map. -/
@[simp] theorem protocolObserveAATSemanticOperation_function
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolObserveAATSemanticOperation X vertex).semanticFunction = X.observe vertex :=
  rfl

/-! ## Protocol n1015 (A1) source and exact doctrine morphisms -/

/-- The exact protocol source `1 + Sigma_v X(v) + Sigma_e X(s(e))` from
n1015 (A1). -/
inductive ProtocolAATSource {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) : Type (u + 1)
  | point
  | state (vertex : input.schema.Vertex) (value : X.State vertex)
  | step {source target : input.schema.Vertex}
      (edge : input.schema.Edge source target) (value : X.State source)

/-- An arbitrary semantic protocol morphism acts on all A1 source summands
while retaining every vertex and named edge. -/
def protocolAATSourceMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    ProtocolAATSource X → ProtocolAATSource Y
  | .point => .point
  | .state vertex value => .state vertex (protocolStateMap a vertex value)
  | .step edge value => .step edge (protocolStateMap a _ value)

/-- Every protocol semantic morphism fixes the distinguished A1 point. -/
@[simp] theorem protocolAATSourceMap_point {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    protocolAATSourceMap a (.point : ProtocolAATSource X) = .point :=
  rfl

/-- Each protocol state summand is mapped by the original component map. -/
@[simp] theorem protocolAATSourceMap_state {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (vertex : input.schema.Vertex) (value : X.State vertex) :
    protocolAATSourceMap a (.state vertex value) =
      .state vertex (protocolStateMap a vertex value) :=
  rfl

/-- Each protocol step retains its edge name and maps its source state component. -/
@[simp] theorem protocolAATSourceMap_step {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target)
    (value : X.State source) :
    protocolAATSourceMap a (.step edge value) =
      .step edge (protocolStateMap a source value) :=
  rfl

/-- The protocol A1 source construction preserves semantic identities. -/
@[simp] theorem protocolAATSourceMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATSourceMap (𝟙 X) = id := by
  funext source
  cases source <;> rfl

/-- The protocol A1 source construction preserves composition. -/
@[simp] theorem protocolAATSourceMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    protocolAATSourceMap (a ≫ b) =
      protocolAATSourceMap b ∘ protocolAATSourceMap a := by
  funext source
  cases source <;> rfl

/-- Read every named state summand of a protocol A1 source. -/
def protocolAATSourceState? {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation} :
    ProtocolAATSource X → Option (Σ vertex, X.State vertex)
  | .state vertex value => some ⟨vertex, value⟩
  | _ => none

/-- Protocol state readback after transport is the original component map. -/
@[simp] theorem protocolAATSourceState_map {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (vertex : input.schema.Vertex) (value : X.State vertex) :
    protocolAATSourceState? (protocolAATSourceMap a (.state vertex value)) =
      some ⟨vertex, protocolStateMap a vertex value⟩ :=
  rfl

/-- Source-relative extraction for the protocol vocabulary. -/
def protocolAATExtracts {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    (source : ProtocolAATSource X) (atom : ProtocolAATAtom input) : Prop :=
  match source with
  | .point => True
  | .state vertex _ =>
      atom = .state vertex ∨ atom = .observation vertex ∨ atom = .observe vertex
  | .step edge _ => atom = .edge edge

/-- The distinguished protocol source extracts every atom in the fixed vocabulary. -/
theorem protocolAATExtracts_point {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    (atom : ProtocolAATAtom input) :
    protocolAATExtracts (.point : ProtocolAATSource X) atom :=
  trivial

/-- A protocol state source does not extract the distinguished point atom. -/
theorem protocolAATExtracts_state_not_point {input : ProtocolFamilyInput.{u}}
    {X : ProtocolRealization input.schema input.observation}
    (vertex : input.schema.Vertex) (value : X.State vertex) :
    ¬ protocolAATExtracts (.state vertex value) (.point : ProtocolAATAtom input) := by
  simp [protocolAATExtracts]

/-- The protocol extraction doctrine with exactly the n1015 (A1) source. -/
def protocolAATExtractionDoctrine {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ExtractionDoctrine (protocolAATCarrier input) where
  Source := ProtocolAATSource X
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows _ _ := True
  semanticAllows _ source atom := protocolAATExtracts source atom
  resolutionAllows _ _ _ := True
  sourceSemantics _ _ := True
  normalize := id

/-- Every arbitrary protocol morphism becomes an exact AAT doctrine morphism
with its complete, possibly noninjective, state action in the source map. -/
def protocolAATExactDoctrineHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    ExactDoctrineHom (protocolAATExtractionDoctrine X)
      (protocolAATExtractionDoctrine Y) where
  sourceMap := protocolAATSourceMap a
  atomEquiv := Equiv.refl _
  normalize_eq _ := rfl
  extraction_iff source atom := by
    cases source <;> simp [ExtractionDoctrine.extracts, protocolAATExtractionDoctrine,
      protocolAATExtracts, protocolAATSourceMap]

/-- The exact-doctrine translation preserves the protocol identity morphism. -/
@[simp] theorem protocolAATExactDoctrineHom_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATExactDoctrineHom (𝟙 X) =
      ExactDoctrineHom.id (protocolAATExtractionDoctrine X) := by
  apply ExactDoctrineHom.ext
  · exact protocolAATSourceMap_id X
  · rfl

/-- The exact-doctrine translation preserves composition of protocol morphisms. -/
@[simp] theorem protocolAATExactDoctrineHom_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    protocolAATExactDoctrineHom (a ≫ b) =
      ExactDoctrineHom.comp (protocolAATExactDoctrineHom a)
        (protocolAATExactDoctrineHom b) := by
  apply ExactDoctrineHom.ext
  · exact protocolAATSourceMap_comp a b
  · rfl

/-- The doctrine translation exposes each original protocol state component map. -/
@[simp] theorem protocolAATExactDoctrineHom_sourceMap_state
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (vertex : input.schema.Vertex) (value : X.State vertex) :
    (protocolAATExactDoctrineHom a).sourceMap (.state vertex value) =
      .state vertex (protocolStateMap a vertex value) :=
  rfl

/-- The AAT doctrine translation retains every semantic protocol morphism. -/
theorem protocolAATExactDoctrineHom_injective {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} :
    Function.Injective
      (protocolAATExactDoctrineHom : (X ⟶ Y) →
        ExactDoctrineHom (protocolAATExtractionDoctrine X)
          (protocolAATExtractionDoctrine Y)) := by
  intro f g equality
  apply ProtocolRealization.Hom.ext
  apply NatTrans.ext
  funext object
  cases object with
  | mk vertex =>
      funext value
      have sourceEquality := congrArg ExactDoctrineHom.sourceMap equality
      have stateEquality := congrFun sourceEquality (.state vertex value)
      injection stateEquality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
