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
configuration maps, while their exact semantic functions are exposed by
separate typed APIs.  This module does not construct a complete core, Law,
geometry, or a readback from arbitrary AAT morphisms.
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

/-- A singleton configuration for one typed primitive role.  Relation and
identification data are empty, hence are supported by the selected family. -/
def singletonRoleConfiguration {U : AtomCarrier.{u}} (selected : U.Atom) :
    AtomConfiguration U where
  family.mem atom := atom = selected
  relation _ _ := False
  identification _ _ := False

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
  configuration := singletonRoleConfiguration (lensRoleAtom role)
  StructureMaps := Type u
  SelectedQuantities := ULift.{u + 1, u} input.View
  structureMaps := role.Carrier
  selectedQuantities := ULift.up input.reference

@[simp] theorem lensAATArchitectureObject_structureMaps
    {input : LensFamilyInput.{u}}
    {X : LensRealization input.View input.reference}
    (role : LensPrimitiveObject input X) :
    (lensAATArchitectureObject role).structureMaps = role.Carrier :=
  rfl

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
      (singletonRoleConfiguration (U := lensAATCarrier input) source)
      (singletonRoleConfiguration (U := lensAATCarrier input) target) where
  atomMap atom := match atom with
    | .point => name
    | _ => target
  maps_family := by
    intro atom hatom
    subst atom
    cases source <;> simp_all [singletonRoleConfiguration]
  maps_relation := False.elim
  maps_identification := False.elim

/-- The point Atom records the exact authored lens operation name. -/
@[simp] theorem lensNamedConfigurationHom_point {input : LensFamilyInput.{u}}
    (name source target : LensAATAtom input) (source_ne_point : source ≠ .point) :
    (lensNamedConfigurationHom name source target source_ne_point).atomMap .point = name :=
  rfl

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

@[simp] theorem lensGetAATFunction_eq {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensGetAATFunction X = X.get :=
  rfl

@[simp] theorem lensPutAATFunction_eq {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensPutAATFunction X = fun stateView => X.put stateView.1 stateView.2 :=
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

@[simp] theorem lensAATSourceMap_point {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    lensAATSourceMap f (.point : LensAATSource X) = .point :=
  rfl

@[simp] theorem lensAATSourceMap_state {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (value : X.Carrier) :
    lensAATSourceMap f (.state value) = .state (f.toFun value) :=
  rfl

@[simp] theorem lensAATSourceMap_view {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (value : input.View) :
    lensAATSourceMap f (.view value) = .view value :=
  rfl

@[simp] theorem lensAATSourceMap_write {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (state : X.Carrier) (view : input.View) :
    lensAATSourceMap f (.write state view) = .write (f.toFun state) view :=
  rfl

@[simp] theorem lensAATSourceMap_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensAATSourceMap (𝟙 X) = id := by
  funext source
  cases source <;> rfl

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
  configuration := singletonRoleConfiguration (.state vertex)
  StructureMaps := Type u
  SelectedQuantities := Type u
  structureMaps := X.State vertex
  selectedQuantities := input.observation.obj (input.schema.vertexObject vertex)

/-- The actual AAT observation object at a named protocol vertex. -/
def protocolObservationAATArchitectureObject {input : ProtocolFamilyInput.{u}}
    (_X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) : ArchitectureObject (protocolAATCarrier input) where
  configuration := singletonRoleConfiguration (.observation vertex)
  StructureMaps := Type u
  SelectedQuantities := Type u
  structureMaps := input.observation.obj (input.schema.vertexObject vertex)
  selectedQuantities := input.observation.obj (input.schema.vertexObject vertex)

@[simp] theorem protocolStateAATArchitectureObject_structureMaps
    {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolStateAATArchitectureObject X vertex).structureMaps = X.State vertex :=
  rfl

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
      (singletonRoleConfiguration (U := protocolAATCarrier input) source)
      (singletonRoleConfiguration (U := protocolAATCarrier input) target) where
  atomMap atom := match atom with
    | .point => name
    | _ => target
  maps_family := by
    intro atom hatom
    subst atom
    cases source <;> simp_all [singletonRoleConfiguration]
  maps_relation := False.elim
  maps_identification := False.elim

/-- The point Atom records the exact named protocol edge or observation. -/
@[simp] theorem protocolNamedConfigurationHom_point {input : ProtocolFamilyInput.{u}}
    (name source target : ProtocolAATAtom input) (source_ne_point : source ≠ .point) :
    (protocolNamedConfigurationHom name source target source_ne_point).atomMap .point = name :=
  rfl

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

@[simp] theorem protocolEdgeAATFunction_eq {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target) :
    protocolEdgeAATFunction X edge = X.edgeAction edge :=
  rfl

@[simp] theorem protocolObserveAATFunction_eq {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    protocolObserveAATFunction X vertex = X.observe vertex :=
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

@[simp] theorem protocolAATSourceMap_point {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    protocolAATSourceMap a (.point : ProtocolAATSource X) = .point :=
  rfl

@[simp] theorem protocolAATSourceMap_state {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (vertex : input.schema.Vertex) (value : X.State vertex) :
    protocolAATSourceMap a (.state vertex value) =
      .state vertex (protocolStateMap a vertex value) :=
  rfl

@[simp] theorem protocolAATSourceMap_step {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target)
    (value : X.State source) :
    protocolAATSourceMap a (.step edge value) =
      .step edge (protocolStateMap a source value) :=
  rfl

@[simp] theorem protocolAATSourceMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATSourceMap (𝟙 X) = id := by
  funext source
  cases source <;> rfl

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
