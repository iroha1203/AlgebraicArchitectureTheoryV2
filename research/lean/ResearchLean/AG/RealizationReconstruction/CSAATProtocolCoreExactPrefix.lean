import ResearchLean.AG.RealizationReconstruction.CSAATLensCoreExactPrefix
import Formal.Util.AssertStandardAxioms

/-!
# Genuine protocol all-object core exactness

Every named edge action and observation of an arbitrary raw protocol structure
is conjugated through a genuine semantic isomorphism.  Recognized architecture
objects are mapped to those conjugates; a Cantor-separated marker keeps the
unrecognized branch unrecognized.  The result preserves and reflects every
relation/observation instance and proves exact residual equality for every
context, object, index, and Atom.

Endpoint finiteness and semantic laws are ambient fields of the fixed protocol
realizations.  These proofs impose no lawfulness premise on the arbitrary raw
`ProtocolLawStructure` processed by the object map.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation

universe u

/-- Conjugate every edge action and observation of an arbitrary raw protocol
structure through a genuine protocol isomorphism. -/
def protocolIsoTransportLawStructure
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (data : ProtocolLawStructure input X.State) :
    ProtocolLawStructure input Y.State where
  edgeAction edge state :=
    protocolStateMap e.hom _
      (data.edgeAction edge (protocolStateMap e.inv _ state))
  observe vertex state :=
    data.observe vertex (protocolStateMap e.inv vertex state)

/-- Raw protocol structures are determined by every named edge action and
observation. -/
theorem protocolLawStructure_ext {input : ProtocolFamilyInput.{u}}
    {State : input.schema.Vertex → Type u}
    {a b : ProtocolLawStructure input State}
    (hedge : @a.edgeAction = @b.edgeAction)
    (hobserve : a.observe = b.observe) : a = b := by
  cases a
  cases b
  cases hedge
  cases hobserve
  rfl

/-- Conjugation sends the actual source protocol structure to the actual
target structure. -/
theorem protocolIsoTransportLawStructure_actual
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    protocolIsoTransportLawStructure e X.toLawStructure = Y.toLawStructure := by
  apply protocolLawStructure_ext
  · funext source target edge state
    change protocolStateMap e.hom target
        (X.edgeAction edge (protocolStateMap e.inv source state)) =
      Y.edgeAction edge state
    rw [protocolEdge_square]
    exact congrArg (Y.edgeAction edge)
      ((protocolIsoStateEquiv e source).right_inv state)
  · funext vertex state
    change X.observe vertex (protocolStateMap e.inv vertex state) =
      Y.observe vertex state
    exact e.inv.toLawHom.observation_naturality vertex state

/-- Map every architecture object.  Recognized protocol structures are
conjugated; all other objects receive a Cantor-separated marker. -/
noncomputable def protocolIsoObjectMap
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (object : ArchitectureObject (protocolAATCarrier input)) :
    ArchitectureObject (protocolAATCarrier input) := by
  classical
  by_cases h : object.StructureMaps =
      ULift.{u + 1, u} (ProtocolLawStructure input X.State)
  · exact {
      configuration := object.configuration
      StructureMaps := ULift.{u + 1, u} (ProtocolLawStructure input Y.State)
      SelectedQuantities := object.SelectedQuantities
      structureMaps := ULift.up
        (protocolIsoTransportLawStructure e (h ▸ object.structureMaps).down)
      selectedQuantities := object.selectedQuantities }
  · exact {
      configuration := object.configuration
      StructureMaps := Set
        (ULift.{u + 1, u} (ProtocolLawStructure input Y.State))
      SelectedQuantities := object.SelectedQuantities
      structureMaps := ∅
      selectedQuantities := object.selectedQuantities }

theorem protocolIsoObjectMap_configuration_eq
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (object : ArchitectureObject (protocolAATCarrier input)) :
    (protocolIsoObjectMap e object).configuration = object.configuration := by
  classical
  simp only [protocolIsoObjectMap]
  split <;> rfl

theorem protocolIsoObjectMap_selectedQuantities_eq
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (object : ArchitectureObject (protocolAATCarrier input)) :
    (protocolIsoObjectMap e object).SelectedQuantities =
      object.SelectedQuantities := by
  classical
  simp only [protocolIsoObjectMap]
  split <;> rfl

/-- Objects formed by the source reader map to target-reader objects on the
same arbitrary configuration. -/
theorem protocolIsoObjectMap_object_formation_eq
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (configuration : AtomConfiguration (protocolAATCarrier input)) :
    protocolIsoObjectMap e
        ((protocolCoreObjectReading input X).object configuration) =
      (protocolCoreObjectReading input Y).object configuration := by
  classical
  simp only [protocolIsoObjectMap]
  split
  · rename_i h
    simp only [protocolCoreObjectReading] at h ⊢
    rw [protocolIsoTransportLawStructure_actual]
  · rename_i h
    exact (h rfl).elim

/-- The target reader is exactly the mapped source reader, including the
unrecognized-object branch. -/
theorem protocolIsoObjectMap_reader_eq
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (object : ArchitectureObject (protocolAATCarrier input)) :
    protocolLawStructure? input Y.State (protocolIsoObjectMap e object) =
      (protocolLawStructure? input X.State object).map
        (protocolIsoTransportLawStructure e) := by
  classical
  by_cases h : object.StructureMaps =
      ULift.{u + 1, u} (ProtocolLawStructure input X.State)
  · simp only [protocolIsoObjectMap, dif_pos h]
    unfold protocolLawStructure?
    split
    · rfl
    · rename_i bad
      exact (bad rfl).elim
  · simp only [protocolIsoObjectMap, dif_neg h]
    unfold protocolLawStructure?
    split
    · rename_i impossible
      exact (set_not_equiv_type
        (ULift.{u + 1, u} (ProtocolLawStructure input Y.State))
        impossible).elim
    · simp

/-- Forward raw hom from an arbitrary source protocol structure. -/
def protocolIsoTransportLawHom
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (data : ProtocolLawStructure input X.State) :
    ProtocolLawHom data (protocolIsoTransportLawStructure e data) where
  stateMap := protocolStateMap e.hom
  edge_naturality edge state := by
    change protocolStateMap e.hom _ (data.edgeAction edge state) =
      protocolStateMap e.hom _
        (data.edgeAction edge
          (protocolStateMap e.inv _ (protocolStateMap e.hom _ state)))
    exact congrArg (fun mapped => protocolStateMap e.hom _
      (data.edgeAction edge mapped))
        ((protocolIsoStateEquiv e _).left_inv state).symm
  observation_naturality vertex state := by
    change data.observe vertex
        (protocolStateMap e.inv vertex (protocolStateMap e.hom vertex state)) =
      data.observe vertex state
    exact congrArg (data.observe vertex)
      ((protocolIsoStateEquiv e vertex).left_inv state)

/-- Inverse raw hom from the conjugated protocol structure. -/
def protocolIsoTransportLawHomInv
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (data : ProtocolLawStructure input X.State) :
    ProtocolLawHom (protocolIsoTransportLawStructure e data) data where
  stateMap := protocolStateMap e.inv
  edge_naturality edge state := by
    change protocolStateMap e.inv _
        (protocolStateMap e.hom _
          (data.edgeAction edge (protocolStateMap e.inv _ state))) =
      data.edgeAction edge (protocolStateMap e.inv _ state)
    exact (protocolIsoStateEquiv e _).left_inv _
  observation_naturality _ _ := rfl

/-- Conjugation preserves and reflects every relation and observation Law
instance of every arbitrary raw protocol structure. -/
theorem protocolIsoTransportLawStructure_holds_iff
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (data : ProtocolLawStructure input X.State)
    (index : ProtocolLawIndex X.State) :
    index.Holds data ↔
      (protocolIsoLawIndexEquiv e index).Holds
        (protocolIsoTransportLawStructure e data) := by
  change index.Holds data ↔
    (protocolLawIndexMap (protocolIsoTransportLawHom e data) index).Holds
      (protocolIsoTransportLawStructure e data)
  exact protocolLawIndex_holds_iff_of_inverse
    (protocolIsoTransportLawHom e data)
    (protocolIsoTransportLawHomInv e data)
    (fun vertex => (protocolIsoStateEquiv e vertex).left_inv)
    (fun vertex => (protocolIsoStateEquiv e vertex).right_inv) index

/-- The source and mapped arbitrary-object readers agree on every relation or
observation truth value. -/
theorem protocolIsoObjectMap_readHolds_iff
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (object : ArchitectureObject (protocolAATCarrier input))
    (index : ProtocolLawIndex X.State) :
    (protocolLawStructure? input X.State object).elim False index.Holds ↔
      (protocolLawStructure? input Y.State
        (protocolIsoObjectMap e object)).elim False
          (protocolIsoLawIndexEquiv e index).Holds := by
  rw [protocolIsoObjectMap_reader_eq]
  cases hreader : protocolLawStructure? input X.State object with
  | none => simp
  | some data =>
      simpa using protocolIsoTransportLawStructure_holds_iff e data index

/-- Exact residual equality for all contexts, arbitrary architecture objects,
all relation/observation indices, and every protocol Atom. -/
theorem protocolIsoObjectMap_equationResidual_eq
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (sourceContext : Site.ArchitectureContext
      (protocolLawObject input X.State X.toLawStructure))
    (targetContext : Site.ArchitectureContext
      (protocolLawObject input Y.State Y.toLawStructure))
    (object : ArchitectureObject (protocolAATCarrier input))
    (index : ProtocolLawIndex X.State)
    (atom : ProtocolAATAtom input) :
    protocolIsoLawCoordinateEquiv e
        ((protocolLawEquationSystem input X.State
          X.toLawStructure).equationResidual
            ⟨sourceContext⟩ object (ULift.up index) atom) =
      (protocolLawEquationSystem input Y.State
        Y.toLawStructure).equationResidual
          ⟨targetContext⟩ (protocolIsoObjectMap e object)
            (ULift.up (protocolIsoLawIndexEquiv e index)) atom := by
  classical
  change protocolIsoLawCoordinateEquiv e
      (MvPolynomial.C (if
        (protocolLawStructure? input X.State object).elim False index.Holds
        then 0 else 1)) =
    MvPolynomial.C (if
      (protocolLawStructure? input Y.State
        (protocolIsoObjectMap e object)).elim False
          (protocolIsoLawIndexEquiv e index).Holds then 0 else 1)
  rw [show
    ((protocolLawStructure? input X.State object).elim False index.Holds) =
      ((protocolLawStructure? input Y.State
        (protocolIsoObjectMap e object)).elim False
          (protocolIsoLawIndexEquiv e index).Holds) from
      propext (protocolIsoObjectMap_readHolds_iff e object index)]
  simp

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
