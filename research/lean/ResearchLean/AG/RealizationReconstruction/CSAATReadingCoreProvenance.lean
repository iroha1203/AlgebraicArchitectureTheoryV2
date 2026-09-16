import ResearchLean.AG.RealizationReconstruction.CSAATGeometryRawIntegration
import Formal.AG.ReadingFunctoriality.Core
import Formal.Util.AssertStandardAxioms

/-!
# Reading-core provenance for the two independent CS semantics

This module constructs the first `AATCorePackage` and dependent `ReadingCore`
endpoints used by G-123(E).  The core is generated from the original n1015
source doctrine; neither the completed Law object nor its geometry is accepted
as a primitive core input.  The composition rule acts on every list-finite
family, while its specialization to the distinguished all-vocabulary source is
proved equal to the existing lens/protocol Law endpoint.

The operation reading contains every configuration homomorphism, so the named
get/put, edge, and observation maps are not removed by the core construction.
The present circuit reading uses the rejecting finite detector: this proves
soundness without accepting a Law certificate, but does not claim obstruction
completeness.  Functorial core change, arbitrary-AAT readback, and the final
cross-model classification remain separate obligations.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Shared generated readings -/

/-- A family-supported point configuration on an arbitrary selected family. -/
def supportedPointConfiguration {U : AtomCarrier.{u}}
    (F : AtomFamily U) (point : U.Atom) : AtomConfiguration U where
  family := F
  relation source target := F.mem source ∧ F.mem target ∧ target = point
  identification _ _ := False

/-- The point configuration is supported on exactly its supplied family. -/
theorem supportedPointConfiguration_familySupported {U : AtomCarrier.{u}}
    (F : AtomFamily U) (point : U.Atom) :
    (supportedPointConfiguration F point).FamilySupported := by
  constructor
  · rintro source target ⟨hsource, htarget, _⟩
    exact ⟨hsource, htarget⟩
  · intro source target h
    exact False.elim h

/-- When every Atom is selected, the supported point configuration is the
existing complete typed-role configuration. -/
theorem supportedPointConfiguration_eq_typedRoleConfiguration
    {U : AtomCarrier.{u}} (F : AtomFamily U) (point : U.Atom)
    (all_mem : ∀ atom, F.mem atom) :
    supportedPointConfiguration F point = typedRoleConfiguration point := by
  apply AtomConfiguration.ext
  · apply AtomFamily.ext
    intro atom
    exact iff_of_true (all_mem atom) trivial
  · intro source target
    simp [supportedPointConfiguration, typedRoleConfiguration, all_mem]
  · intro source target
    simp [supportedPointConfiguration, typedRoleConfiguration]

/-- One composition rule acts on every explicitly list-finite family and does
not alter the family selected by the caller. -/
def pointCompositionReading {U : AtomCarrier.{u}} (point : U.Atom) :
    CompositionReading U where
  compose F _ := supportedPointConfiguration F point
  family_eq _ _ := rfl
  family_supported F _ := supportedPointConfiguration_familySupported F point

/-- All configuration homomorphisms are retained as operations. -/
def allConfigurationHomOperationReading (U : AtomCarrier.{u}) :
    OperationReading U where
  Op A B := ConfigurationHom A.configuration B.configuration
  configurationMap operation := operation

/-- No invariant is silently imposed on the independent CS semantics. -/
def emptyInvariantReading (U : AtomCarrier.{u}) : InvariantFamily U where
  Index := PEmpty
  invariant index := PEmpty.elim index

/-- A rejecting detector is sound for any equation system because it accepts
no finite datum. -/
noncomputable def rejectingEquationReading {U : AtomCarrier.{u}}
    (A : ArchitectureObject U)
    (E : ArchitecturalEquationSystem (Site.contextMorphismPreorderCategory A)) :
    EquationReading A where
  contextPreorder := Site.contextMorphismPreorderCategory A
  equationSystem := E
  circuits.code _ := .reject
  circuitSound := by
    intro index object datum _ haccepts
    simp [CircuitDetectorCode.eval] at haccepts

/-- Equation, signature, coverage, and overlap form one dependent endpoint.
Transporting this bundle once preserves their common indexing object and avoids
accepting any of the four components as an unrelated post-hoc core field. -/
structure CSAATCoreGeometryData {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) where
  equationReading : EquationReading A
  signature : ArchitectureSignature U
  requirements : Site.CoverageRequirements A
    equationReading.equationSystem signature
  overlap : Site.ContextOverlapPullback equationReading.contextPreorder

/-! ## Lens core -/

/-- The distinguished n1015 lens source has an explicit finite atomization. -/
theorem lensAATAtomization_listFinite (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    ((lensAATExtractionDoctrine X).atomize
      (.point : LensAATSource X)).ListFinite := by
  refine ⟨[.point, .state, .view, .read, .write, .get, .put], ?_⟩
  intro atom _
  cases atom <;> simp

/-- The lens object reading keeps every caller-supplied configuration while
using the exact original raw get/put data and reference view. -/
def lensCoreObjectReading (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    ObjectReading (lensAATCarrier input) where
  object configuration := {
    configuration := configuration
    StructureMaps := ULift.{u + 1, u} (LensLawStructure input.View X.Carrier)
    SelectedQuantities := ULift.{u + 1, u} input.View
    structureMaps := ULift.up X.toLensData.toLawStructure
    selectedQuantities := ULift.up input.reference }
  configuration_eq _ := rfl

/-- Specializing the family-generic composition rule to the distinguished
source reconstructs the existing lens Law object. -/
theorem lensCoreGeneratedObject_eq_lawObject
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensCoreObjectReading input X).object
        ((pointCompositionReading (.point : LensAATAtom input)).compose
          ((lensAATExtractionDoctrine X).atomize (.point : LensAATSource X))
          (lensAATAtomization_listFinite input X)) =
      lensLawObject input X.Carrier X.toLensData.toLawStructure := by
  have hconfiguration :
      supportedPointConfiguration
          ((lensAATExtractionDoctrine X).atomize (.point : LensAATSource X))
          (.point : LensAATAtom input) =
        typedRoleConfiguration (.point : LensAATAtom input) := by
    apply supportedPointConfiguration_eq_typedRoleConfiguration
    intro atom
    exact ⟨trivial, lensAATExtracts_point (X := X) atom, trivial, trivial⟩
  change (lensCoreObjectReading input X).object
      (supportedPointConfiguration _ (.point : LensAATAtom input)) = _
  rw [hconfiguration]
  rfl

/-- The pre-transport lens endpoint bundle uses the actual Law system and the
existing concrete coverage and overlap readings. -/
noncomputable def lensAATCoreEndpointGeometryData
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    CSAATCoreGeometryData
      (lensLawObject input X.Carrier X.toLensData.toLawStructure) where
  equationReading := rejectingEquationReading _
    (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
  signature := lensAATGeometrySignature input
  requirements := lensAATGeometryCoverageRequirements input X
  overlap := completeLawOverlap _

/-- The complete lens geometry bundle is transported once to the object
generated from the original source doctrine. -/
noncomputable def lensAATCoreGeneratedGeometryData
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    CSAATCoreGeometryData
      ((lensCoreObjectReading input X).object
        ((pointCompositionReading (.point : LensAATAtom input)).compose
          ((lensAATExtractionDoctrine X).atomize (.point : LensAATSource X))
          (lensAATAtomization_listFinite input X))) :=
  (lensCoreGeneratedObject_eq_lawObject input X).symm ▸
    lensAATCoreEndpointGeometryData input X

/-- The transported lens bundle is heterogeneously equal to the original
endpoint bundle, recording its exact provenance. -/
theorem lensAATCoreGeneratedGeometryData_heq
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    HEq (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreEndpointGeometryData input X) := by
  unfold lensAATCoreGeneratedGeometryData
  exact eqRec_heq _ _

/-- Primitive Atom axioms for the exact lens Atom vocabulary. -/
def lensAATAtomAxioms (input : LensFamilyInput.{u}) :
    AtomAxiomSystem (lensAATCarrier input) where
  primitiveExistence := ⟨.point⟩
  predicateStability a b := by
    simp [SameCoordinates, lensAATCarrier]

/-- The complete lens core reading is assembled only from the n1015 source,
the family-generic composition rule, and the original lens data. -/
noncomputable def lensAATCoreReading (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    CoreReading (lensAATCarrier input) where
  doctrine := lensAATExtractionDoctrine X
  source := .point
  family_listFinite := lensAATAtomization_listFinite input X
  composition := pointCompositionReading .point
  objectReading := lensCoreObjectReading input X
  equationReading := (lensAATCoreGeneratedGeometryData input X).equationReading
  invariantReading := emptyInvariantReading _
  signatureReading := (lensAATCoreGeneratedGeometryData input X).signature
  operationReading := allConfigurationHomOperationReading _

/-- The lens `AATCorePackage` generated from primitive axioms and the
constructed admissible reading. -/
noncomputable def lensAATCorePackage (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    AATCorePackage (lensAATCarrier input) :=
  AATCorePackage.generate (lensAATAtomAxioms input) (lensAATCoreReading input X)

/-- The generated core object is the previously constructed Law object. -/
theorem lensAATCorePackage_object_eq (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCorePackage input X).object =
      lensLawObject input X.Carrier X.toLensData.toLawStructure :=
  lensCoreGeneratedObject_eq_lawObject input X

/-! ## Protocol core -/

/-- The distinguished n1015 protocol source has an explicit finite
atomization obtained only from the fixed finite vertex and named-edge inputs. -/
theorem protocolAATAtomization_listFinite
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ((protocolAATExtractionDoctrine X).atomize
      (.point : ProtocolAATSource X)).ListFinite := by
  classical
  let vertices := input.schema.vertexFintype.elems.toList
  let namedEdges := input.schema.namedEdgeFintype.elems.toList
  let vertexAtoms : List (ProtocolAATAtom input) :=
    vertices.flatMap fun vertex => [.state vertex, .observation vertex, .observe vertex]
  let edgeAtoms : List (ProtocolAATAtom input) :=
    namedEdges.map fun named => .edge named.2.2
  refine ⟨.point :: vertexAtoms ++ edgeAtoms, ?_⟩
  intro atom _
  cases atom with
  | point => simp
  | state vertex =>
      right
      apply List.mem_append_left
      simp [vertexAtoms, vertices]
      exact ⟨vertex, @Fintype.complete _ input.schema.vertexFintype vertex, rfl⟩
  | observation vertex =>
      right
      apply List.mem_append_left
      simp [vertexAtoms, vertices]
      exact ⟨vertex, @Fintype.complete _ input.schema.vertexFintype vertex, rfl⟩
  | @edge source target name =>
      right
      apply List.mem_append_right
      simp [edgeAtoms, namedEdges]
      exact ⟨source, target, name,
        @Fintype.complete _ input.schema.namedEdgeFintype ⟨source, target, name⟩, rfl⟩
  | observe vertex =>
      right
      apply List.mem_append_left
      simp [vertexAtoms, vertices]
      exact ⟨vertex, @Fintype.complete _ input.schema.vertexFintype vertex, rfl⟩

/-- The protocol object reading keeps every caller-supplied configuration
while using the exact original edge actions and observations. -/
def protocolCoreObjectReading (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ObjectReading (protocolAATCarrier input) where
  object configuration := {
    configuration := configuration
    StructureMaps := ULift.{u + 1, u} (ProtocolLawStructure input X.State)
    SelectedQuantities := PUnit
    structureMaps := ULift.up X.toLawStructure
    selectedQuantities := PUnit.unit }
  configuration_eq _ := rfl

/-- Specializing the family-generic composition rule to the distinguished
source reconstructs the existing protocol Law object. -/
theorem protocolCoreGeneratedObject_eq_lawObject
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolCoreObjectReading input X).object
        ((pointCompositionReading (.point : ProtocolAATAtom input)).compose
          ((protocolAATExtractionDoctrine X).atomize (.point : ProtocolAATSource X))
          (protocolAATAtomization_listFinite input X)) =
      protocolLawObject input X.State X.toLawStructure := by
  have hconfiguration :
      supportedPointConfiguration
          ((protocolAATExtractionDoctrine X).atomize (.point : ProtocolAATSource X))
          (.point : ProtocolAATAtom input) =
        typedRoleConfiguration (.point : ProtocolAATAtom input) := by
    apply supportedPointConfiguration_eq_typedRoleConfiguration
    intro atom
    exact ⟨trivial, protocolAATExtracts_point (X := X) atom, trivial, trivial⟩
  change (protocolCoreObjectReading input X).object
      (supportedPointConfiguration _ (.point : ProtocolAATAtom input)) = _
  rw [hconfiguration]
  rfl

/-- The pre-transport protocol endpoint bundle uses the actual Law system and
the existing concrete coverage and overlap readings. -/
noncomputable def protocolAATCoreEndpointGeometryData
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    CSAATCoreGeometryData
      (protocolLawObject input X.State X.toLawStructure) where
  equationReading := rejectingEquationReading _
    (protocolLawEquationSystem input X.State X.toLawStructure)
  signature := protocolAATGeometrySignature input
  requirements := protocolAATGeometryCoverageRequirements input X
  overlap := completeLawOverlap _

/-- The complete protocol geometry bundle is transported once to the object
generated from the original source doctrine. -/
noncomputable def protocolAATCoreGeneratedGeometryData
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    CSAATCoreGeometryData
      ((protocolCoreObjectReading input X).object
        ((pointCompositionReading (.point : ProtocolAATAtom input)).compose
          ((protocolAATExtractionDoctrine X).atomize (.point : ProtocolAATSource X))
          (protocolAATAtomization_listFinite input X))) :=
  (protocolCoreGeneratedObject_eq_lawObject input X).symm ▸
    protocolAATCoreEndpointGeometryData input X

/-- The transported protocol bundle is heterogeneously equal to its original
endpoint bundle. -/
theorem protocolAATCoreGeneratedGeometryData_heq
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    HEq (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreEndpointGeometryData input X) := by
  unfold protocolAATCoreGeneratedGeometryData
  exact eqRec_heq _ _

/-- Primitive Atom axioms for the exact protocol Atom vocabulary. -/
def protocolAATAtomAxioms (input : ProtocolFamilyInput.{u}) :
    AtomAxiomSystem (protocolAATCarrier input) where
  primitiveExistence := ⟨.point⟩
  predicateStability a b := by
    simp [SameCoordinates, protocolAATCarrier]

/-- The complete protocol core reading is assembled only from the n1015
source, the family-generic composition rule, and the original protocol data. -/
noncomputable def protocolAATCoreReading (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    CoreReading (protocolAATCarrier input) where
  doctrine := protocolAATExtractionDoctrine X
  source := .point
  family_listFinite := protocolAATAtomization_listFinite input X
  composition := pointCompositionReading .point
  objectReading := protocolCoreObjectReading input X
  equationReading := (protocolAATCoreGeneratedGeometryData input X).equationReading
  invariantReading := emptyInvariantReading _
  signatureReading := (protocolAATCoreGeneratedGeometryData input X).signature
  operationReading := allConfigurationHomOperationReading _

/-- The protocol `AATCorePackage` generated from primitive axioms and the
constructed admissible reading. -/
noncomputable def protocolAATCorePackage (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    AATCorePackage (protocolAATCarrier input) :=
  AATCorePackage.generate (protocolAATAtomAxioms input)
    (protocolAATCoreReading input X)

/-- The generated protocol core object is the previously constructed Law
object. -/
theorem protocolAATCorePackage_object_eq (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolAATCorePackage input X).object =
      protocolLawObject input X.State X.toLawStructure :=
  protocolCoreGeneratedObject_eq_lawObject input X

/-! ## Dependent reading cores and endpoint provenance -/

/-- The concrete lens coverage and overlap are selected on the generated
core, after transporting along the proved generated-object equality. -/
noncomputable def lensAATSelectedGeometryReading
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Site.SelectedGeometryReading (lensAATCorePackage input X) where
  requirements := (lensAATCoreGeneratedGeometryData input X).requirements
  overlap := (lensAATCoreGeneratedGeometryData input X).overlap

/-- The lens endpoint is now a genuine dependent `ReadingCore`, with the
coherent raw system constructed on its selected site. -/
noncomputable def lensAATReadingCore (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    ReadingCore (lensAATCarrier input) where
  core := lensAATCorePackage input X
  geometry := lensAATSelectedGeometryReading input X
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := equationCoordinateRawSystemOn
    (lensAATSelectedGeometryReading input X).toAATSite

/-- The lens ReadingCore carries the source-generated core package rather than
an endpoint object supplied independently. -/
@[simp] theorem lensAATReadingCore_core (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATReadingCore input X).core = lensAATCorePackage input X :=
  rfl

/-- The named lens get map is retained by the generated core's operation
reading at its original source and target objects. -/
def lensAATCoreSelectedGet (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCorePackage input X).reading.operationReading.Op
      (lensGetAATOperation X).source (lensGetAATOperation X).target :=
  (lensGetAATOperation X).configurationMap

/-- The named lens put map is retained by the same operation reading. -/
def lensAATCoreSelectedPut (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCorePackage input X).reading.operationReading.Op
      (lensPutAATOperation X).source (lensPutAATOperation X).target :=
  (lensPutAATOperation X).configurationMap

/-- The selected core get operation has exactly the original named
configuration map. -/
@[simp] theorem lensAATCoreSelectedGet_configurationMap
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCorePackage input X).reading.operationReading.configurationMap
      (lensAATCoreSelectedGet input X) =
        (lensGetAATOperation X).configurationMap :=
  rfl

/-- The selected core put operation has exactly the original named
configuration map. -/
@[simp] theorem lensAATCoreSelectedPut_configurationMap
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCorePackage input X).reading.operationReading.configurationMap
      (lensAATCoreSelectedPut input X) =
        (lensPutAATOperation X).configurationMap :=
  rfl

/-- The concrete protocol coverage and overlap are selected on the generated
core after transport along the generated-object equality. -/
noncomputable def protocolAATSelectedGeometryReading
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Site.SelectedGeometryReading (protocolAATCorePackage input X) where
  requirements := (protocolAATCoreGeneratedGeometryData input X).requirements
  overlap := (protocolAATCoreGeneratedGeometryData input X).overlap

/-- The protocol endpoint is a genuine dependent `ReadingCore`. -/
noncomputable def protocolAATReadingCore (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ReadingCore (protocolAATCarrier input) where
  core := protocolAATCorePackage input X
  geometry := protocolAATSelectedGeometryReading input X
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := equationCoordinateRawSystemOn
    (protocolAATSelectedGeometryReading input X).toAATSite

/-- The protocol ReadingCore carries the source-generated core package. -/
@[simp] theorem protocolAATReadingCore_core (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolAATReadingCore input X).core = protocolAATCorePackage input X :=
  rfl

/-- Every named protocol edge map is retained by the generated core operation
reading at its original source and target objects. -/
def protocolAATCoreSelectedEdge (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) :
    (protocolAATCorePackage input X).reading.operationReading.Op
      (protocolEdgeAATOperation X edge).source
      (protocolEdgeAATOperation X edge).target :=
  (protocolEdgeAATOperation X edge).configurationMap

/-- Every named protocol observation map is retained by the same operation
reading. -/
def protocolAATCoreSelectedObserve (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolAATCorePackage input X).reading.operationReading.Op
      (protocolObserveAATOperation X vertex).source
      (protocolObserveAATOperation X vertex).target :=
  (protocolObserveAATOperation X vertex).configurationMap

/-- The selected core edge operation has the original named configuration
map. -/
@[simp] theorem protocolAATCoreSelectedEdge_configurationMap
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) :
    (protocolAATCorePackage input X).reading.operationReading.configurationMap
      (protocolAATCoreSelectedEdge input X edge) =
        (protocolEdgeAATOperation X edge).configurationMap :=
  rfl

/-- The selected core observation operation has the original named
configuration map. -/
@[simp] theorem protocolAATCoreSelectedObserve_configurationMap
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolAATCorePackage input X).reading.operationReading.configurationMap
      (protocolAATCoreSelectedObserve input X vertex) =
        (protocolObserveAATOperation X vertex).configurationMap :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
