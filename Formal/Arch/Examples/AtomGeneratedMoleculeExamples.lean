import Formal.Arch.AAT.GeneratedCurvature
import Formal.Arch.AAT.GeneratedDiagram
import Formal.Arch.AAT.GeneratedPath
import Formal.Arch.AAT.GeneratedSynthesis
import Formal.Arch.Evolution.Chapter8HomotopySkeleton
import Formal.Arch.Evolution.Chapter9DiagramFilling

namespace Formal.Arch.AtomGeneratedMoleculeExamples

inductive ComponentAtom where
  | api
  | database
  deriving DecidableEq, Repr

def componentKind (_atom : ComponentAtom) : AtomKind :=
  AtomKind.existence

def componentAxis (_atom : ComponentAtom) : Axis :=
  Axis.static

/-- Minimal source-like atom system with two component existence facts. -/
def componentSystem : AtomAxiomSystem where
  Atom := ComponentAtom
  Predicate := AtomKind
  kind := componentKind
  axis := componentAxis
  predicate := componentKind
  predicateKind := fun kind => kind
  predicateAxis := fun _ => Axis.static
  predicateKindAligned := by
    intro atom
    rfl
  predicateAxisAligned := by
    intro atom
    cases atom <;> rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def componentPort (name : String) : AtomPort where
  name := name
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun kind => kind = AtomKind.existence
  acceptsAxis := fun axis => axis = Axis.static

def apiPort : AtomPort :=
  componentPort "api"

def databasePort : AtomPort :=
  componentPort "database"

def singletonValence (port : AtomPort) : AtomValence where
  ports := fun candidate => candidate = port
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨port, rfl⟩

def componentShape (atom : ComponentAtom) : AtomShape where
  family := AtomKind.existence
  axis := Axis.static
  subject := { name := match atom with
    | ComponentAtom.api => "api"
    | ComponentAtom.database => "database" }
  predicate := "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.neutral
  arity := 1
  valence := match atom with
    | ComponentAtom.api => singletonValence apiPort
    | ComponentAtom.database => singletonValence databasePort
  singleFactShape := True
  singleFactShapeEvidence := trivial

def componentShapePresentation :
    AtomShapePresentation componentSystem where
  shapeOf := componentShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

def selectedComponentAtoms : ComponentAtom -> Prop
  | ComponentAtom.api => True
  | ComponentAtom.database => True

def componentPortCompatible :
    PortCompatible apiPort databasePort := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def databasePortCompatible :
    PortCompatible databasePort apiPort := by
  exact PortCompatible.symm componentPortCompatible

def apiDatabaseComposition :
    CompatibleComposition
      (AtomShapeOf componentShapePresentation ComponentAtom.api)
      (AtomShapeOf componentShapePresentation ComponentAtom.database) where
  leftPort := apiPort
  rightPort := databasePort
  leftHasPort := rfl
  rightHasPort := rfl
  portsCompatible := componentPortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _
    exact ⟨rfl, rfl⟩

def databaseApiComposition :
    CompatibleComposition
      (AtomShapeOf componentShapePresentation ComponentAtom.database)
      (AtomShapeOf componentShapePresentation ComponentAtom.api) where
  leftPort := databasePort
  rightPort := apiPort
  leftHasPort := rfl
  rightHasPort := rfl
  portsCompatible := databasePortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _
    exact ⟨rfl, rfl⟩

def componentCompositionGraph :
    AAT.CompositionGraph
      componentShapePresentation selectedComponentAtoms where
  compatiblePairs := by
    intro left right _hLeft _hRight hDistinct
    cases left
    · cases right
      · exact False.elim (hDistinct rfl)
      · exact apiDatabaseComposition
    · cases right
      · exact databaseApiComposition
      · exact False.elim (hDistinct rfl)
  graphBoundary := True

/-- Positive example: component atoms form a generated molecule only through compatible shapes. -/
def generatedComponentMolecule :
    AAT.GeneratedMolecule componentShapePresentation where
  atoms := selectedComponentAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact componentSystem.primitive atom
  compositionGraph := componentCompositionGraph
  requiredPortsMatched := by
    intro atom _ _ hRequired
    cases atom <;> cases hRequired
  notArbitrarySet := True
  notArbitrarySetEvidence := trivial

def generatedComponentMolecule_api_database_compatible :
    CompatibleComposition
      (AtomShapeOf componentShapePresentation ComponentAtom.api)
      (AtomShapeOf componentShapePresentation ComponentAtom.database) := by
  exact generatedComponentMolecule.compatible_pairs
    (by trivial)
    (by trivial)
    (by intro h; cases h)

theorem generatedComponentMolecule_to_legacy_molecule_contains_api :
    generatedComponentMolecule.toMolecule.atoms ComponentAtom.api := by
  trivial

theorem generatedComponentMolecule_atoms_primitive :
    componentSystem.Primitive ComponentAtom.api := by
  exact generatedComponentMolecule.atoms_primitive (by trivial)

/-- Generated architecture object whose carrier is exactly the generated molecule. -/
def generatedComponentObject :
    AAT.GeneratedArchitectureObject componentShapePresentation where
  molecule := generatedComponentMolecule
  carrierList :=
    [ ⟨ComponentAtom.api, by trivial⟩
    , ⟨ComponentAtom.database, by trivial⟩
    ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom <;> simp
  objectBoundary := True

theorem generatedComponentObject_carrier_atom_primitive
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    componentSystem.Primitive carrier.val := by
  exact generatedComponentObject.carrier_atom_primitive carrier

theorem generatedComponentObject_no_relation_atom
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    (AtomShapeOf componentShapePresentation carrier.val).family ≠
      AtomKind.relation := by
  cases carrier.val <;> intro hRelation <;> cases hRelation

instance generatedComponentRelationDecidable :
    DecidableRel (AAT.GeneratedRelation generatedComponentObject) := by
  intro source target
  exact isFalse (by
    intro hEdge
    rcases hEdge with ⟨relation, hRelation⟩
    exact generatedComponentObject_no_relation_atom relation hRelation.1)

instance componentSystemAtomDecidableEq :
    DecidableEq componentSystem.Atom :=
  inferInstanceAs (DecidableEq ComponentAtom)

theorem generatedComponentGraph_no_edges :
    ∀ source target,
      ¬ (AAT.GeneratedArchGraph generatedComponentObject).edge
        source target := by
  intro source target hEdge
  rcases hEdge with ⟨relation, hRelation⟩
  exact generatedComponentObject_no_relation_atom relation hRelation.1

theorem generatedComponentGraph_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph generatedComponentObject) := by
  intro hClosed
  rcases hClosed with ⟨_carrier, walk, hPositive⟩
  cases walk with
  | nil _ =>
      simp [Walk.length] at hPositive
  | cons hEdge _rest =>
      exact generatedComponentGraph_no_edges _ _ hEdge

/-- Generated law model built from the generated object, not from a hand-authored graph. -/
def generatedComponentLawModel :
    AAT.GeneratedArchitectureLawModel generatedComponentObject where
  generatedWalkAcyclic := generatedComponentGraph_walkAcyclic
  lawModelBoundary := True

def generatedComponentZeroCurvaturePackage :
    AAT.ZeroCurvaturePackage generatedComponentLawModel.generatedAATCore := by
  exact generatedComponentLawModel.generatedZeroCurvaturePackage

theorem generatedComponent_lawfulWithinMoleculeConfiguration :
    AAT.LawfulWithinMoleculeConfiguration
      generatedComponentLawModel.generatedDesignLaw
      generatedComponentLawModel.requiredGeneratedMolecule := by
  exact generatedComponentLawModel.generated_lawfulWithinMoleculeConfiguration

theorem generatedComponent_requiredSignatureAxesZero :
    ArchitectureSignature.RequiredSignatureAxesZero
      generatedComponentLawModel.generatedSignatureOf := by
  exact generatedComponentLawModel.generated_requiredSignatureAxesZero

theorem generatedComponent_architectureFlatWithin :
    ArchitectureFlatWithin generatedComponentObject.generatedFlatnessModel
      generatedComponentObject.generatedComponentUniverse := by
  exact generatedComponentLawModel.generatedArchitectureFlatWithin

theorem generatedComponent_architectureFlat :
    ArchitectureFlat generatedComponentObject.generatedFlatnessModel := by
  exact generatedComponentLawModel.generatedArchitectureFlat

theorem generatedComponent_totalCurvature_eq_zero :
    totalCurvature AAT.generatedObservationDistance
      generatedComponentObject.generatedSemanticSemantics
      generatedComponentObject.generatedSemanticDiagrams = 0 := by
  exact generatedComponentObject.generated_totalCurvature_eq_zero

theorem generatedComponent_noMeasuredNumericalCurvatureObstruction :
    NoMeasuredNumericalCurvatureObstruction AAT.generatedObservationDistance
      generatedComponentObject.generatedSemanticSemantics
      generatedComponentObject.generatedSemanticDiagrams := by
  exact generatedComponentObject.generated_noMeasuredNumericalCurvatureObstruction

def generatedComponentNilPath
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    AAT.GeneratedArchitecturePath generatedComponentObject carrier carrier :=
  AAT.GeneratedArchitecturePath.nil carrier

theorem generatedComponentNilPath_length_zero
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    AAT.GeneratedArchitecturePath.length
      (generatedComponentNilPath carrier) = 0 := by
  rfl

def generatedComponentNilDiagram
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    AAT.GeneratedArchitectureDiagram generatedComponentObject
      (source := carrier) (target := carrier) :=
  AAT.GeneratedArchitectureDiagram.reflexive
    (generatedComponentNilPath carrier)

theorem generatedComponentNilDiagram_filler
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    AAT.GeneratedDiagramFiller
      (object := generatedComponentObject)
      (fun _ _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ => False)
      (fun _ _ _ _ => False)
      (generatedComponentNilDiagram carrier) := by
  exact AAT.generatedDiagramFiller_refl
    (generatedComponentNilPath carrier)

theorem generatedComponentNilDiagram_chapter9_filler
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    AAT.GeneratedDiagramFiller
      (object := generatedComponentObject)
      (fun _ _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ => False)
      (fun _ _ _ _ => False)
      (generatedComponentNilDiagram carrier) := by
  exact _root_.Formal.Arch.Chapter9DiagramFilling.generatedDiagramFiller_refl
    (generatedComponentNilPath carrier)

theorem generatedComponent_chapter8_refutes_homotopy_from_observation_diff
    {α : Type}
    {IndependentSquare :
      (W X Y Z : AAT.GeneratedCarrier generatedComponentObject) ->
        AAT.GeneratedArchitectureStep generatedComponentObject W X ->
        AAT.GeneratedArchitectureStep generatedComponentObject X Z ->
        AAT.GeneratedArchitectureStep generatedComponentObject W Y ->
        AAT.GeneratedArchitectureStep generatedComponentObject Y Z -> Prop}
    {SameExternalContract :
      (X Y : AAT.GeneratedCarrier generatedComponentObject) ->
        AAT.GeneratedArchitectureStep generatedComponentObject X Y ->
        AAT.GeneratedArchitectureStep generatedComponentObject X Y -> Prop}
    {RepairFill :
      (X Y : AAT.GeneratedCarrier generatedComponentObject) ->
        AAT.GeneratedArchitecturePath generatedComponentObject X Y ->
        AAT.GeneratedArchitecturePath generatedComponentObject X Y -> Prop}
    {Obs :
      {X Y : AAT.GeneratedCarrier generatedComponentObject} ->
        AAT.GeneratedArchitecturePath generatedComponentObject X Y -> α}
    (hIndependentSquare :
      ∀ {W X Y Z T : AAT.GeneratedCarrier generatedComponentObject}
        (a : AAT.GeneratedArchitectureStep generatedComponentObject W X)
        (b : AAT.GeneratedArchitectureStep generatedComponentObject X Z)
        (c : AAT.GeneratedArchitectureStep generatedComponentObject W Y)
        (d : AAT.GeneratedArchitectureStep generatedComponentObject Y Z)
        (rest : AAT.GeneratedArchitecturePath generatedComponentObject Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : AAT.GeneratedCarrier generatedComponentObject}
        (s t : AAT.GeneratedArchitectureStep generatedComponentObject X Y)
        (rest : AAT.GeneratedArchitecturePath generatedComponentObject Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : AAT.GeneratedCarrier generatedComponentObject}
        {p q : AAT.GeneratedArchitecturePath generatedComponentObject X Y},
        RepairFill X Y p q ->
          (suffix : AAT.GeneratedArchitecturePath generatedComponentObject Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : AAT.GeneratedCarrier generatedComponentObject}
        (step : AAT.GeneratedArchitectureStep generatedComponentObject X Y)
        {p q : AAT.GeneratedArchitecturePath generatedComponentObject Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {source target : AAT.GeneratedCarrier generatedComponentObject}
    {left right : AAT.GeneratedArchitecturePath generatedComponentObject source target}
    (hTrajectoryDiff : Obs left ≠ Obs right) :
    ¬ AAT.GeneratedPathHomotopy
      IndependentSquare SameExternalContract RepairFill left right := by
  exact
    Formal.Arch.Chapter8HomotopySkeleton.generatedSignatureTrajectory_refutesGeneratedPathHomotopy
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      hTrajectoryDiff

def generatedComponentIdentityOperation :
    AAT.GeneratedOperation generatedComponentObject generatedComponentObject where
  atomMap := id
  shapeTransform := fun source target => source = target
  transformsAtomShape := by
    intro _carrier
    rfl
  preservesPrimitive := by
    intro carrier
    exact generatedComponentObject.carrier_atom_primitive carrier
  operationDoesNotCreateAtomsEvidence :=
    componentSystem.tool_output_does_not_create_atoms
  operationBoundary := True

theorem generatedComponentIdentityOperation_transforms_shape
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    generatedComponentIdentityOperation.shapeTransform
      (AtomShapeOf componentShapePresentation carrier.val)
      (AtomShapeOf componentShapePresentation
        (generatedComponentIdentityOperation.atomMap carrier).val) := by
  exact generatedComponentIdentityOperation.atomShape_transformed carrier

theorem generatedComponentIdentityOperation_does_not_create_atoms :
    componentSystem.noToolOutputCreatesAtoms := by
  exact generatedComponentIdentityOperation.operation_does_not_create_atoms

def generatedComponentIdentityOperationTransportPackage :
    AAT.OperationTransportPackage
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore := by
  exact generatedComponentIdentityOperation.toOperationTransportPackage
    generatedComponentLawModel generatedComponentLawModel

theorem generatedComponentIdentityOperation_transports_molecule :
    ∃ targetMolecule,
      generatedComponentIdentityOperationTransportPackage.selectedTargetMolecule
        targetMolecule ∧
      generatedComponentLawModel.generatedAATCore.molecules targetMolecule := by
  exact
    generatedComponentIdentityOperationTransportPackage.target_molecule_exists
      (molecule := generatedComponentMolecule.toMolecule)
      rfl
      rfl

theorem generatedComponentIdentityOperation_transports_law :
    ∃ targetLaw,
      generatedComponentIdentityOperationTransportPackage.selectedTargetLaw
        targetLaw ∧
      generatedComponentLawModel.generatedAATCore.laws targetLaw := by
  exact
    generatedComponentIdentityOperationTransportPackage.target_law_exists
      (law := generatedComponentLawModel.generatedDesignLaw)
      rfl
      generatedComponentLawModel.generated_law_on_core

def generatedComponentSynthesisCandidate :
    AAT.GeneratedSynthesisCandidate generatedComponentObject where
  lawModel := generatedComponentLawModel
  flatWithin := generatedComponent_architectureFlatWithin
  synthesisDoesNotCreateAtomsEvidence :=
    componentSystem.tool_output_does_not_create_atoms
  synthesisBoundary := True

theorem generatedComponentSynthesisCandidate_flatWithin :
    ArchitectureFlatWithin generatedComponentObject.generatedFlatnessModel
      generatedComponentObject.generatedComponentUniverse := by
  exact generatedComponentSynthesisCandidate.candidate_flatWithin

theorem generatedComponentSynthesisCandidate_totalCurvature_eq_zero :
    totalCurvature AAT.generatedObservationDistance
      generatedComponentObject.generatedSemanticSemantics
      generatedComponentObject.generatedSemanticDiagrams = 0 := by
  exact generatedComponentSynthesisCandidate.candidate_totalCurvature_eq_zero

theorem generatedComponentSynthesisCandidate_does_not_create_atoms :
    componentSystem.noToolOutputCreatesAtoms := by
  exact generatedComponentSynthesisCandidate.synthesis_does_not_create_atoms

def generatedComponentSynthesisSoundnessPackage :
    AAT.SynthesisSoundnessPackage
      generatedComponentLawModel.generatedAATCore
      (AAT.GeneratedSynthesisCandidate generatedComponentObject) := by
  exact generatedComponentSynthesisCandidate.toSynthesisSoundnessPackage

theorem generatedComponentSynthesis_candidate_noRequiredObstructionCircuit :
    AAT.NoRequiredObstructionCircuit
      generatedComponentLawModel.generatedDesignLaw
      generatedComponentLawModel.requiredGeneratedMolecule := by
  exact
    generatedComponentSynthesisSoundnessPackage.candidate_noRequiredObstructionCircuit

theorem generatedComponentSynthesis_candidate_lawful :
    AAT.LawfulWithinMoleculeConfiguration
      generatedComponentLawModel.generatedDesignLaw
      generatedComponentLawModel.requiredGeneratedMolecule := by
  exact
    generatedComponentSynthesisSoundnessPackage.candidate_lawfulWithinMoleculeConfiguration

end Formal.Arch.AtomGeneratedMoleculeExamples
