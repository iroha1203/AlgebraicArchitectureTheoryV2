import Formal.Arch.AAT.GeneratedRepair

namespace Formal.Arch.AtomGeneratedRepairExamples

inductive RepairAtom where
  | api
  | database
  deriving DecidableEq, Repr

def repairKind (_atom : RepairAtom) : AtomKind :=
  AtomKind.existence

def repairAxis (_atom : RepairAtom) : Axis :=
  Axis.static

/-- Source-like atom system used by the generated repair acceptance example. -/
def repairSystem : AtomAxiomSystem where
  Atom := RepairAtom
  Predicate := AtomKind
  kind := repairKind
  axis := repairAxis
  predicate := repairKind
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

def requiredServicePort : AtomPort where
  name := "required-service"
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := True
  acceptsFamily := fun kind => kind = AtomKind.existence
  acceptsAxis := fun axis => axis = Axis.static

def providedServicePort : AtomPort where
  name := "provided-service"
  kind := AtomPortKind.subject
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun kind => kind = AtomKind.existence
  acceptsAxis := fun axis => axis = Axis.static

def requiredProvidedCompatible :
    PortCompatible requiredServicePort providedServicePort := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def providedRequiredCompatible :
    PortCompatible providedServicePort requiredServicePort := by
  exact PortCompatible.symm requiredProvidedCompatible

def apiRequiresServiceValence : AtomValence where
  ports := fun port => port = requiredServicePort
  requiredPort := fun port => port = requiredServicePort
  requiredPortHasPort := by
    intro port hRequired
    exact hRequired
  hasPort := ⟨requiredServicePort, rfl⟩

def databaseProvidesServiceValence : AtomValence where
  ports := fun port => port = providedServicePort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨providedServicePort, rfl⟩

def repairShape (atom : RepairAtom) : AtomShape where
  family := AtomKind.existence
  axis := Axis.static
  subject := { name := match atom with
    | RepairAtom.api => "api"
    | RepairAtom.database => "database" }
  predicate := "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := AtomDirection.neutral
  arity := 1
  valence := match atom with
    | RepairAtom.api => apiRequiresServiceValence
    | RepairAtom.database => databaseProvidesServiceValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def repairShapePresentation :
    AtomShapePresentation repairSystem where
  shapeOf := repairShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

def missingPortAtoms : RepairAtom -> Prop
  | RepairAtom.api => True
  | RepairAtom.database => False

def repairedAtoms : RepairAtom -> Prop
  | RepairAtom.api => True
  | RepairAtom.database => True

/-- Broken pre-molecule configuration: the API atom requires a service port. -/
def missingPortConfiguration :
    AAT.GeneratedRepairProblemConfiguration repairShapePresentation where
  atoms := missingPortAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact repairSystem.primitive atom
  problemBoundary := True

def missingPortApiCarrier :
    AAT.GeneratedRepairProblemCarrier missingPortConfiguration :=
  ⟨RepairAtom.api, by trivial⟩

theorem missingPortConfiguration_missing_match :
    ¬ ∃ other otherPort,
      missingPortConfiguration.atoms other ∧
      other ≠ RepairAtom.api ∧
      (AtomShapeOf repairShapePresentation other).valence.ports otherPort ∧
      PortCompatible requiredServicePort otherPort := by
  intro hMatch
  rcases hMatch with
    ⟨other, _otherPort, hOther, hDistinct, _hOtherPort, _hCompatible⟩
  cases other
  · exact hDistinct rfl
  · cases hOther

def missingPortRepairProblem :
    AAT.GeneratedRepairProblem missingPortConfiguration :=
  AAT.GeneratedRepairProblem.missingRequiredPort
    missingPortApiCarrier
    requiredServicePort
    (by rfl)
    missingPortConfiguration_missing_match

def repairApiDatabaseComposition :
    CompatibleComposition
      (AtomShapeOf repairShapePresentation RepairAtom.api)
      (AtomShapeOf repairShapePresentation RepairAtom.database) where
  leftPort := requiredServicePort
  rightPort := providedServicePort
  leftHasPort := rfl
  rightHasPort := rfl
  portsCompatible := requiredProvidedCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _
    exact ⟨rfl, rfl⟩

def repairDatabaseApiComposition :
    CompatibleComposition
      (AtomShapeOf repairShapePresentation RepairAtom.database)
      (AtomShapeOf repairShapePresentation RepairAtom.api) where
  leftPort := providedServicePort
  rightPort := requiredServicePort
  leftHasPort := rfl
  rightHasPort := rfl
  portsCompatible := providedRequiredCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _
    exact ⟨rfl, rfl⟩

def repairedCompositionGraph :
    AAT.CompositionGraph repairShapePresentation repairedAtoms where
  compatiblePairs := by
    intro left right _hLeft _hRight hDistinct
    cases left
    · cases right
      · exact False.elim (hDistinct rfl)
      · exact repairApiDatabaseComposition
    · cases right
      · exact repairDatabaseApiComposition
      · exact False.elim (hDistinct rfl)
  graphBoundary := True

/-- Repaired target molecule: the required service port is matched by database. -/
def repairedGeneratedMolecule :
    AAT.GeneratedMolecule repairShapePresentation where
  atoms := repairedAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact repairSystem.primitive atom
  compositionGraph := repairedCompositionGraph
  requiredPortsMatched := by
    intro atom port _hAtom hRequired
    cases atom
    · subst port
      exact
        ⟨RepairAtom.database, providedServicePort,
          by trivial,
          (by intro h; cases h),
          by rfl,
          requiredProvidedCompatible⟩
    · change False at hRequired
      cases hRequired
  notArbitrarySet := True
  notArbitrarySetEvidence := trivial

def repairedGeneratedObject :
    AAT.GeneratedArchitectureObject repairShapePresentation where
  molecule := repairedGeneratedMolecule
  carrierList :=
    [ ⟨RepairAtom.api, by trivial⟩
    , ⟨RepairAtom.database, by trivial⟩
    ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom <;> simp
  objectBoundary := True

theorem repairedGeneratedObject_no_relation_atom
    (carrier : AAT.GeneratedCarrier repairedGeneratedObject) :
    (AtomShapeOf repairShapePresentation carrier.val).family ≠
      AtomKind.relation := by
  cases carrier.val <;> intro hRelation <;> cases hRelation

theorem repairedGeneratedGraph_no_edges :
    ∀ source target,
      ¬ (AAT.GeneratedArchGraph repairedGeneratedObject).edge
        source target := by
  intro source target hEdge
  rcases hEdge with ⟨relation, hRelation⟩
  exact
    repairedGeneratedObject_no_relation_atom
      relation hRelation.relationFamily

theorem repairedGeneratedGraph_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph repairedGeneratedObject) := by
  intro hClosed
  rcases hClosed with ⟨_carrier, walk, hPositive⟩
  cases walk with
  | nil _ =>
      simp [Walk.length] at hPositive
  | cons hEdge _rest =>
      exact repairedGeneratedGraph_no_edges _ _ hEdge

def repairedGeneratedGraphRank :
    AAT.GeneratedGraphRank repairedGeneratedObject where
  rank := fun _carrier => 0
  edgeRankDecreases := by
    intro source target hEdge
    exact False.elim (repairedGeneratedGraph_no_edges source target hEdge)

theorem repairedGeneratedGraphRank_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph repairedGeneratedObject) :=
  repairedGeneratedGraphRank.walkAcyclic

theorem repaired_law_model_from_graph_rank :
    ∃ model : AAT.GeneratedArchitectureLawModel repairedGeneratedObject,
      ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel :=
  AAT.GeneratedArchitectureLawModel.generated_law_model_from_generated_graph_rank
    repairedGeneratedGraphRank True

def repairedGeneratedLawModel :
    AAT.GeneratedArchitectureLawModel repairedGeneratedObject :=
  AAT.GeneratedArchitectureLawModel.ofGraphRank
    repairedGeneratedGraphRank True

def repairedGeneratedZeroCurvaturePackage :
    AAT.ZeroCurvaturePackage repairedGeneratedLawModel.generatedAATCore := by
  exact repairedGeneratedLawModel.generatedZeroCurvaturePackage

def repairedApiCarrier :
    AAT.GeneratedCarrier repairedGeneratedObject :=
  ⟨RepairAtom.api, by trivial⟩

def missingPortRepairOperation :
    AAT.GeneratedRepairProblemOperation
      missingPortConfiguration repairedGeneratedObject where
  atomMap := by
    intro carrier
    cases carrier with
    | mk atom hAtom =>
        cases atom
        · exact repairedApiCarrier
        · cases hAtom
  shapeTransform := fun source target => source = target
  transformsAtomShape := by
    intro carrier
    cases carrier with
    | mk atom hAtom =>
        cases atom
        · rfl
        · cases hAtom
  operationDoesNotCreateAtomsEvidence :=
    repairSystem.tool_output_does_not_create_atoms
  operationBoundary := True

def missingPortRepairCleared :
    AAT.GeneratedRepairProblemCleared
      missingPortRepairOperation missingPortRepairProblem :=
  AAT.GeneratedRepairProblemCleared.missingRequiredPortCleared
    RepairAtom.database
    providedServicePort
    (by
      exact
        ⟨by trivial,
          (by intro h; cases h),
          by rfl,
          requiredProvidedCompatible⟩)

/--
Generated repair acceptance: the source is a failed atom configuration, and the
target is a valid generated object.
-/
def generatedMissingPortRepair :
    AAT.GeneratedRepairFromProblem
      missingPortConfiguration repairedGeneratedObject where
  operation := missingPortRepairOperation
  repairProblem := missingPortRepairProblem
  clearsProblem := missingPortRepairCleared
  repairBoundary := True

theorem missingPortConfiguration_not_generatedMolecule
    (molecule : AAT.GeneratedMolecule repairShapePresentation)
    (hAtoms : ∀ atom, molecule.atoms atom ↔ missingPortAtoms atom) :
    False := by
  exact
    molecule.missing_required_port_not_generatedMolecule
      ((hAtoms RepairAtom.api).2 trivial)
      (by rfl)
      (by
        intro hMatch
        rcases hMatch with
          ⟨other, _otherPort, hOther, hDistinct, _hOtherPort, _hCompatible⟩
        have hSourceAtom : missingPortAtoms other := (hAtoms other).1 hOther
        cases other
        · exact hDistinct rfl
        · cases hSourceAtom)

def generatedMissingPortRepair_clears_problem :
    AAT.GeneratedRepairProblemCleared
      generatedMissingPortRepair.operation
      generatedMissingPortRepair.repairProblem := by
  exact generatedMissingPortRepair.clears_selected_problem

def generatedMissingPortRepair_target_generated_molecule :
    AAT.GeneratedMolecule repairShapePresentation := by
  exact generatedMissingPortRepair.target_generated_molecule

theorem generatedMissingPortRepair_problem_shapeLevel :
    generatedMissingPortRepair.repairProblem.shapeLevel := by
  exact generatedMissingPortRepair.problem_shapeLevel

theorem generatedMissingPortRepair_transforms_shape :
    missingPortRepairOperation.shapeTransform
      (AtomShapeOf repairShapePresentation missingPortApiCarrier.val)
      (AtomShapeOf repairShapePresentation
        (missingPortRepairOperation.atomMap missingPortApiCarrier).val) := by
  exact missingPortRepairOperation.atomShape_transformed missingPortApiCarrier

theorem generatedMissingPortRepair_target_atom_primitive :
    repairSystem.Primitive
      (missingPortRepairOperation.atomMap missingPortApiCarrier).val := by
  exact missingPortRepairOperation.target_atom_primitive missingPortApiCarrier

theorem generatedMissingPortRepair_does_not_create_atoms :
    repairSystem.noToolOutputCreatesAtoms := by
  exact generatedMissingPortRepair.repair_problem_does_not_create_atoms

def generatedMissingPortRepairClearingPackage :
    AAT.RepairClearingPackage
      repairedGeneratedLawModel.generatedAATCore
      (Sum
        (AAT.GeneratedRepairProblemConfiguration repairShapePresentation)
        (AAT.GeneratedArchitectureObject repairShapePresentation))
      Unit
      (Sum.inl missingPortConfiguration)
      (Sum.inr repairedGeneratedObject) := by
  exact generatedMissingPortRepair.toRepairClearingPackage
    repairedGeneratedLawModel

theorem generatedMissingPortRepair_target_noRequiredObstructionCircuit :
    AAT.NoRequiredObstructionCircuit
      repairedGeneratedLawModel.generatedDesignLaw
      repairedGeneratedLawModel.requiredGeneratedMolecule := by
  exact
    generatedMissingPortRepairClearingPackage.target_noRequiredObstructionCircuit

theorem generatedMissingPortRepair_target_lawful :
    AAT.LawfulWithinMoleculeConfiguration
      repairedGeneratedLawModel.generatedDesignLaw
      repairedGeneratedLawModel.requiredGeneratedMolecule := by
  exact
    generatedMissingPortRepairClearingPackage.target_lawfulWithinMoleculeConfiguration

end Formal.Arch.AtomGeneratedRepairExamples
