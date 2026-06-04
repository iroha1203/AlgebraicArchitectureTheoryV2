import Formal.Arch.AAT.GeneratedCurvature
import Formal.Arch.AAT.GeneratedDistance
import Formal.Arch.AAT.GeneratedDiagram
import Formal.Arch.AAT.GeneratedPath
import Formal.Arch.AAT.GeneratedSynthesis
import Formal.Arch.Evolution.Chapter7TheoremPackages
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

theorem generatedComponentMolecule_not_arbitrary_set :
    generatedComponentMolecule.notArbitrarySet := by
  exact generatedComponentMolecule.not_arbitrary_set

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
    exact
      generatedComponentObject_no_relation_atom
        relation hRelation.relationFamily)

instance componentSystemAtomDecidableEq :
    DecidableEq componentSystem.Atom :=
  inferInstanceAs (DecidableEq ComponentAtom)

theorem generatedComponentGraph_no_edges :
    ∀ source target,
      ¬ (AAT.GeneratedArchGraph generatedComponentObject).edge
        source target := by
  intro source target hEdge
  rcases hEdge with ⟨relation, hRelation⟩
  exact
    generatedComponentObject_no_relation_atom
      relation hRelation.relationFamily

theorem generatedComponentGraph_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph generatedComponentObject) := by
  intro hClosed
  rcases hClosed with ⟨_carrier, walk, hPositive⟩
  cases walk with
  | nil _ =>
      simp [Walk.length] at hPositive
  | cons hEdge _rest =>
      exact generatedComponentGraph_no_edges _ _ hEdge

def generatedComponentGraphRank :
    AAT.GeneratedGraphRank generatedComponentObject where
  rank := fun _carrier => 0
  edgeRankDecreases := by
    intro source target hEdge
    exact False.elim (generatedComponentGraph_no_edges source target hEdge)

theorem generatedComponentGraphRank_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph generatedComponentObject) :=
  generatedComponentGraphRank.walkAcyclic

theorem generatedComponent_law_model_from_graph_rank :
    ∃ model : AAT.GeneratedArchitectureLawModel generatedComponentObject,
      ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel :=
  AAT.GeneratedArchitectureLawModel.generated_law_model_from_generated_graph_rank
    generatedComponentGraphRank True

/-- Generated law model built from the generated object, not from a hand-authored graph. -/
def generatedComponentLawModel :
    AAT.GeneratedArchitectureLawModel generatedComponentObject :=
  AAT.GeneratedArchitectureLawModel.ofGraphRank
    generatedComponentGraphRank True

theorem generatedComponentLawModel_carries_generated_graph_rank :
    generatedComponentLawModel.graphRank = generatedComponentGraphRank := by
  rfl

theorem generatedComponentLawModel_walkAcyclic_derived_from_graph_rank :
    generatedComponentLawModel.generatedWalkAcyclic =
      generatedComponentGraphRank.walkAcyclic := by
  rfl

inductive DirectedRelationAtom where
  | api
  | apiToDatabase
  | database
  deriving DecidableEq, Repr

def directedRelationKind : DirectedRelationAtom -> AtomKind
  | .api => AtomKind.existence
  | .apiToDatabase => AtomKind.relation
  | .database => AtomKind.existence

def directedRelationAxis (_atom : DirectedRelationAtom) : Axis :=
  Axis.static

/-- Atom system with an explicit API -> database relation atom. -/
def directedRelationSystem : AtomAxiomSystem where
  Atom := DirectedRelationAtom
  Predicate := AtomKind
  kind := directedRelationKind
  axis := directedRelationAxis
  predicate := directedRelationKind
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

def relationSourcePort : AtomPort where
  name := "relation-source"
  kind := AtomPortKind.relationSource
  family := AtomKind.relation
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def apiRelationSourcePort : AtomPort where
  name := "api-relation-source"
  kind := AtomPortKind.relationSource
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def relationTargetPort : AtomPort where
  name := "relation-target"
  kind := AtomPortKind.relationTarget
  family := AtomKind.relation
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def databaseRelationTargetPort : AtomPort where
  name := "database-relation-target"
  kind := AtomPortKind.relationTarget
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def directedApiValence : AtomValence where
  ports := fun port => port = apiPort ∨ port = apiRelationSourcePort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨apiPort, Or.inl rfl⟩

def directedRelationValence : AtomValence where
  ports := fun port => port = relationSourcePort ∨ port = relationTargetPort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨relationSourcePort, Or.inl rfl⟩

def directedDatabaseValence : AtomValence where
  ports := fun port => port = databasePort ∨ port = databaseRelationTargetPort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨databasePort, Or.inl rfl⟩

def directedRelationShape (atom : DirectedRelationAtom) : AtomShape where
  family := directedRelationKind atom
  axis := Axis.static
  subject := { name := match atom with
    | .api => "api"
    | .apiToDatabase => "api-to-database"
    | .database => "database" }
  predicate := match atom with
    | .api => "component"
    | .apiToDatabase => "relation"
    | .database => "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := match atom with
    | .apiToDatabase => AtomDirection.outgoing
    | _ => AtomDirection.neutral
  arity := match atom with
    | .apiToDatabase => 2
    | _ => 1
  valence := match atom with
    | .api => directedApiValence
    | .apiToDatabase => directedRelationValence
    | .database => directedDatabaseValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def directedRelationShapePresentation :
    AtomShapePresentation directedRelationSystem where
  shapeOf := directedRelationShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

def directedRelationSelectedAtoms : DirectedRelationAtom -> Prop
  | .api => True
  | .apiToDatabase => True
  | .database => True

def relationSourcePortCompatible :
    PortCompatible relationSourcePort apiRelationSourcePort := by
  exact ⟨rfl, trivial, trivial, trivial, trivial⟩

def relationSourcePortCompatibleSymm :
    PortCompatible apiRelationSourcePort relationSourcePort :=
  PortCompatible.symm relationSourcePortCompatible

def relationTargetPortCompatible :
    PortCompatible relationTargetPort databaseRelationTargetPort := by
  exact ⟨rfl, trivial, trivial, trivial, trivial⟩

def relationTargetPortCompatibleSymm :
    PortCompatible databaseRelationTargetPort relationTargetPort :=
  PortCompatible.symm relationTargetPortCompatible

def directedApiDatabaseComposition :
    CompatibleComposition
      (AtomShapeOf directedRelationShapePresentation DirectedRelationAtom.api)
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.database) where
  leftPort := apiPort
  rightPort := databasePort
  leftHasPort := Or.inl rfl
  rightHasPort := Or.inl rfl
  portsCompatible := componentPortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _hPredicate
    exact ⟨rfl, rfl⟩

def directedDatabaseApiComposition :
    CompatibleComposition
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.database)
      (AtomShapeOf directedRelationShapePresentation DirectedRelationAtom.api) where
  leftPort := databasePort
  rightPort := apiPort
  leftHasPort := Or.inl rfl
  rightHasPort := Or.inl rfl
  portsCompatible := databasePortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _hPredicate
    exact ⟨rfl, rfl⟩

def directedRelationApiSourceComposition :
    CompatibleComposition
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.apiToDatabase)
      (AtomShapeOf directedRelationShapePresentation DirectedRelationAtom.api) where
  leftPort := relationSourcePort
  rightPort := apiRelationSourcePort
  leftHasPort := Or.inl rfl
  rightHasPort := Or.inr rfl
  portsCompatible := relationSourcePortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent : ("relation" : String) ≠ "component" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedApiRelationSourceComposition :
    CompatibleComposition
      (AtomShapeOf directedRelationShapePresentation DirectedRelationAtom.api)
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.apiToDatabase) where
  leftPort := apiRelationSourcePort
  rightPort := relationSourcePort
  leftHasPort := Or.inr rfl
  rightHasPort := Or.inl rfl
  portsCompatible := relationSourcePortCompatibleSymm
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent : ("component" : String) ≠ "relation" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedRelationDatabaseTargetComposition :
    CompatibleComposition
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.apiToDatabase)
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.database) where
  leftPort := relationTargetPort
  rightPort := databaseRelationTargetPort
  leftHasPort := Or.inr rfl
  rightHasPort := Or.inr rfl
  portsCompatible := relationTargetPortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent : ("relation" : String) ≠ "component" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedDatabaseRelationTargetComposition :
    CompatibleComposition
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.database)
      (AtomShapeOf directedRelationShapePresentation
        DirectedRelationAtom.apiToDatabase) where
  leftPort := databaseRelationTargetPort
  rightPort := relationTargetPort
  leftHasPort := Or.inr rfl
  rightHasPort := Or.inr rfl
  portsCompatible := relationTargetPortCompatibleSymm
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent : ("component" : String) ≠ "relation" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedRelationCompositionGraph :
    AAT.CompositionGraph
      directedRelationShapePresentation directedRelationSelectedAtoms where
  compatiblePairs := by
    intro left right _hLeft _hRight hDistinct
    cases left
    · cases right
      · exact False.elim (hDistinct rfl)
      · exact directedApiRelationSourceComposition
      · exact directedApiDatabaseComposition
    · cases right
      · exact directedRelationApiSourceComposition
      · exact False.elim (hDistinct rfl)
      · exact directedRelationDatabaseTargetComposition
    · cases right
      · exact directedDatabaseApiComposition
      · exact directedDatabaseRelationTargetComposition
      · exact False.elim (hDistinct rfl)
  graphBoundary := True

/-- Positive graph example with an oriented API -> database relation atom. -/
def directedRelationGeneratedMolecule :
    AAT.GeneratedMolecule directedRelationShapePresentation where
  atoms := directedRelationSelectedAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact directedRelationSystem.primitive atom
  compositionGraph := directedRelationCompositionGraph
  requiredPortsMatched := by
    intro atom _port _hAtom hRequired
    cases atom <;> cases hRequired

def directedRelationGeneratedObject :
    AAT.GeneratedArchitectureObject directedRelationShapePresentation where
  molecule := directedRelationGeneratedMolecule
  carrierList :=
    [ ⟨DirectedRelationAtom.api, by trivial⟩
    , ⟨DirectedRelationAtom.apiToDatabase, by trivial⟩
    , ⟨DirectedRelationAtom.database, by trivial⟩
    ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom <;> simp
  objectBoundary := True

def directedRelationApiCarrier :
    AAT.GeneratedCarrier directedRelationGeneratedObject :=
  ⟨DirectedRelationAtom.api, by trivial⟩

def directedRelationAtomCarrier :
    AAT.GeneratedCarrier directedRelationGeneratedObject :=
  ⟨DirectedRelationAtom.apiToDatabase, by trivial⟩

def directedRelationDatabaseCarrier :
    AAT.GeneratedCarrier directedRelationGeneratedObject :=
  ⟨DirectedRelationAtom.database, by trivial⟩

def directedRelationAtom_api_to_database :
    AAT.GeneratedRelationAtom
      directedRelationGeneratedObject
      directedRelationAtomCarrier
      directedRelationApiCarrier
      directedRelationDatabaseCarrier where
  relationFamily := rfl
  relationSourceDistinct := by
    intro hEq
    cases hEq
  relationTargetDistinct := by
    intro hEq
    cases hEq
  endpointsDistinct := by
    intro hEq
    cases hEq
  sourceCompositionUsesRelationSource := by
    native_decide
  targetCompositionUsesRelationTarget := by
    native_decide

theorem directedRelationGeneratedGraph_api_to_database_edge :
    (AAT.GeneratedArchGraph directedRelationGeneratedObject).edge
      directedRelationApiCarrier directedRelationDatabaseCarrier := by
  exact ⟨directedRelationAtomCarrier, directedRelationAtom_api_to_database⟩

def directedRelationGeneratedGraph_api_to_database_witness :
    AAT.GeneratedRelationEdgeWitness
      directedRelationGeneratedObject
      directedRelationApiCarrier
      directedRelationDatabaseCarrier :=
  AAT.GeneratedArchGraph.generated_relation_atom_witness
    directedRelationGeneratedObject
    directedRelationAtom_api_to_database

theorem directedRelationGeneratedGraph_edge_uses_source_target_ports :
    (directedRelationGeneratedGraph_api_to_database_witness.relationSourceComposition.leftPort.kind =
        AtomPortKind.relationSource) ∧
      (directedRelationGeneratedGraph_api_to_database_witness.relationTargetComposition.leftPort.kind =
          AtomPortKind.relationTarget) := by
  native_decide

theorem directedRelationGeneratedGraph_no_database_to_api_edge :
    ¬ (AAT.GeneratedArchGraph directedRelationGeneratedObject).edge
      directedRelationDatabaseCarrier directedRelationApiCarrier := by
  intro hEdge
  rcases hEdge with ⟨relation, hRelation⟩
  rcases relation with ⟨atom, hAtom⟩
  cases atom
  · cases hRelation.relationFamily
  · have hSourceKind : False := by
      simpa [AAT.GeneratedMolecule.compatible_pairs,
        AAT.CompositionGraph.compatible_pairs,
        directedRelationGeneratedObject,
        directedRelationGeneratedMolecule,
        directedRelationDatabaseCarrier,
        directedRelationCompositionGraph,
        directedRelationDatabaseTargetComposition,
        directedDatabaseRelationTargetComposition,
        relationTargetPort]
        using hRelation.sourceCompositionUsesRelationSource.1
    exact hSourceKind
  · cases hRelation.relationFamily

def directedRelationCarrierRank
    (carrier : AAT.GeneratedCarrier directedRelationGeneratedObject) : Nat :=
  match carrier.val with
  | DirectedRelationAtom.api => 1
  | DirectedRelationAtom.apiToDatabase => 2
  | DirectedRelationAtom.database => 0

theorem directedRelationGeneratedGraph_edge_only_api_to_database
    {source target : AAT.GeneratedCarrier directedRelationGeneratedObject}
    (hEdge : (AAT.GeneratedArchGraph directedRelationGeneratedObject).edge
      source target) :
    source.val = DirectedRelationAtom.api ∧
      target.val = DirectedRelationAtom.database := by
  rcases hEdge with ⟨relation, hRelation⟩
  rcases relation with ⟨relationAtom, hRelationAtom⟩
  rcases source with ⟨sourceAtom, hSourceAtom⟩
  rcases target with ⟨targetAtom, hTargetAtom⟩
  cases relationAtom
  · cases hRelation.relationFamily
  · constructor
    · cases sourceAtom
      · rfl
      · exact False.elim (hRelation.relationSourceDistinct rfl)
      · have hSourceKind : False := by
          simpa [AAT.GeneratedMolecule.compatible_pairs,
            AAT.CompositionGraph.compatible_pairs,
            directedRelationGeneratedObject,
            directedRelationGeneratedMolecule,
            directedRelationCompositionGraph,
            directedRelationDatabaseTargetComposition,
            directedDatabaseRelationTargetComposition,
            relationTargetPort]
            using hRelation.sourceCompositionUsesRelationSource.1
        exact False.elim hSourceKind
    · cases targetAtom
      · have hTargetKind : False := by
          simpa [AAT.GeneratedMolecule.compatible_pairs,
            AAT.CompositionGraph.compatible_pairs,
            directedRelationGeneratedObject,
            directedRelationGeneratedMolecule,
            directedRelationCompositionGraph,
            directedRelationApiSourceComposition,
            directedApiRelationSourceComposition,
            relationSourcePort]
            using hRelation.targetCompositionUsesRelationTarget.1
        exact False.elim hTargetKind
      · exact False.elim (hRelation.relationTargetDistinct rfl)
      · rfl
  · cases hRelation.relationFamily

def directedRelationGraphRank :
    AAT.GeneratedGraphRank directedRelationGeneratedObject where
  rank := directedRelationCarrierRank
  edgeRankDecreases := by
    intro source target hEdge
    rcases directedRelationGeneratedGraph_edge_only_api_to_database hEdge with
      ⟨hSource, hTarget⟩
    simp [directedRelationCarrierRank, hSource, hTarget]

theorem directedRelationGraphRank_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph directedRelationGeneratedObject) :=
  directedRelationGraphRank.walkAcyclic

theorem directedRelation_law_model_from_graph_rank :
    ∃ model : AAT.GeneratedArchitectureLawModel directedRelationGeneratedObject,
      ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel :=
  AAT.GeneratedArchitectureLawModel.generated_law_model_from_generated_graph_rank
    directedRelationGraphRank True

def directedRelationLawModel :
    AAT.GeneratedArchitectureLawModel directedRelationGeneratedObject :=
  AAT.GeneratedArchitectureLawModel.ofGraphRank
    directedRelationGraphRank True

inductive DirectedRuntimeAtom where
  | api
  | apiRuntimeDatabase
  | database
  deriving DecidableEq, Repr

def directedRuntimeKind : DirectedRuntimeAtom -> AtomKind
  | .api => AtomKind.existence
  | .apiRuntimeDatabase => AtomKind.runtimeInteraction
  | .database => AtomKind.existence

def directedRuntimeAxis : DirectedRuntimeAtom -> Axis
  | .apiRuntimeDatabase => Axis.runtime
  | _ => Axis.static

/-- Atom system with an explicit API -> database runtime interaction atom. -/
def directedRuntimeSystem : AtomAxiomSystem where
  Atom := DirectedRuntimeAtom
  Predicate := AtomKind
  kind := directedRuntimeKind
  axis := directedRuntimeAxis
  predicate := directedRuntimeKind
  predicateKind := fun kind => kind
  predicateAxis := fun kind =>
    match kind with
    | AtomKind.runtimeInteraction => Axis.runtime
    | _ => Axis.static
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

def runtimeSourcePort : AtomPort where
  name := "runtime-source"
  kind := AtomPortKind.runtimeSource
  family := AtomKind.runtimeInteraction
  axis := Axis.runtime
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def apiRuntimeSourcePort : AtomPort where
  name := "api-runtime-source"
  kind := AtomPortKind.runtimeSource
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def runtimeTargetPort : AtomPort where
  name := "runtime-target"
  kind := AtomPortKind.runtimeTarget
  family := AtomKind.runtimeInteraction
  axis := Axis.runtime
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def databaseRuntimeTargetPort : AtomPort where
  name := "database-runtime-target"
  kind := AtomPortKind.runtimeTarget
  family := AtomKind.existence
  axis := Axis.static
  required := False
  acceptsFamily := fun _ => True
  acceptsAxis := fun _ => True

def directedRuntimeApiValence : AtomValence where
  ports := fun port => port = apiPort ∨ port = apiRuntimeSourcePort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨apiPort, Or.inl rfl⟩

def directedRuntimeInteractionValence : AtomValence where
  ports := fun port => port = runtimeSourcePort ∨ port = runtimeTargetPort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨runtimeSourcePort, Or.inl rfl⟩

def directedRuntimeDatabaseValence : AtomValence where
  ports := fun port => port = databasePort ∨ port = databaseRuntimeTargetPort
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨databasePort, Or.inl rfl⟩

def directedRuntimeShape (atom : DirectedRuntimeAtom) : AtomShape where
  family := directedRuntimeKind atom
  axis := directedRuntimeAxis atom
  subject := { name := match atom with
    | .api => "api"
    | .apiRuntimeDatabase => "api-runtime-database"
    | .database => "database" }
  predicate := match atom with
    | .api => "component"
    | .apiRuntimeDatabase => "runtime-interaction"
    | .database => "component"
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := match atom with
    | .apiRuntimeDatabase => AtomDirection.outgoing
    | _ => AtomDirection.neutral
  arity := match atom with
    | .apiRuntimeDatabase => 2
    | _ => 1
  valence := match atom with
    | .api => directedRuntimeApiValence
    | .apiRuntimeDatabase => directedRuntimeInteractionValence
    | .database => directedRuntimeDatabaseValence
  singleFactShape := True
  singleFactShapeEvidence := trivial

def directedRuntimeShapePresentation :
    AtomShapePresentation directedRuntimeSystem where
  shapeOf := directedRuntimeShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

def directedRuntimeSelectedAtoms : DirectedRuntimeAtom -> Prop
  | .api => True
  | .apiRuntimeDatabase => True
  | .database => True

def runtimeSourcePortCompatible :
    PortCompatible runtimeSourcePort apiRuntimeSourcePort := by
  exact ⟨rfl, trivial, trivial, trivial, trivial⟩

def runtimeSourcePortCompatibleSymm :
    PortCompatible apiRuntimeSourcePort runtimeSourcePort :=
  PortCompatible.symm runtimeSourcePortCompatible

def runtimeTargetPortCompatible :
    PortCompatible runtimeTargetPort databaseRuntimeTargetPort := by
  exact ⟨rfl, trivial, trivial, trivial, trivial⟩

def runtimeTargetPortCompatibleSymm :
    PortCompatible databaseRuntimeTargetPort runtimeTargetPort :=
  PortCompatible.symm runtimeTargetPortCompatible

def directedRuntimeApiDatabaseComposition :
    CompatibleComposition
      (AtomShapeOf directedRuntimeShapePresentation DirectedRuntimeAtom.api)
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.database) where
  leftPort := apiPort
  rightPort := databasePort
  leftHasPort := Or.inl rfl
  rightHasPort := Or.inl rfl
  portsCompatible := componentPortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _hPredicate
    exact ⟨rfl, rfl⟩

def directedRuntimeDatabaseApiComposition :
    CompatibleComposition
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.database)
      (AtomShapeOf directedRuntimeShapePresentation DirectedRuntimeAtom.api) where
  leftPort := databasePort
  rightPort := apiPort
  leftHasPort := Or.inl rfl
  rightHasPort := Or.inl rfl
  portsCompatible := databasePortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro _hPredicate
    exact ⟨rfl, rfl⟩

def directedRuntimeApiSourceComposition :
    CompatibleComposition
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.apiRuntimeDatabase)
      (AtomShapeOf directedRuntimeShapePresentation DirectedRuntimeAtom.api) where
  leftPort := runtimeSourcePort
  rightPort := apiRuntimeSourcePort
  leftHasPort := Or.inl rfl
  rightHasPort := Or.inr rfl
  portsCompatible := runtimeSourcePortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent :
        ("runtime-interaction" : String) ≠ "component" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedApiRuntimeSourceComposition :
    CompatibleComposition
      (AtomShapeOf directedRuntimeShapePresentation DirectedRuntimeAtom.api)
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.apiRuntimeDatabase) where
  leftPort := apiRuntimeSourcePort
  rightPort := runtimeSourcePort
  leftHasPort := Or.inr rfl
  rightHasPort := Or.inl rfl
  portsCompatible := runtimeSourcePortCompatibleSymm
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent :
        ("component" : String) ≠ "runtime-interaction" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedRuntimeDatabaseTargetComposition :
    CompatibleComposition
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.apiRuntimeDatabase)
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.database) where
  leftPort := runtimeTargetPort
  rightPort := databaseRuntimeTargetPort
  leftHasPort := Or.inr rfl
  rightHasPort := Or.inr rfl
  portsCompatible := runtimeTargetPortCompatible
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent :
        ("runtime-interaction" : String) ≠ "component" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedDatabaseRuntimeTargetComposition :
    CompatibleComposition
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.database)
      (AtomShapeOf directedRuntimeShapePresentation
        DirectedRuntimeAtom.apiRuntimeDatabase) where
  leftPort := databaseRuntimeTargetPort
  rightPort := runtimeTargetPort
  leftHasPort := Or.inr rfl
  rightHasPort := Or.inr rfl
  portsCompatible := runtimeTargetPortCompatibleSymm
  objectSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  payloadSlotsCompatible := by
    intro _ _ hSlot _
    cases hSlot
  predicateSlotsCompatible := by
    intro hPredicate
    have hDifferent :
        ("component" : String) ≠ "runtime-interaction" := by
      decide
    exact False.elim (hDifferent hPredicate)

def directedRuntimeCompositionGraph :
    AAT.CompositionGraph
      directedRuntimeShapePresentation directedRuntimeSelectedAtoms where
  compatiblePairs := by
    intro left right _hLeft _hRight hDistinct
    cases left
    · cases right
      · exact False.elim (hDistinct rfl)
      · exact directedApiRuntimeSourceComposition
      · exact directedRuntimeApiDatabaseComposition
    · cases right
      · exact directedRuntimeApiSourceComposition
      · exact False.elim (hDistinct rfl)
      · exact directedRuntimeDatabaseTargetComposition
    · cases right
      · exact directedRuntimeDatabaseApiComposition
      · exact directedDatabaseRuntimeTargetComposition
      · exact False.elim (hDistinct rfl)
  graphBoundary := True

/-- Positive graph example with an oriented API -> database runtime interaction atom. -/
def directedRuntimeGeneratedMolecule :
    AAT.GeneratedMolecule directedRuntimeShapePresentation where
  atoms := directedRuntimeSelectedAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom _
    exact directedRuntimeSystem.primitive atom
  compositionGraph := directedRuntimeCompositionGraph
  requiredPortsMatched := by
    intro atom _port _hAtom hRequired
    cases atom <;> cases hRequired

def directedRuntimeGeneratedObject :
    AAT.GeneratedArchitectureObject directedRuntimeShapePresentation where
  molecule := directedRuntimeGeneratedMolecule
  carrierList :=
    [ ⟨DirectedRuntimeAtom.api, by trivial⟩
    , ⟨DirectedRuntimeAtom.apiRuntimeDatabase, by trivial⟩
    , ⟨DirectedRuntimeAtom.database, by trivial⟩
    ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom _hAtom =>
        cases atom <;> simp
  objectBoundary := True

def directedRuntimeApiCarrier :
    AAT.GeneratedCarrier directedRuntimeGeneratedObject :=
  ⟨DirectedRuntimeAtom.api, by trivial⟩

def directedRuntimeInteractionCarrier :
    AAT.GeneratedCarrier directedRuntimeGeneratedObject :=
  ⟨DirectedRuntimeAtom.apiRuntimeDatabase, by trivial⟩

def directedRuntimeDatabaseCarrier :
    AAT.GeneratedCarrier directedRuntimeGeneratedObject :=
  ⟨DirectedRuntimeAtom.database, by trivial⟩

def directedRuntimeInteraction_api_to_database :
    AAT.GeneratedRuntimeRelationAtom
      directedRuntimeGeneratedObject
      directedRuntimeInteractionCarrier
      directedRuntimeApiCarrier
      directedRuntimeDatabaseCarrier where
  interactionFamily := rfl
  interactionSourceDistinct := by
    intro hEq
    cases hEq
  interactionTargetDistinct := by
    intro hEq
    cases hEq
  endpointsDistinct := by
    intro hEq
    cases hEq
  sourceCompositionUsesRuntimeSource := by
    native_decide
  targetCompositionUsesRuntimeTarget := by
    native_decide

theorem directedRuntimeGeneratedGraph_api_to_database_edge :
    (AAT.GeneratedRuntimeGraph directedRuntimeGeneratedObject).edge
      directedRuntimeApiCarrier directedRuntimeDatabaseCarrier := by
  exact
    ⟨directedRuntimeInteractionCarrier,
      directedRuntimeInteraction_api_to_database⟩

def directedRuntimeGeneratedGraph_api_to_database_witness :
    AAT.GeneratedRuntimeEdgeWitness
      directedRuntimeGeneratedObject
      directedRuntimeApiCarrier
      directedRuntimeDatabaseCarrier :=
  AAT.GeneratedRuntimeGraph.generated_runtime_atom_witness
    directedRuntimeGeneratedObject
    directedRuntimeInteraction_api_to_database

theorem directedRuntimeGeneratedGraph_edge_uses_source_target_ports :
    (directedRuntimeGeneratedGraph_api_to_database_witness.interactionSourceComposition.leftPort.kind =
        AtomPortKind.runtimeSource) ∧
      (directedRuntimeGeneratedGraph_api_to_database_witness.interactionTargetComposition.leftPort.kind =
          AtomPortKind.runtimeTarget) := by
  native_decide

theorem directedRuntimeGeneratedGraph_no_database_to_api_edge :
    ¬ (AAT.GeneratedRuntimeGraph directedRuntimeGeneratedObject).edge
      directedRuntimeDatabaseCarrier directedRuntimeApiCarrier := by
  intro hEdge
  rcases hEdge with ⟨interaction, hInteraction⟩
  rcases interaction with ⟨atom, hAtom⟩
  cases atom
  · cases hInteraction.interactionFamily
  · have hSourceKind : False := by
      simpa [AAT.GeneratedMolecule.compatible_pairs,
        AAT.CompositionGraph.compatible_pairs,
        directedRuntimeGeneratedObject,
        directedRuntimeGeneratedMolecule,
        directedRuntimeDatabaseCarrier,
        directedRuntimeCompositionGraph,
        directedRuntimeDatabaseTargetComposition,
        directedDatabaseRuntimeTargetComposition,
        runtimeTargetPort]
        using hInteraction.sourceCompositionUsesRuntimeSource.1
    exact hSourceKind
  · cases hInteraction.interactionFamily

def directedRuntimeCarrierRank
    (carrier : AAT.GeneratedCarrier directedRuntimeGeneratedObject) : Nat :=
  match carrier.val with
  | DirectedRuntimeAtom.api => 1
  | DirectedRuntimeAtom.apiRuntimeDatabase => 2
  | DirectedRuntimeAtom.database => 0

theorem directedRuntimeGeneratedGraph_edge_only_api_to_database
    {source target : AAT.GeneratedCarrier directedRuntimeGeneratedObject}
    (hEdge : (AAT.GeneratedRuntimeGraph directedRuntimeGeneratedObject).edge
      source target) :
    source.val = DirectedRuntimeAtom.api ∧
      target.val = DirectedRuntimeAtom.database := by
  rcases hEdge with ⟨interaction, hInteraction⟩
  rcases interaction with ⟨interactionAtom, hInteractionAtom⟩
  rcases source with ⟨sourceAtom, hSourceAtom⟩
  rcases target with ⟨targetAtom, hTargetAtom⟩
  cases interactionAtom
  · cases hInteraction.interactionFamily
  · constructor
    · cases sourceAtom
      · rfl
      · exact False.elim (hInteraction.interactionSourceDistinct rfl)
      · have hSourceKind : False := by
          simpa [AAT.GeneratedMolecule.compatible_pairs,
            AAT.CompositionGraph.compatible_pairs,
            directedRuntimeGeneratedObject,
            directedRuntimeGeneratedMolecule,
            directedRuntimeCompositionGraph,
            directedRuntimeDatabaseTargetComposition,
            directedDatabaseRuntimeTargetComposition,
            runtimeTargetPort]
            using hInteraction.sourceCompositionUsesRuntimeSource.1
        exact False.elim hSourceKind
    · cases targetAtom
      · have hTargetKind : False := by
          simpa [AAT.GeneratedMolecule.compatible_pairs,
            AAT.CompositionGraph.compatible_pairs,
            directedRuntimeGeneratedObject,
            directedRuntimeGeneratedMolecule,
            directedRuntimeCompositionGraph,
            directedRuntimeApiSourceComposition,
            directedApiRuntimeSourceComposition,
            runtimeSourcePort]
            using hInteraction.targetCompositionUsesRuntimeTarget.1
        exact False.elim hTargetKind
      · exact False.elim (hInteraction.interactionTargetDistinct rfl)
      · rfl
  · cases hInteraction.interactionFamily

def directedRuntimeGraphRank :
    AAT.GeneratedRuntimeGraphRank directedRuntimeGeneratedObject where
  rank := directedRuntimeCarrierRank
  edgeRankDecreases := by
    intro source target hEdge
    rcases directedRuntimeGeneratedGraph_edge_only_api_to_database hEdge with
      ⟨hSource, hTarget⟩
    simp [directedRuntimeCarrierRank, hSource, hTarget]

theorem directedRuntimeGraphRank_walkAcyclic :
    WalkAcyclic (AAT.GeneratedRuntimeGraph directedRuntimeGeneratedObject) :=
  directedRuntimeGraphRank.walkAcyclic

def selectedApiOnlyAtoms : ComponentAtom -> Prop
  | ComponentAtom.api => True
  | ComponentAtom.database => False

theorem selectedApiOnlyAtoms_no_database :
    ¬ selectedApiOnlyAtoms ComponentAtom.database := by
  intro hAtom
  exact hAtom

def apiOnlyCompositionGraph :
    AAT.CompositionGraph
      componentShapePresentation selectedApiOnlyAtoms where
  compatiblePairs := by
    intro left right hLeft hRight hDistinct
    cases left
    · cases right
      · exact False.elim (hDistinct rfl)
      · cases hRight
    · cases hLeft
  graphBoundary := True

/--
Source-side generated molecule containing only the API atom.

This is intentionally smaller than `generatedComponentMolecule`, so generated
operation transport has to move between two distinct generated molecules.
-/
def generatedApiOnlyMolecule :
    AAT.GeneratedMolecule componentShapePresentation where
  atoms := selectedApiOnlyAtoms
  finiteConfiguration := True
  atomsPrimitive := by
    intro atom hAtom
    cases atom
    · exact componentSystem.primitive ComponentAtom.api
    · cases hAtom
  compositionGraph := apiOnlyCompositionGraph
  requiredPortsMatched := by
    intro atom _port hAtom hRequired
    cases atom
    · cases hRequired
    · exact False.elim (selectedApiOnlyAtoms_no_database hAtom)

/-- Source-side generated object whose carrier is exactly the API atom. -/
def generatedApiOnlyObject :
    AAT.GeneratedArchitectureObject componentShapePresentation where
  molecule := generatedApiOnlyMolecule
  carrierList := [ ⟨ComponentAtom.api, by trivial⟩ ]
  carrierListNodup := by
    simp
  carrierListCovers := by
    intro carrier
    cases carrier with
    | mk atom hAtom =>
        cases atom
        · simp
        · cases hAtom
  objectBoundary := True

theorem generatedApiOnlyObject_no_relation_atom
    (carrier : AAT.GeneratedCarrier generatedApiOnlyObject) :
    (AtomShapeOf componentShapePresentation carrier.val).family ≠
      AtomKind.relation := by
  cases carrier.val <;> intro hRelation <;> cases hRelation

instance generatedApiOnlyRelationDecidable :
    DecidableRel (AAT.GeneratedRelation generatedApiOnlyObject) := by
  intro source target
  exact isFalse (by
    intro hEdge
    rcases hEdge with ⟨relation, hRelation⟩
    exact
      generatedApiOnlyObject_no_relation_atom
        relation hRelation.relationFamily)

theorem generatedApiOnlyGraph_no_edges :
    ∀ source target,
      ¬ (AAT.GeneratedArchGraph generatedApiOnlyObject).edge
        source target := by
  intro source target hEdge
  rcases hEdge with ⟨relation, hRelation⟩
  exact
    generatedApiOnlyObject_no_relation_atom
      relation hRelation.relationFamily

theorem generatedApiOnlyGraph_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph generatedApiOnlyObject) := by
  intro hClosed
  rcases hClosed with ⟨_carrier, walk, hPositive⟩
  cases walk with
  | nil _ =>
      simp [Walk.length] at hPositive
  | cons hEdge _rest =>
      exact generatedApiOnlyGraph_no_edges _ _ hEdge

def generatedApiOnlyGraphRank :
    AAT.GeneratedGraphRank generatedApiOnlyObject where
  rank := fun _carrier => 0
  edgeRankDecreases := by
    intro source target hEdge
    exact False.elim (generatedApiOnlyGraph_no_edges source target hEdge)

theorem generatedApiOnlyGraphRank_walkAcyclic :
    WalkAcyclic (AAT.GeneratedArchGraph generatedApiOnlyObject) :=
  generatedApiOnlyGraphRank.walkAcyclic

/-- Source-side generated law model for the API-only object. -/
def generatedApiOnlyLawModel :
    AAT.GeneratedArchitectureLawModel generatedApiOnlyObject :=
  AAT.GeneratedArchitectureLawModel.ofGraphRank
    generatedApiOnlyGraphRank True

def generatedApiOnlyCarrier :
    AAT.GeneratedCarrier generatedApiOnlyObject :=
  ⟨ComponentAtom.api, by trivial⟩

def generatedComponentApiCarrier :
    AAT.GeneratedCarrier generatedComponentObject :=
  ⟨ComponentAtom.api, by trivial⟩

def generatedComponentDatabaseCarrier :
    AAT.GeneratedCarrier generatedComponentObject :=
  ⟨ComponentAtom.database, by trivial⟩

theorem generatedComponentObject_api_shapeDistance_self_eq_zero :
    generatedComponentObject.generatedCarrierShapeDistance
      generatedComponentApiCarrier generatedComponentApiCarrier = 0 := by
  exact
    generatedComponentObject.generatedCarrierShapeDistance_self
      generatedComponentApiCarrier

/--
Acceptance: generated carrier distance is computed from AtomShape coordinates.

The API and database atoms share family / axis / predicate / direction / arity
and differ only in subject, so the generated mismatch-count distance is one.
-/
theorem generatedComponentObject_api_database_shapeDistance_eq_one :
    generatedComponentObject.generatedCarrierShapeDistance
      generatedComponentApiCarrier generatedComponentDatabaseCarrier = 1 := by
  native_decide

theorem generatedApiOnlyMolecule_is_distinct_from_component_molecule :
    generatedApiOnlyMolecule.toMolecule ≠
      generatedComponentMolecule.toMolecule := by
  intro hEqual
  have hTarget :
      generatedComponentMolecule.toMolecule.atoms ComponentAtom.database := by
    trivial
  rw [← hEqual] at hTarget
  exact hTarget

/--
Non-identity generated operation from the API-only object into the fuller
component object.
-/
def generatedApiExpansionOperation :
    AAT.GeneratedOperation generatedApiOnlyObject generatedComponentObject where
  atomMap := fun _carrier => generatedComponentApiCarrier
  shapeTransform := fun source target => source = target
  transformsAtomShape := by
    intro carrier
    cases carrier with
    | mk atom hAtom =>
        cases atom
        · rfl
        · cases hAtom
  operationBoundary := True

theorem generatedApiExpansionOperation_transforms_shape
    (carrier : AAT.GeneratedCarrier generatedApiOnlyObject) :
    generatedApiExpansionOperation.shapeTransform
      (AtomShapeOf componentShapePresentation carrier.val)
      (AtomShapeOf componentShapePresentation
        (generatedApiExpansionOperation.atomMap carrier).val) := by
  exact
    Formal.Arch.Chapter7TheoremPackages.generatedOperation_atomShape_transformed
      generatedApiExpansionOperation carrier

theorem generatedApiExpansionOperation_does_not_create_atoms :
    componentSystem.noToolOutputCreatesAtoms := by
  exact generatedApiExpansionOperation.operation_does_not_create_atoms

theorem generatedApiExpansionOperation_target_atom_primitive :
    componentSystem.Primitive
      (generatedApiExpansionOperation.atomMap generatedApiOnlyCarrier).val := by
  exact generatedApiExpansionOperation.target_atom_primitive generatedApiOnlyCarrier

def generatedApiExpansionOperationTransportPackage :
    AAT.OperationTransportPackage
      generatedApiOnlyLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore := by
  exact
    (Formal.Arch.Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage
      generatedApiExpansionOperation
      generatedApiOnlyLawModel generatedComponentLawModel)

theorem generatedApiExpansionOperation_transports_molecule :
    ∃ targetMolecule,
      generatedApiExpansionOperationTransportPackage.selectedTargetMolecule
        targetMolecule ∧
      generatedComponentLawModel.generatedAATCore.molecules targetMolecule := by
  exact
    generatedApiExpansionOperationTransportPackage.target_molecule_exists
      (molecule := generatedApiOnlyMolecule.toMolecule)
      rfl
      generatedApiOnlyLawModel.generated_molecule_on_core

theorem generatedApiExpansionOperation_transports_law :
    ∃ targetLaw,
      generatedApiExpansionOperationTransportPackage.selectedTargetLaw
        targetLaw ∧
      generatedComponentLawModel.generatedAATCore.laws targetLaw := by
  exact
    generatedApiExpansionOperationTransportPackage.target_law_exists
      (law := generatedApiOnlyLawModel.generatedDesignLaw)
      rfl
      generatedApiOnlyLawModel.generated_law_on_core

theorem generatedApiExpansionOperation_target_molecule_is_distinct :
    generatedApiExpansionOperationTransportPackage.selectedTargetMolecule
        generatedComponentMolecule.toMolecule ∧
      generatedApiOnlyMolecule.toMolecule ≠
        generatedComponentMolecule.toMolecule := by
  exact
    ⟨rfl, generatedApiOnlyMolecule_is_distinct_from_component_molecule⟩

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

theorem generatedComponent_shapeCoordinateTotalCurvature_eq_zero :
    totalCurvature AAT.generatedAtomShapeCoordinateDistance
      generatedComponentObject.generatedAtomShapeCoordinateSemantics
      generatedComponentObject.generatedSemanticDiagrams = 0 := by
  exact generatedComponentObject.generated_shapeCoordinateTotalCurvature_eq_zero

theorem generatedComponent_noMeasuredShapeCoordinateCurvatureObstruction :
    NoMeasuredNumericalCurvatureObstruction
      AAT.generatedAtomShapeCoordinateDistance
      generatedComponentObject.generatedAtomShapeCoordinateSemantics
      generatedComponentObject.generatedSemanticDiagrams := by
  exact
    generatedComponentObject.generated_noMeasuredShapeCoordinateCurvatureObstruction

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
  operationBoundary := True

theorem generatedComponentIdentityOperation_transforms_shape
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    generatedComponentIdentityOperation.shapeTransform
      (AtomShapeOf componentShapePresentation carrier.val)
      (AtomShapeOf componentShapePresentation
        (generatedComponentIdentityOperation.atomMap carrier).val) := by
  exact
    Formal.Arch.Chapter7TheoremPackages.generatedOperation_atomShape_transformed
      generatedComponentIdentityOperation carrier

theorem generatedComponentIdentityOperation_does_not_create_atoms :
    componentSystem.noToolOutputCreatesAtoms := by
  exact generatedComponentIdentityOperation.operation_does_not_create_atoms

def generatedComponentIdentityOperationTransportPackage :
    AAT.OperationTransportPackage
      generatedComponentLawModel.generatedAATCore
      generatedComponentLawModel.generatedAATCore := by
  exact
    (Formal.Arch.Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage
      generatedComponentIdentityOperation
      generatedComponentLawModel generatedComponentLawModel)

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
  synthesisBoundary := True

theorem generatedComponentSynthesisCandidate_flatWithin_from_law_model :
    generatedComponentSynthesisCandidate.candidate_flatWithin =
      generatedComponentLawModel.generatedArchitectureFlatWithin := by
  rfl

theorem generatedComponentSynthesisCandidate_flatWithin :
    ArchitectureFlatWithin generatedComponentObject.generatedFlatnessModel
      generatedComponentObject.generatedComponentUniverse := by
  exact
    Formal.Arch.Chapter7TheoremPackages.generatedSynthesisCandidate_flatWithin
      generatedComponentSynthesisCandidate

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
  exact
    Formal.Arch.Chapter7TheoremPackages.generatedSynthesisCandidate_toSynthesisSoundnessPackage
      generatedComponentSynthesisCandidate

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
