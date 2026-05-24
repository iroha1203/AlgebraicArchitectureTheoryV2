import Formal.Arch.Extension.Flatness

namespace Formal.Arch

universe u v w q r s t

/--
Abstract ArchMap model for the Lean formal bridge.

This is not the Rust `archmap-v0` JSON artifact. It is a bounded, selected
map candidate from source artifacts into an AAT flatness model, carrying the
preservation, forgetting, coverage, precondition, and non-conclusion boundaries
that a theorem package may read.
-/
structure ArchMapModel (Src : Type u) (Tgt : Type v) (Abs : Type w)
    (StaticObs : Type q) (SrcExpr : Type r) (TgtExpr : Type s)
    (SemanticObs : Type t) where
  target : ArchitectureFlatnessModel Tgt Abs StaticObs TgtExpr SemanticObs
  targetUniverse : ComponentUniverse target.static
  objectMap : Src -> Tgt
  semanticDiagramMap : RequiredDiagram SrcExpr -> RequiredDiagram TgtExpr
  selectedSourceObject : Src -> Prop
  selectedSourceRelation : Src -> Src -> Prop
  selectedSemanticDiagram : RequiredDiagram SrcExpr -> Prop
  sourceNonfillabilityWitness : RequiredDiagram SrcExpr -> Prop
  targetNonfillabilityWitness : RequiredDiagram TgtExpr -> Prop
  selectedLaw : Prop
  selectedPolicyBoundary : Prop
  selectedFlatnessPrecondition : Prop
  forgettingBoundary : Prop
  unsupportedRelationBoundary : Prop
  semanticCoverageGapBoundary : Prop
  semanticMeasuredZeroBoundary : Prop
  coverageBoundary : Prop
  exactnessBoundary : Prop
  formalPromotionGuardrail : Prop
  nonConclusions : Prop

namespace ArchMapModel

variable {Src : Type u} {Tgt : Type v} {Abs : Type w}
  {StaticObs : Type q} {SrcExpr : Type r} {TgtExpr : Type s}
  {SemanticObs : Type t}

/-- Selected source objects land in the selected target component universe. -/
def ObjectPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ∀ src, M.selectedSourceObject src ->
    M.objectMap src ∈ M.targetUniverse.components

/--
Selected source relations are represented by target static dependency edges.
Unsupported or forgotten relations remain outside this predicate.
-/
def RelationPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ∀ src dst, M.selectedSourceRelation src dst ->
    M.target.static.edge (M.objectMap src) (M.objectMap dst)

/-- Object and relation preservation, separated from forgetting boundaries. -/
def ObjectRelationPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ObjectPreservation M ∧ RelationPreservation M

/-- Selected semantic diagrams are mapped into the measured target diagram universe. -/
def SemanticDiagramPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ∀ diagram, M.selectedSemanticDiagram diagram ->
    M.semanticDiagramMap diagram ∈ M.target.measuredSemantic

/-- Selected semantic commutation is preserved in the target semantics. -/
def SemanticCommutationPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ∀ diagram, M.selectedSemanticDiagram diagram ->
    DiagramCommutes M.target.semantic (M.semanticDiagramMap diagram)

/-- Selected nonfillability witnesses are mapped to target nonfillability witnesses. -/
def NonfillabilityWitnessPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ∀ diagram, M.selectedSemanticDiagram diagram ->
    M.sourceNonfillabilityWitness diagram ->
    M.targetNonfillabilityWitness (M.semanticDiagramMap diagram)

/--
Semantic measured-zero and semantic-unmeasured boundaries are recorded as
separate fields. This marker prevents a coverage gap from being read as zero.
-/
def SemanticMeasuredZeroUnmeasuredSeparated
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  M.semanticMeasuredZeroBoundary ∧ M.semanticCoverageGapBoundary

/-- Selected law and policy-boundary preservation supplied by the ArchMap bridge. -/
def LawPolicyPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  M.selectedLaw ∧ M.selectedPolicyBoundary

/--
Selected preconditions needed to connect the map to the bounded flatness /
zero-curvature theorem package.
-/
def FlatnessPreconditionPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  M.selectedFlatnessPrecondition ∧
  ExhaustiveFlatnessCoverage M.target M.targetUniverse ∧
  ExactFlatnessObservation M.target M.targetUniverse

/-- The target already has the selected static/runtime/semantic flatness evidence. -/
def SelectedTargetFlatness
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  StaticFlatWithin M.target M.targetUniverse ∧
  RuntimeFlatWithin M.target M.targetUniverse ∧
  SemanticFlatWithin M.target

/-- Bounded AAT structure preservation exposed by the ArchMap formal bridge. -/
def AATStructurePreserved
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ObjectRelationPreservation M ∧
  SemanticDiagramPreservation M ∧
  SemanticCommutationPreservation M ∧
  NonfillabilityWitnessPreservation M ∧
  LawPolicyPreservation M ∧
  ArchitectureFlatWithin M.target M.targetUniverse ∧
  M.forgettingBoundary ∧
  M.unsupportedRelationBoundary ∧
  M.coverageBoundary ∧
  M.exactnessBoundary ∧
  M.formalPromotionGuardrail ∧
  M.nonConclusions

/--
Top-level bounded homomorphism preservation predicate for ArchMap.

This packages the selected object, relation, semantic-diagram, law/policy, and
flatness-precondition preservation fields without reading any Rust validation
report, AIR projection, theorem-check checklist, or LLM output as a proof term.
-/
def BoundedHomomorphismPreservation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  ObjectPreservation M ∧
  RelationPreservation M ∧
  SemanticDiagramPreservation M ∧
  SemanticCommutationPreservation M ∧
  NonfillabilityWitnessPreservation M ∧
  LawPolicyPreservation M ∧
  FlatnessPreconditionPreservation M ∧
  SelectedTargetFlatness M ∧
  M.forgettingBoundary ∧
  M.unsupportedRelationBoundary ∧
  M.semanticCoverageGapBoundary ∧
  M.semanticMeasuredZeroBoundary ∧
  M.coverageBoundary ∧
  M.exactnessBoundary ∧
  M.formalPromotionGuardrail ∧
  M.nonConclusions

/--
ArchMap-to-AAT homomorphic relation exposed by the formal bridge.

This reads an ArchMap model as a bounded homomorphism candidate into the AAT
architecture surface and records the induced bounded AAT structure.  It is not
a parser for `archmap-v0` JSON and does not assert global repository
completeness.
-/
def AATHomomorphicRelation
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop :=
  BoundedHomomorphismPreservation M ∧ AATStructurePreserved M

/--
Theorem package for selected ArchMap preservation.

All conclusions are relative to the selected source universe, target component
universe, semantic coverage, exactness, and explicit flatness preconditions.
-/
structure ArchMapPreservationPackage
    (M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs) :
    Prop where
  objectRelationPreservation : ObjectRelationPreservation M
  semanticDiagramPreservation : SemanticDiagramPreservation M
  semanticCommutationPreservation : SemanticCommutationPreservation M
  nonfillabilityWitnessPreservation : NonfillabilityWitnessPreservation M
  semanticMeasuredZeroUnmeasuredSeparated :
    SemanticMeasuredZeroUnmeasuredSeparated M
  lawPolicyPreservation : LawPolicyPreservation M
  flatnessPreconditionPreservation : FlatnessPreconditionPreservation M
  selectedTargetFlatness : SelectedTargetFlatness M
  forgettingBoundary : M.forgettingBoundary
  unsupportedRelationBoundary : M.unsupportedRelationBoundary
  coverageBoundary : M.coverageBoundary
  exactnessBoundary : M.exactnessBoundary
  formalPromotionGuardrail : M.formalPromotionGuardrail
  nonConclusions : M.nonConclusions

namespace ArchMapPreservationPackage

variable {M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs}

/-- Access selected object preservation from the package. -/
theorem objectPreservation
    (pkg : ArchMapPreservationPackage M) :
    ObjectPreservation M :=
  pkg.objectRelationPreservation.1

/-- Access selected relation preservation from the package. -/
theorem relationPreservation
    (pkg : ArchMapPreservationPackage M) :
    RelationPreservation M :=
  pkg.objectRelationPreservation.2

/-- Access selected semantic diagram preservation from the package. -/
theorem semanticDiagramPreserved
    (pkg : ArchMapPreservationPackage M) :
    SemanticDiagramPreservation M :=
  pkg.semanticDiagramPreservation

/-- Access selected semantic commutation preservation from the package. -/
theorem semanticCommutationPreserved
    (pkg : ArchMapPreservationPackage M) :
    SemanticCommutationPreservation M :=
  pkg.semanticCommutationPreservation

/-- Access selected nonfillability witness preservation from the package. -/
theorem nonfillabilityWitnessPreserved
    (pkg : ArchMapPreservationPackage M) :
    NonfillabilityWitnessPreservation M :=
  pkg.nonfillabilityWitnessPreservation

/-- Access law and policy preservation from the package. -/
theorem lawPolicyPreserved
    (pkg : ArchMapPreservationPackage M) :
    LawPolicyPreservation M :=
  pkg.lawPolicyPreservation

/-- Access selected flatness preconditions from the package. -/
theorem flatnessPreconditionsPreserved
    (pkg : ArchMapPreservationPackage M) :
    FlatnessPreconditionPreservation M :=
  pkg.flatnessPreconditionPreservation

/-- Access the explicit non-conclusions recorded by the package. -/
theorem nonConclusions_recorded
    (pkg : ArchMapPreservationPackage M) :
    M.nonConclusions :=
  pkg.nonConclusions

/-- Access the bundled bounded homomorphism preservation predicate. -/
theorem boundedHomomorphismPreserved
    (pkg : ArchMapPreservationPackage M) :
    BoundedHomomorphismPreservation M :=
  ⟨pkg.objectRelationPreservation.1,
    pkg.objectRelationPreservation.2,
    pkg.semanticDiagramPreservation,
    pkg.semanticCommutationPreservation,
    pkg.nonfillabilityWitnessPreservation,
    pkg.lawPolicyPreservation,
    pkg.flatnessPreconditionPreservation,
    pkg.selectedTargetFlatness,
    pkg.forgettingBoundary,
    pkg.unsupportedRelationBoundary,
    pkg.semanticMeasuredZeroUnmeasuredSeparated.2,
    pkg.semanticMeasuredZeroUnmeasuredSeparated.1,
    pkg.coverageBoundary,
    pkg.exactnessBoundary,
    pkg.formalPromotionGuardrail,
    pkg.nonConclusions⟩

/-- The package keeps measured semantic zero separate from unmeasured coverage gaps. -/
theorem semanticMeasuredZero_not_coverageGap
    (pkg : ArchMapPreservationPackage M) :
    M.semanticMeasuredZeroBoundary ∧ M.semanticCoverageGapBoundary :=
  pkg.semanticMeasuredZeroUnmeasuredSeparated

/--
Selected flatness evidence plus preserved preconditions yields bounded target
architecture flatness. This is the bridge to the zero-curvature theorem package.
-/
theorem architectureFlatWithin
    (pkg : ArchMapPreservationPackage M) :
    ArchitectureFlatWithin M.target M.targetUniverse :=
  pkg.flatnessPreconditionPreservation.2.2
    pkg.selectedTargetFlatness.1
    pkg.selectedTargetFlatness.2.1
    pkg.selectedTargetFlatness.2.2

/--
Selected preservation conditions imply the bounded AAT structure-preservation
package. No Rust artifact, validator pass, or global completeness claim is used.
-/
theorem aatStructurePreserved
    (pkg : ArchMapPreservationPackage M) :
    AATStructurePreserved M :=
  ⟨pkg.objectRelationPreservation,
    pkg.semanticDiagramPreservation,
    pkg.semanticCommutationPreservation,
    pkg.nonfillabilityWitnessPreservation,
    pkg.lawPolicyPreservation,
    pkg.architectureFlatWithin,
    pkg.forgettingBoundary,
    pkg.unsupportedRelationBoundary,
    pkg.coverageBoundary,
    pkg.exactnessBoundary,
    pkg.formalPromotionGuardrail,
    pkg.nonConclusions⟩

/--
The package presents the selected ArchMap as a bounded homomorphic relation
into the AAT architecture surface.
-/
theorem aatHomomorphicRelation
    (pkg : ArchMapPreservationPackage M) :
    AATHomomorphicRelation M :=
  ⟨pkg.boundedHomomorphismPreserved, pkg.aatStructurePreserved⟩

end ArchMapPreservationPackage

/-- Convenience theorem spelling for package-based structure preservation. -/
theorem aatStructurePreserved_of_archMapPreservationPackage
    {M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs}
    (pkg : ArchMapPreservationPackage M) :
    AATStructurePreserved M :=
  pkg.aatStructurePreserved

/-- Convenience theorem spelling for the ArchMap-to-AAT homomorphic relation. -/
theorem aatHomomorphicRelation_of_archMapPreservationPackage
    {M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs}
    (pkg : ArchMapPreservationPackage M) :
    AATHomomorphicRelation M :=
  pkg.aatHomomorphicRelation

namespace Examples

/-- One-component source/target graph used by the bounded positive example. -/
def unitNoEdgeGraph : ArchGraph Unit where
  edge _ _ := False

/-- The full finite universe for the one-component ArchMap target. -/
def unitUniverse : ComponentUniverse unitNoEdgeGraph :=
  ComponentUniverse.full unitNoEdgeGraph [()] (by simp) (by
    intro c
    cases c
    simp)

/-- One-component target flatness model with no static, runtime, or semantic edges. -/
def unitFlatnessModel :
    ArchitectureFlatnessModel Unit Unit Unit Unit Unit where
  static := unitNoEdgeGraph
  runtime := unitNoEdgeGraph
  projection := { expose := fun _ => () }
  abstractStatic := unitNoEdgeGraph
  staticObservation := { observe := fun _ => () }
  boundaryAllowed := fun _ _ => True
  abstractionAllowed := fun _ _ => True
  runtimeAllowed := fun _ _ => True
  semantic := { eval := fun _ => () }
  requiredSemantic := fun _ => False
  measuredSemantic := []

/-- Concrete bounded ArchMap model for a positive finite preservation example. -/
def unitArchMapModel :
    ArchMapModel Unit Unit Unit Unit Unit Unit Unit where
  target := unitFlatnessModel
  targetUniverse := unitUniverse
  objectMap := fun _ => ()
  semanticDiagramMap := fun d => d
  selectedSourceObject := fun _ => True
  selectedSourceRelation := fun _ _ => False
  selectedSemanticDiagram := fun _ => False
  sourceNonfillabilityWitness := fun _ => False
  targetNonfillabilityWitness := fun _ => False
  selectedLaw := True
  selectedPolicyBoundary := True
  selectedFlatnessPrecondition := True
  forgettingBoundary := True
  unsupportedRelationBoundary := True
  semanticCoverageGapBoundary := True
  semanticMeasuredZeroBoundary := True
  coverageBoundary := True
  exactnessBoundary := True
  formalPromotionGuardrail := True
  nonConclusions := True

theorem unitWalkAcyclic : WalkAcyclic unitNoEdgeGraph := by
  intro hClosed
  rcases hClosed with ⟨c, w, hLen⟩
  cases w with
  | nil c =>
      simp [Walk.length] at hLen
  | cons hEdge _rest =>
      exact False.elim hEdge

theorem unitProjectionSound :
    ProjectionSound unitNoEdgeGraph
      ({ expose := fun _ : Unit => () } : InterfaceProjection Unit Unit)
      unitNoEdgeGraph := by
  intro src dst hEdge
  exact False.elim hEdge

theorem unitLSPCompatible :
    LSPCompatible
      ({ expose := fun _ : Unit => () } : InterfaceProjection Unit Unit)
      ({ observe := fun _ : Unit => () } : Observation Unit Unit) := by
  intro x y _hSame
  cases x
  cases y
  rfl

theorem unitStaticFlatWithin :
    StaticFlatWithin unitFlatnessModel unitUniverse := by
  exact ⟨unitWalkAcyclic, unitProjectionSound, unitLSPCompatible,
    (by intro src dst hEdge; exact False.elim hEdge),
    (by intro src dst hEdge; exact False.elim hEdge)⟩

theorem unitRuntimeFlatWithin :
    RuntimeFlatWithin unitFlatnessModel unitUniverse := by
  intro src dst _hSrc _hDst hEdge
  exact False.elim hEdge

theorem unitSemanticFlatWithin :
    SemanticFlatWithin unitFlatnessModel := by
  intro d hMeasured
  cases hMeasured

theorem unitSemanticCoverageComplete :
    SemanticCoverageComplete unitFlatnessModel := by
  intro d hRequired
  exact False.elim hRequired

theorem unitNoUnmeasuredRequiredAxis :
    NoUnmeasuredRequiredAxis unitFlatnessModel unitUniverse :=
  ⟨staticCoverageComplete_of_componentUniverse unitFlatnessModel unitUniverse,
    (by
      intro src dst hEdge
      exact False.elim hEdge),
    unitSemanticCoverageComplete⟩

theorem unitArchitectureFlatWithin :
    ArchitectureFlatWithin unitFlatnessModel unitUniverse :=
  ⟨unitNoUnmeasuredRequiredAxis, unitStaticFlatWithin,
    unitRuntimeFlatWithin, unitSemanticFlatWithin⟩

theorem unitFlatnessPreconditionPreservation :
    FlatnessPreconditionPreservation unitArchMapModel :=
  ⟨trivial, unitNoUnmeasuredRequiredAxis,
    exactFlatnessObservation_of_exhaustiveCoverage unitNoUnmeasuredRequiredAxis⟩

theorem unitSelectedTargetFlatness :
    SelectedTargetFlatness unitArchMapModel :=
  ⟨unitStaticFlatWithin, unitRuntimeFlatWithin, unitSemanticFlatWithin⟩

/--
Positive finite package: a selected one-object ArchMap preserves the bounded
homomorphism fields and reaches the AAT structure-preservation accessor.
-/
def unitArchMapPreservationPackage :
    ArchMapPreservationPackage unitArchMapModel where
  objectRelationPreservation := ⟨
    (by
      intro src _hSelected
      exact unitUniverse.covers ()),
    (by
      intro src dst hRel
      exact False.elim hRel)⟩
  semanticDiagramPreservation := by
    intro diagram hSelected
    exact False.elim hSelected
  semanticCommutationPreservation := by
    intro diagram hSelected
    exact False.elim hSelected
  nonfillabilityWitnessPreservation := by
    intro diagram hSelected _hWitness
    exact False.elim hSelected
  semanticMeasuredZeroUnmeasuredSeparated := ⟨trivial, trivial⟩
  lawPolicyPreservation := ⟨trivial, trivial⟩
  flatnessPreconditionPreservation := unitFlatnessPreconditionPreservation
  selectedTargetFlatness := unitSelectedTargetFlatness
  forgettingBoundary := trivial
  unsupportedRelationBoundary := trivial
  coverageBoundary := trivial
  exactnessBoundary := trivial
  formalPromotionGuardrail := trivial
  nonConclusions := trivial

theorem unitArchMap_aatStructurePreserved :
    AATStructurePreserved unitArchMapModel :=
  unitArchMapPreservationPackage.aatStructurePreserved

theorem unitArchMap_boundedHomomorphismPreserved :
    BoundedHomomorphismPreservation unitArchMapModel :=
  unitArchMapPreservationPackage.boundedHomomorphismPreserved

theorem unitArchMap_aatHomomorphicRelation :
    AATHomomorphicRelation unitArchMapModel :=
  unitArchMapPreservationPackage.aatHomomorphicRelation

end Examples

end ArchMapModel

end Formal.Arch
