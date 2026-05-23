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

end ArchMapPreservationPackage

/-- Convenience theorem spelling for package-based structure preservation. -/
theorem aatStructurePreserved_of_archMapPreservationPackage
    {M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs}
    (pkg : ArchMapPreservationPackage M) :
    AATStructurePreserved M :=
  pkg.aatStructurePreserved

end ArchMapModel

end Formal.Arch
