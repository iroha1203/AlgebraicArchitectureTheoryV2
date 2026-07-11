import ResearchLean.AG.QualitySurface.ComponentRefinementSupportLift
import ResearchLean.AG.QualitySurface.RepairTransportCechCommutatorCurvature

/-!
Cycle 77 evidence for `G-aat-quality-surface-01`.

This file adds a finite semantic repair cocycle witness.  Local branch-family
adequacy is supplied by the component-level support-lift checker from Cycle 76,
but a separate Cech-style overlap cocycle still carries a protected semantic
repair residual.  Thus the visible local adequacy projection does not
determine finite semantic repair residual emptiness.

The construction is deliberately finite and witness-level: a semantic atom is
projected to the existing `BridgeComponent` vocabulary, and the residual atom
is read from exact overlap support.  It does not assert source extraction
completeness, ArchMap correctness, runtime repair synthesis, canonical global
semantic ontology, global sheaf completeness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCocycleWitness

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open CurvatureBasisExchange
open BranchTransversalScanKernel
open BranchReflectionAdequacyKernel
open HandoffCechExactness
open HandoffCechOverlapBasis
open RepairTransportCechCommutatorCurvature
open ArbitraryBranchFamilyAdequacy
open ComponentRefinementSupportLift

/-! ## Finite semantic repair atoms -/

/-- Finite semantic atoms used by the selected repair-gluing witness. -/
inductive SemanticRepairAtom where
  | traceContract
  | repairFrontierObligation
deriving DecidableEq

open SemanticRepairAtom

/--
Projection from semantic repair atoms to the protected bridge component whose
overlap support carries the semantic obligation.
-/
def semanticComponent : SemanticRepairAtom -> BridgeComponent
  | traceContract => BridgeComponent.trace
  | repairFrontierObligation => BridgeComponent.repairFrontier

/-- A semantic repair support predicate. -/
abbrev SemanticRepairSupport := SemanticRepairAtom -> Prop

/-- Semantic trace-only repair support. -/
def semanticTraceOnlySupport : SemanticRepairSupport
  | traceContract => True
  | repairFrontierObligation => False

/-- Semantic support touching both trace and repair-frontier obligations. -/
def semanticTraceRepairFrontierSupport : SemanticRepairSupport
  | traceContract => True
  | repairFrontierObligation => True

/-- A semantic support projects to component-level repair support. -/
def componentSupportOfSemantic
    (support : SemanticRepairSupport) : HandoffRepairSupport :=
  fun component =>
    exists atom, support atom /\ semanticComponent atom = component

/-- The semantic trace-plus-repair support projects to the selected component support. -/
theorem semanticTraceRepairFrontier_projects_to_componentSupport
    (component : BridgeComponent) :
    componentSupportOfSemantic semanticTraceRepairFrontierSupport component <->
      traceRepairFrontierRepairSupport component := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨atom, _hsupport, hcomponent⟩
    cases atom <;> simp [semanticComponent, traceRepairFrontierRepairSupport]
      at hcomponent ⊢
    · exact Or.inl hcomponent.symm
    · exact Or.inr hcomponent.symm
  · intro hcomponent
    rcases hcomponent with htrace | hrepair
    · subst component
      exact ⟨traceContract, trivial, rfl⟩
    · subst component
      exact ⟨repairFrontierObligation, trivial, rfl⟩

/-- The semantic trace-only support projects to trace-only component support. -/
theorem semanticTraceOnly_projects_to_traceOnlyComponentSupport
    (component : BridgeComponent) :
    componentSupportOfSemantic semanticTraceOnlySupport component <->
      traceOnlyRepairPlan.touched component := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨atom, hsupport, hcomponent⟩
    cases atom
    · simp [semanticComponent, traceOnlyRepairPlan, singletonRepairSupport]
        at hcomponent ⊢
      exact hcomponent.symm
    · cases hsupport
  · intro hcomponent
    cases component with
    | support =>
        simp [traceOnlyRepairPlan, singletonRepairSupport] at hcomponent
    | trace =>
        exact ⟨traceContract, trivial, rfl⟩
    | repairFrontier =>
        simp [traceOnlyRepairPlan, singletonRepairSupport] at hcomponent

/-! ## Semantic overlap residuals -/

/-- A semantic atom is residual when its projected component appears in overlap support. -/
def SemanticOverlapResidual
    (cover : HandoffCechCover)
    (atom : SemanticRepairAtom) : Prop :=
  HandoffCechOverlapSupport cover (semanticComponent atom)

/-- The cover carries at least one semantic overlap residual. -/
def SemanticRepairCocycleResidualNonempty
    (cover : HandoffCechCover) : Prop :=
  exists atom, SemanticOverlapResidual cover atom

/-- A semantic repair support hits every semantic overlap residual. -/
def SemanticRepairTransversal
    (cover : HandoffCechCover)
    (support : SemanticRepairSupport) : Prop :=
  forall atom,
    SemanticOverlapResidual cover atom -> support atom

/-- The selected semantic witness cover has the repair-frontier residual atom. -/
theorem repairFrontierSemanticResidual :
    SemanticOverlapResidual
      repairFrontierOverlapBasisCover repairFrontierObligation := by
  exact
    (repairFrontierOverlapBasis).1
      BridgeComponent.repairFrontier rfl

/-- The selected semantic witness cover has nonempty semantic repair residual. -/
theorem repairFrontierSemanticResidual_nonempty :
    SemanticRepairCocycleResidualNonempty
      repairFrontierOverlapBasisCover :=
  ⟨repairFrontierObligation, repairFrontierSemanticResidual⟩

/-- Trace-only semantic repair support misses the selected semantic residual. -/
theorem semanticTraceOnly_misses_repairFrontierResidual :
    Not
      (SemanticRepairTransversal
        repairFrontierOverlapBasisCover semanticTraceOnlySupport) := by
  intro htransversal
  exact
    htransversal repairFrontierObligation
      repairFrontierSemanticResidual

/-- Trace-plus-repair semantic support hits the selected semantic residuals. -/
theorem semanticTraceRepairFrontier_hits_residuals :
    SemanticRepairTransversal
      repairFrontierOverlapBasisCover
      semanticTraceRepairFrontierSupport := by
  intro atom _hresidual
  cases atom <;> trivial

/-! ## Local adequacy versus semantic residual emptiness -/

/-- Local branch-family adequacy pass used by the selected semantic witness. -/
def LocalBranchFamilyAdequacyPass : Prop :=
  firstUncoveredTargetBranch?
      (CodeComponentLiftCovered
        selectedCollapsedComponentLift collapsedVisibleExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
        SelectedScanBranch.branch)
      selectedScanOrder = none

/-- The local finite branch-family adequacy checker passes. -/
theorem localBranchFamilyAdequacy_pass :
    LocalBranchFamilyAdequacyPass :=
  selectedComponentLift_firstUncovered_none

/--
Semantic repair gluing exactness for this finite witness means that the
semantic overlap residual is empty.  This is a semantic reading of the overlap
cocycle, not a claim about source extraction or runtime repair synthesis.
-/
def SemanticRepairGluingExact
    (cover : HandoffCechCover) : Prop :=
  Not (SemanticRepairCocycleResidualNonempty cover)

/-- A nonempty semantic residual obstructs semantic repair gluing. -/
theorem semanticResidual_obstructs_globalGluing
    {cover : HandoffCechCover}
    (hresidual : SemanticRepairCocycleResidualNonempty cover) :
    Not (SemanticRepairGluingExact cover) := by
  intro hexact
  exact hexact hresidual

/--
The selected flat Cech path has no semantic repair residual, because its
protected overlap support is empty.
-/
theorem repairTransportFlat_semanticGluingExact :
    SemanticRepairGluingExact repairTransportFlatCechCover := by
  intro hresidual
  rcases hresidual with ⟨atom, hsupport⟩
  exact
    flatPath_overlapSupportEmpty
      ⟨semanticComponent atom, by
        simpa [selectedRepairTransportCechCommutatorCell]
          using hsupport⟩

/--
A semantic repair gluing obstruction witness pairs local branch adequacy with
semantic overlap residual that blocks semantic gluing exactness.
-/
def SemanticRepairGluingObstructionWitness
    (cover : HandoffCechCover) : Prop :=
  LocalBranchFamilyAdequacyPass /\
    SemanticRepairCocycleResidualNonempty cover /\
    Not (SemanticRepairGluingExact cover)

/--
The selected finite witness has local adequacy, but its semantic repair overlap
cocycle is nonempty, so semantic gluing fails.
-/
theorem localSemanticRepairAdequacy_not_globalGluing :
    SemanticRepairGluingObstructionWitness
      repairFrontierOverlapBasisCover := by
  exact
    ⟨localBranchFamilyAdequacy_pass,
      repairFrontierSemanticResidual_nonempty,
      semanticResidual_obstructs_globalGluing
        repairFrontierSemanticResidual_nonempty⟩

/-! ## Visible/local nonfaithfulness -/

/--
The visible local surface records local branch adequacy and the same chart
list.  It deliberately forgets the semantic overlap residual.
-/
def SameSemanticVisibleLocalProjection
    (left right : HandoffCechCover) : Prop :=
  LocalBranchFamilyAdequacyPass /\
    left.charts = right.charts

/-- The flat cover and selected semantic residual cover have the same visible local projection. -/
theorem flat_and_semanticResidual_same_visibleLocal :
    SameSemanticVisibleLocalProjection
      repairTransportFlatCechCover repairFrontierOverlapBasisCover := by
  refine
    ⟨localBranchFamilyAdequacy_pass,
      ?_⟩
  rfl

/--
Visible local projection is not sufficient for semantic residual emptiness:
the selected residual cover has the same local visible surface as the flat
cover, while the flat cover is semantically exact and the residual cover is
not.
-/
theorem visibleLocalProjection_not_faithful_to_semanticRepairGluing :
    SameSemanticVisibleLocalProjection
        repairTransportFlatCechCover repairFrontierOverlapBasisCover /\
      SemanticRepairGluingExact repairTransportFlatCechCover /\
      SemanticRepairCocycleResidualNonempty
        repairFrontierOverlapBasisCover /\
      Not (SemanticRepairGluingExact repairFrontierOverlapBasisCover) := by
  exact
    ⟨flat_and_semanticResidual_same_visibleLocal,
      repairTransportFlat_semanticGluingExact,
      repairFrontierSemanticResidual_nonempty,
      semanticResidual_obstructs_globalGluing
        repairFrontierSemanticResidual_nonempty⟩

/-! ## Theorem package -/

/--
Cycle-77 theorem package: finite semantic repair atoms project to protected
components, local branch adequacy can pass, trace-only semantic support still
misses the repair-frontier residual, and visible/local projection cannot
recover semantic repair-gluing failure.
-/
theorem semanticRepairCocycleWitness_package :
    LocalBranchFamilyAdequacyPass /\
      SemanticRepairCocycleResidualNonempty
        repairFrontierOverlapBasisCover /\
      SemanticRepairTransversal
        repairFrontierOverlapBasisCover
        semanticTraceRepairFrontierSupport /\
      Not
        (SemanticRepairTransversal
          repairFrontierOverlapBasisCover semanticTraceOnlySupport) /\
      SemanticRepairGluingObstructionWitness
        repairFrontierOverlapBasisCover /\
      SameSemanticVisibleLocalProjection
        repairTransportFlatCechCover repairFrontierOverlapBasisCover /\
      SemanticRepairGluingExact repairTransportFlatCechCover /\
      Not (SemanticRepairGluingExact repairFrontierOverlapBasisCover) /\
      (forall component,
        componentSupportOfSemantic semanticTraceRepairFrontierSupport
            component <->
          traceRepairFrontierRepairSupport component) /\
      (forall component,
        componentSupportOfSemantic semanticTraceOnlySupport component <->
          traceOnlyRepairPlan.touched component) := by
  exact
    ⟨localBranchFamilyAdequacy_pass,
      repairFrontierSemanticResidual_nonempty,
      semanticTraceRepairFrontier_hits_residuals,
      semanticTraceOnly_misses_repairFrontierResidual,
      localSemanticRepairAdequacy_not_globalGluing,
      flat_and_semanticResidual_same_visibleLocal,
      repairTransportFlat_semanticGluingExact,
      semanticResidual_obstructs_globalGluing
        repairFrontierSemanticResidual_nonempty,
      semanticTraceRepairFrontier_projects_to_componentSupport,
      semanticTraceOnly_projects_to_traceOnlyComponentSupport⟩

end SemanticRepairCocycleWitness
end QualitySurface
end ResearchLean.AG
