import ResearchLean.AG.QualitySurface.SourceRefHandoffComponentSupport

/-!
Cycle 64 evidence for `G-aat-quality-surface-01`.

This file reads source-ref handoff component support as a declared repair
transversal problem.  The construction is relative to selected finite
handoff atlases and declared component-level repair predicates.  It does not
assert runtime repair synthesis, global minimal repair planning, source
extraction completeness, ArchMap correctness, arbitrary route enumeration, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace HandoffRepairTransversalTheorem

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open SourceRefHandoffBridge
open SourceRefHandoffHolonomyCorrespondence
open SourceRefHandoffComponentSupport

/-! ## Declared component-level repair plans -/

/-- Component support touched by a declared handoff repair plan. -/
abbrev HandoffRepairSupport := BridgeComponent -> Prop

/--
A bounded handoff repair plan.

`clears` is a declared component-support clearance predicate, not a runtime
repair result.  The boundary law says that a plan may clear only components it
touches.
-/
structure HandoffRepairPlan where
  touched : HandoffRepairSupport
  clears : BridgeComponent -> Prop
  clears_only_if_touched :
    forall component, clears component -> touched component

/-- Component support that remains after declared component clearance. -/
def DeclaredResidualComponentSupport
    (atlas : SourceRefHandoffAtlas)
    (plan : HandoffRepairPlan)
    (component : BridgeComponent) : Prop :=
  HandoffComponentSupport atlas component /\ Not (plan.clears component)

/-- Declared clearance of every supported component. -/
def DeclaredHandoffRepairClears
    (atlas : SourceRefHandoffAtlas)
    (plan : HandoffRepairPlan) : Prop :=
  forall component,
    HandoffComponentSupport atlas component -> plan.clears component

/-- A repair support is a transversal for the handoff component support. -/
def HandoffRepairTransversal
    (atlas : SourceRefHandoffAtlas)
    (support : HandoffRepairSupport) : Prop :=
  forall component,
    HandoffComponentSupport atlas component -> support component

/-- A plan is component-complete when every touched supported component clears. -/
def ComponentCompleteHandoffRepairPlan
    (atlas : SourceRefHandoffAtlas)
    (plan : HandoffRepairPlan) : Prop :=
  forall component,
    HandoffComponentSupport atlas component ->
      plan.touched component -> plan.clears component

/-- A missed component support remains as declared residual support. -/
theorem missedHandoffComponentSupport_survives
    {atlas : SourceRefHandoffAtlas}
    {plan : HandoffRepairPlan}
    {component : BridgeComponent}
    (hsupport : HandoffComponentSupport atlas component)
    (hmiss : Not (plan.touched component)) :
    DeclaredResidualComponentSupport atlas plan component := by
  refine ⟨hsupport, ?_⟩
  intro hclear
  exact hmiss (plan.clears_only_if_touched component hclear)

/-- Declared clearance forces the touched support to hit every component support. -/
theorem hitsEveryHandoffComponentSupport_of_declaredClearance
    {atlas : SourceRefHandoffAtlas}
    {plan : HandoffRepairPlan}
    (hclear : DeclaredHandoffRepairClears atlas plan) :
    HandoffRepairTransversal atlas plan.touched := by
  intro component hsupport
  exact plan.clears_only_if_touched component (hclear component hsupport)

/-- Component completeness turns a transversal into declared clearance. -/
theorem declaredClearance_of_hitsEveryHandoffComponentSupport_of_componentComplete
    {atlas : SourceRefHandoffAtlas}
    {plan : HandoffRepairPlan}
    (hcomplete : ComponentCompleteHandoffRepairPlan atlas plan)
    (hhits : HandoffRepairTransversal atlas plan.touched) :
    DeclaredHandoffRepairClears atlas plan := by
  intro component hsupport
  exact hcomplete component hsupport (hhits component hsupport)

/-- In a component-complete regime, declared clearance is exactly transversality. -/
theorem declaredClearance_iff_hitsEvery_of_componentComplete
    {atlas : SourceRefHandoffAtlas}
    {plan : HandoffRepairPlan}
    (hcomplete : ComponentCompleteHandoffRepairPlan atlas plan) :
    DeclaredHandoffRepairClears atlas plan <->
      HandoffRepairTransversal atlas plan.touched := by
  constructor
  · exact hitsEveryHandoffComponentSupport_of_declaredClearance
  · exact
      declaredClearance_of_hitsEveryHandoffComponentSupport_of_componentComplete
        hcomplete

/-! ## Exact singleton component support in Cycle 63 deletion witnesses -/

/-- The support-law deletion atlas has exactly the support component. -/
theorem supportLawDeletion_componentSupport_iff
    (component : BridgeComponent) :
    HandoffComponentSupport supportLawDeletionAtlas component <->
      component = BridgeComponent.support := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨loop, hmem, hsupport⟩
    simp [supportLawDeletionAtlas, componentSupportAtlas] at hmem
    subst loop
    cases component with
    | support => rfl
    | trace =>
        exact False.elim
          (hsupport supportDeletion_traceCompatible)
    | repairFrontier =>
        exact False.elim
          (hsupport supportDeletion_repairFrontierCompatible)
  · intro hcomponent
    subst component
    exact supportLawDeletion_componentSupport

/-- The trace-law deletion atlas has exactly the trace component. -/
theorem traceLawDeletion_componentSupport_iff
    (component : BridgeComponent) :
    HandoffComponentSupport traceLawDeletionAtlas component <->
      component = BridgeComponent.trace := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨loop, hmem, hsupport⟩
    simp [traceLawDeletionAtlas, componentSupportAtlas,
      traceLawDeletionHandoff] at hmem
    subst loop
    cases component with
    | support =>
        exact False.elim
          (hsupport traceRenamedHandoff_supportCompatible)
    | trace => rfl
    | repairFrontier =>
        exact False.elim
          (hsupport traceRenamedHandoff_repairFrontierCompatible)
  · intro hcomponent
    subst component
    exact traceLawDeletion_componentSupport

/-- The repair-frontier-law deletion atlas has exactly the repair-frontier component. -/
theorem repairFrontierLawDeletion_componentSupport_iff
    (component : BridgeComponent) :
    HandoffComponentSupport repairFrontierLawDeletionAtlas component <->
      component = BridgeComponent.repairFrontier := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨loop, hmem, hsupport⟩
    simp [repairFrontierLawDeletionAtlas, componentSupportAtlas] at hmem
    subst loop
    cases component with
    | support =>
        exact False.elim
          (hsupport repairFrontierDeletion_supportCompatible)
    | trace =>
        exact False.elim
          (hsupport repairFrontierDeletion_traceCompatible)
    | repairFrontier => rfl
  · intro hcomponent
    subst component
    exact repairFrontierLawDeletion_componentSupport

/-! ## Minimal transversals and visible nonfaithfulness -/

/-- Inclusion-minimal repair transversal for a selected handoff atlas. -/
def MinimalHandoffRepairTransversal
    (atlas : SourceRefHandoffAtlas)
    (support : HandoffRepairSupport) : Prop :=
  HandoffRepairTransversal atlas support /\
    forall other : HandoffRepairSupport,
      HandoffRepairTransversal atlas other ->
        (forall component, other component -> support component) ->
          forall component, support component -> other component

/-- Singleton support for one bridge component. -/
def singletonRepairSupport
    (component : BridgeComponent) : HandoffRepairSupport :=
  fun candidate => candidate = component

/-- The support-law deletion witness has a singleton minimal repair transversal. -/
theorem supportLawDeletion_minimalTransversal :
    MinimalHandoffRepairTransversal supportLawDeletionAtlas
      (singletonRepairSupport BridgeComponent.support) := by
  constructor
  · intro component hsupport
    exact (supportLawDeletion_componentSupport_iff component).mp hsupport
  · intro other hother _hsub component hsingle
    subst component
    exact hother BridgeComponent.support supportLawDeletion_componentSupport

/-- The trace-law deletion witness has a singleton minimal repair transversal. -/
theorem traceLawDeletion_minimalTransversal :
    MinimalHandoffRepairTransversal traceLawDeletionAtlas
      (singletonRepairSupport BridgeComponent.trace) := by
  constructor
  · intro component hsupport
    exact (traceLawDeletion_componentSupport_iff component).mp hsupport
  · intro other hother _hsub component hsingle
    subst component
    exact hother BridgeComponent.trace traceLawDeletion_componentSupport

/-- The repair-frontier-law deletion witness has a singleton minimal repair transversal. -/
theorem repairFrontierLawDeletion_minimalTransversal :
    MinimalHandoffRepairTransversal repairFrontierLawDeletionAtlas
      (singletonRepairSupport BridgeComponent.repairFrontier) := by
  constructor
  · intro component hsupport
    exact (repairFrontierLawDeletion_componentSupport_iff component).mp hsupport
  · intro other hother _hsub component hsingle
    subst component
    exact hother BridgeComponent.repairFrontier
      repairFrontierLawDeletion_componentSupport

/-- Lossful visible shape projection for one-component repair displays. -/
inductive VisibleRepairShape where
  | oneComponent
  deriving DecidableEq

/--
The visible projection deliberately forgets the protected component identity.

It is only intended for singleton component-repair displays in this theorem
package.
-/
def visibleOneComponentRepairShapeProjection
    (_support : HandoffRepairSupport) : VisibleRepairShape :=
  VisibleRepairShape.oneComponent

/-- The support and trace singleton repairs have the same visible projection. -/
theorem support_trace_same_visibleOneComponentRepairShape :
    visibleOneComponentRepairShapeProjection
        (singletonRepairSupport BridgeComponent.support) =
      visibleOneComponentRepairShapeProjection
        (singletonRepairSupport BridgeComponent.trace) := by
  rfl

/-- The support and trace singleton repair supports are protected-distinct. -/
theorem support_trace_transversalSupport_distinct :
    singletonRepairSupport BridgeComponent.support ≠
      singletonRepairSupport BridgeComponent.trace := by
  intro heq
  have hsupport :
      singletonRepairSupport BridgeComponent.support BridgeComponent.support := rfl
  have htrace :
      singletonRepairSupport BridgeComponent.trace BridgeComponent.support := by
    simpa [heq] using hsupport
  cases htrace

/--
The visible one-component repair shape is not faithful to protected repair
transversal support.
-/
theorem oneComponentRepairShape_not_faithful_to_repairTransversal :
    exists supportTrace : HandoffRepairSupport,
      visibleOneComponentRepairShapeProjection
          (singletonRepairSupport BridgeComponent.support) =
        visibleOneComponentRepairShapeProjection supportTrace /\
      singletonRepairSupport BridgeComponent.support ≠ supportTrace /\
      MinimalHandoffRepairTransversal supportLawDeletionAtlas
        (singletonRepairSupport BridgeComponent.support) /\
      MinimalHandoffRepairTransversal traceLawDeletionAtlas supportTrace := by
  exact
    ⟨singletonRepairSupport BridgeComponent.trace,
      support_trace_same_visibleOneComponentRepairShape,
      support_trace_transversalSupport_distinct,
      supportLawDeletion_minimalTransversal,
      traceLawDeletion_minimalTransversal⟩

/-! ## Theorem package -/

/--
Cycle-64 theorem package: declared component-support clearance induces a
repair transversal; component-complete repair plans turn transversality into
declared clearance; the three Cycle-63 deletion witnesses have singleton
minimal repair transversals; and one-component visible repair shape is not
faithful to protected repair transversal support.
-/
theorem handoffRepairTransversal_package :
    (forall (atlas : SourceRefHandoffAtlas) (plan : HandoffRepairPlan),
      DeclaredHandoffRepairClears atlas plan ->
        HandoffRepairTransversal atlas plan.touched) /\
      (forall (atlas : SourceRefHandoffAtlas) (plan : HandoffRepairPlan),
        ComponentCompleteHandoffRepairPlan atlas plan ->
          (DeclaredHandoffRepairClears atlas plan <->
            HandoffRepairTransversal atlas plan.touched)) /\
      (forall component,
        HandoffComponentSupport supportLawDeletionAtlas component <->
          component = BridgeComponent.support) /\
      (forall component,
        HandoffComponentSupport traceLawDeletionAtlas component <->
          component = BridgeComponent.trace) /\
      (forall component,
        HandoffComponentSupport repairFrontierLawDeletionAtlas component <->
          component = BridgeComponent.repairFrontier) /\
      MinimalHandoffRepairTransversal supportLawDeletionAtlas
        (singletonRepairSupport BridgeComponent.support) /\
      MinimalHandoffRepairTransversal traceLawDeletionAtlas
        (singletonRepairSupport BridgeComponent.trace) /\
      MinimalHandoffRepairTransversal repairFrontierLawDeletionAtlas
        (singletonRepairSupport BridgeComponent.repairFrontier) /\
      exists supportTrace : HandoffRepairSupport,
        visibleOneComponentRepairShapeProjection
            (singletonRepairSupport BridgeComponent.support) =
          visibleOneComponentRepairShapeProjection supportTrace /\
        singletonRepairSupport BridgeComponent.support ≠ supportTrace /\
        MinimalHandoffRepairTransversal supportLawDeletionAtlas
          (singletonRepairSupport BridgeComponent.support) /\
        MinimalHandoffRepairTransversal traceLawDeletionAtlas supportTrace := by
  exact
    ⟨fun _atlas _plan =>
        hitsEveryHandoffComponentSupport_of_declaredClearance,
      fun _atlas _plan hcomplete =>
        declaredClearance_iff_hitsEvery_of_componentComplete hcomplete,
      supportLawDeletion_componentSupport_iff,
      traceLawDeletion_componentSupport_iff,
      repairFrontierLawDeletion_componentSupport_iff,
      supportLawDeletion_minimalTransversal,
      traceLawDeletion_minimalTransversal,
      repairFrontierLawDeletion_minimalTransversal,
      oneComponentRepairShape_not_faithful_to_repairTransversal⟩

end HandoffRepairTransversalTheorem
end QualitySurface
end ResearchLean.AG
