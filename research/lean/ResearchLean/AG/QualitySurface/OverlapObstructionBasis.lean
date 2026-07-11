import ResearchLean.AG.QualitySurface.HandoffCechExactness

/-!
Cycle 66 evidence for `G-aat-quality-surface-01`.

This file turns finite Cech-style handoff overlap support into a selected
overlap obstruction basis.  A basis is required to be sound and complete for
the cover's full overlap component support; it is not merely a witness for the
same nonempty/global-failure boolean.  In a component-complete declared repair
regime, clearing the overlap is equivalent to hitting every basis component.

The claim is relative to selected finite source-ref handoff covers, supplied
overlap cocycle data, bounded handoff laws, the finite `BridgeComponent`
vocabulary, and declared component-level repair predicates.  It does not assert
canonical global minimality, runtime repair synthesis, source extraction
completeness, ArchMap correctness, arbitrary route enumeration, or whole-codebase
quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace HandoffCechOverlapBasis

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open SourceRefHandoffBridge
open SourceRefHandoffHolonomyCorrespondence
open SourceRefHandoffObstructionLocus
open SourceRefHandoffComponentSupport
open HandoffRepairTransversalTheorem
open HandoffCechExactness

/-! ## Overlap obstruction bases -/

/-- A component predicate is sound when every listed component is real overlap support. -/
def OverlapBasisSound
    (cover : HandoffCechCover)
    (basis : BridgeComponent -> Prop) : Prop :=
  forall component,
    basis component -> HandoffCechOverlapSupport cover component

/-- A component predicate generates the full overlap support when it covers every support. -/
def OverlapBasisGenerates
    (cover : HandoffCechCover)
    (basis : BridgeComponent -> Prop) : Prop :=
  forall component,
    HandoffCechOverlapSupport cover component -> basis component

/--
A selected overlap obstruction basis is both sound and complete for the cover's
full overlap component support.
-/
def OverlapObstructionBasis
    (cover : HandoffCechCover)
    (basis : BridgeComponent -> Prop) : Prop :=
  OverlapBasisSound cover basis /\
    OverlapBasisGenerates cover basis

/-- Drop one component from a selected basis predicate. -/
def basisDrops
    (basis : BridgeComponent -> Prop)
    (dropped : BridgeComponent) : BridgeComponent -> Prop :=
  fun component => basis component /\ component ≠ dropped

/--
Irredundancy means the basis is exact, and deleting any listed component
destroys generation of the same cover's overlap support.
-/
def OverlapBasisIrredundant
    (cover : HandoffCechCover)
    (basis : BridgeComponent -> Prop) : Prop :=
  OverlapObstructionBasis cover basis /\
    forall component,
      basis component ->
        Not (OverlapBasisGenerates cover (basisDrops basis component))

/-- A declared repair support hits every selected basis component. -/
def OverlapBasisTransversal
    (basis : BridgeComponent -> Prop)
    (support : HandoffRepairSupport) : Prop :=
  forall component,
    basis component -> support component

/-- A basis-complete repair package pairs basis exactness with component completeness. -/
def HandoffCechBasisCompleteRepairPlan
    (cover : HandoffCechCover)
    (basis : BridgeComponent -> Prop)
    (plan : HandoffRepairPlan) : Prop :=
  OverlapObstructionBasis cover basis /\
    ComponentCompleteHandoffRepairPlan cover.overlapCocycle plan

/-- An exact basis is equivalent to full overlap component support. -/
theorem overlapBasis_iff_overlapSupport
    {cover : HandoffCechCover}
    {basis : BridgeComponent -> Prop}
    (hbasis : OverlapObstructionBasis cover basis)
    (component : BridgeComponent) :
    basis component <-> HandoffCechOverlapSupport cover component := by
  constructor
  · exact hbasis.1 component
  · exact hbasis.2 component

/--
Under local chart exactness, an empty generated basis is equivalent to global
handoff exactness.
-/
theorem overlapBasis_empty_iff_globalExact_of_local
    {cover : HandoffCechCover}
    (hlocal : HandoffCechLocalExact cover) :
    OverlapBasisGenerates cover (fun _ => False) <->
      HandoffCechGlobalExact cover := by
  constructor
  · intro hgen
    have hempty : HandoffCechOverlapSupportEmpty cover := by
      intro hnonempty
      rcases hnonempty with ⟨component, hsupport⟩
      exact hgen component hsupport
    exact
      (handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty
        cover).mpr
        ⟨hlocal, hempty⟩
  · intro hglobal component hsupport
    have hempty : HandoffCechOverlapSupportEmpty cover :=
      ((handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty
        cover).mp hglobal).2
    exact False.elim (hempty ⟨component, hsupport⟩)

/-- Hitting an exact basis is equivalent to hitting the full overlap support. -/
theorem overlapBasisTransversal_iff_fullOverlapTransversal
    {cover : HandoffCechCover}
    {basis : BridgeComponent -> Prop}
    {support : HandoffRepairSupport}
    (hbasis : OverlapObstructionBasis cover basis) :
    OverlapBasisTransversal basis support <->
      HandoffCechOverlapRepairTransversal cover support := by
  constructor
  · intro hbasisHit component hsupport
    exact hbasisHit component (hbasis.2 component hsupport)
  · intro hfull component hbasisComponent
    exact hfull component (hbasis.1 component hbasisComponent)

/--
For component-complete declared repair plans, overlap repair clearance is
equivalent to hitting every selected basis component.
-/
theorem declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
    {cover : HandoffCechCover}
    {basis : BridgeComponent -> Prop}
    {plan : HandoffRepairPlan}
    (hbasis : OverlapObstructionBasis cover basis)
    (hcomplete :
      ComponentCompleteHandoffRepairPlan cover.overlapCocycle plan) :
    HandoffCechRepairObligation cover plan <->
      OverlapBasisTransversal basis plan.touched := by
  calc
    HandoffCechRepairObligation cover plan <->
        HandoffCechOverlapRepairTransversal cover plan.touched :=
      handoffCech_repairObligation_iff_overlapRepairTransversal_of_componentComplete
        (cover := cover) (plan := plan) hcomplete
    _ <-> OverlapBasisTransversal basis plan.touched :=
      (overlapBasisTransversal_iff_fullOverlapTransversal
        (cover := cover) (basis := basis) (support := plan.touched)
        hbasis).symm

/-! ## Selected singleton overlap bases -/

/-- Singleton component basis. -/
def singletonOverlapBasis
    (component : BridgeComponent) : BridgeComponent -> Prop :=
  fun candidate => candidate = component

/-- The support-law deletion overlap cover. -/
def supportOverlapBasisCover : HandoffCechCover where
  charts := [alignedSourceRefHandoffAtlas]
  overlapCocycle := supportLawDeletionAtlas

/-- The trace-law deletion overlap cover. -/
def traceOverlapBasisCover : HandoffCechCover where
  charts := [alignedSourceRefHandoffAtlas]
  overlapCocycle := traceLawDeletionAtlas

/-- The repair-frontier-law deletion overlap cover. -/
def repairFrontierOverlapBasisCover : HandoffCechCover where
  charts := [alignedSourceRefHandoffAtlas]
  overlapCocycle := repairFrontierLawDeletionAtlas

/-- The support-law deletion overlap cover has exact local charts. -/
theorem supportOverlapBasisCover_localExact :
    HandoffCechLocalExact supportOverlapBasisCover := by
  intro chart hmem
  simp [supportOverlapBasisCover] at hmem
  subst chart
  exact alignedSourceRefHandoffAtlas_interactionExact

/-- The trace-law deletion overlap cover has exact local charts. -/
theorem traceOverlapBasisCover_localExact :
    HandoffCechLocalExact traceOverlapBasisCover := by
  intro chart hmem
  simp [traceOverlapBasisCover] at hmem
  subst chart
  exact alignedSourceRefHandoffAtlas_interactionExact

/-- The repair-frontier-law deletion overlap cover has exact local charts. -/
theorem repairFrontierOverlapBasisCover_localExact :
    HandoffCechLocalExact repairFrontierOverlapBasisCover := by
  intro chart hmem
  simp [repairFrontierOverlapBasisCover] at hmem
  subst chart
  exact alignedSourceRefHandoffAtlas_interactionExact

/-- The support deletion cover's exact overlap basis is the support component. -/
theorem supportOverlapBasis :
    OverlapObstructionBasis supportOverlapBasisCover
      (singletonOverlapBasis BridgeComponent.support) := by
  constructor
  · intro component hsingle
    subst component
    simpa [supportOverlapBasisCover, HandoffCechOverlapSupport]
      using supportLawDeletion_componentSupport
  · intro component hsupport
    exact
      (supportLawDeletion_componentSupport_iff component).mp
        (by
          simpa [supportOverlapBasisCover, HandoffCechOverlapSupport]
            using hsupport)

/-- The trace deletion cover's exact overlap basis is the trace component. -/
theorem traceOverlapBasis :
    OverlapObstructionBasis traceOverlapBasisCover
      (singletonOverlapBasis BridgeComponent.trace) := by
  constructor
  · intro component hsingle
    subst component
    simpa [traceOverlapBasisCover, HandoffCechOverlapSupport]
      using traceLawDeletion_componentSupport
  · intro component hsupport
    exact
      (traceLawDeletion_componentSupport_iff component).mp
        (by
          simpa [traceOverlapBasisCover, HandoffCechOverlapSupport]
            using hsupport)

/-- The repair-frontier deletion cover's exact overlap basis is the repair-frontier component. -/
theorem repairFrontierOverlapBasis :
    OverlapObstructionBasis repairFrontierOverlapBasisCover
      (singletonOverlapBasis BridgeComponent.repairFrontier) := by
  constructor
  · intro component hsingle
    subst component
    simpa [repairFrontierOverlapBasisCover, HandoffCechOverlapSupport]
      using repairFrontierLawDeletion_componentSupport
  · intro component hsupport
    exact
      (repairFrontierLawDeletion_componentSupport_iff component).mp
        (by
          simpa [repairFrontierOverlapBasisCover,
            HandoffCechOverlapSupport] using hsupport)

/-- The support deletion cover has nonempty overlap support. -/
theorem supportOverlapBasisCover_overlapSupportNonempty :
    HandoffCechOverlapSupportNonempty supportOverlapBasisCover :=
  ⟨BridgeComponent.support,
    (supportOverlapBasis).1 BridgeComponent.support rfl⟩

/-- The trace deletion cover has nonempty overlap support. -/
theorem traceOverlapBasisCover_overlapSupportNonempty :
    HandoffCechOverlapSupportNonempty traceOverlapBasisCover :=
  ⟨BridgeComponent.trace,
    (traceOverlapBasis).1 BridgeComponent.trace rfl⟩

/-- The repair-frontier deletion cover has nonempty overlap support. -/
theorem repairFrontierOverlapBasisCover_overlapSupportNonempty :
    HandoffCechOverlapSupportNonempty repairFrontierOverlapBasisCover :=
  ⟨BridgeComponent.repairFrontier,
    (repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl⟩

/-- The support deletion cover remains globally obstructed. -/
theorem supportOverlapBasisCover_notGlobalExact :
    Not (HandoffCechGlobalExact supportOverlapBasisCover) :=
  (handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
    supportOverlapBasisCover_localExact).mp
    supportOverlapBasisCover_overlapSupportNonempty

/-- The trace deletion cover remains globally obstructed. -/
theorem traceOverlapBasisCover_notGlobalExact :
    Not (HandoffCechGlobalExact traceOverlapBasisCover) :=
  (handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
    traceOverlapBasisCover_localExact).mp
    traceOverlapBasisCover_overlapSupportNonempty

/-- The repair-frontier deletion cover remains globally obstructed. -/
theorem repairFrontierOverlapBasisCover_notGlobalExact :
    Not (HandoffCechGlobalExact repairFrontierOverlapBasisCover) :=
  (handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
    repairFrontierOverlapBasisCover_localExact).mp
    repairFrontierOverlapBasisCover_overlapSupportNonempty

/-- Dropping the support component destroys generation on the same cover. -/
theorem supportOverlapBasis_drop_not_generates :
    Not
      (OverlapBasisGenerates supportOverlapBasisCover
        (basisDrops
          (singletonOverlapBasis BridgeComponent.support)
          BridgeComponent.support)) := by
  intro hgen
  have hdrop :=
    hgen BridgeComponent.support
      ((supportOverlapBasis).1 BridgeComponent.support rfl)
  exact hdrop.2 rfl

/-- Dropping the trace component destroys generation on the same cover. -/
theorem traceOverlapBasis_drop_not_generates :
    Not
      (OverlapBasisGenerates traceOverlapBasisCover
        (basisDrops
          (singletonOverlapBasis BridgeComponent.trace)
          BridgeComponent.trace)) := by
  intro hgen
  have hdrop :=
    hgen BridgeComponent.trace
      ((traceOverlapBasis).1 BridgeComponent.trace rfl)
  exact hdrop.2 rfl

/-- Dropping the repair-frontier component destroys generation on the same cover. -/
theorem repairFrontierOverlapBasis_drop_not_generates :
    Not
      (OverlapBasisGenerates repairFrontierOverlapBasisCover
        (basisDrops
          (singletonOverlapBasis BridgeComponent.repairFrontier)
          BridgeComponent.repairFrontier)) := by
  intro hgen
  have hdrop :=
    hgen BridgeComponent.repairFrontier
      ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl)
  exact hdrop.2 rfl

/-- The support deletion cover has an irredundant singleton overlap basis. -/
theorem supportOverlapBasis_irredundant :
    OverlapBasisIrredundant supportOverlapBasisCover
      (singletonOverlapBasis BridgeComponent.support) := by
  constructor
  · exact supportOverlapBasis
  · intro component hsingle
    subst component
    exact supportOverlapBasis_drop_not_generates

/-- The trace deletion cover has an irredundant singleton overlap basis. -/
theorem traceOverlapBasis_irredundant :
    OverlapBasisIrredundant traceOverlapBasisCover
      (singletonOverlapBasis BridgeComponent.trace) := by
  constructor
  · exact traceOverlapBasis
  · intro component hsingle
    subst component
    exact traceOverlapBasis_drop_not_generates

/-- The repair-frontier deletion cover has an irredundant singleton overlap basis. -/
theorem repairFrontierOverlapBasis_irredundant :
    OverlapBasisIrredundant repairFrontierOverlapBasisCover
      (singletonOverlapBasis BridgeComponent.repairFrontier) := by
  constructor
  · exact repairFrontierOverlapBasis
  · intro component hsingle
    subst component
    exact repairFrontierOverlapBasis_drop_not_generates

/-! ## Visible one-component display nonfaithfulness -/

/-- Lossful visible shape for one-component overlap-basis displays. -/
inductive VisibleOverlapBasisShape where
  | oneComponent
  deriving DecidableEq

/--
The visible projection deliberately forgets the protected component identity.
It is only intended for singleton overlap-basis displays in this theorem
package.
-/
def visibleOneComponentOverlapBasisProjection
    (_basis : BridgeComponent -> Prop) : VisibleOverlapBasisShape :=
  VisibleOverlapBasisShape.oneComponent

/-- The support and trace singleton bases have the same visible one-component display. -/
theorem support_trace_same_visibleOneComponentOverlapBasisShape :
    visibleOneComponentOverlapBasisProjection
        (singletonOverlapBasis BridgeComponent.support) =
      visibleOneComponentOverlapBasisProjection
        (singletonOverlapBasis BridgeComponent.trace) := by
  rfl

/-- The support and trace singleton bases are protected-distinct. -/
theorem support_trace_overlapBasis_distinct :
    singletonOverlapBasis BridgeComponent.support ≠
      singletonOverlapBasis BridgeComponent.trace := by
  intro heq
  have hsupport :
      singletonOverlapBasis BridgeComponent.support BridgeComponent.support := rfl
  have htrace :
      singletonOverlapBasis BridgeComponent.trace BridgeComponent.support := by
    simpa [heq] using hsupport
  cases htrace

/--
The visible one-component overlap-basis display is not faithful to protected
overlap basis identity or to its selected cover.
-/
theorem oneComponentOverlapBasisShape_not_faithful_to_overlapBasis :
    exists traceBasis : BridgeComponent -> Prop,
      visibleOneComponentOverlapBasisProjection
          (singletonOverlapBasis BridgeComponent.support) =
        visibleOneComponentOverlapBasisProjection traceBasis /\
      singletonOverlapBasis BridgeComponent.support ≠ traceBasis /\
      OverlapBasisIrredundant supportOverlapBasisCover
        (singletonOverlapBasis BridgeComponent.support) /\
      OverlapBasisIrredundant traceOverlapBasisCover traceBasis := by
  exact
    ⟨singletonOverlapBasis BridgeComponent.trace,
      support_trace_same_visibleOneComponentOverlapBasisShape,
      support_trace_overlapBasis_distinct,
      supportOverlapBasis_irredundant,
      traceOverlapBasis_irredundant⟩

/-! ## Theorem package -/

/--
Cycle-66 theorem package: selected finite overlap obstruction bases are exact
for full overlap support; empty generation is equivalent to global exactness
under local exactness; component-complete declared repair clears a cover exactly
when the repair support hits every basis component; the three deletion covers
have irredundant singleton bases; and a visible one-component display is not
faithful to protected basis identity.
-/
theorem overlapObstructionBasisRepairDuality_package :
    (forall {cover : HandoffCechCover}
        {basis : BridgeComponent -> Prop}
        (_hbasis : OverlapObstructionBasis cover basis)
        (component : BridgeComponent),
      basis component <-> HandoffCechOverlapSupport cover component) /\
      (forall {cover : HandoffCechCover},
        HandoffCechLocalExact cover ->
          (OverlapBasisGenerates cover (fun _ => False) <->
            HandoffCechGlobalExact cover)) /\
      (forall {cover : HandoffCechCover}
          {basis : BridgeComponent -> Prop}
          {plan : HandoffRepairPlan},
        OverlapObstructionBasis cover basis ->
          ComponentCompleteHandoffRepairPlan cover.overlapCocycle plan ->
            (HandoffCechRepairObligation cover plan <->
              OverlapBasisTransversal basis plan.touched)) /\
      OverlapBasisIrredundant supportOverlapBasisCover
        (singletonOverlapBasis BridgeComponent.support) /\
      OverlapBasisIrredundant traceOverlapBasisCover
        (singletonOverlapBasis BridgeComponent.trace) /\
      OverlapBasisIrredundant repairFrontierOverlapBasisCover
        (singletonOverlapBasis BridgeComponent.repairFrontier) /\
      Not (HandoffCechGlobalExact supportOverlapBasisCover) /\
      Not (HandoffCechGlobalExact traceOverlapBasisCover) /\
      Not (HandoffCechGlobalExact repairFrontierOverlapBasisCover) /\
      (exists traceBasis : BridgeComponent -> Prop,
        visibleOneComponentOverlapBasisProjection
            (singletonOverlapBasis BridgeComponent.support) =
          visibleOneComponentOverlapBasisProjection traceBasis /\
        singletonOverlapBasis BridgeComponent.support ≠ traceBasis /\
        OverlapBasisIrredundant supportOverlapBasisCover
          (singletonOverlapBasis BridgeComponent.support) /\
        OverlapBasisIrredundant traceOverlapBasisCover traceBasis) := by
  exact
    ⟨fun {cover} {basis} hbasis component =>
        overlapBasis_iff_overlapSupport
          (cover := cover) (basis := basis) hbasis component,
      fun {cover} hlocal =>
        overlapBasis_empty_iff_globalExact_of_local
          (cover := cover) hlocal,
      fun {cover} {basis} {plan} hbasis hcomplete =>
        declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
          (cover := cover) (basis := basis) (plan := plan) hbasis
          hcomplete,
      supportOverlapBasis_irredundant,
      traceOverlapBasis_irredundant,
      repairFrontierOverlapBasis_irredundant,
      supportOverlapBasisCover_notGlobalExact,
      traceOverlapBasisCover_notGlobalExact,
      repairFrontierOverlapBasisCover_notGlobalExact,
      oneComponentOverlapBasisShape_not_faithful_to_overlapBasis⟩

end HandoffCechOverlapBasis
end QualitySurface
end ResearchLean.AG
