import Formal.AG.Research.QualitySurface.SemanticRepairCocycleWitness

/-!
Cycle 78 evidence for `G-aat-quality-surface-01`.

This file refines the Cycle 77 semantic repair witness by splitting the
repair-frontier semantic vocabulary into a visible surface atom and a protected
obligation atom.  Both semantic supports project to the same protected
`BridgeComponent` support, so the component-level branch adequacy checker sees
the same pass.  The refined semantic residual, however, is carried by the
obligation atom, and only the obligation-aware semantic support hits it.

The result is a finite projection-kernel theorem.  Component support is not
faithful to semantic repair-residual clearance once multiple semantic atoms
project to the same protected component.  The claim remains witness-level and
does not assert source extraction completeness, ArchMap correctness, runtime
repair synthesis, canonical global semantic ontology, global sheaf
completeness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticSupportProjectionKernel

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open HandoffCechExactness
open HandoffCechOverlapBasis
open BranchReflectionAdequacyKernel
open ComponentRefinementSupportLift
open SemanticRepairCocycleWitness

/-! ## Refined semantic repair supports -/

/--
Refined semantic atoms split the repair-frontier component into a visible
surface atom and a protected obligation atom.
-/
inductive RefinedSemanticRepairAtom where
  | traceContract
  | repairFrontierSurface
  | repairFrontierObligation
deriving DecidableEq

open RefinedSemanticRepairAtom

/-- Projection from refined semantic atoms to protected bridge components. -/
def refinedSemanticComponent :
    RefinedSemanticRepairAtom -> BridgeComponent
  | traceContract => BridgeComponent.trace
  | repairFrontierSurface => BridgeComponent.repairFrontier
  | repairFrontierObligation => BridgeComponent.repairFrontier

/-- A refined semantic repair support predicate. -/
abbrev RefinedSemanticRepairSupport :=
  RefinedSemanticRepairAtom -> Prop

/-- Support that records the visible repair-frontier surface but not the obligation. -/
def surfaceRepairSupport : RefinedSemanticRepairSupport
  | traceContract => True
  | repairFrontierSurface => True
  | repairFrontierObligation => False

/-- Support that records the protected repair-frontier obligation. -/
def obligationRepairSupport : RefinedSemanticRepairSupport
  | traceContract => True
  | repairFrontierSurface => False
  | repairFrontierObligation => True

/-- Support that records every refined semantic repair atom in the selected witness. -/
def completeRepairSupport : RefinedSemanticRepairSupport
  | traceContract => True
  | repairFrontierSurface => True
  | repairFrontierObligation => True

/-- Component support induced by a refined semantic support. -/
def componentSupportOfRefinedSemantic
    (support : RefinedSemanticRepairSupport) : HandoffRepairSupport :=
  fun component =>
    exists atom, support atom /\ refinedSemanticComponent atom = component

/--
The surface-reading semantic support projects to the selected component-level
trace plus repair-frontier support.
-/
theorem surfaceRepairSupport_projects_to_componentSupport
    (component : BridgeComponent) :
    componentSupportOfRefinedSemantic surfaceRepairSupport component <->
      traceRepairFrontierRepairSupport component := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨atom, hsupport, hcomponent⟩
    cases atom <;> simp [surfaceRepairSupport, refinedSemanticComponent,
      traceRepairFrontierRepairSupport] at hsupport hcomponent ⊢
    · exact Or.inl hcomponent.symm
    · exact Or.inr hcomponent.symm
  · intro hcomponent
    rcases hcomponent with htrace | hrepair
    · subst component
      exact ⟨traceContract, trivial, rfl⟩
    · subst component
      exact ⟨repairFrontierSurface, trivial, rfl⟩

/--
The obligation-aware semantic support projects to the same selected
component-level trace plus repair-frontier support.
-/
theorem obligationRepairSupport_projects_to_componentSupport
    (component : BridgeComponent) :
    componentSupportOfRefinedSemantic obligationRepairSupport component <->
      traceRepairFrontierRepairSupport component := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨atom, hsupport, hcomponent⟩
    cases atom <;> simp [obligationRepairSupport,
      refinedSemanticComponent, traceRepairFrontierRepairSupport]
      at hsupport hcomponent ⊢
    · exact Or.inl hcomponent.symm
    · exact Or.inr hcomponent.symm
  · intro hcomponent
    rcases hcomponent with htrace | hrepair
    · subst component
      exact ⟨traceContract, trivial, rfl⟩
    · subst component
      exact ⟨repairFrontierObligation, trivial, rfl⟩

/--
The complete refined semantic support also projects to the selected
component-level trace plus repair-frontier support.
-/
theorem completeRepairSupport_projects_to_componentSupport
    (component : BridgeComponent) :
    componentSupportOfRefinedSemantic completeRepairSupport component <->
      traceRepairFrontierRepairSupport component := by
  constructor
  · intro hcomponent
    rcases hcomponent with ⟨atom, _hsupport, hcomponent⟩
    cases atom <;> simp [refinedSemanticComponent,
      traceRepairFrontierRepairSupport]
      at hcomponent ⊢
    · exact Or.inl hcomponent.symm
    · exact Or.inr hcomponent.symm
    · exact Or.inr hcomponent.symm
  · intro hcomponent
    rcases hcomponent with htrace | hrepair
    · subst component
      exact ⟨traceContract, trivial, rfl⟩
    · subst component
      exact ⟨repairFrontierSurface, trivial, rfl⟩

/-- The two refined semantic supports are indistinguishable after component projection. -/
theorem surface_and_obligation_same_componentProjection
    (component : BridgeComponent) :
    componentSupportOfRefinedSemantic surfaceRepairSupport component <->
      componentSupportOfRefinedSemantic obligationRepairSupport component := by
  exact
    (surfaceRepairSupport_projects_to_componentSupport component).trans
      (obligationRepairSupport_projects_to_componentSupport component).symm

/-- Surface-reading and complete semantic supports are indistinguishable after component projection. -/
theorem surface_and_complete_same_componentProjection
    (component : BridgeComponent) :
    componentSupportOfRefinedSemantic surfaceRepairSupport component <->
      componentSupportOfRefinedSemantic completeRepairSupport component := by
  exact
    (surfaceRepairSupport_projects_to_componentSupport component).trans
      (completeRepairSupport_projects_to_componentSupport component).symm

/-! ## Generic projection criterion -/

/-- Component support induced by an arbitrary semantic projection. -/
def SemanticComponentSupport
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (support : Atom -> Prop)
    (component : BridgeComponent) : Prop :=
  exists atom, support atom /\ projection atom = component

/-- Semantic residual induced by an arbitrary semantic projection and Cech cover. -/
def SemanticProjectedResidual
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (atom : Atom) : Prop :=
  HandoffCechOverlapSupport cover (projection atom)

/-- A semantic support closes every projected semantic residual. -/
def SemanticRepairClosed
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (support : Atom -> Prop) : Prop :=
  forall atom,
    SemanticProjectedResidual projection cover atom -> support atom

/--
Residual fibers are singleton when no other semantic atom maps to the component
of a residual atom.
-/
def ResidualFiberSingleton
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover) : Prop :=
  forall residual candidate,
    SemanticProjectedResidual projection cover residual ->
      projection candidate = projection residual ->
        candidate = residual

/--
If every residual component has a singleton semantic fiber, then component
projection reflects semantic repair closure.
-/
theorem componentProjection_reflects_semanticRepairClosed_of_residualFiberSingleton
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsingleton : ResidualFiberSingleton projection cover)
    (hsameComponent :
      forall component,
        SemanticComponentSupport projection sourceSupport component <->
          SemanticComponentSupport projection targetSupport component)
    (hclosed : SemanticRepairClosed projection cover sourceSupport) :
    SemanticRepairClosed projection cover targetSupport := by
  intro residual hresidual
  have hsource : sourceSupport residual :=
    hclosed residual hresidual
  have htargetComponent :
      SemanticComponentSupport projection targetSupport
        (projection residual) :=
    (hsameComponent (projection residual)).mp
      ⟨residual, hsource, rfl⟩
  rcases htargetComponent with ⟨candidate, htarget, hprojection⟩
  have hcandidate : candidate = residual :=
    hsingleton residual candidate hresidual hprojection
  subst candidate
  exact htarget

/-! ## Selected projection-kernel counterexample -/

/-- The complete support closes every projected residual of the selected cover. -/
theorem completeRepairSupport_semanticRepairClosed :
    SemanticRepairClosed
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport := by
  intro atom _hresidual
  cases atom <;> trivial

/-- The surface-reading support does not close every projected residual. -/
theorem surfaceRepairSupport_not_semanticRepairClosed :
    Not
      (SemanticRepairClosed
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport) := by
  intro hclosed
  exact
    hclosed repairFrontierObligation
      ((repairFrontierOverlapBasis).1
        BridgeComponent.repairFrontier rfl)

/-- The selected refined semantic projection has a non-singleton residual fiber. -/
theorem refinedSemanticProjection_not_residualFiberSingleton :
    Not
      (ResidualFiberSingleton
        refinedSemanticComponent repairFrontierOverlapBasisCover) := by
  intro hsingleton
  have hsame :
      repairFrontierSurface = repairFrontierObligation :=
    hsingleton repairFrontierObligation repairFrontierSurface
      ((repairFrontierOverlapBasis).1
        BridgeComponent.repairFrontier rfl)
      rfl
  cases hsame

/--
Selected counterexample: component projection can be the same while semantic
repair closure differs.
-/
theorem selected_projectionKernel_not_faithful_to_semanticRepairClosed :
    LocalBranchFamilyAdequacyPass /\
      (forall component,
        SemanticComponentSupport refinedSemanticComponent
            surfaceRepairSupport component <->
          SemanticComponentSupport refinedSemanticComponent
            completeRepairSupport component) /\
      SemanticRepairClosed
        refinedSemanticComponent repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualFiberSingleton
          refinedSemanticComponent repairFrontierOverlapBasisCover) := by
  exact
    ⟨localBranchFamilyAdequacy_pass,
      surface_and_complete_same_componentProjection,
      completeRepairSupport_semanticRepairClosed,
      surfaceRepairSupport_not_semanticRepairClosed,
      refinedSemanticProjection_not_residualFiberSingleton⟩

/-! ## Refined semantic residual clearance -/

/--
A refined semantic residual is the protected repair-frontier obligation atom
whose projected component occurs in the overlap support.
-/
def RefinedSemanticRepairResidual
    (cover : HandoffCechCover)
    (atom : RefinedSemanticRepairAtom) : Prop :=
  HandoffCechOverlapSupport cover (refinedSemanticComponent atom) /\
    atom = repairFrontierObligation

/-- A refined support clears all refined semantic residuals of a cover. -/
def RefinedSemanticRepairTransversal
    (cover : HandoffCechCover)
    (support : RefinedSemanticRepairSupport) : Prop :=
  forall atom,
    RefinedSemanticRepairResidual cover atom -> support atom

/-- The selected cover carries the refined repair-frontier obligation residual. -/
theorem refinedRepairFrontierResidual :
    RefinedSemanticRepairResidual
      repairFrontierOverlapBasisCover repairFrontierObligation := by
  exact
    ⟨(repairFrontierOverlapBasis).1
        BridgeComponent.repairFrontier rfl,
      rfl⟩

/-- The surface-reading support misses the refined obligation residual. -/
theorem surfaceRepairSupport_misses_refinedResidual :
    Not
      (RefinedSemanticRepairTransversal
        repairFrontierOverlapBasisCover surfaceRepairSupport) := by
  intro htransversal
  exact htransversal repairFrontierObligation refinedRepairFrontierResidual

/-- The obligation-aware support hits the refined obligation residuals. -/
theorem obligationRepairSupport_hits_refinedResidual :
    RefinedSemanticRepairTransversal
      repairFrontierOverlapBasisCover obligationRepairSupport := by
  intro atom hresidual
  rcases hresidual with ⟨_hsupport, hobligation⟩
  subst atom
  trivial

/-! ## Component-projected adequacy is not faithful -/

/--
Component-projected local adequacy records only that a refined semantic support
projects to the selected component-level support and that the selected branch
adequacy checker passes.
-/
def ComponentProjectedLocalAdequacy
    (support : RefinedSemanticRepairSupport) : Prop :=
  (forall component,
    componentSupportOfRefinedSemantic support component <->
      traceRepairFrontierRepairSupport component) /\
    LocalBranchFamilyAdequacyPass

/-- The surface-reading support passes the component-projected local adequacy surface. -/
theorem surfaceRepairSupport_componentProjectedAdequacy :
    ComponentProjectedLocalAdequacy surfaceRepairSupport :=
  ⟨surfaceRepairSupport_projects_to_componentSupport,
    localBranchFamilyAdequacy_pass⟩

/-- The obligation-aware support passes the same component-projected local adequacy surface. -/
theorem obligationRepairSupport_componentProjectedAdequacy :
    ComponentProjectedLocalAdequacy obligationRepairSupport :=
  ⟨obligationRepairSupport_projects_to_componentSupport,
    localBranchFamilyAdequacy_pass⟩

/--
The component-projected local surface is not faithful to refined semantic
residual clearance: the two supports have the same component projection and
the same local adequacy pass, but only the obligation-aware support clears the
refined semantic residual.
-/
theorem componentProjection_not_faithful_to_refinedSemanticClearance :
    (forall component,
      componentSupportOfRefinedSemantic surfaceRepairSupport component <->
        componentSupportOfRefinedSemantic obligationRepairSupport component) /\
      ComponentProjectedLocalAdequacy surfaceRepairSupport /\
      ComponentProjectedLocalAdequacy obligationRepairSupport /\
      Not
        (RefinedSemanticRepairTransversal
          repairFrontierOverlapBasisCover surfaceRepairSupport) /\
      RefinedSemanticRepairTransversal
        repairFrontierOverlapBasisCover obligationRepairSupport := by
  exact
    ⟨surface_and_obligation_same_componentProjection,
      surfaceRepairSupport_componentProjectedAdequacy,
      obligationRepairSupport_componentProjectedAdequacy,
      surfaceRepairSupport_misses_refinedResidual,
      obligationRepairSupport_hits_refinedResidual⟩

/-! ## Theorem package -/

/--
Cycle-78 theorem package: same component support and same local adequacy pass
do not determine refined semantic residual clearance.
-/
theorem semanticSupportProjectionKernel_package :
    (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {sourceSupport targetSupport : Atom -> Prop},
      ResidualFiberSingleton projection cover ->
        (forall component,
          SemanticComponentSupport projection sourceSupport component <->
            SemanticComponentSupport projection targetSupport component) ->
          SemanticRepairClosed projection cover sourceSupport ->
            SemanticRepairClosed projection cover targetSupport) /\
      LocalBranchFamilyAdequacyPass /\
      Not
        (ResidualFiberSingleton
          refinedSemanticComponent repairFrontierOverlapBasisCover) /\
      SemanticRepairClosed
        refinedSemanticComponent repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
    (forall component,
      componentSupportOfRefinedSemantic surfaceRepairSupport component <->
        traceRepairFrontierRepairSupport component) /\
      (forall component,
        componentSupportOfRefinedSemantic obligationRepairSupport component <->
          traceRepairFrontierRepairSupport component) /\
      (forall component,
        componentSupportOfRefinedSemantic surfaceRepairSupport component <->
          componentSupportOfRefinedSemantic obligationRepairSupport component) /\
      ComponentProjectedLocalAdequacy surfaceRepairSupport /\
      ComponentProjectedLocalAdequacy obligationRepairSupport /\
      RefinedSemanticRepairResidual
        repairFrontierOverlapBasisCover repairFrontierObligation /\
      Not
        (RefinedSemanticRepairTransversal
          repairFrontierOverlapBasisCover surfaceRepairSupport) /\
      RefinedSemanticRepairTransversal
        repairFrontierOverlapBasisCover obligationRepairSupport /\
      (LocalBranchFamilyAdequacyPass /\
        Not
          (RefinedSemanticRepairTransversal
            repairFrontierOverlapBasisCover surfaceRepairSupport) /\
        RefinedSemanticRepairTransversal
          repairFrontierOverlapBasisCover obligationRepairSupport) := by
  exact
    ⟨fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        componentProjection_reflects_semanticRepairClosed_of_residualFiberSingleton,
      localBranchFamilyAdequacy_pass,
      refinedSemanticProjection_not_residualFiberSingleton,
      completeRepairSupport_semanticRepairClosed,
      surfaceRepairSupport_not_semanticRepairClosed,
      surfaceRepairSupport_projects_to_componentSupport,
      obligationRepairSupport_projects_to_componentSupport,
      surface_and_obligation_same_componentProjection,
      surfaceRepairSupport_componentProjectedAdequacy,
      obligationRepairSupport_componentProjectedAdequacy,
      refinedRepairFrontierResidual,
      surfaceRepairSupport_misses_refinedResidual,
      obligationRepairSupport_hits_refinedResidual,
      ⟨localBranchFamilyAdequacy_pass,
        surfaceRepairSupport_misses_refinedResidual,
        obligationRepairSupport_hits_refinedResidual⟩⟩

end SemanticSupportProjectionKernel
end QualitySurface
end Formal.AG.Research
