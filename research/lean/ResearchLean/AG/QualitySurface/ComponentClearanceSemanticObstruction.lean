import ResearchLean.AG.QualitySurface.SemanticRepairCocycleWitness

/-!
Cycle 79 evidence for `G-aat-quality-surface-01`.

This file separates declared component-level Cech clearance from semantic
repair residual emptiness.  The selected repair/transport curved Cech path has
an exact component overlap basis, and a component-complete declared repair plan
touching trace plus repair-frontier clears that component basis.  The same
cover still carries a semantic repair residual, so finite semantic repair
gluing exactness, defined as residual emptiness, fails.

The result is deliberately about declared component clearance, not runtime
repair execution.  It does not assert source extraction completeness, ArchMap
correctness, runtime repair synthesis, canonical global semantic ontology,
general sheaf gluing, global sheaf completeness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ComponentClearanceSemanticObstruction

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open HandoffCechExactness
open HandoffCechOverlapBasis
open RepairTransportCechCommutatorCurvature
open BranchReflectionAdequacyKernel
open ComponentRefinementSupportLift
open SemanticRepairCocycleWitness

/-! ## Declared trace / repair-frontier component clearance -/

/-- Declared component repair plan touching and clearing trace plus repair-frontier. -/
def traceRepairFrontierDeclaredPlan : HandoffRepairPlan where
  touched := traceRepairFrontierRepairSupport
  clears := traceRepairFrontierRepairSupport
  clears_only_if_touched := by
    intro component hclear
    exact hclear

/-- The declared plan is component-complete on the selected curved path. -/
theorem traceRepairFrontierDeclaredPlan_componentComplete :
    ComponentCompleteHandoffRepairPlan
      selectedRepairTransportCechCommutatorCell.curvedPath.overlapCocycle
      traceRepairFrontierDeclaredPlan := by
  intro component _hsupport htouched
  exact htouched

/-- The declared plan hits the selected repair/transport curvature basis. -/
theorem traceRepairFrontierDeclaredPlan_hits_curvatureBasis :
    OverlapBasisTransversal
      repairTransportCurvatureBasis
      traceRepairFrontierDeclaredPlan.touched := by
  intro component hbasis
  rcases hbasis with htrace | hrepair
  · subst component
    exact Or.inl rfl
  · subst component
    exact Or.inr rfl

/-- The declared plan clears the component overlap support of the selected curved path. -/
theorem traceRepairFrontierDeclaredPlan_clears_curvedPath :
    HandoffCechRepairObligation
      selectedRepairTransportCechCommutatorCell.curvedPath
      traceRepairFrontierDeclaredPlan := by
  exact
    (curvedPath_declaredClearance_iff_hitsCurvatureBasis
      (plan := traceRepairFrontierDeclaredPlan)
      traceRepairFrontierDeclaredPlan_componentComplete).mpr
      traceRepairFrontierDeclaredPlan_hits_curvatureBasis

/--
The semantic trace-plus-repair support projects to exactly the component
support touched by the declared plan.
-/
theorem semanticTraceRepairFrontier_projects_to_declaredPlan
    (component : BridgeComponent) :
    componentSupportOfSemantic semanticTraceRepairFrontierSupport component <->
      traceRepairFrontierDeclaredPlan.touched component := by
  exact semanticTraceRepairFrontier_projects_to_componentSupport component

/-! ## Semantic residual remains after declared component clearance -/

/-- The selected curved path carries the semantic repair-frontier residual. -/
theorem curvedPath_semanticRepairFrontierResidual :
    SemanticOverlapResidual
      selectedRepairTransportCechCommutatorCell.curvedPath
      SemanticRepairAtom.repairFrontierObligation := by
  simpa [SemanticOverlapResidual, semanticComponent]
    using curvedPath_repairFrontierOverlapSupport

/-- The selected curved path has nonempty semantic repair residual. -/
theorem curvedPath_semanticResidualNonempty :
    SemanticRepairCocycleResidualNonempty
      selectedRepairTransportCechCommutatorCell.curvedPath :=
  ⟨SemanticRepairAtom.repairFrontierObligation,
    curvedPath_semanticRepairFrontierResidual⟩

/--
Even under declared component clearance, finite semantic repair gluing
exactness fails because residual emptiness fails.
-/
theorem declaredComponentClearance_not_semanticGluingExact :
    Not
      (SemanticRepairGluingExact
        selectedRepairTransportCechCommutatorCell.curvedPath) :=
  semanticResidual_obstructs_globalGluing
    curvedPath_semanticResidualNonempty

/-- The semantic trace-plus-repair support hits every selected curved-path semantic residual. -/
theorem semanticTraceRepairFrontier_hits_curvedPathResiduals :
    SemanticRepairTransversal
      selectedRepairTransportCechCommutatorCell.curvedPath
      semanticTraceRepairFrontierSupport := by
  intro atom _hresidual
  cases atom <;> trivial

/-! ## Theorem package -/

/--
Declared component-level clearance does not imply finite semantic residual
emptiness for the selected curved Cech path.
-/
def ComponentClearanceWithoutSemanticExactness
    (cover : HandoffCechCover)
    (plan : HandoffRepairPlan) : Prop :=
  HandoffCechLocalExact cover /\
    OverlapObstructionBasis cover repairTransportCurvatureBasis /\
    ComponentCompleteHandoffRepairPlan cover.overlapCocycle plan /\
    HandoffCechRepairObligation cover plan /\
    LocalBranchFamilyAdequacyPass /\
    SemanticRepairTransversal cover semanticTraceRepairFrontierSupport /\
    SemanticRepairCocycleResidualNonempty cover /\
    Not (SemanticRepairGluingExact cover) /\
    (forall component,
      componentSupportOfSemantic semanticTraceRepairFrontierSupport component <->
        plan.touched component)

/-- The selected curved Cech path witnesses component clearance without semantic exactness. -/
theorem selected_componentClearance_without_semanticExactness :
    ComponentClearanceWithoutSemanticExactness
      selectedRepairTransportCechCommutatorCell.curvedPath
      traceRepairFrontierDeclaredPlan := by
  exact
    ⟨repairTransportCurvedCechCover_localExact,
      curvedPath_overlapBasis,
      traceRepairFrontierDeclaredPlan_componentComplete,
      traceRepairFrontierDeclaredPlan_clears_curvedPath,
      localBranchFamilyAdequacy_pass,
      semanticTraceRepairFrontier_hits_curvedPathResiduals,
      curvedPath_semanticResidualNonempty,
      declaredComponentClearance_not_semanticGluingExact,
      semanticTraceRepairFrontier_projects_to_declaredPlan⟩

/--
Existential form: there is a finite cover and declared component-complete
repair plan that clears component overlap support while semantic residual
emptiness still fails.
-/
theorem exists_componentClearance_without_semanticGluingExact :
    exists cover : HandoffCechCover, exists plan : HandoffRepairPlan,
      ComponentClearanceWithoutSemanticExactness cover plan := by
  exact
    ⟨selectedRepairTransportCechCommutatorCell.curvedPath,
      traceRepairFrontierDeclaredPlan,
      selected_componentClearance_without_semanticExactness⟩

/--
Cycle-79 theorem package: component-level declared clearance, local adequacy,
semantic residual transversality, and semantic residual nonemptiness coexist in
the selected finite witness.
-/
theorem componentClearanceSemanticObstruction_package :
    ComponentCompleteHandoffRepairPlan
      selectedRepairTransportCechCommutatorCell.curvedPath.overlapCocycle
      traceRepairFrontierDeclaredPlan /\
      HandoffCechRepairObligation
        selectedRepairTransportCechCommutatorCell.curvedPath
        traceRepairFrontierDeclaredPlan /\
      SemanticRepairTransversal
        selectedRepairTransportCechCommutatorCell.curvedPath
        semanticTraceRepairFrontierSupport /\
      SemanticRepairCocycleResidualNonempty
        selectedRepairTransportCechCommutatorCell.curvedPath /\
      Not
        (SemanticRepairGluingExact
          selectedRepairTransportCechCommutatorCell.curvedPath) /\
      ComponentClearanceWithoutSemanticExactness
        selectedRepairTransportCechCommutatorCell.curvedPath
        traceRepairFrontierDeclaredPlan /\
      (exists cover : HandoffCechCover, exists plan : HandoffRepairPlan,
        ComponentClearanceWithoutSemanticExactness cover plan) := by
  exact
    ⟨traceRepairFrontierDeclaredPlan_componentComplete,
      traceRepairFrontierDeclaredPlan_clears_curvedPath,
      semanticTraceRepairFrontier_hits_curvedPathResiduals,
      curvedPath_semanticResidualNonempty,
      declaredComponentClearance_not_semanticGluingExact,
      selected_componentClearance_without_semanticExactness,
      exists_componentClearance_without_semanticGluingExact⟩

end ComponentClearanceSemanticObstruction
end QualitySurface
end ResearchLean.AG
