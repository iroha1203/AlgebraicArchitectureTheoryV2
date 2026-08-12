import ResearchLean.AG.UniformInvariance.GLocalV1Observation
import ResearchLean.AG.UniformInvariance.ConditionCAllAFiring
import Formal.Util.AssertStandardAxioms

/-!
# Positive and negative instances for the permanent `G_local-v1` kernel

This module discharges the acceptance-point instance-pair obligation for the
six Prop-valued predicates introduced by the permanent reduction kernel.  It
fires them on the reviewed nontrivial G-107 presentation `pFire`: the full
scope has several generated packets, and its local unmapped fiber contains an
actual edge and FaceTwin row.  The negative reachability example adds one raw
coarse edge to the empty scope, so its failure is structural rather than a
checker bit supplied by the fixture.

## Implementation notes

The pairs reuse the reviewed `pFire` raw presentation and the same generic
reducer that defines `obsG`; no expected predicate value is stored in a
fixture.  Six unrelated synthetic presentations and Boolean `decide` examples
were rejected because they could exercise a target-fitted fragment instead of
the production kernel.  Negative examples therefore change only raw retained
state or mapped-cell membership, and positive examples are derived from actual
generated packets and local unmapped cells.
-/

namespace AAT.AG.ResolutionInvariance

open FiniteComparisonPresentation
open ResolutionInvarianceFiringWitness

namespace GLocalV1KernelInstancePairs

set_option maxRecDepth 10000

/-- The complete coarse-target scope of the reviewed firing presentation,
used by all positive kernel instances below. -/
def targetFull : Finset pFire.CoarseTarget :=
  pFire.gLocalV1FullTargetSubset

/-- The raw-table initial reduction state at the full firing scope. -/
def initialState : pFire.GLocalV1V5State targetFull :=
  pFire.gLocalV1InitialState targetFull

/-- The empty coarse-target scope used by the unreachable-state negative
instance. -/
def emptyScope : Finset pFire.CoarseTarget := ∅

/-- The first raw coarse edge, named only to build the structural negative
state and not stored by the observation. -/
def coarseEdgeZero : pFire.CoarseEdge :=
  (0 : ResolutionInvarianceFiringWitness.coarseNerve.EdgeComponent)

/-- The first coarse chart of the actual local-fiber positive and negative
instances. -/
def coarseChartZero : pFire.CoarseChart :=
  (0 : ResolutionInvarianceFiringWitness.coarseNerve.Chart)

/-- A mapped fine edge, used as the negative local-unmapped-edge instance. -/
def fineEdgeZero : pFire.FineEdge :=
  (0 : ResolutionInvarianceFiringWitness.fineNerve.EdgeComponent)

/-- An actual unmapped fine edge in the zero coarse-chart fiber. -/
def fineEdgeThree : pFire.FineEdge :=
  (3 : ResolutionInvarianceFiringWitness.fineNerve.EdgeComponent)

/-- A mapped fine face, used as the negative local-unmapped-FaceTwin
instance. -/
def fineFaceZero : pFire.FineFace :=
  (0 : ResolutionInvarianceFiringWitness.fineNerve.FaceComponent)

/-- An actual unmapped fine face whose FaceTwin row lies in the zero local
fiber. -/
def fineFaceOne : pFire.FineFace :=
  (1 : ResolutionInvarianceFiringWitness.fineNerve.FaceComponent)

/-- A state containing one coarse edge outside the empty scope.  It is raw
negative data only and is never an observation or terminal certificate. -/
def outsideState : pFire.GLocalV1V5State emptyScope :=
  ⟨{coarseEdgeZero}, ∅, ∅, ∅⟩

/-- Positive `SubstateOf` instance: the reviewed initial state is a substate
of itself. -/
theorem initial_substateOf_self : initialState.SubstateOf initialState :=
  GLocalV1V5State.substateOf_refl _

/-- Negative `SubstateOf` instance: the edge added to the empty scope is not
contained in that scope's raw-table initial state. -/
theorem outside_not_substateOf_emptyInitial :
    ¬ outsideState.SubstateOf (pFire.gLocalV1InitialState emptyScope) := by
  intro hsubstate
  have hnot : coarseEdgeZero ∉ pFire.gLocalV1CoarseEdges emptyScope := by
    decide
  exact hnot (hsubstate.coarseEdges (by simp [outsideState]))

/-- Positive `GLocalV1Step` instance: the full firing initial state has an
actual raw-table-generated packet successor. -/
theorem exists_initial_step :
    ∃ next, pFire.GLocalV1Step targetFull initialState next := by
  have hnonempty : pFire.gLocalV1PacketVariants targetFull initialState ≠ ∅ := by
    decide
  obtain ⟨packet, hpacket⟩ := Finset.nonempty_iff_ne_empty.mpr hnonempty
  exact ⟨packet.apply initialState, packet, hpacket, rfl⟩

/-- Negative `GLocalV1Step` instance: strict retained-cell decrease forbids a
self-step at the same nontrivial initial state. -/
theorem not_initial_step_self :
    ¬ pFire.GLocalV1Step targetFull initialState initialState := by
  intro hstep
  exact (Nat.lt_irrefl initialState.measure)
    (pFire.gLocalV1_step_strict targetFull hstep)

/-- Positive `GLocalV1Reachable` instance: the canonical initial state is
reachable by the empty generated-packet path. -/
theorem initial_reachable : pFire.GLocalV1Reachable targetFull initialState :=
  Relation.ReflTransGen.refl

/-- Negative `GLocalV1Reachable` instance: every reachable state is a substate
of the empty-scope initial state, while `outsideState` contains an extra edge. -/
theorem outside_not_reachable :
    ¬ pFire.GLocalV1Reachable emptyScope outsideState := by
  intro hreach
  have hsubstate :=
    pFire.gLocalV1_reachable_substateOf_initial emptyScope outsideState hreach
  exact outside_not_substateOf_emptyInitial hsubstate

/-- Positive `GLocalV1Irreducible` instance: the complete structural terminal
enumeration supplies an actual irreducible leaf of the firing reduction. -/
theorem exists_irreducible :
    ∃ state, pFire.GLocalV1Irreducible targetFull state := by
  obtain ⟨state, hstate⟩ := pFire.gLocalV1TerminalStates_nonempty targetFull
  exact ⟨state,
    ((pFire.mem_gLocalV1TerminalStates_iff_reachable_irreducible
      targetFull state).mp hstate).2⟩

/-- Negative `GLocalV1Irreducible` instance: the full firing initial state has
one of the registered generated packets. -/
theorem initial_not_irreducible :
    ¬ pFire.GLocalV1Irreducible targetFull initialState := by
  obtain ⟨next, hstep⟩ := exists_initial_step
  exact pFire.gLocalV1_not_irreducible_of_step targetFull hstep

/-- Positive local-edge instance: fine edge three is retained, unmapped, and
has both endpoints in the zero coarse-chart fiber. -/
theorem fineEdgeThree_local :
    pFire.gLocalV1LocalFineEdge targetFull initialState
      coarseChartZero fineEdgeThree := by
  decide

/-- Negative local-edge instance: fine edge zero is mapped and therefore is
not a member of the local unmapped fiber. -/
theorem fineEdgeZero_not_local :
    ¬ pFire.gLocalV1LocalFineEdge targetFull initialState
      coarseChartZero fineEdgeZero := by
  decide

/-- Positive local-FaceTwin instance: the row generated by fine face one is
retained, unmapped, and all three boundary edges lie in the local fiber. -/
theorem fineFaceOne_local :
    pFire.gLocalV1LocalFineFaceClass targetFull initialState coarseChartZero
      (pFire.gLocalV1FineFaceKey targetFull fineFaceOne) := by
  decide

/-- Negative local-FaceTwin instance: the row generated by fine face zero is
mapped and hence is not a local unmapped FaceTwin row. -/
theorem fineFaceZero_not_local :
    ¬ pFire.gLocalV1LocalFineFaceClass targetFull initialState coarseChartZero
      (pFire.gLocalV1FineFaceKey targetFull fineFaceZero) := by
  decide

end GLocalV1KernelInstancePairs
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.GLocalV1KernelInstancePairs
