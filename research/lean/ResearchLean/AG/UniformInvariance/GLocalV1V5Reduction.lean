import ResearchLean.AG.UniformInvariance.ExecutableRationalRank
import ResearchLean.AG.UniformInvariance.FiniteComparisonPresentation
import ResearchLean.AG.UniformInvariance.GLocalV1ObservationValue
import Formal.Util.AssertStandardAxioms

/-!
# Executable permanent `G_local-v1` v5 reduction

This module transcribes the permanent v5 rewrite DAG implemented by the
registered `r2_hunt.py` structural reducer.  Every scope, FaceTwin class,
packet, reachable state, terminal, critical cell, and condition is generated
from the raw tables of a `FiniteComparisonPresentation`.  Packets store removal
sets only: validity, terminal status, condition values, and expected
observations are never supplied as fields.

The four packet families are the two v4 unit families, coordinate dependency,
and the closed doubled cycle.  Reachability is enumerated by layers.  Its fuel
is the initial retained-edge/FaceTwin count plus one, and every generated
packet strictly reduces that count.  Packet-kind union ranges over every
outgoing packet of every reachable state, not a selected terminal trace.

## Implementation notes

States retain only surviving raw cells and packets retain only removal sets;
recognizer validity, strict decrease, reachability, irreducibility, and terminal
conditions remain derived predicates.  Supplying a certified trace, a chosen
terminal, or precomputed condition bits was rejected because each would encode
part of the observation.  Executable list/finset closure is paired with
structural reachability theorems instead of using an opaque relation closure,
so later observation code computes every path while proofs retain the intrinsic
semantics.
-/

namespace AAT.AG.ResolutionInvariance

open ExecutableRationalLinearAlgebra
open scoped BigOperators

universe u

namespace FiniteComparisonPresentation

/-! ## Scoped raw tables and FaceTwin classes -/

/-- Coarse targets selected by a target subset.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseScopeTargets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseTarget := A

/-- Fine targets lying over a selected coarse-target subset.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineScopeTargets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineTarget :=
  Finset.univ.filter fun target => P.computedFactor target ∈ A

/-- Scoped support of a coarse chart.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseChartSupport (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (chart : P.CoarseChart) :
    Finset P.CoarseTarget :=
  P.coarseChartSupport chart ∩ A

/-- Scoped support of a fine chart.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineChartSupport (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (chart : P.FineChart) :
    Finset P.FineTarget :=
  P.fineChartSupport chart ∩ P.gLocalV1FineScopeTargets A

/-- Derived scoped support of a coarse edge.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseEdgeSupport (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdge) :
    Finset P.CoarseTarget :=
  P.gLocalV1CoarseChartSupport A (P.coarseEdgeLeft edge) ∩
    P.gLocalV1CoarseChartSupport A (P.coarseEdgeRight edge)

/-- Derived scoped support of a fine edge.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineEdgeSupport (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdge) :
    Finset P.FineTarget :=
  P.gLocalV1FineChartSupport A (P.fineEdgeLeft edge) ∩
    P.gLocalV1FineChartSupport A (P.fineEdgeRight edge)

/-- Derived scoped support of a coarse face.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseFaceSupport (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFace) :
    Finset P.CoarseTarget :=
  P.gLocalV1CoarseEdgeSupport A (P.coarseFaceEdge0 face) ∩
    P.gLocalV1CoarseEdgeSupport A (P.coarseFaceEdge1 face) ∩
      P.gLocalV1CoarseEdgeSupport A (P.coarseFaceEdge2 face)

/-- Derived scoped support of a fine face.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineFaceSupport (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFace) :
    Finset P.FineTarget :=
  P.gLocalV1FineEdgeSupport A (P.fineFaceEdge0 face) ∩
    P.gLocalV1FineEdgeSupport A (P.fineFaceEdge1 face) ∩
      P.gLocalV1FineEdgeSupport A (P.fineFaceEdge2 face)

/-- Scoped coarse charts.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseCharts (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseChart :=
  Finset.univ.filter fun chart => (P.gLocalV1CoarseChartSupport A chart).Nonempty

/-- Scoped fine charts.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineCharts (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineChart :=
  Finset.univ.filter fun chart => (P.gLocalV1FineChartSupport A chart).Nonempty

/-- Scoped coarse edges.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseEdge :=
  Finset.univ.filter fun edge => (P.gLocalV1CoarseEdgeSupport A edge).Nonempty

/-- Scoped fine edges.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineEdge :=
  Finset.univ.filter fun edge => (P.gLocalV1FineEdgeSupport A edge).Nonempty

/-- Scoped coarse faces.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseFaces (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseFace :=
  Finset.univ.filter fun face => (P.gLocalV1CoarseFaceSupport A face).Nonempty

/-- Scoped fine faces.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineFaces (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineFace :=
  Finset.univ.filter fun face => (P.gLocalV1FineFaceSupport A face).Nonempty

/-- A coarse FaceTwin key is exactly the ordered boundary triple together with
its scoped support.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
structure GLocalV1CoarseFaceTwinKey (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) where
  edge0 : P.CoarseEdge
  edge1 : P.CoarseEdge
  edge2 : P.CoarseEdge
  support : Finset P.CoarseTarget
  deriving DecidableEq, Fintype

/-- A fine FaceTwin key is exactly the ordered boundary triple together with
its scoped support.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
structure GLocalV1FineFaceTwinKey (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) where
  edge0 : P.FineEdge
  edge1 : P.FineEdge
  edge2 : P.FineEdge
  support : Finset P.FineTarget
  deriving DecidableEq, Fintype

/-- The coarse FaceTwin key generated by one scoped raw face.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseFaceKey (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFace) :
    P.GLocalV1CoarseFaceTwinKey A :=
  ⟨P.coarseFaceEdge0 face, P.coarseFaceEdge1 face, P.coarseFaceEdge2 face,
    P.gLocalV1CoarseFaceSupport A face⟩

/-- The fine FaceTwin key generated by one scoped raw face.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineFaceKey (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFace) :
    P.GLocalV1FineFaceTwinKey A :=
  ⟨P.fineFaceEdge0 face, P.fineFaceEdge1 face, P.fineFaceEdge2 face,
    P.gLocalV1FineFaceSupport A face⟩

/-- All coarse FaceTwin classes generated by the scoped raw face table.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseFaceClasses (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset (P.GLocalV1CoarseFaceTwinKey A) :=
  (P.gLocalV1CoarseFaces A).image (P.gLocalV1CoarseFaceKey A)

/-- All fine FaceTwin classes generated by the scoped raw face table.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineFaceClasses (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset (P.GLocalV1FineFaceTwinKey A) :=
  (P.gLocalV1FineFaces A).image (P.gLocalV1FineFaceKey A)

/-- Actual coarse members of one generated FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseFaceMembers (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (key : P.GLocalV1CoarseFaceTwinKey A) :
    Finset P.CoarseFace :=
  (P.gLocalV1CoarseFaces A).filter fun face =>
    P.gLocalV1CoarseFaceKey A face = key

/-- Actual fine members of one generated FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineFaceMembers (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (key : P.GLocalV1FineFaceTwinKey A) :
    Finset P.FineFace :=
  (P.gLocalV1FineFaces A).filter fun face => P.gLocalV1FineFaceKey A face = key

/-! ## Finite graph primitives -/

/-- One undirected reachability expansion inside a selected vertex/edge set.

Position: finite-graph expansion API used by the v5 connectivity and critical-edge
recognizers in fixed GOAL claim (v).  Vertices, edges, and endpoints are supplied
as raw finite data; no reachability trace or connectivity certificate is accepted.
-/
def gLocalV1ReachabilityStep {V E : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (vertices : Finset V) (edges : Finset E) (left right : E → V)
    (reached : Finset V) : Finset V :=
  reached ∪ vertices.filter fun vertex =>
    decide (∃ edge ∈ edges,
      (left edge ∈ reached ∧ right edge = vertex) ∨
        (right edge ∈ reached ∧ left edge = vertex))

/-- Bounded undirected reachability closure.  `Fintype.card V` expansions are
enough because each strict expansion adds a new vertex.

Position: bounded reachability API used by the v5 connectivity and critical-edge
recognizers in fixed GOAL claim (v).  It iterates the raw expansion for the finite
vertex-cardinality bound and accepts no path or closure certificate.
-/
def gLocalV1ReachabilityClosure {V E : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (vertices : Finset V) (edges : Finset E) (left right : E → V)
    (start : V) : Finset V :=
  Nat.iterate (gLocalV1ReachabilityStep vertices edges left right)
    (Fintype.card V) {start}

/-- Pairwise connectivity in a finite undirected subgraph.

Position: v5 reducer predicate for the connected-fiber tests in fixed GOAL claim
(v).  It computes pairwise reachability from the supplied finite graph and accepts
no connectivity proof or expected Boolean value.
-/
def gLocalV1Connected {V E : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (vertices : Finset V) (edges : Finset E) (left right : E → V) : Bool :=
  decide (∀ start ∈ vertices, ∀ target ∈ vertices,
    target ∈ gLocalV1ReachabilityClosure vertices edges left right start)

/-- Whether the endpoints of an edge remain connected after deleting it.  A
self-loop is critical by reflexivity, exactly as in the permanent source.

Position: v5 reducer API for the critical-edge flags in fixed GOAL claim (v).  It
deletes the selected raw edge and recomputes bounded reachability; no alternate
path or criticality certificate is supplied.
-/
def gLocalV1PathWithoutEdge {V E : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E]
    (vertices : Finset V) (edges : Finset E) (left right : E → V)
    (omitted : E) : Bool :=
  right omitted ∈
    gLocalV1ReachabilityClosure vertices (edges.erase omitted) left right
      (left omitted)

/-! ## States, packets, and retained-cell measure -/

/-- A retained-cell state of the full v5 reduction.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
structure GLocalV1V5State (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) where
  coarseEdges : Finset P.CoarseEdge
  coarseFaceClasses : Finset (P.GLocalV1CoarseFaceTwinKey A)
  fineEdges : Finset P.FineEdge
  fineFaceClasses : Finset (P.GLocalV1FineFaceTwinKey A)
  deriving DecidableEq

/-- One generated v5 packet.  Only the registered kind and removal sets are
stored; no validity, result, terminal, or observation certificate is a field.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
structure GLocalV1V5Packet (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) where
  kind : GLocalV1PacketKind
  coarseEdges : Finset P.CoarseEdge
  coarseFaceClasses : Finset (P.GLocalV1CoarseFaceTwinKey A)
  fineFaceClasses : Finset (P.GLocalV1FineFaceTwinKey A)
  finePivotEdges : Finset P.FineEdge
  residualFineEdges : Finset P.FineEdge
  deriving DecidableEq

/-- Initial state retaining every scoped edge and generated FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1InitialState (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : P.GLocalV1V5State A :=
  ⟨P.gLocalV1CoarseEdges A, P.gLocalV1CoarseFaceClasses A,
    P.gLocalV1FineEdges A, P.gLocalV1FineFaceClasses A⟩

/-- Total retained-edge/FaceTwin measure.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def GLocalV1V5State.measure {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} (state : P.GLocalV1V5State A) : Nat :=
  state.coarseEdges.card + state.coarseFaceClasses.card +
    state.fineEdges.card + state.fineFaceClasses.card

/-- Apply packet removal sets to a retained-cell state.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def GLocalV1V5Packet.apply {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} (packet : P.GLocalV1V5Packet A)
    (state : P.GLocalV1V5State A) : P.GLocalV1V5State A :=
  ⟨state.coarseEdges \ packet.coarseEdges,
    state.coarseFaceClasses \ packet.coarseFaceClasses,
    state.fineEdges \ (packet.finePivotEdges ∪ packet.residualFineEdges),
    state.fineFaceClasses \ packet.fineFaceClasses⟩

/-- Componentwise retained-cell inclusion between reduction states.  This is
the invariant that lets executable clients enumerate only subsets of the
canonical initial raw tables, rather than every inhabitant of the ambient
finite key types.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
structure GLocalV1V5State.SubstateOf {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} (left right : P.GLocalV1V5State A) : Prop where
  coarseEdges : left.coarseEdges ⊆ right.coarseEdges
  coarseFaceClasses : left.coarseFaceClasses ⊆ right.coarseFaceClasses
  fineEdges : left.fineEdges ⊆ right.fineEdges
  fineFaceClasses : left.fineFaceClasses ⊆ right.fineFaceClasses

/-- Every retained-cell state is a substate of itself.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem GLocalV1V5State.substateOf_refl {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} (state : P.GLocalV1V5State A) :
    state.SubstateOf state :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Componentwise retained-cell inclusion is transitive.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem GLocalV1V5State.SubstateOf.trans {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} {left middle right : P.GLocalV1V5State A}
    (hleft : left.SubstateOf middle) (hmiddle : middle.SubstateOf right) :
    left.SubstateOf right :=
  ⟨fun _ h => hmiddle.coarseEdges (hleft.coarseEdges h),
    fun _ h => hmiddle.coarseFaceClasses (hleft.coarseFaceClasses h),
    fun _ h => hmiddle.fineEdges (hleft.fineEdges h),
    fun _ h => hmiddle.fineFaceClasses (hleft.fineFaceClasses h)⟩

/-- Applying a packet only removes retained cells.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem GLocalV1V5Packet.apply_substateOf {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} (packet : P.GLocalV1V5Packet A)
    (state : P.GLocalV1V5State A) : (packet.apply state).SubstateOf state := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro value hvalue
  · exact (Finset.mem_sdiff.mp hvalue).1
  · exact (Finset.mem_sdiff.mp hvalue).1
  · exact (Finset.mem_sdiff.mp hvalue).1
  · exact (Finset.mem_sdiff.mp hvalue).1

/-! ## Packet-recognizer primitives -/

/-- Signed `+,-,+` coefficient of an edge in an ordered face boundary.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1SignedCoefficient {E : Type*} [DecidableEq E]
    (edge0 edge1 edge2 edge : E) : Int :=
  (if edge0 = edge then 1 else 0) - (if edge1 = edge then 1 else 0) +
    (if edge2 = edge then 1 else 0)

/-- Coarse FaceTwin classes in which an edge occurs in the ordered boundary.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseOccurrenceClasses (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (edge : P.CoarseEdge) : Finset (P.GLocalV1CoarseFaceTwinKey A) :=
  state.coarseFaceClasses.filter fun key =>
    key.edge0 = edge ∨ key.edge1 = edge ∨ key.edge2 = edge

/-- Fine FaceTwin classes in which an edge occurs in the ordered boundary.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineOccurrenceClasses (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (edge : P.FineEdge) : Finset (P.GLocalV1FineFaceTwinKey A) :=
  state.fineFaceClasses.filter fun key =>
    key.edge0 = edge ∨ key.edge1 = edge ∨ key.edge2 = edge

/-- Actual retained coarse faces.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1RetainedCoarseFaceMembers (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.CoarseFace :=
  state.coarseFaceClasses.biUnion (P.gLocalV1CoarseFaceMembers A)

/-- Actual retained fine faces.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1RetainedFineFaceMembers (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.FineFace :=
  state.fineFaceClasses.biUnion (P.gLocalV1FineFaceMembers A)

/-- Whether a fine FaceTwin class has any actual member mapping into one
selected coarse FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineClassHitsCoarseClass (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (fineKey : P.GLocalV1FineFaceTwinKey A)
    (coarseKey : P.GLocalV1CoarseFaceTwinKey A) : Bool :=
  decide (∃ fineFace ∈ P.gLocalV1FineFaceMembers A fineKey,
    ∃ coarseFace ∈ P.gLocalV1CoarseFaceMembers A coarseKey,
      P.faceMap fineFace = some coarseFace)

/-- Whether every actual member of a fine FaceTwin class maps into one coarse
FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineClassMapsIntoCoarseClass (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (fineKey : P.GLocalV1FineFaceTwinKey A)
    (coarseKey : P.GLocalV1CoarseFaceTwinKey A) : Bool :=
  decide (∀ fineFace ∈ P.gLocalV1FineFaceMembers A fineKey,
    ∃ coarseFace ∈ P.gLocalV1CoarseFaceMembers A coarseKey,
      P.faceMap fineFace = some coarseFace)

/-- Fine classes meeting a selected set of coarse classes.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1SelectedFinePreimageClasses (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseClasses : Finset (P.GLocalV1CoarseFaceTwinKey A)) :
    Finset (P.GLocalV1FineFaceTwinKey A) :=
  state.fineFaceClasses.filter fun fineKey =>
    decide (∃ coarseKey ∈ coarseClasses,
      P.gLocalV1FineClassHitsCoarseClass A fineKey coarseKey)

/-- The selected fine preimage is unambiguous exactly when every hit class
maps all actual members into a single selected coarse class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FinePreimageUnambiguous (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseClasses : Finset (P.GLocalV1CoarseFaceTwinKey A)) : Bool :=
  let preimages := P.gLocalV1SelectedFinePreimageClasses A state coarseClasses
  decide (∀ fineKey ∈ preimages, ∃ coarseKey ∈ coarseClasses,
    P.gLocalV1FineClassMapsIntoCoarseClass A fineKey coarseKey)

/-- Residual fine edges mapping into a selected coarse-edge set.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ResidualFineEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseEdges : Finset P.CoarseEdge) :
    Finset P.FineEdge :=
  state.fineEdges.filter fun edge =>
    decide (∃ coarseEdge ∈ coarseEdges, P.edgeMap edge = some coarseEdge)

/-- Residual mapped edges are removable precisely when they are face-free,
non-self-loop bridges after the provisional removals.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ResidualEdgesRemovable (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (residual : Finset P.FineEdge) : Bool :=
  decide (∀ edge ∈ residual,
    P.gLocalV1FineOccurrenceClasses A state edge = ∅ ∧
      P.fineEdgeLeft edge ≠ P.fineEdgeRight edge ∧
      gLocalV1PathWithoutEdge (P.gLocalV1FineCharts A) state.fineEdges
        P.fineEdgeLeft P.fineEdgeRight edge = false)

/-- All injective v4 pivot assignments for a fixed fine preimage.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1V4PivotAssignments (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseEdge : P.CoarseEdge)
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A)) :
    Finset ((key : {key // key ∈ preimages}) → P.FineEdge) :=
  Finset.univ.filter fun assignment =>
    decide
      ((∀ key, assignment key ∈ state.fineEdges ∧
          P.edgeMap (assignment key) = some coarseEdge ∧
          Int.natAbs (gLocalV1SignedCoefficient key.1.edge0 key.1.edge1
            key.1.edge2 (assignment key)) = 1 ∧
          P.gLocalV1FineOccurrenceClasses A state (assignment key) = {key.1}) ∧
        Function.Injective assignment)

/-- Fine pivot edges used by one v4 assignment.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1V4PivotEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A))
    (assignment : (key : {key // key ∈ preimages}) → P.FineEdge) :
    Finset P.FineEdge :=
  preimages.attach.image assignment

/-! ## The two v4 unit packet families -/

/-- All v4 coarse-unit packets generated at a state.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1V4CoarsePackets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  state.coarseFaceClasses.biUnion fun coarseKey =>
    state.coarseEdges.biUnion fun coarseEdge =>
      if _hunit : P.gLocalV1CoarseOccurrenceClasses A state coarseEdge = {coarseKey} ∧
          Int.natAbs (gLocalV1SignedCoefficient coarseKey.edge0 coarseKey.edge1
            coarseKey.edge2 coarseEdge) = 1 then
        let preimages := P.gLocalV1SelectedFinePreimageClasses A state {coarseKey}
        if _hambiguous : P.gLocalV1FinePreimageUnambiguous A state {coarseKey} = true then
          (P.gLocalV1V4PivotAssignments A state coarseEdge preimages).biUnion
            fun assignment =>
              let pivots := P.gLocalV1V4PivotEdges A preimages assignment
              let provisional : P.GLocalV1V5State A :=
                ⟨state.coarseEdges, state.coarseFaceClasses,
                  state.fineEdges \ pivots,
                  state.fineFaceClasses \ preimages⟩
              let residual := P.gLocalV1ResidualFineEdges A provisional {coarseEdge}
              if _hresidual : P.gLocalV1ResidualEdgesRemovable A provisional residual = true then
                {⟨.v4Coarse, {coarseEdge}, {coarseKey}, preimages, pivots, residual⟩}
              else ∅
        else ∅
      else ∅

/-- All v4 fine-only unit packets generated at a state.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1V4FineOnlyPackets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  state.fineFaceClasses.biUnion fun fineKey =>
    state.fineEdges.biUnion fun fineEdge =>
      if _hpacket :
          (∀ face ∈ P.gLocalV1FineFaceMembers A fineKey, P.faceMap face = none) ∧
          P.edgeMap fineEdge = none ∧
          Int.natAbs (gLocalV1SignedCoefficient fineKey.edge0 fineKey.edge1
            fineKey.edge2 fineEdge) = 1 ∧
          P.gLocalV1FineOccurrenceClasses A state fineEdge = {fineKey} then
        {⟨.v4FineOnly, ∅, ∅, {fineKey}, {fineEdge}, ∅⟩}
      else ∅

/-- All inherited v4 packet variants at a state.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1V4Packets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  P.gLocalV1V4CoarsePackets A state ∪ P.gLocalV1V4FineOnlyPackets A state

/-! ## Coordinate-dependency packets -/

/-- Retained coarse self-loops available to the two v5 global recognizers.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1RetainedCoarseSelfLoops (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.CoarseEdge :=
  state.coarseEdges.filter fun edge =>
    P.coarseEdgeLeft edge = P.coarseEdgeRight edge

/-- Coarse FaceTwin classes whose ordered boundary meets a selected edge set.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseClassesMeeting (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (edges : Finset P.CoarseEdge) :
    Finset (P.GLocalV1CoarseFaceTwinKey A) :=
  state.coarseFaceClasses.filter fun key =>
    key.edge0 ∈ edges ∨ key.edge1 ∈ edges ∨ key.edge2 ∈ edges

/-- Coordinate coarse-pivot assignments.  Every selected FaceTwin relation has
exactly one signed unit coordinate among all retained coarse edges, that
coordinate lies in the selected edge set, and the pivots cover the selected
set.  Inspecting the full retained support matches the permanent beta-support
recognizer and prevents an unselected nonzero coordinate from being hidden.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoordinateCoarseAssignments (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (selectedEdges : Finset P.CoarseEdge)
    (selectedClasses : Finset (P.GLocalV1CoarseFaceTwinKey A)) :
    Finset ((key : {key // key ∈ selectedClasses}) → P.CoarseEdge) :=
  Finset.univ.filter fun assignment =>
    decide
      ((∀ key, assignment key ∈ selectedEdges ∧
          Int.natAbs (gLocalV1SignedCoefficient key.1.edge0 key.1.edge1
            key.1.edge2 (assignment key)) = 1 ∧
          (∀ edge ∈ state.coarseEdges,
            gLocalV1SignedCoefficient key.1.edge0 key.1.edge1 key.1.edge2 edge ≠ 0 →
              edge = assignment key)) ∧
        (∀ edge ∈ selectedEdges, ∃ key, assignment key = edge))

/-- Assign every selected fine preimage class to the unique selected coarse
FaceTwin class containing all of its mapped actual members.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineClassAssignments (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (selectedClasses : Finset (P.GLocalV1CoarseFaceTwinKey A))
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A)) :
    Finset ((key : {key // key ∈ preimages}) → {key // key ∈ selectedClasses}) :=
  Finset.univ.filter fun assignment =>
    decide (∀ key,
      P.gLocalV1FineClassMapsIntoCoarseClass A key.1 (assignment key).1)

/-- Fine unit-coordinate assignments compatible with coarse coordinate pivots
and the partial edge map.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoordinateFineAssignments (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (selectedClasses : Finset (P.GLocalV1CoarseFaceTwinKey A))
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A))
    (coarseAssignment : (key : {key // key ∈ selectedClasses}) → P.CoarseEdge)
    (classAssignment : (key : {key // key ∈ preimages}) →
      {key // key ∈ selectedClasses}) :
    Finset ((key : {key // key ∈ preimages}) → P.FineEdge) :=
  Finset.univ.filter fun assignment =>
    decide (∀ key, assignment key ∈ state.fineEdges ∧
      Int.natAbs (gLocalV1SignedCoefficient key.1.edge0 key.1.edge1
        key.1.edge2 (assignment key)) = 1 ∧
      (∀ edge ∈ state.fineEdges,
        gLocalV1SignedCoefficient key.1.edge0 key.1.edge1 key.1.edge2 edge ≠ 0 →
          edge = assignment key) ∧
      P.edgeMap (assignment key) = some (coarseAssignment (classAssignment key)))

/-- The set image of a coordinate fine-pivot assignment.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoordinateFinePivots (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A))
    (assignment : (key : {key // key ∈ preimages}) → P.FineEdge) :
    Finset P.FineEdge :=
  preimages.attach.image assignment

/-- Full coordinate-dependency packet enumeration.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoordinatePackets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  (P.gLocalV1RetainedCoarseSelfLoops A state).powerset.biUnion fun selectedEdges =>
    if _hnonempty : selectedEdges.Nonempty then
      let selectedClasses := P.gLocalV1CoarseClassesMeeting A state selectedEdges
      if _hclasses : selectedClasses.Nonempty then
        (P.gLocalV1CoordinateCoarseAssignments A state selectedEdges selectedClasses).biUnion
          fun coarseAssignment =>
            let preimages :=
              P.gLocalV1SelectedFinePreimageClasses A state selectedClasses
            if _hambiguous :
                P.gLocalV1FinePreimageUnambiguous A state selectedClasses = true then
              (P.gLocalV1FineClassAssignments A selectedClasses preimages).biUnion
                fun classAssignment =>
                  (P.gLocalV1CoordinateFineAssignments A state selectedClasses preimages
                    coarseAssignment classAssignment).biUnion fun fineAssignment =>
                      let pivots :=
                        P.gLocalV1CoordinateFinePivots A preimages fineAssignment
                      let provisional : P.GLocalV1V5State A :=
                        ⟨state.coarseEdges, state.coarseFaceClasses,
                          state.fineEdges \ pivots,
                          state.fineFaceClasses \ preimages⟩
                      if _hpivots : ∀ pivot ∈ pivots,
                          P.gLocalV1FineOccurrenceClasses A provisional pivot = ∅ then
                        let residual :=
                          P.gLocalV1ResidualFineEdges A provisional selectedEdges
                        if _hresidual :
                            P.gLocalV1ResidualEdgesRemovable A provisional residual = true then
                          {⟨.coordinateDependency, selectedEdges, selectedClasses,
                            preimages, pivots, residual⟩}
                        else ∅
                      else ∅
            else ∅
      else ∅
    else ∅

/-! ## Closed doubled-cycle packets -/

/-- A selected coarse relation set is exactly one directed simple doubled
cycle: every source and target occurs once, all relations have `(u,v,u)`, and
the directed incidence graph is connected.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1IsCoarseDoubledCycle (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (selectedEdges : Finset P.CoarseEdge)
    (selectedClasses : Finset (P.GLocalV1CoarseFaceTwinKey A)) : Bool :=
  decide
    (2 ≤ selectedEdges.card ∧ selectedClasses.card = selectedEdges.card ∧
      (∀ key ∈ selectedClasses,
        key.edge0 = key.edge2 ∧ key.edge0 ∈ selectedEdges ∧
          key.edge1 ∈ selectedEdges ∧ key.edge0 ≠ key.edge1) ∧
      (∀ edge ∈ selectedEdges,
        (selectedClasses.filter fun key => key.edge0 = edge).card = 1) ∧
      (∀ edge ∈ selectedEdges,
        (selectedClasses.filter fun key => key.edge1 = edge).card = 1) ∧
      gLocalV1Connected selectedEdges selectedClasses
        (fun key => key.edge0) (fun key => key.edge1) = true)

/-- Fine sheet edges used by a family of doubled preimage classes.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1DoubledSheetEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A)) : Finset P.FineEdge :=
  preimages.biUnion fun key => {key.edge0, key.edge1}

/-- Validate the fine disjoint union of directed covering cycles above a
selected coarse doubled cycle.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1IsFineDoubledCover (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (selectedClasses : Finset (P.GLocalV1CoarseFaceTwinKey A))
    (preimages : Finset (P.GLocalV1FineFaceTwinKey A))
    (classAssignment : (key : {key // key ∈ preimages}) →
      {key // key ∈ selectedClasses}) : Bool :=
  let sheetEdges := P.gLocalV1DoubledSheetEdges A preimages
  decide
    ((∀ key,
        key.1.edge0 = key.1.edge2 ∧ key.1.edge0 ≠ key.1.edge1 ∧
          P.fineEdgeLeft key.1.edge0 = P.fineEdgeRight key.1.edge0 ∧
          P.fineEdgeLeft key.1.edge1 = P.fineEdgeRight key.1.edge1 ∧
          P.edgeMap key.1.edge0 = some (classAssignment key).1.edge0 ∧
          P.edgeMap key.1.edge1 = some (classAssignment key).1.edge1) ∧
      (∀ edge ∈ sheetEdges,
        (preimages.filter fun key => key.edge0 = edge).card = 1) ∧
      (∀ edge ∈ sheetEdges,
        (preimages.filter fun key => key.edge1 = edge).card = 1) ∧
      sheetEdges ⊆ state.fineEdges)

/-- Full closed-doubled-cycle packet enumeration.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1DoubledCyclePackets (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  (P.gLocalV1RetainedCoarseSelfLoops A state).powerset.biUnion fun selectedEdges =>
    let selectedClasses := P.gLocalV1CoarseClassesMeeting A state selectedEdges
    if _hcycle : P.gLocalV1IsCoarseDoubledCycle A selectedEdges selectedClasses = true then
      let preimages := P.gLocalV1SelectedFinePreimageClasses A state selectedClasses
      if _hambiguous :
          P.gLocalV1FinePreimageUnambiguous A state selectedClasses = true then
        (P.gLocalV1FineClassAssignments A selectedClasses preimages).biUnion
          fun classAssignment =>
            if _hcover :
                P.gLocalV1IsFineDoubledCover A state selectedClasses preimages classAssignment = true then
              let sheetEdges := P.gLocalV1DoubledSheetEdges A preimages
              let provisional : P.GLocalV1V5State A :=
                ⟨state.coarseEdges, state.coarseFaceClasses,
                  state.fineEdges \ sheetEdges,
                  state.fineFaceClasses \ preimages⟩
              if _hsheets : ∀ edge ∈ sheetEdges,
                  P.gLocalV1FineOccurrenceClasses A provisional edge = ∅ then
                let residual :=
                  P.gLocalV1ResidualFineEdges A provisional selectedEdges
                if _hresidual :
                    P.gLocalV1ResidualEdgesRemovable A provisional residual = true then
                  {⟨.closedDoubledCycle, selectedEdges, selectedClasses,
                    preimages, sheetEdges, residual⟩}
                else ∅
              else ∅
            else ∅
      else ∅
    else ∅

/-- All four raw permanent packet families generated at one state, before the
strict-decrease guard is applied.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1RawPacketVariants (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  P.gLocalV1V4Packets A state ∪ P.gLocalV1CoordinatePackets A state ∪
    P.gLocalV1DoubledCyclePackets A state

/-- All permanent packet variants.  The guard is computed from the removal
sets and makes strict decrease an executable invariant rather than a supplied
certificate.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1PacketVariants (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5Packet A) :=
  (P.gLocalV1RawPacketVariants A state).filter fun packet =>
    (packet.apply state).measure < state.measure

/-- Every generated v5 packet strictly decreases the retained-cell measure.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_packet_strict (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (packet : P.GLocalV1V5Packet A)
    (hpacket : packet ∈ P.gLocalV1PacketVariants A state) :
    (packet.apply state).measure < state.measure := by
  exact (Finset.mem_filter.mp hpacket).2

/-- One generated reduction transition.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def GLocalV1Step (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (left right : P.GLocalV1V5State A) : Prop :=
  ∃ packet ∈ P.gLocalV1PacketVariants A left, packet.apply left = right

/-- The transition relation is decidable by finite packet search.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
instance gLocalV1StepDecidable (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : DecidableRel (P.GLocalV1Step A) := by
  intro left right
  unfold GLocalV1Step
  infer_instance

/-- Every reduction transition strictly decreases retained-cell measure.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_step_strict (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {left right : P.GLocalV1V5State A}
    (hstep : P.GLocalV1Step A left right) : right.measure < left.measure := by
  obtain ⟨packet, hpacket, rfl⟩ := hstep
  exact P.gLocalV1_packet_strict A left packet hpacket

/-- Every generated reduction step only removes retained cells.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_step_substateOf (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {left right : P.GLocalV1V5State A}
    (hstep : P.GLocalV1Step A left right) : right.SubstateOf left := by
  obtain ⟨packet, _hpacket, rfl⟩ := hstep
  exact packet.apply_substateOf left

/-! ## Complete well-founded DAG enumeration -/

/-- All states reachable from one state.  The recursive call visits every
outgoing packet, and terminates solely by `gLocalV1_packet_strict`; there is no
externally chosen depth bound or selected trace.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ReachableFrom (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5State A) :=
  {state} ∪ (P.gLocalV1PacketVariants A state).attach.biUnion fun packet =>
    P.gLocalV1ReachableFrom A (packet.1.apply state)
termination_by state.measure
decreasing_by
  exact P.gLocalV1_packet_strict A state packet.1 packet.2

/-- Complete reachable-state set from the canonical initial state.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ReachableStates (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset (P.GLocalV1V5State A) :=
  P.gLocalV1ReachableFrom A (P.gLocalV1InitialState A)

/-- Intrinsic reachability is the reflexive-transitive closure of generated
packet transitions.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def GLocalV1Reachable (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Prop :=
  Relation.ReflTransGen (P.GLocalV1Step A) (P.gLocalV1InitialState A) state

/-- Irreducibility means that no registered packet remains.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def GLocalV1Irreducible (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Prop :=
  P.gLocalV1PacketVariants A state = ∅

/-- A generated reduction step refutes irreducibility of its source state.
This is the public elimination API for `GLocalV1Irreducible`; downstream
fixtures need not expose the packet-enumeration definition.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_not_irreducible_of_step (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {state next : P.GLocalV1V5State A}
    (hstep : P.GLocalV1Step A state next) :
    ¬ P.GLocalV1Irreducible A state := by
  intro hIrreducible
  change P.gLocalV1PacketVariants A state = ∅ at hIrreducible
  obtain ⟨packet, hpacket, _⟩ := hstep
  rw [hIrreducible] at hpacket
  simp at hpacket

/-- All irreducible leaves reached by the full reduction DAG.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1TerminalFrom (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset (P.GLocalV1V5State A) :=
  if _hterminal : P.gLocalV1PacketVariants A state = ∅ then
    {state}
  else
    (P.gLocalV1PacketVariants A state).attach.biUnion fun packet =>
      P.gLocalV1TerminalFrom A (packet.1.apply state)
termination_by state.measure
decreasing_by
  exact P.gLocalV1_packet_strict A state packet.1 packet.2

/-- All distinct irreducible terminals of the canonical initial state.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1TerminalStates (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset (P.GLocalV1V5State A) :=
  P.gLocalV1TerminalFrom A (P.gLocalV1InitialState A)

/-- The initial retained-cell measure plus one is an explicit upper bound on
the number of states in every strict reduction trace.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ReachabilityFuel (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Nat :=
  (P.gLocalV1InitialState A).measure + 1

/-! ## Reachability and terminal completeness -/

/-- Every state belongs to its own recursively enumerated reachable set.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_self_mem_reachableFrom (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    state ∈ P.gLocalV1ReachableFrom A state := by
  rw [gLocalV1ReachableFrom]
  simp

/-- A successor's reachable set is included in its predecessor's reachable
set.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_reachableFrom_step_subset (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {left right : P.GLocalV1V5State A}
    (hstep : P.GLocalV1Step A left right) :
    P.gLocalV1ReachableFrom A right ⊆ P.gLocalV1ReachableFrom A left := by
  obtain ⟨packet, hpacket, rfl⟩ := hstep
  rw (occs := .pos [2]) [gLocalV1ReachableFrom]
  intro target htarget
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨packet, hpacket⟩, by simp, htarget⟩

/-- Reachability closure reverses to inclusion of recursive reachable sets.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_reachableFrom_mono (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {left right : P.GLocalV1V5State A}
    (hreach : Relation.ReflTransGen (P.GLocalV1Step A) left right) :
    P.gLocalV1ReachableFrom A right ⊆ P.gLocalV1ReachableFrom A left := by
  induction hreach with
  | refl => exact fun _ h => h
  | tail _ hstep ih =>
      exact fun target htarget =>
        ih (P.gLocalV1_reachableFrom_step_subset A hstep htarget)

/-- Recursive enumeration contains only states reached by generated packet
transitions.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_mem_reachableFrom_implies (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (left right : P.GLocalV1V5State A)
    (hmem : right ∈ P.gLocalV1ReachableFrom A left) :
    Relation.ReflTransGen (P.GLocalV1Step A) left right := by
  induction left using (measure GLocalV1V5State.measure).wf.induction generalizing right with
  | h left ih =>
      rw [gLocalV1ReachableFrom] at hmem
      rcases Finset.mem_union.mp hmem with hroot | hdescendant
      · exact Finset.mem_singleton.mp hroot ▸ Relation.ReflTransGen.refl
      · obtain ⟨packet, hpacketAttached, hright⟩ :=
          Finset.mem_biUnion.mp hdescendant
        have hpacket : packet.1 ∈ P.gLocalV1PacketVariants A left := packet.2
        have htail := ih (packet.1.apply left)
          (P.gLocalV1_packet_strict A left packet.1 hpacket) right hright
        exact Relation.ReflTransGen.head ⟨packet.1, hpacket, rfl⟩ htail

/-- The complete recursive reachable set is exactly reflexive-transitive
packet reachability.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem mem_gLocalV1ReachableStates_iff (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    state ∈ P.gLocalV1ReachableStates A ↔ P.GLocalV1Reachable A state := by
  constructor
  · exact P.gLocalV1_mem_reachableFrom_implies A _ state
  · intro hreach
    exact P.gLocalV1_reachableFrom_mono A hreach
      (P.gLocalV1_self_mem_reachableFrom A state)

/-! ## Memoized bounded reachability -/

/-- One breadth expansion of a finite state set.  Unlike the structural
well-founded recursion, this union visits a state at most once per measure
layer and therefore implements the memoization discipline of the permanent
v5 source.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ReachabilityExpansion (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (states : Finset (P.GLocalV1V5State A)) :
    Finset (P.GLocalV1V5State A) :=
  states ∪ states.biUnion fun state =>
    (P.gLocalV1PacketVariants A state).image fun packet => packet.apply state

/-- One breadth expansion retains every previously reached state.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1ReachabilityExpansion_self_subset
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (states : Finset (P.GLocalV1V5State A)) :
    states ⊆ P.gLocalV1ReachabilityExpansion A states := by
  intro state hstate
  exact Finset.mem_union_left _ hstate

/-- Breadth expansion is monotone in its finite state set.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1ReachabilityExpansion_mono
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    {left right : Finset (P.GLocalV1V5State A)} (hsubset : left ⊆ right) :
    P.gLocalV1ReachabilityExpansion A left ⊆
      P.gLocalV1ReachabilityExpansion A right := by
  intro state hstate
  rcases Finset.mem_union.mp hstate with hold | hnew
  · exact Finset.mem_union_left _ (hsubset hold)
  · obtain ⟨source, hsource, himage⟩ := Finset.mem_biUnion.mp hnew
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨source, hsubset hsource, himage⟩

/-- Iterated breadth expansion is monotone in its seed set.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1ReachabilityExpansion_iterate_mono
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (steps : Nat) {left right : Finset (P.GLocalV1V5State A)}
    (hsubset : left ⊆ right) :
    (P.gLocalV1ReachabilityExpansion A)^[steps] left ⊆
      (P.gLocalV1ReachabilityExpansion A)^[steps] right := by
  induction steps generalizing left right with
  | zero => exact hsubset
  | succ steps ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (P.gLocalV1ReachabilityExpansion_mono A hsubset)

/-- Increasing the breadth-iteration count preserves all reached states.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1ReachabilityExpansion_iterate_subset_succ
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (steps : Nat) (states : Finset (P.GLocalV1V5State A)) :
    (P.gLocalV1ReachabilityExpansion A)^[steps] states ⊆
      (P.gLocalV1ReachabilityExpansion A)^[steps + 1] states := by
  rw [show steps + 1 = steps.succ by omega, Function.iterate_succ_apply]
  exact P.gLocalV1ReachabilityExpansion_iterate_mono A steps
    (P.gLocalV1ReachabilityExpansion_self_subset A states)

/-- Membership after fewer breadth iterations persists after any larger
iteration count.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_mem_iterate_of_le (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (states : Finset (P.GLocalV1V5State A))
    {small large : Nat} (hle : small ≤ large)
    {state : P.GLocalV1V5State A}
    (hstate : state ∈ (P.gLocalV1ReachabilityExpansion A)^[small] states) :
    state ∈ (P.gLocalV1ReachabilityExpansion A)^[large] states := by
  induction large, hle using Nat.le_induction with
  | base => exact hstate
  | succ large _ ih =>
      exact P.gLocalV1ReachabilityExpansion_iterate_subset_succ A large states ih

/-- A generated successor is present after one breadth expansion.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_mem_expansion_of_step (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (states : Finset (P.GLocalV1V5State A))
    {left right : P.GLocalV1V5State A} (hleft : left ∈ states)
    (hstep : P.GLocalV1Step A left right) :
    right ∈ P.gLocalV1ReachabilityExpansion A states := by
  obtain ⟨packet, hpacket, rfl⟩ := hstep
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨left, hleft, Finset.mem_image.mpr ⟨packet, hpacket, rfl⟩⟩

/-- Iterated breadth expansion contains only intrinsically reachable states,
provided every seed state is reachable.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_iterate_reachable
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (start : P.GLocalV1V5State A) (steps : Nat)
    (states : Finset (P.GLocalV1V5State A))
    (hstates : ∀ state ∈ states,
      Relation.ReflTransGen (P.GLocalV1Step A) start state) :
    ∀ state ∈ (P.gLocalV1ReachabilityExpansion A)^[steps] states,
      Relation.ReflTransGen (P.GLocalV1Step A) start state := by
  induction steps generalizing states with
  | zero => simpa using hstates
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      apply ih
      intro state hstate
      rcases Finset.mem_union.mp hstate with hold | hnew
      · exact hstates state hold
      · obtain ⟨source, hsource, himage⟩ := Finset.mem_biUnion.mp hnew
        obtain ⟨packet, hpacket, rfl⟩ := Finset.mem_image.mp himage
        exact (hstates source hsource).tail ⟨packet, hpacket, rfl⟩

/-- The structural well-founded reachable set is contained in the bounded
memoized breadth expansion.  The bound is the retained-cell measure plus one,
because every generated step strictly decreases that measure.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_mem_reachableFrom_implies_mem_iterate
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (left right : P.GLocalV1V5State A)
    (hmem : right ∈ P.gLocalV1ReachableFrom A left) :
    right ∈ (P.gLocalV1ReachabilityExpansion A)^[left.measure + 1] {left} := by
  induction left using (measure GLocalV1V5State.measure).wf.induction
      generalizing right with
  | h left ih =>
      rw [gLocalV1ReachableFrom] at hmem
      rcases Finset.mem_union.mp hmem with hroot | hdescendant
      · have hzero : right ∈
            (P.gLocalV1ReachabilityExpansion A)^[0] {left} := by
          simp [Finset.mem_singleton.mp hroot]
        exact P.gLocalV1_mem_iterate_of_le A {left} (Nat.zero_le _) hzero
      · obtain ⟨packet, hpacketAttached, hright⟩ :=
          Finset.mem_biUnion.mp hdescendant
        have hpacket : packet.1 ∈ P.gLocalV1PacketVariants A left := packet.2
        have hnext := ih (packet.1.apply left)
          (P.gLocalV1_packet_strict A left packet.1 hpacket) right hright
        have hsingleton : ({packet.1.apply left} :
            Finset (P.GLocalV1V5State A)) ⊆
              P.gLocalV1ReachabilityExpansion A {left} := by
          intro state hstate
          have heq : state = packet.1.apply left := Finset.mem_singleton.mp hstate
          subst state
          exact P.gLocalV1_mem_expansion_of_step A {left} (by simp)
            ⟨packet.1, hpacket, rfl⟩
        have hlifted := P.gLocalV1ReachabilityExpansion_iterate_mono A
          (packet.1.apply left).measure.succ hsingleton hnext
        rw [← Function.iterate_succ_apply] at hlifted
        have hmeasure := P.gLocalV1_packet_strict A left packet.1 hpacket
        have hsteps : (packet.1.apply left).measure.succ.succ ≤ left.measure.succ :=
          Nat.succ_le_succ hmeasure
        exact P.gLocalV1_mem_iterate_of_le A {left} hsteps hlifted

/-- Memoized complete reachable-state set.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1MemoizedReachableStates (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset (P.GLocalV1V5State A) :=
  (P.gLocalV1ReachabilityExpansion A)^[P.gLocalV1ReachabilityFuel A]
    {P.gLocalV1InitialState A}

/-- Memoized bounded reachability is exactly intrinsic packet reachability.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem mem_gLocalV1MemoizedReachableStates_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) :
    state ∈ P.gLocalV1MemoizedReachableStates A ↔
      P.GLocalV1Reachable A state := by
  constructor
  · intro hstate
    exact P.gLocalV1_iterate_reachable A (P.gLocalV1InitialState A)
      (P.gLocalV1ReachabilityFuel A) {P.gLocalV1InitialState A}
      (by
        intro seed hseed
        have heq : seed = P.gLocalV1InitialState A := Finset.mem_singleton.mp hseed
        subst seed
        exact Relation.ReflTransGen.refl) state hstate
  · intro hreach
    exact P.gLocalV1_mem_reachableFrom_implies_mem_iterate A _ state
      ((P.mem_gLocalV1ReachableStates_iff A state).mpr hreach)

/-- Memoized executable terminal-state set.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1MemoizedTerminalStates (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset (P.GLocalV1V5State A) :=
  (P.gLocalV1MemoizedReachableStates A).filter fun state =>
    P.gLocalV1PacketVariants A state = ∅

/-- Memoized terminal membership is exactly reachable irreducibility.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem mem_gLocalV1MemoizedTerminalStates_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) :
    state ∈ P.gLocalV1MemoizedTerminalStates A ↔
      P.GLocalV1Reachable A state ∧ P.GLocalV1Irreducible A state := by
  simp [gLocalV1MemoizedTerminalStates,
    P.mem_gLocalV1MemoizedReachableStates_iff, GLocalV1Irreducible]

/-- Every reachable state is componentwise contained in the canonical initial
raw-table state.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_reachable_substateOf_initial
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (hreach : P.GLocalV1Reachable A state) :
    state.SubstateOf (P.gLocalV1InitialState A) := by
  induction hreach with
  | refl => exact GLocalV1V5State.substateOf_refl _
  | tail _ hstep ih =>
      exact (P.gLocalV1_step_substateOf A hstep).trans ih

/-- An irreducible state is the unique leaf of its own terminal recursion.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_self_mem_terminalFrom_of_irreducible
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (hirreducible : P.GLocalV1Irreducible A state) :
    state ∈ P.gLocalV1TerminalFrom A state := by
  rw [gLocalV1TerminalFrom]
  simp [GLocalV1Irreducible] at hirreducible
  simp [hirreducible]

/-- A successor's terminal leaves are leaves of its predecessor.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_terminalFrom_step_subset (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {left right : P.GLocalV1V5State A}
    (hstep : P.GLocalV1Step A left right) :
    P.gLocalV1TerminalFrom A right ⊆ P.gLocalV1TerminalFrom A left := by
  obtain ⟨packet, hpacket, rfl⟩ := hstep
  have hnonempty : P.gLocalV1PacketVariants A left ≠ ∅ := by
    exact Finset.ne_empty_of_mem hpacket
  rw (occs := .pos [2]) [gLocalV1TerminalFrom]
  simp only [dif_neg hnonempty]
  intro target htarget
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨packet, hpacket⟩, by simp, htarget⟩

/-- Reachability closure reverses to inclusion of terminal-leaf sets.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_terminalFrom_mono (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) {left right : P.GLocalV1V5State A}
    (hreach : Relation.ReflTransGen (P.GLocalV1Step A) left right) :
    P.gLocalV1TerminalFrom A right ⊆ P.gLocalV1TerminalFrom A left := by
  induction hreach with
  | refl => exact fun _ h => h
  | tail _ hstep ih =>
      exact fun target htarget =>
        ih (P.gLocalV1_terminalFrom_step_subset A hstep htarget)

/-- Every recursively generated terminal is intrinsically irreducible.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_mem_terminalFrom_irreducible
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (left right : P.GLocalV1V5State A)
    (hmem : right ∈ P.gLocalV1TerminalFrom A left) :
    P.GLocalV1Irreducible A right := by
  induction left using (measure GLocalV1V5State.measure).wf.induction generalizing right with
  | h left ih =>
      rw [gLocalV1TerminalFrom] at hmem
      split at hmem
      next hterminal =>
        have hright : right = left := Finset.mem_singleton.mp hmem
        simpa [GLocalV1Irreducible, hright] using hterminal
      next hnonterminal =>
        obtain ⟨packet, _hpacketAttached, hright⟩ :=
          Finset.mem_biUnion.mp hmem
        exact ih (packet.1.apply left)
          (P.gLocalV1_packet_strict A left packet.1 packet.2) right hright

/-- Every recursively generated terminal is reached by generated packets.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_mem_terminalFrom_reachable
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (left right : P.GLocalV1V5State A)
    (hmem : right ∈ P.gLocalV1TerminalFrom A left) :
    Relation.ReflTransGen (P.GLocalV1Step A) left right := by
  induction left using (measure GLocalV1V5State.measure).wf.induction generalizing right with
  | h left ih =>
      rw [gLocalV1TerminalFrom] at hmem
      split at hmem
      next _ =>
        exact Finset.mem_singleton.mp hmem ▸ Relation.ReflTransGen.refl
      next _ =>
        obtain ⟨packet, _hpacketAttached, hright⟩ :=
          Finset.mem_biUnion.mp hmem
        have htail := ih (packet.1.apply left)
          (P.gLocalV1_packet_strict A left packet.1 packet.2) right hright
        exact Relation.ReflTransGen.head ⟨packet.1, packet.2, rfl⟩ htail

/-- Terminal membership is exactly reachable irreducibility.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem mem_gLocalV1TerminalStates_iff_reachable_irreducible
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) :
    state ∈ P.gLocalV1TerminalStates A ↔
      P.GLocalV1Reachable A state ∧ P.GLocalV1Irreducible A state := by
  constructor
  · intro hmem
    exact ⟨P.gLocalV1_mem_terminalFrom_reachable A _ state hmem,
      P.gLocalV1_mem_terminalFrom_irreducible A _ state hmem⟩
  · rintro ⟨hreach, hirreducible⟩
    exact P.gLocalV1_terminalFrom_mono A hreach
      (P.gLocalV1_self_mem_terminalFrom_of_irreducible A state hirreducible)

/-- Every terminal state is componentwise contained in the canonical initial
raw-table state.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1_terminal_substateOf_initial
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A)
    (hterminal : state ∈ P.gLocalV1TerminalStates A) :
    state.SubstateOf (P.gLocalV1InitialState A) :=
  P.gLocalV1_reachable_substateOf_initial A state
    ((P.mem_gLocalV1TerminalStates_iff_reachable_irreducible A state).mp
      hterminal).1

/-- The memoized terminal set equals the structural well-founded terminal
set, so executable observation and proof-level terminal semantics coincide.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1MemoizedTerminalStates_eq_terminalStates
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    P.gLocalV1MemoizedTerminalStates A = P.gLocalV1TerminalStates A := by
  ext state
  rw [P.mem_gLocalV1MemoizedTerminalStates_iff,
    P.mem_gLocalV1TerminalStates_iff_reachable_irreducible]

/-- Termination API for the raw v5 reducer: strict retained-cell decrease makes
the recursively generated terminal set nonempty from every state.  The premise
comes only from the computed packet recognizers, not a supplied terminal or
trace certificate.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1TerminalFrom_nonempty (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    (P.gLocalV1TerminalFrom A state).Nonempty := by
  induction state using (measure GLocalV1V5State.measure).wf.induction with
  | h state ih =>
      rw [gLocalV1TerminalFrom]
      split
      next _ => simp
      next hnonterminal =>
        have hpackets : (P.gLocalV1PacketVariants A state).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hnonterminal
        obtain ⟨packet, hpacket⟩ := hpackets
        obtain ⟨terminal, hterminal⟩ :=
          ih (packet.apply state) (P.gLocalV1_packet_strict A state packet hpacket)
        refine ⟨terminal, Finset.mem_biUnion.mpr ?_⟩
        exact ⟨⟨packet, hpacket⟩, by simp, hterminal⟩

/-- The full v5 reduction always produces at least one irreducible terminal.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1TerminalStates_nonempty (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.gLocalV1TerminalStates A).Nonempty :=
  P.gLocalV1TerminalFrom_nonempty A (P.gLocalV1InitialState A)

/-! ## All-path packet-kind union -/

/-- Executable all-path packet summary used by the permanent scope record.  It
collects kinds from every computed outgoing packet of every memoized reachable
state; a selected reduction trace is deliberately not an input.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1PacketKindFinset (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset GLocalV1PacketKind :=
  (P.gLocalV1MemoizedReachableStates A).biUnion fun state =>
    (P.gLocalV1PacketVariants A state).image GLocalV1V5Packet.kind

/-- Canonical-list API for the all-path packet-kind summary.  The closed
four-kind registry fixes output order without adding a packet certificate.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1PacketKindUnion (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List GLocalV1PacketKind :=
  [.v4Coarse, .v4FineOnly, .coordinateDependency, .closedDoubledCycle].filter
    fun kind => kind ∈ P.gLocalV1PacketKindFinset A

/-- A packet kind occurs exactly when an outgoing packet of that kind exists at
some reachable state.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem mem_gLocalV1PacketKindUnion_iff_reachable_packet
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (kind : GLocalV1PacketKind) :
    kind ∈ P.gLocalV1PacketKindUnion A ↔
      ∃ state ∈ P.gLocalV1MemoizedReachableStates A,
        ∃ packet ∈ P.gLocalV1PacketVariants A state, packet.kind = kind := by
  have hregistry :
      kind ∈ P.gLocalV1PacketKindUnion A ↔ kind ∈ P.gLocalV1PacketKindFinset A := by
    cases kind <;> simp [gLocalV1PacketKindUnion]
  rw [hregistry]
  simp [gLocalV1PacketKindFinset]

/-! ## Terminal critical cells and registered flags -/

/-- Coarse retained edges lying on a cycle, with self-loops included.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseCriticalEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.CoarseEdge :=
  state.coarseEdges.filter fun edge =>
    gLocalV1PathWithoutEdge (P.gLocalV1CoarseCharts A) state.coarseEdges
      P.coarseEdgeLeft P.coarseEdgeRight edge

/-- Fine retained edges lying on a cycle, with self-loops included.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineCriticalEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.FineEdge :=
  state.fineEdges.filter fun edge =>
    gLocalV1PathWithoutEdge (P.gLocalV1FineCharts A) state.fineEdges
      P.fineEdgeLeft P.fineEdgeRight edge

/-- Endpoint vertices of a coarse edge family.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseEdgeVertices (P : FiniteComparisonPresentation)
    (edges : Finset P.CoarseEdge) : Finset P.CoarseChart :=
  edges.biUnion fun edge => {P.coarseEdgeLeft edge, P.coarseEdgeRight edge}

/-- Endpoint vertices of a fine edge family.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineEdgeVertices (P : FiniteComparisonPresentation)
    (edges : Finset P.FineEdge) : Finset P.FineChart :=
  edges.biUnion fun edge => {P.fineEdgeLeft edge, P.fineEdgeRight edge}

/-- Coarse critical vertices are endpoints of critical edges and of every
boundary edge in each retained FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseCriticalVertices (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.CoarseChart :=
  P.gLocalV1CoarseEdgeVertices (P.gLocalV1CoarseCriticalEdges A state) ∪
    state.coarseFaceClasses.biUnion fun key =>
      P.gLocalV1CoarseEdgeVertices {key.edge0, key.edge1, key.edge2}

/-- Fine critical vertices are endpoints of critical edges and of every
boundary edge in each retained FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineCriticalVertices (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.FineChart :=
  P.gLocalV1FineEdgeVertices (P.gLocalV1FineCriticalEdges A state) ∪
    state.fineFaceClasses.biUnion fun key =>
      P.gLocalV1FineEdgeVertices {key.edge0, key.edge1, key.edge2}

/-- Whether a retained fine FaceTwin class maps into retained coarse faces.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineClassMapsToRetainedFace (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (key : P.GLocalV1FineFaceTwinKey A) : Bool :=
  decide (∃ fineFace ∈ P.gLocalV1FineFaceMembers A key,
    ∃ coarseFace ∈ P.gLocalV1RetainedCoarseFaceMembers A state,
      P.faceMap fineFace = some coarseFace)

/-- Fine vertices active for C0/C1: endpoints of retained edges mapping to a
coarse critical edge, together with endpoints of retained faces mapping to a
retained coarse face.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ActiveFineVertices (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.FineChart :=
  P.gLocalV1FineEdgeVertices
      (state.fineEdges.filter fun fineEdge =>
        decide (∃ coarseEdge ∈ P.gLocalV1CoarseCriticalEdges A state,
          P.edgeMap fineEdge = some coarseEdge)) ∪
    (state.fineFaceClasses.filter fun key =>
      P.gLocalV1FineClassMapsToRetainedFace A state key).biUnion fun key =>
        P.gLocalV1FineEdgeVertices {key.edge0, key.edge1, key.edge2}

/-- Active fine ports over one coarse vertex.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1Ports (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) : Finset P.FineChart :=
  (P.gLocalV1ActiveFineVertices A state).filter fun fineChart =>
    P.chartMap fineChart = coarseChart

/-- Coarse non-self-loop bridges retained at a terminal.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CoarseBridges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.CoarseEdge :=
  state.coarseEdges.filter fun edge =>
    P.coarseEdgeLeft edge ≠ P.coarseEdgeRight edge ∧
      gLocalV1PathWithoutEdge (P.gLocalV1CoarseCharts A) state.coarseEdges
        P.coarseEdgeLeft P.coarseEdgeRight edge = false

/-- Fine non-self-loop bridges retained at a terminal.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineBridges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.FineEdge :=
  state.fineEdges.filter fun edge =>
    P.fineEdgeLeft edge ≠ P.fineEdgeRight edge ∧
      gLocalV1PathWithoutEdge (P.gLocalV1FineCharts A) state.fineEdges
        P.fineEdgeLeft P.fineEdgeRight edge = false

/-- Compatibility alias for the permanent bridge flag on the fine side.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1Bridges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.FineEdge :=
  P.gLocalV1FineBridges A state

/-- Guarded coarse edges are coarse critical edges together with images of fine
critical edges.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1GuardedCoarseEdges (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    Finset P.CoarseEdge :=
  P.gLocalV1CoarseCriticalEdges A state ∪
    (P.gLocalV1FineCriticalEdges A state).biUnion fun edge =>
      match P.edgeMap edge with
      | none => ∅
      | some coarseEdge => {coarseEdge}

/-! ## Certified SLOT/KILL swap relation -/

/-- Whether two edges form the unordered pair selected in one boundary slot.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1BoundarySlotPair {E : Type u} [DecidableEq E]
    (leftBoundary rightBoundary : E × E × E) (left right : E) : Bool :=
  let pairMatches (a b : E) := ({a, b} : Finset E) = {left, right}
  decide
    ((leftBoundary.1 ≠ rightBoundary.1 ∧
        leftBoundary.2.1 = rightBoundary.2.1 ∧
        leftBoundary.2.2 = rightBoundary.2.2 ∧
        pairMatches leftBoundary.1 rightBoundary.1) ∨
      (leftBoundary.1 = rightBoundary.1 ∧
        leftBoundary.2.1 ≠ rightBoundary.2.1 ∧
        leftBoundary.2.2 = rightBoundary.2.2 ∧
        pairMatches leftBoundary.2.1 rightBoundary.2.1) ∨
      (leftBoundary.1 = rightBoundary.1 ∧
        leftBoundary.2.1 = rightBoundary.2.1 ∧
        leftBoundary.2.2 ≠ rightBoundary.2.2 ∧
        pairMatches leftBoundary.2.2 rightBoundary.2.2))

/-- The registered SLOT certificate for a direct LiftTwin relation.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1SlotCertified (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (left right : P.FineEdge) : Bool :=
  let retainedFineFaces := P.gLocalV1RetainedFineFaceMembers A state
  decide (∃ leftFace ∈ retainedFineFaces, ∃ rightFace ∈ retainedFineFaces,
    P.gLocalV1FineFaceSupport A leftFace = P.gLocalV1FineFaceSupport A rightFace ∧
      (∃ coarseKey ∈ state.coarseFaceClasses,
        ∃ mappedLeft ∈ P.gLocalV1CoarseFaceMembers A coarseKey,
        ∃ mappedRight ∈ P.gLocalV1CoarseFaceMembers A coarseKey,
          P.faceMap leftFace = some mappedLeft ∧
          P.faceMap rightFace = some mappedRight) ∧
      gLocalV1BoundarySlotPair
        (P.fineFaceEdge0 leftFace, P.fineFaceEdge1 leftFace,
          P.fineFaceEdge2 leftFace)
        (P.fineFaceEdge0 rightFace, P.fineFaceEdge1 rightFace,
          P.fineFaceEdge2 rightFace) left right = true)

/-- The registered KILL certificate for a direct LiftTwin relation.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1KillCertified (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseEdge : P.CoarseEdge) (left right : P.FineEdge) : Bool :=
  let retainedFineFaces := P.gLocalV1RetainedFineFaceMembers A state
  let retainedCoarseFaces := P.gLocalV1RetainedCoarseFaceMembers A state
  decide ((retainedFineFaces.filter fun relationFace =>
    let z := P.fineFaceEdge2 relationFace
    let orientation :=
      (P.fineFaceEdge0 relationFace = left ∧
        P.fineFaceEdge1 relationFace = right) ∨
      (P.fineFaceEdge0 relationFace = right ∧
        P.fineFaceEdge1 relationFace = left)
    orientation ∧
      P.gLocalV1FineEdgeSupport A left = P.gLocalV1FineEdgeSupport A right ∧
      P.gLocalV1FineEdgeSupport A right = P.gLocalV1FineEdgeSupport A z ∧
      (state.coarseEdges.filter fun mappedZ =>
        P.edgeMap z = some mappedZ ∧
        (retainedCoarseFaces.filter fun mappedRelation =>
          P.faceMap relationFace = some mappedRelation ∧
          P.coarseFaceEdge0 mappedRelation = coarseEdge ∧
          P.coarseFaceEdge1 mappedRelation = coarseEdge ∧
          P.coarseFaceEdge2 mappedRelation = mappedZ ∧
          (retainedFineFaces.filter fun killFace =>
            P.fineFaceEdge0 killFace = z ∧ P.fineFaceEdge1 killFace = z ∧
            P.fineFaceEdge2 killFace = z ∧
            P.gLocalV1FineFaceSupport A relationFace =
              P.gLocalV1FineFaceSupport A killFace ∧
            (retainedCoarseFaces.filter fun mappedKill =>
              P.faceMap killFace = some mappedKill ∧
              P.coarseFaceEdge0 mappedKill = mappedZ ∧
              P.coarseFaceEdge1 mappedKill = mappedZ ∧
              P.coarseFaceEdge2 mappedKill = mappedZ).Nonempty).Nonempty).Nonempty).Nonempty
    ).Nonempty)

/-- Direct certified SLOT-or-KILL adjacency between two retained lifts.  The
permanent relation first requires equal scoped edge supports and only then
tests either certificate.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CertifiedPair (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseEdge : P.CoarseEdge) (left right : P.FineEdge) : Bool :=
  left ≠ right &&
    P.gLocalV1FineEdgeSupport A left = P.gLocalV1FineEdgeSupport A right &&
    (P.gLocalV1SlotCertified A state left right ||
      P.gLocalV1KillCertified A state coarseEdge left right)

/-- Retained fine lifts of one coarse edge.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1FineLifts (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseEdge : P.CoarseEdge) :
    Finset P.FineEdge :=
  state.fineEdges.filter fun fineEdge => P.edgeMap fineEdge = some coarseEdge

/-- The direct certified swap graph, represented as an undirected family of
ordered edge pairs.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1CertifiedSwapGraph (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseEdge : P.CoarseEdge) : Finset (P.FineEdge × P.FineEdge) :=
  let lifts := P.gLocalV1FineLifts A state coarseEdge
  (lifts ×ˢ lifts).filter fun pair =>
    P.gLocalV1CertifiedPair A state coarseEdge pair.1 pair.2

/-! ## Permanent terminal conditions C0--C6 -/

/-- Permanent C0 on one terminal: the factor-image union of active fine chart
supports equals each original coarse critical chart support.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC0 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseChart ∈ P.gLocalV1CoarseCriticalVertices A state,
    ((P.gLocalV1Ports A state coarseChart).biUnion fun fineChart =>
      (P.gLocalV1FineChartSupport A fineChart).image P.computedFactor) =
        P.gLocalV1CoarseChartSupport A coarseChart)

/-- Permanent C1 on one terminal: every critical coarse-chart port fiber is
nonempty and connected using all scoped fine edges, not only retained edges.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC1 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseChart ∈ P.gLocalV1CoarseCriticalVertices A state,
    (P.gLocalV1Ports A state coarseChart).Nonempty ∧
      gLocalV1Connected (P.gLocalV1Ports A state coarseChart)
        (P.gLocalV1FineEdges A) P.fineEdgeLeft P.fineEdgeRight = true)

/-- Permanent C2 on one terminal: every original coarse critical edge has a
retained mapped fine lift.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC2 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseEdge ∈ P.gLocalV1CoarseCriticalEdges A state,
    ∃ fineEdge ∈ state.fineEdges, P.edgeMap fineEdge = some coarseEdge)

/-- Whether a retained fine edge belongs to the local unmapped fiber over one
coarse chart.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1LocalFineEdge (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart)
    (edge : P.FineEdge) : Prop :=
  edge ∈ state.fineEdges ∧ P.edgeMap edge = none ∧
    P.chartMap (P.fineEdgeLeft edge) = coarseChart ∧
    P.chartMap (P.fineEdgeRight edge) = coarseChart

/-- Whether a retained fine FaceTwin class contributes its one registered
boundary row to a local unmapped fiber.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1LocalFineFaceClass (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) (key : P.GLocalV1FineFaceTwinKey A) : Prop :=
  key ∈ state.fineFaceClasses ∧
    (∃ face ∈ P.gLocalV1FineFaceMembers A key, P.faceMap face = none) ∧
    P.gLocalV1LocalFineEdge A state coarseChart key.edge0 ∧
    P.gLocalV1LocalFineEdge A state coarseChart key.edge1 ∧
    P.gLocalV1LocalFineEdge A state coarseChart key.edge2

/-- Local unmapped edge membership is constructively decidable.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
instance gLocalV1LocalFineEdgeDecidable (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) (edge : P.FineEdge) :
    Decidable (P.gLocalV1LocalFineEdge A state coarseChart edge) := by
  unfold gLocalV1LocalFineEdge
  infer_instance

/-- Local unmapped FaceTwin membership is constructively decidable.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
instance gLocalV1LocalFineFaceClassDecidable (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) (key : P.GLocalV1FineFaceTwinKey A) :
    Decidable (P.gLocalV1LocalFineFaceClass A state coarseChart key) := by
  unfold gLocalV1LocalFineFaceClass
  infer_instance

/-- Fine charts in one local unmapped fiber.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
abbrev GLocalV1LocalChart (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (coarseChart : P.CoarseChart) :=
  {chart : P.FineChart // chart ∈ P.gLocalV1FineCharts A ∧
    P.chartMap chart = coarseChart}

/-- Retained unmapped fine edges in one local fiber.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
abbrev GLocalV1LocalEdge (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) :=
  {edge : P.FineEdge // P.gLocalV1LocalFineEdge A state coarseChart edge}

/-- Retained FaceTwin boundary rows in one local unmapped fiber.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
abbrev GLocalV1LocalFace (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) :=
  {key : P.GLocalV1FineFaceTwinKey A //
    P.gLocalV1LocalFineFaceClass A state coarseChart key}

/-- Local fiber `d0` matrix.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1LocalD0Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) :
    Matrix (P.GLocalV1LocalEdge A state coarseChart)
      (P.GLocalV1LocalChart A coarseChart) ℚ :=
  fun edge chart =>
    (if P.fineEdgeRight edge.1 = chart.1 then 1 else 0) -
      (if P.fineEdgeLeft edge.1 = chart.1 then 1 else 0)

/-- Local fiber `d1` matrix with one row per retained FaceTwin class.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1LocalD1Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) :
    Matrix (P.GLocalV1LocalFace A state coarseChart)
      (P.GLocalV1LocalEdge A state coarseChart) ℚ :=
  fun face edge =>
    (gLocalV1SignedCoefficient face.1.edge0 face.1.edge1 face.1.edge2 edge.1 : ℚ)

/-- Executable local unmapped H1 dimension, used only to decide C3.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1LocalUnmappedH1Dimension (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (coarseChart : P.CoarseChart) : Nat :=
  Fintype.card (P.GLocalV1LocalEdge A state coarseChart) -
    rationalMatrixRank (P.gLocalV1LocalD1Matrix A state coarseChart) -
      rationalMatrixRank (P.gLocalV1LocalD0Matrix A state coarseChart)

/-- Permanent registered C3 exception: every local unmapped fiber has exact
rational H1 dimension zero.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC3 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseChart ∈ P.gLocalV1CoarseCharts A,
    P.gLocalV1LocalUnmappedH1Dimension A state coarseChart = 0)

/-- C3's Boolean is true exactly when every registered local unmapped H1
dimension is zero.

Position: reducer API theorem supporting fixed GOAL claim (v). Any material premise concerns raw `FiniteComparisonPresentation` tables or generated states and packets; no trace, terminal, condition, or observation certificate is assumed.
-/
theorem gLocalV1ConditionC3_eq_true_iff_localUnmappedH1Zero
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) :
    P.gLocalV1ConditionC3 A state = true ↔
      ∀ coarseChart ∈ P.gLocalV1CoarseCharts A,
        P.gLocalV1LocalUnmappedH1Dimension A state coarseChart = 0 := by
  simp [gLocalV1ConditionC3]

/-- Permanent C4 on one terminal: each retained coarse FaceTwin class is hit
by an actual retained fine face.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC4 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseKey ∈ state.coarseFaceClasses,
    ∃ fineKey ∈ state.fineFaceClasses,
    ∃ fineFace ∈ P.gLocalV1FineFaceMembers A fineKey,
    ∃ coarseFace ∈ P.gLocalV1CoarseFaceMembers A coarseKey,
      P.faceMap fineFace = some coarseFace)

/-- Permanent C5 on guarded coarse edges: every retained lift set is connected
in the certified SLOT/KILL swap graph.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC5 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseEdge ∈ P.gLocalV1GuardedCoarseEdges A state,
    let lifts := P.gLocalV1FineLifts A state coarseEdge
    gLocalV1Connected lifts (P.gLocalV1CertifiedSwapGraph A state coarseEdge)
      Prod.fst Prod.snd = true)

/-- Permanent C6 on guarded coarse self-loops: every certified lift component
contains a fine self-loop.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1ConditionC6 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) : Bool :=
  decide (∀ coarseEdge ∈ P.gLocalV1GuardedCoarseEdges A state,
    P.coarseEdgeLeft coarseEdge = P.coarseEdgeRight coarseEdge →
    let lifts := P.gLocalV1FineLifts A state coarseEdge
    let swaps := P.gLocalV1CertifiedSwapGraph A state coarseEdge
    ∀ lift ∈ lifts, ∃ selfLoop ∈ lifts,
      P.fineEdgeLeft selfLoop = P.fineEdgeRight selfLoop ∧
      selfLoop ∈ gLocalV1ReachabilityClosure lifts swaps Prod.fst Prod.snd lift)

/-! ## Universal terminal evaluation -/

/-- Universal whole-scope condition record over every irreducible terminal.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1WholeConditions (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : GLocalV1WholeConditions where
  c0 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC0 A state = true)
  c5 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC5 A state = true)
  c6 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC6 A state = true)

/-- Universal nonempty-subset condition record over every irreducible
terminal.

Position: definition/predicate in the permanent v5 reducer supporting fixed GOAL claim (v). Any material input comes from raw `FiniteComparisonPresentation` tables or a generated retained-cell state; no trace, terminal, condition, or observation certificate is supplied.
-/
def gLocalV1AConditions (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : GLocalV1AConditions where
  c1 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC1 A state = true)
  c2 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC2 A state = true)
  c3 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC3 A state = true)
  c4 := decide (∀ state ∈ P.gLocalV1MemoizedTerminalStates A,
    P.gLocalV1ConditionC4 A state = true)

end FiniteComparisonPresentation
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
