import ResearchLean.AG.CrossStageCoherence.CellChain

/-!
# Comparison-section descent for cell chains

This module proves theorem (C) of the fixed G-109 target.  A comparison
section assigns one `C_G` coordinate to every semantic path node, is normalized
at empty paths, and is natural for the reviewed twisted affine cell action.
Universal closed-route coherence is equivalent to existence of such a section
on every finite presentation.

## Implementation notes

The forward construction chooses a representative and a route in each finite
cell-graph component.  It does not store path independence in the section:
path independence is derived from `CellChainCoherent` by closing two routes
with the explicit reverse operation.  Components containing the unique
semantic empty-path node are normalized by transporting the identity backward
to the representative; other components receive the identity base coordinate.
The existential section formulation remains a theorem and is not used to
define `CellChainCoherent`.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 4000000

namespace CellChain

/-- Reverse a typed zigzag, reversing every oriented cell step. -/
def reverse {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {first last : CellChainNode P source target} :
    CellChain P first last → CellChain P last first
  | .nil node => .nil node
  | .cons step tail =>
      (reverse tail).append (.cons step.reverse (.nil _))

/-- The one-step chain used to expose section naturality as route transport. -/
def singleton {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) : CellChain P before after :=
  .cons step (.nil after)

end CellChain

/-- Reversing a typed cell step gives the inverse affine equivalence. -/
theorem cellAffineStep_reverse
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    CellAffineStep data step.reverse = (CellAffineStep data step).symm := by
  apply Equiv.ext
  intro coordinate
  simp only [CellAffineStep, cellGaugeAffineEquiv,
    cellAuthoredFactor_reverse, cellCanonicalFactor_reverse]
  change (cellAuthoredFactor data step)⁻¹ * coordinate *
      cellCanonicalFactor data 1 step =
    (cellAuthoredFactor data step)⁻¹ * coordinate *
      cellCanonicalFactor data 1 step
  rfl

/-- Route transport preserves typed concatenation in traversal order. -/
theorem cellRouteTransport_append
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first middle last : CellChainNode P source target}
    (head : CellChain P first middle) (tail : CellChain P middle last) :
    CellRouteTransport data (head.append tail) =
      (CellRouteTransport data head).trans (CellRouteTransport data tail) := by
  induction head with
  | nil node => rfl
  | cons step rest inductionHypothesis =>
      simp only [CellChain.append, CellRouteTransport]
      rw [inductionHypothesis]
      rfl

/-- Route transport along the reversed zigzag is the inverse equivalence. -/
theorem cellRouteTransport_reverse
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    CellRouteTransport data chain.reverse =
      (CellRouteTransport data chain).symm := by
  induction chain with
  | nil node => rfl
  | cons step tail inductionHypothesis =>
      rw [CellChain.reverse, cellRouteTransport_append,
        inductionHypothesis]
      simp only [CellRouteTransport, cellAffineStep_reverse]
      rfl

/-! ## Comparison sections -/

/--
The descent datum of theorem (C): node coordinates, empty-path normalization,
and the authored/canonical twisted affine cell equation.
-/
structure CellComparisonSection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) where
  /-- One composite-fiber gauge coordinate at every semantic path node. -/
  value : ∀ {source target : P.Vertex},
    CellChainNode P source target →
      CompositeFiberAut (data.lift.geometry target)
  /-- Empty paths carry the normalized identity coordinate. -/
  nil_normalization : ∀ vertex : P.Vertex,
    value (CellChainNode.nil P vertex) = 1
  /-- Every declared cell satisfies the forward authored/canonical equation. -/
  naturality : ∀ cell : P.TwoCell,
    value (CellChainNode.right P cell) =
      data.comparator cell * value (CellChainNode.left P cell) *
        (upperCanonicalTwoCellComparator data 1 cell)⁻¹

namespace CellComparisonSection

/--
Forward naturality generates affine naturality for every typed oriented step,
including all dependent endpoint and path transports.
-/
theorem naturality_affine
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (comparison : CellComparisonSection data)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    comparison.value after =
      CellAffineStep data step (comparison.value before) := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  subst source
  subst target
  cases orientation
  · have before_node : before = CellChainNode.left P cell :=
      CellChainNode.ext (by
        simpa [orientedCellBeforePath, castPresentedPath] using before_eq)
    have after_node : after = CellChainNode.right P cell :=
      CellChainNode.ext (by
        simpa [orientedCellAfterPath, castPresentedPath] using after_eq)
    subst before
    subst after
    rw [cellAffineStep_apply]
    simpa [cellAuthoredFactor, cellCanonicalFactor] using
      comparison.naturality cell
  · have before_node : before = CellChainNode.right P cell :=
      CellChainNode.ext (by
        simpa [orientedCellBeforePath, castPresentedPath] using before_eq)
    have after_node : after = CellChainNode.left P cell :=
      CellChainNode.ext (by
        simpa [orientedCellAfterPath, castPresentedPath] using after_eq)
    subst before
    subst after
    rw [cellAffineStep_apply]
    have forward := comparison.naturality cell
    simp only [cellAuthoredFactor, cellCanonicalFactor,
      castCompositeFiberAut]
    rw [forward]
    group

/-- Reverse-step naturality gives the explicit inverse affine equation. -/
theorem naturality_backward
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (comparison : CellComparisonSection data)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    comparison.value before =
      (cellAuthoredFactor data step)⁻¹ * comparison.value after *
        cellCanonicalFactor data 1 step := by
  rw [comparison.naturality_affine step, cellAffineStep_apply]
  group

end CellComparisonSection

/-! ## Connected components and route independence -/

/-- Connectivity by an actual typed cell chain, packaged as a setoid. -/
def cellChainConnectedSetoid
    (P : FiniteTransportPresentation.{u})
    (source target : P.Vertex) : Setoid (CellChainNode P source target) where
  r first last := Nonempty (CellChain P first last)
  iseqv := {
    refl := fun node => ⟨.nil node⟩
    symm := fun reachable => ⟨reachable.some.reverse⟩
    trans := fun first second => ⟨first.some.append second.some⟩ }

/-- One connected component of the fixed-endpoint finite cell graph. -/
abbrev CellChainComponent (P : FiniteTransportPresentation.{u})
    (source target : P.Vertex) :=
  Quotient (cellChainConnectedSetoid P source target)

/-- Send a semantic node to its connected component. -/
def cellChainComponent {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    (node : CellChainNode P source target) :
    CellChainComponent P source target :=
  Quotient.mk _ node

/-- Classical representative of one finite cell-graph component. -/
noncomputable def cellChainComponentRoot
    {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    (component : CellChainComponent P source target) :
    CellChainNode P source target :=
  Quotient.out component

/-- The chosen representative is connected to every node in its component. -/
theorem cellChainComponentRoot_reachable
    {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    (component : CellChainComponent P source target)
    (node : CellChainNode P source target)
    (node_component : cellChainComponent node = component) :
    Nonempty (CellChain P (cellChainComponentRoot component) node) := by
  change (cellChainConnectedSetoid P source target).r
    (cellChainComponentRoot component) node
  exact Quotient.exact
    ((Quotient.out_eq component).trans node_component.symm)

/-- Choose a typed route from a component representative to one of its nodes. -/
noncomputable def cellChainComponentRoute
    {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    (component : CellChainComponent P source target)
    (node : CellChainNode P source target)
    (node_component : cellChainComponent node = component) :
    CellChain P (cellChainComponentRoot component) node :=
  Classical.choice
    (cellChainComponentRoot_reachable component node node_component)

/--
Universal closed-route coherence makes affine transport independent of the
chosen route between fixed nodes.
-/
theorem cellRouteTransport_eq_of_cellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (coherent : CellChainCoherent data)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (left right : CellChain P first last) :
    CellRouteTransport data left = CellRouteTransport data right := by
  let loop : CellChain P last last := left.reverse.append right
  have loopIdentity := coherent source target last loop
  apply Equiv.ext
  intro coordinate
  have evaluated := congrArg
    (fun equivalence :
      CompositeFiberAut (data.lift.geometry target) ≃
        CompositeFiberAut (data.lift.geometry target) =>
      equivalence (CellRouteTransport data left coordinate))
    loopIdentity
  rw [show loop = left.reverse.append right by rfl,
    cellRouteTransport_append,
    cellRouteTransport_reverse] at evaluated
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.refl_apply] using evaluated.symm

/-! ## From sections to route coherence -/

/-- Section naturality transports its coordinate along every typed route. -/
theorem cellComparisonSection_route
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (comparison : CellComparisonSection data)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    CellRouteTransport data chain (comparison.value first) =
      comparison.value last := by
  induction chain with
  | nil node => rfl
  | cons step tail inductionHypothesis =>
      simp only [CellRouteTransport, Equiv.trans_apply]
      rw [← comparison.naturality_affine step]
      exact inductionHypothesis

/-- Every comparison section forces universal closed-route coherence. -/
theorem cellComparisonSection_cellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (comparison : CellComparisonSection data) :
    CellChainCoherent data := by
  apply (cellChainCoherent_iff_holonomy_eq_one data).2
  intro source target node chain
  have fixed := cellComparisonSection_route data comparison chain
  rw [cellRouteTransport_closed_apply] at fixed
  apply mul_right_cancel (b := comparison.value node)
  simpa only [one_mul] using fixed

/-! ## From route coherence to a normalized section -/

namespace CellChainNode

/-- The empty-path node transported across an explicit endpoint equality. -/
def nilOfEq (P : FiniteTransportPresentation.{u})
    {source target : P.Vertex} (endpoint_eq : source = target) :
    CellChainNode P source target := by
  subst target
  exact nil P source

end CellChainNode

/--
Base coordinate of one component.  A component meeting the unique empty-path
node is normalized there; every other component starts at the identity.
-/
noncomputable def cellChainComponentBaseCoordinate
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    (component : CellChainComponent P source target) :
    CompositeFiberAut (data.lift.geometry target) := by
  classical
  exact
    if endpoint_eq : source = target then
      let nilNode := CellChainNode.nilOfEq P endpoint_eq
      if reachable : Nonempty
          (CellChain P (cellChainComponentRoot component) nilNode) then
        (CellRouteTransport data (Classical.choice reachable)).symm 1
      else
        1
    else
      1

/-- Transport the component base coordinate to one semantic node. -/
noncomputable def cellComparisonValue
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    (node : CellChainNode P source target) :
    CompositeFiberAut (data.lift.geometry target) :=
  let component := cellChainComponent node
  CellRouteTransport data
      (cellChainComponentRoute component node rfl)
    (cellChainComponentBaseCoordinate data component)

/-- Expose the selected component route used to evaluate one node. -/
theorem cellComparisonValue_eq_componentRoute
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    (component : CellChainComponent P source target)
    (node : CellChainNode P source target)
    (node_component : cellChainComponent node = component) :
    cellComparisonValue data node =
      CellRouteTransport data
        (cellChainComponentRoute component node node_component)
        (cellChainComponentBaseCoordinate data component) := by
  subst component
  rfl

/-- The coherence-generated value is normalized at every empty-path node. -/
theorem cellComparisonValue_nil
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (coherent : CellChainCoherent data)
    (vertex : P.Vertex) :
    cellComparisonValue data (CellChainNode.nil P vertex) = 1 := by
  let node := CellChainNode.nil P vertex
  let component := cellChainComponent node
  let chosenRoute := cellChainComponentRoute component node rfl
  have reachable : Nonempty
      (CellChain P (cellChainComponentRoot component) node) :=
    ⟨chosenRoute⟩
  let normalizationRoute :
      CellChain P (cellChainComponentRoot component) node :=
    Classical.choice reachable
  have routeEquality := cellRouteTransport_eq_of_cellChainCoherent
    data coherent chosenRoute normalizationRoute
  change CellRouteTransport data chosenRoute
      (cellChainComponentBaseCoordinate data component) = 1
  rw [cellChainComponentBaseCoordinate,
    dif_pos (show (vertex : P.Vertex) = vertex from rfl)]
  simp only [CellChainNode.nilOfEq]
  rw [dif_pos reachable]
  change CellRouteTransport data chosenRoute
      ((CellRouteTransport data normalizationRoute).symm 1) = 1
  rw [routeEquality]
  exact Equiv.apply_symm_apply _ _

/-- The coherence-generated value satisfies every oriented affine cell equation. -/
theorem cellComparisonValue_naturality
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (coherent : CellChainCoherent data)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    cellComparisonValue data after =
      CellAffineStep data step (cellComparisonValue data before) := by
  let stepChain := CellChain.singleton step
  have related :
      (cellChainConnectedSetoid P source target).r before after :=
    ⟨stepChain⟩
  have componentEquality : cellChainComponent before =
      cellChainComponent after :=
    Quotient.sound related
  let component := cellChainComponent before
  let beforeRoute := cellChainComponentRoute component before rfl
  have afterComponent : cellChainComponent after = component :=
    componentEquality.symm
  let afterRoute :=
    cellChainComponentRoute component after afterComponent
  let extendedRoute := beforeRoute.append stepChain
  have routeEquality := cellRouteTransport_eq_of_cellChainCoherent
    data coherent afterRoute extendedRoute
  rw [cellComparisonValue_eq_componentRoute data component after
      afterComponent,
    cellComparisonValue_eq_componentRoute data component before rfl]
  change CellRouteTransport data afterRoute
      (cellChainComponentBaseCoordinate data component) = _
  rw [routeEquality, show extendedRoute = beforeRoute.append stepChain by rfl,
    cellRouteTransport_append]
  rfl

/-- Construct the comparison section from universal closed-route coherence. -/
noncomputable def comparisonSectionOfCellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (coherent : CellChainCoherent data) :
    CellComparisonSection data where
  value := cellComparisonValue data
  nil_normalization := cellComparisonValue_nil data coherent
  naturality := by
    intro cell
    have forward := cellComparisonValue_naturality data coherent
      (CellChainStep.forward cell)
    rw [cellAffineStep_apply] at forward
    simpa [cellAuthoredFactor, cellCanonicalFactor] using forward

/--
Theorem (C): universal cell-chain coherence is equivalent, nondefinitionally,
to existence of a normalized affine comparison section on any presentation.
-/
theorem cellChainCoherent_iff_nonempty_comparisonSection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    CellChainCoherent data ↔ Nonempty (CellComparisonSection data) := by
  constructor
  · intro coherent
    exact ⟨comparisonSectionOfCellChainCoherent data coherent⟩
  · rintro ⟨comparison⟩
    exact cellComparisonSection_cellChainCoherent data comparison

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
