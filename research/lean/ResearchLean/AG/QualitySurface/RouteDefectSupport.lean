import ResearchLean.AG.QualitySurface.ComponentDefectPropagation
import ResearchLean.AG.QualitySurface.TransportTableLawRouteLocalization
import ResearchLean.AG.QualitySurface.VisibleRepairTransportCommutator

/-!
Cycle 38 evidence for `G-aat-quality-surface-01`.

This file reads repair/transport endpoint defects as a component-indexed route
defect support.  The support is not merely used as a new name for an existing
defect predicate: the selected witnesses also compute exact support shapes with
off-coordinate nonmembership.

The claim is relative to supplied finite source-ref packets, selected
repair/transport route endpoints, and the explicit packet-to-tuple bridge.  It
does not assert a global lawful-criterion minimality matrix, source extraction
completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace RouteDefectSupportTheory

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion

/-! ## Route defect support calculus -/

/-- Component agreement for a source-ref route endpoint pair. -/
def RouteComponentAgreement
    (left right : SourceRefPacket) :
    SourceRefPacketProtectedComponent -> Prop
  | .obligation => left.obligation = right.obligation
  | .repairFrontier atom => left.repairFrontier atom ↔ right.repairFrontier atom
  | .sourceRefTable atom => left.sourceRefTable atom = right.sourceRefTable atom

/-- Component-indexed support of a route endpoint defect. -/
def RouteDefectSupport
    (left right : SourceRefPacket)
    (component : SourceRefPacketProtectedComponent) : Prop :=
  ¬ RouteComponentAgreement left right component

/-- Empty route defect support, stated positively to avoid double-negation loss. -/
def RouteDefectSupportEmpty
    (left right : SourceRefPacket) : Prop :=
  ∀ component, RouteComponentAgreement left right component

/-- Route defect support is the component-indexed packet holonomy defect. -/
theorem routeDefectSupport_iff_packetHolonomyDefect
    (left right : SourceRefPacket)
    (component : SourceRefPacketProtectedComponent) :
    RouteDefectSupport left right component ↔
      SourceRefPacketHolonomyDefect left right component := by
  cases component <;> rfl

/-- Empty route defect support is exactly packet zero holonomy. -/
theorem routeDefectSupport_empty_iff_noPacketHolonomy
    (left right : SourceRefPacket) :
    RouteDefectSupportEmpty left right ↔
      NoSourceRefPacketHolonomyDefect left right := by
  constructor
  · intro hempty
    exact ⟨hempty SourceRefPacketProtectedComponent.obligation,
      by
        intro atom
        exact hempty (SourceRefPacketProtectedComponent.repairFrontier atom),
      by
        intro atom
        exact hempty (SourceRefPacketProtectedComponent.sourceRefTable atom)⟩
  · intro hzero component
    cases component with
    | obligation => exact hzero.1
    | repairFrontier atom => exact hzero.2.1 atom
    | sourceRefTable atom => exact hzero.2.2 atom

/-- Route defect support projects to tuple protected-component defects. -/
theorem routeDefectSupport_projects_to_tupleDefects
    {p : CodebaseTraceHolonomyPacket.TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hdefect : RouteDefectSupport left right component) :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      (packetComponentToTupleComponent component) :=
  sourceRefPacketHolonomy_projects_to_tupleHolonomy
    gridLeft gridRight
    ((routeDefectSupport_iff_packetHolonomyDefect
      left right component).mp hdefect)

/-- Route defect support propagates across a zero packet-holonomy leg on the left. -/
theorem routeDefectSupport_propagates_left_of_zero
    {left middle right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect left middle)
    (component : SourceRefPacketProtectedComponent) :
    RouteDefectSupport middle right component ↔
      RouteDefectSupport left right component := by
  constructor
  · intro hsupport
    have hpacket :
        SourceRefPacketHolonomyDefect middle right component :=
      (routeDefectSupport_iff_packetHolonomyDefect
        middle right component).mp hsupport
    have hpacket' :
        SourceRefPacketHolonomyDefect left right component :=
      (ComponentHolonomyDefectPropagation.packetComponentDefect_propagates_left_of_zero
        hzero component).mp hpacket
    exact (routeDefectSupport_iff_packetHolonomyDefect
      left right component).mpr hpacket'
  · intro hsupport
    have hpacket :
        SourceRefPacketHolonomyDefect left right component :=
      (routeDefectSupport_iff_packetHolonomyDefect
        left right component).mp hsupport
    have hpacket' :
        SourceRefPacketHolonomyDefect middle right component :=
      (ComponentHolonomyDefectPropagation.packetComponentDefect_propagates_left_of_zero
        hzero component).mpr hpacket
    exact (routeDefectSupport_iff_packetHolonomyDefect
      middle right component).mpr hpacket'

/-- Route defect support propagates across a zero packet-holonomy leg on the right. -/
theorem routeDefectSupport_propagates_right_of_zero
    {left middle right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect middle right)
    (component : SourceRefPacketProtectedComponent) :
    RouteDefectSupport left middle component ↔
      RouteDefectSupport left right component := by
  constructor
  · intro hsupport
    have hpacket :
        SourceRefPacketHolonomyDefect left middle component :=
      (routeDefectSupport_iff_packetHolonomyDefect
        left middle component).mp hsupport
    have hpacket' :
        SourceRefPacketHolonomyDefect left right component :=
      (ComponentHolonomyDefectPropagation.packetComponentDefect_propagates_right_of_zero
        hzero component).mp hpacket
    exact (routeDefectSupport_iff_packetHolonomyDefect
      left right component).mpr hpacket'
  · intro hsupport
    have hpacket :
        SourceRefPacketHolonomyDefect left right component :=
      (routeDefectSupport_iff_packetHolonomyDefect
        left right component).mp hsupport
    have hpacket' :
        SourceRefPacketHolonomyDefect left middle component :=
      (ComponentHolonomyDefectPropagation.packetComponentDefect_propagates_right_of_zero
        hzero component).mpr hpacket
    exact (routeDefectSupport_iff_packetHolonomyDefect
      left middle component).mpr hpacket'

/-! ## Cycle 37 table-law route exact support -/

abbrev tableRouteLeft : SourceRefPacket :=
  TransportTableLawRouteLocalization.tokenSwapRoute_repairThenTransportPacket

abbrev tableRouteRight : SourceRefPacket :=
  TransportTableLawRouteLocalization.tokenSwapRoute_transportThenRepairPacket

/-- The Cycle 37 table-law route has endpoint table defect support. -/
theorem tokenSwapRoute_defectSupport_endpointTable :
    RouteDefectSupport
      tableRouteLeft tableRouteRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
  (routeDefectSupport_iff_packetHolonomyDefect
    tableRouteLeft tableRouteRight
    (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint)).mpr
    TransportTableLawRouteLocalization.tokenSwapRoute_selectedSourceRefTableComponentDefect

/-- The Cycle 37 table-law route also has worker table defect support. -/
theorem tokenSwapRoute_defectSupport_workerTable :
    RouteDefectSupport
      tableRouteLeft tableRouteRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.worker) := by
  intro hagree
  change some SourceRefToken.endpointRef =
    some SourceRefToken.workerRef at hagree
  cases hagree

/-- The Cycle 37 table-law route has no obligation defect. -/
theorem tokenSwapRoute_noObligationDefect :
    ¬ RouteDefectSupport
      tableRouteLeft tableRouteRight
      SourceRefPacketProtectedComponent.obligation := by
  intro hdefect
  exact hdefect TransportTableLawRouteLocalization.tokenSwapRoute_obligation_flat

/-- The Cycle 37 table-law route has no repair-frontier defect at any atom. -/
theorem tokenSwapRoute_noRepairFrontierDefect
    (atom : CodeAtom) :
    ¬ RouteDefectSupport
      tableRouteLeft tableRouteRight
      (SourceRefPacketProtectedComponent.repairFrontier atom) := by
  intro hdefect
  exact hdefect (TransportTableLawRouteLocalization.tokenSwapRoute_repairFrontier_flat atom)

/-- The Cycle 37 table-law route has no storage table defect. -/
theorem tokenSwapRoute_noStorageTableDefect :
    ¬ RouteDefectSupport
      tableRouteLeft tableRouteRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) := by
  intro hdefect
  exact hdefect rfl

/--
Exact support computation for the Cycle 37 table-law route: the support is the
endpoint/worker source-ref table pair, with obligation, frontier, and storage
table coordinates flat.
-/
def TokenSwapRouteExactTablePairSupport : Prop :=
    RouteDefectSupport
        tableRouteLeft tableRouteRight
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) ∧
      RouteDefectSupport
        tableRouteLeft tableRouteRight
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.worker) ∧
      ¬ RouteDefectSupport
        tableRouteLeft tableRouteRight
        SourceRefPacketProtectedComponent.obligation ∧
      (∀ atom,
        ¬ RouteDefectSupport
          tableRouteLeft tableRouteRight
          (SourceRefPacketProtectedComponent.repairFrontier atom)) ∧
      ¬ RouteDefectSupport
        tableRouteLeft tableRouteRight
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage)

theorem tokenSwapRoute_defectSupport_exact_tablePair :
    TokenSwapRouteExactTablePairSupport :=
  ⟨tokenSwapRoute_defectSupport_endpointTable,
    tokenSwapRoute_defectSupport_workerTable,
    tokenSwapRoute_noObligationDefect,
    tokenSwapRoute_noRepairFrontierDefect,
    tokenSwapRoute_noStorageTableDefect⟩

/-! ## Cycle 28 visible-only route exact support -/

abbrev visibleRouteLeft : SourceRefPacket :=
  VisibleRepairTransportCommutator.repairThenTransportPacket

abbrev visibleRouteRight : SourceRefPacket :=
  VisibleRepairTransportCommutator.transportThenRepairPacket

/-- The visible-only route has obligation defect support. -/
theorem visibleRepairTransport_defectSupport_obligation :
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      SourceRefPacketProtectedComponent.obligation :=
  (routeDefectSupport_iff_packetHolonomyDefect
    visibleRouteLeft visibleRouteRight
    SourceRefPacketProtectedComponent.obligation).mpr
    VisibleRepairTransportCommutator.repairTransport_obligation_componentDefect

/-- The visible-only route has storage repair-frontier defect support. -/
theorem visibleRepairTransport_defectSupport_storageRepair :
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) :=
  (routeDefectSupport_iff_packetHolonomyDefect
    visibleRouteLeft visibleRouteRight
    (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage)).mpr
    VisibleRepairTransportCommutator.repairTransport_repairFrontier_componentDefect

/-- The visible-only route has storage table defect support. -/
theorem visibleRepairTransport_defectSupport_storageTable :
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) :=
  (routeDefectSupport_iff_packetHolonomyDefect
    visibleRouteLeft visibleRouteRight
    (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage)).mpr
    VisibleRepairTransportCommutator.repairTransport_sourceRefTable_componentDefect

/-- The visible-only route has no repair-frontier defect away from storage. -/
theorem visibleRepairTransport_noRepairFrontierDefect_offStorage
    (atom : CodeAtom) (hoff : atom ≠ CodeAtom.storage) :
    ¬ RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (SourceRefPacketProtectedComponent.repairFrontier atom) := by
  intro hdefect
  apply hdefect
  dsimp [RouteComponentAgreement, visibleRouteLeft, visibleRouteRight]
  rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
    VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
  cases atom with
  | endpoint =>
      constructor <;> intro hfrontier
      · cases hfrontier
      · rcases hfrontier with ⟨_hsupport, htable⟩
        cases htable
  | storage =>
      exact False.elim (hoff rfl)
  | worker =>
      constructor <;> intro hfrontier
      · cases hfrontier
      · rcases hfrontier with ⟨_hsupport, htable⟩
        cases htable

/-- The visible-only route has no source-ref table defect away from storage. -/
theorem visibleRepairTransport_noTableDefect_offStorage
    (atom : CodeAtom) (hoff : atom ≠ CodeAtom.storage) :
    ¬ RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (SourceRefPacketProtectedComponent.sourceRefTable atom) := by
  intro hdefect
  apply hdefect
  dsimp [RouteComponentAgreement, visibleRouteLeft, visibleRouteRight]
  rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
    VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
  cases atom with
  | endpoint => rfl
  | storage => exact False.elim (hoff rfl)
  | worker => rfl

/--
Exact support computation for the Cycle 28 visible-only route: obligation,
storage repair-frontier, and storage source-ref table are supported defects;
repair-frontier and table coordinates away from storage are flat.
-/
def VisibleRepairTransportDefectSupportTriple : Prop :=
    RouteDefectSupport
        visibleRouteLeft visibleRouteRight
        SourceRefPacketProtectedComponent.obligation ∧
      RouteDefectSupport
        visibleRouteLeft visibleRouteRight
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
      RouteDefectSupport
        visibleRouteLeft visibleRouteRight
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      (∀ atom, atom ≠ CodeAtom.storage ->
        ¬ RouteDefectSupport
          visibleRouteLeft visibleRouteRight
          (SourceRefPacketProtectedComponent.repairFrontier atom)) ∧
      (∀ atom, atom ≠ CodeAtom.storage ->
        ¬ RouteDefectSupport
          visibleRouteLeft visibleRouteRight
          (SourceRefPacketProtectedComponent.sourceRefTable atom))

theorem visibleRepairTransport_defectSupport_triple :
    VisibleRepairTransportDefectSupportTriple :=
  ⟨visibleRepairTransport_defectSupport_obligation,
    visibleRepairTransport_defectSupport_storageRepair,
    visibleRepairTransport_defectSupport_storageTable,
    visibleRepairTransport_noRepairFrontierDefect_offStorage,
    visibleRepairTransport_noTableDefect_offStorage⟩

/-! ## Package theorem -/

/--
Cycle-38 theorem package: route defect support has a zero-support criterion,
tuple projection, zero-leg propagation, and exact selected support computations
for the Cycle 37 table-law route and Cycle 28 visible-only route.
-/
theorem routeDefectSupportCalculus_package :
    (∀ left right : SourceRefPacket,
      RouteDefectSupportEmpty left right ↔
        NoSourceRefPacketHolonomyDefect left right) ∧
      (∀ {p : CodebaseTraceHolonomyPacket.TupleProfile}
        (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
        {left right : SourceRefPacket}
        {component : SourceRefPacketProtectedComponent},
        RouteDefectSupport left right component ->
          TupleHolonomyDefectInvariant.TupleHolonomyDefect
            (SourceRefTupleBridge.packetToTuple gridLeft left)
            (SourceRefTupleBridge.packetToTuple gridRight right)
            (packetComponentToTupleComponent component)) ∧
      (∀ {left middle right : SourceRefPacket}
        (_hzero : NoSourceRefPacketHolonomyDefect left middle)
        (component : SourceRefPacketProtectedComponent),
        RouteDefectSupport middle right component ↔
          RouteDefectSupport left right component) ∧
      (∀ {left middle right : SourceRefPacket}
        (_hzero : NoSourceRefPacketHolonomyDefect middle right)
        (component : SourceRefPacketProtectedComponent),
        RouteDefectSupport left middle component ↔
          RouteDefectSupport left right component) ∧
      supportSurfaceReading.Equivalent tableRouteLeft tableRouteRight ∧
      TokenSwapRouteExactTablePairSupport ∧
      supportSurfaceReading.Equivalent visibleRouteLeft visibleRouteRight ∧
      VisibleRepairTransportDefectSupportTriple := by
  exact ⟨routeDefectSupport_empty_iff_noPacketHolonomy,
    by
      intro p gridLeft gridRight left right component hdefect
      exact routeDefectSupport_projects_to_tupleDefects
        gridLeft gridRight hdefect,
    by
      intro left middle right hzero component
      exact routeDefectSupport_propagates_left_of_zero hzero component,
    by
      intro left middle right hzero component
      exact routeDefectSupport_propagates_right_of_zero hzero component,
    TransportTableLawRouteLocalization.tokenSwapRoute_visiblePacketSurface,
    tokenSwapRoute_defectSupport_exact_tablePair,
    VisibleRepairTransportCommutator.repairTransport_visiblePacketSurface_commutes,
    visibleRepairTransport_defectSupport_triple⟩

end RouteDefectSupportTheory
end QualitySurface
end ResearchLean.AG
