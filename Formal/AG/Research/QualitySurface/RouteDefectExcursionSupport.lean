import Formal.AG.Research.QualitySurface.RouteDefectSupport
import Formal.AG.Research.QualitySurface.SourceRefTableLawObstruction

/-!
Cycle 40 evidence for `G-aat-quality-surface-01`.

This file promotes route-defect support from an endpoint-pair predicate to a
path-internal excursion certificate.  A route chain can have empty endpoint
defect support while carrying nonempty internal defect support along its legs.
The selected token-swap/un-swap chain is the finite witness: it starts and ends
at the same full packet, so endpoint support is empty, but both internal legs
carry exact endpoint/worker source-ref table support.

The claim is relative to supplied finite source-ref packets, selected route
chains, and the explicit packet-to-tuple bridge.  It does not assert a global
additive defect group, canonical transport, canonical repair planning, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace RouteDefectExcursionSupport

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SourceRefTableLawObstruction

/-! ## Internal route-chain support -/

/-- Internal route defect support carried by either leg of a length-two chain. -/
def InternalRouteDefectSupport
    (left middle right : SourceRefPacket)
    (component : SourceRefPacketProtectedComponent) : Prop :=
  RouteDefectSupport left middle component ∨
    RouteDefectSupport middle right component

/-- Endpoint route defect support of a length-two chain. -/
def EndpointRouteDefectSupport
    (left _middle right : SourceRefPacket)
    (component : SourceRefPacketProtectedComponent) : Prop :=
  RouteDefectSupport left right component

/-- A component is an internal excursion when it appears internally but not at the endpoint. -/
def RouteDefectExcursion
    (left middle right : SourceRefPacket)
    (component : SourceRefPacketProtectedComponent) : Prop :=
  InternalRouteDefectSupport left middle right component ∧
    ¬ EndpointRouteDefectSupport left middle right component

/-- Same endpoint support for two selected chains. -/
def SameEndpointRouteDefectSupport
    (left₁ middle₁ right₁ left₂ middle₂ right₂ : SourceRefPacket) : Prop :=
  ∀ component,
    EndpointRouteDefectSupport left₁ middle₁ right₁ component ↔
      EndpointRouteDefectSupport left₂ middle₂ right₂ component

/-- Same internal support for two selected chains. -/
def SameInternalRouteDefectSupport
    (left₁ middle₁ right₁ left₂ middle₂ right₂ : SourceRefPacket) : Prop :=
  ∀ component,
    InternalRouteDefectSupport left₁ middle₁ right₁ component ↔
      InternalRouteDefectSupport left₂ middle₂ right₂ component

/-- If the left boundary leg is zero, internal support equals endpoint support. -/
theorem internalRouteDefectSupport_eq_endpoint_leftZero
    {left middle right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect left middle)
    (component : SourceRefPacketProtectedComponent) :
    InternalRouteDefectSupport left middle right component ↔
      EndpointRouteDefectSupport left middle right component := by
  constructor
  · intro hinternal
    cases hinternal with
    | inl hleft =>
        exact (False.elim
          (sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
            ((routeDefectSupport_iff_packetHolonomyDefect
              left middle component).mp hleft) hzero))
    | inr hright =>
        exact (routeDefectSupport_propagates_left_of_zero
          hzero component).mp hright
  · intro hendpoint
    exact Or.inr ((routeDefectSupport_propagates_left_of_zero
      hzero component).mpr hendpoint)

/-- If the right boundary leg is zero, internal support equals endpoint support. -/
theorem internalRouteDefectSupport_eq_endpoint_rightZero
    {left middle right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect middle right)
    (component : SourceRefPacketProtectedComponent) :
    InternalRouteDefectSupport left middle right component ↔
      EndpointRouteDefectSupport left middle right component := by
  constructor
  · intro hinternal
    cases hinternal with
    | inl hleft =>
        exact (routeDefectSupport_propagates_right_of_zero
          hzero component).mp hleft
    | inr hright =>
        exact (False.elim
          (sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
            ((routeDefectSupport_iff_packetHolonomyDefect
              middle right component).mp hright) hzero))
  · intro hendpoint
    exact Or.inl ((routeDefectSupport_propagates_right_of_zero
      hzero component).mpr hendpoint)

/-- Visible tuple equivalence plus empty endpoint support gives source-ref exact visualization. -/
theorem sourceRefExact_of_visible_and_emptyRouteSupport
    {p : CodebaseTraceHolonomyPacket.TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left right : SourceRefPacket}
    (hvisible :
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right)
    (hempty : RouteDefectSupportEmpty left right) :
    SourceRefExactVisualization gridLeft gridRight left right := by
  have hzero :
      NoSourceRefPacketHolonomyDefect left right :=
    (routeDefectSupport_empty_iff_noPacketHolonomy left right).mp
      hempty
  exact (sourceRefExactVisualization_iff_visible_packetZeroHolonomy
    gridLeft gridRight left right).mpr ⟨hvisible, hzero⟩

/-! ## Flat chain and token-swap/un-swap chain -/

abbrev flatChainLeft : SourceRefPacket := fullPacket
abbrev flatChainMiddle : SourceRefPacket := fullPacket
abbrev flatChainRight : SourceRefPacket := fullPacket

abbrev tokenSwapChainLeft : SourceRefPacket := fullPacket
abbrev tokenSwapChainMiddle : SourceRefPacket := tokenSwappedFullPacket
abbrev tokenSwapChainRight : SourceRefPacket := fullPacket

/-- The flat chain has empty endpoint support. -/
theorem flatChain_endpointSupport_empty
    (component : SourceRefPacketProtectedComponent) :
    ¬ EndpointRouteDefectSupport
      flatChainLeft flatChainMiddle flatChainRight component := by
  intro hsupport
  have hzero :
      NoSourceRefPacketHolonomyDefect flatChainLeft flatChainRight :=
    ComponentHolonomyDefectPropagation.noSourceRefPacketHolonomyDefect_refl
      flatChainLeft
  exact sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
    ((routeDefectSupport_iff_packetHolonomyDefect
      flatChainLeft flatChainRight component).mp hsupport) hzero

/-- The flat chain has empty internal support. -/
theorem flatChain_internalSupport_empty
    (component : SourceRefPacketProtectedComponent) :
    ¬ InternalRouteDefectSupport
      flatChainLeft flatChainMiddle flatChainRight component := by
  intro hinternal
  cases hinternal with
  | inl hleft =>
      have hzero :
          NoSourceRefPacketHolonomyDefect flatChainLeft flatChainMiddle :=
        ComponentHolonomyDefectPropagation.noSourceRefPacketHolonomyDefect_refl
          flatChainLeft
      exact sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
        ((routeDefectSupport_iff_packetHolonomyDefect
          flatChainLeft flatChainMiddle component).mp hleft) hzero
  | inr hright =>
      have hzero :
          NoSourceRefPacketHolonomyDefect flatChainMiddle flatChainRight :=
        ComponentHolonomyDefectPropagation.noSourceRefPacketHolonomyDefect_refl
          flatChainMiddle
      exact sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
        ((routeDefectSupport_iff_packetHolonomyDefect
          flatChainMiddle flatChainRight component).mp hright) hzero

/-- The token-swap/un-swap chain has empty endpoint support. -/
theorem tokenSwapUnswap_endpointSupport_empty
    (component : SourceRefPacketProtectedComponent) :
    ¬ EndpointRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight component := by
  intro hsupport
  have hzero :
      NoSourceRefPacketHolonomyDefect tokenSwapChainLeft tokenSwapChainRight :=
    ComponentHolonomyDefectPropagation.noSourceRefPacketHolonomyDefect_refl
      tokenSwapChainLeft
  exact sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
    ((routeDefectSupport_iff_packetHolonomyDefect
      tokenSwapChainLeft tokenSwapChainRight component).mp hsupport) hzero

/-- The first token-swap leg has endpoint table internal support. -/
theorem tokenSwapUnswap_internalSupport_endpointTable :
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
  Or.inl ((routeDefectSupport_iff_packetHolonomyDefect
    tokenSwapChainLeft tokenSwapChainMiddle
    (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint)).mpr
    tokenSwap_sourceRefTable_componentDefect)

/-- The first token-swap leg also has worker table internal support. -/
theorem tokenSwapUnswap_internalSupport_workerTable :
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.worker) := by
  apply Or.inl
  intro hagree
  change some SourceRefToken.workerRef = some SourceRefToken.endpointRef at hagree
  cases hagree

/-- The token-swap/un-swap chain has no internal obligation support. -/
theorem tokenSwapUnswap_noInternalObligationSupport :
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      SourceRefPacketProtectedComponent.obligation := by
  intro hinternal
  cases hinternal with
  | inl hleft =>
      exact hleft rfl
  | inr hright =>
      exact hright rfl

/-- The token-swap/un-swap chain has no internal repair-frontier support. -/
theorem tokenSwapUnswap_noInternalRepairFrontierSupport
    (atom : CodeAtom) :
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.repairFrontier atom) := by
  intro hinternal
  cases hinternal with
  | inl hleft =>
      exact hleft (tokenSwap_repairFrontier_flat atom)
  | inr hright =>
      exact hright (by
        exact (tokenSwap_repairFrontier_flat atom).symm)

/-- The token-swap/un-swap chain has no internal storage-table support. -/
theorem tokenSwapUnswap_noInternalStorageTableSupport :
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) := by
  intro hinternal
  cases hinternal with
  | inl hleft =>
      exact hleft rfl
  | inr hright =>
      exact hright rfl

/--
Exact internal support computation for the token-swap/un-swap chain: endpoint
and worker source-ref table coordinates carry the internal excursion, while
obligation, all repair-frontier coordinates, and storage table are flat.
-/
def TokenSwapUnswapExactInternalTablePairSupport : Prop :=
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) ∧
    InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.worker) ∧
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      SourceRefPacketProtectedComponent.obligation ∧
    (∀ atom,
      ¬ InternalRouteDefectSupport
        tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
        (SourceRefPacketProtectedComponent.repairFrontier atom)) ∧
    ¬ InternalRouteDefectSupport
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage)

/-- The token-swap/un-swap chain has exact endpoint/worker table internal support. -/
theorem tokenSwapUnswap_internalSupport_exact_tablePair :
    TokenSwapUnswapExactInternalTablePairSupport :=
  ⟨tokenSwapUnswap_internalSupport_endpointTable,
    tokenSwapUnswap_internalSupport_workerTable,
    tokenSwapUnswap_noInternalObligationSupport,
    tokenSwapUnswap_noInternalRepairFrontierSupport,
    tokenSwapUnswap_noInternalStorageTableSupport⟩

/-- The token-swap/un-swap chain carries an internal endpoint-table excursion. -/
theorem tokenSwapUnswap_endpointTable_excursion :
    RouteDefectExcursion
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
  ⟨tokenSwapUnswap_internalSupport_endpointTable,
    tokenSwapUnswap_endpointSupport_empty
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint)⟩

/-- Flat and token-swap/un-swap chains agree at endpoint support. -/
theorem flat_tokenSwapUnswap_sameEndpointSupport :
    SameEndpointRouteDefectSupport
      flatChainLeft flatChainMiddle flatChainRight
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight := by
  intro component
  constructor
  · intro hflat
    exact False.elim (flatChain_endpointSupport_empty component hflat)
  · intro hswap
    exact False.elim (tokenSwapUnswap_endpointSupport_empty component hswap)

/-- Endpoint support is not faithful to internal route-defect support. -/
theorem endpointSupport_not_faithful_to_internalSupport :
    SameEndpointRouteDefectSupport
        flatChainLeft flatChainMiddle flatChainRight
        tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight ∧
      ¬ SameInternalRouteDefectSupport
        flatChainLeft flatChainMiddle flatChainRight
        tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight := by
  refine ⟨flat_tokenSwapUnswap_sameEndpointSupport, ?_⟩
  intro hsame
  have hflatInternal :
      InternalRouteDefectSupport
        flatChainLeft flatChainMiddle flatChainRight
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
    (hsame
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint)).mpr
      tokenSwapUnswap_internalSupport_endpointTable
  exact flatChain_internalSupport_empty
    (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint)
    hflatInternal

/-! ## Theorem package -/

/--
Cycle-40 theorem package: internal route-defect support localizes to endpoint
support across zero boundary legs, but endpoint support is not faithful to
path-internal defect excursions.
-/
theorem routeDefectExcursionSupport_package :
    (∀ {left middle right : SourceRefPacket}
      (_hzero : NoSourceRefPacketHolonomyDefect left middle)
      (component : SourceRefPacketProtectedComponent),
      InternalRouteDefectSupport left middle right component ↔
        EndpointRouteDefectSupport left middle right component) ∧
    (∀ {left middle right : SourceRefPacket}
      (_hzero : NoSourceRefPacketHolonomyDefect middle right)
      (component : SourceRefPacketProtectedComponent),
      InternalRouteDefectSupport left middle right component ↔
        EndpointRouteDefectSupport left middle right component) ∧
    (∀ {p : CodebaseTraceHolonomyPacket.TupleProfile}
      (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
      {left right : SourceRefPacket},
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right ->
        RouteDefectSupportEmpty left right ->
        SourceRefExactVisualization gridLeft gridRight left right) ∧
    (∀ component,
      ¬ EndpointRouteDefectSupport
        tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight component) ∧
    TokenSwapUnswapExactInternalTablePairSupport ∧
    RouteDefectExcursion
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) ∧
    SameEndpointRouteDefectSupport
      flatChainLeft flatChainMiddle flatChainRight
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight ∧
    ¬ SameInternalRouteDefectSupport
      flatChainLeft flatChainMiddle flatChainRight
      tokenSwapChainLeft tokenSwapChainMiddle tokenSwapChainRight := by
  exact ⟨by
      intro left middle right hzero component
      exact internalRouteDefectSupport_eq_endpoint_leftZero hzero component,
    by
      intro left middle right hzero component
      exact internalRouteDefectSupport_eq_endpoint_rightZero hzero component,
    by
      intro p gridLeft gridRight left right hvisible hempty
      exact sourceRefExact_of_visible_and_emptyRouteSupport
        gridLeft gridRight hvisible hempty,
    tokenSwapUnswap_endpointSupport_empty,
    tokenSwapUnswap_internalSupport_exact_tablePair,
    tokenSwapUnswap_endpointTable_excursion,
    flat_tokenSwapUnswap_sameEndpointSupport,
    endpointSupport_not_faithful_to_internalSupport.2⟩

end RouteDefectExcursionSupport
end QualitySurface
end Formal.AG.Research
