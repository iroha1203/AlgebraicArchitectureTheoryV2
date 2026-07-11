import ResearchLean.AG.QualitySurface.SourceRefHandoffHolonomyCorrespondence

/-!
Cycle 61 evidence for `G-aat-quality-surface-01`.

This file separates the report-facing first source-ref handoff obstruction
from the protected obstruction locus of failed `(loop, component)` points.
The locus is relative to the selected finite atlas, bounded source-ref
handoff laws, supplied loop membership, and existing heterogeneous route
state.  It does not assert source extraction completeness, ArchMap
correctness, runtime repair synthesis, arbitrary route enumeration, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefHandoffObstructionLocus

open HeterogeneousRouteInteraction
open BridgeComponent
open RouteHolonomyObstructionSupport
open SourceRefHandoffBridge
open SourceRefHandoffHolonomyCorrespondence

/-! ## Order-independent handoff obstruction locus -/

/-- A protected failed `(loop, component)` point in a source-ref handoff atlas. -/
structure HandoffObstructionPoint
    (atlas : SourceRefHandoffAtlas) where
  loop : SourceRefHandoffLoop
  component : BridgeComponent
  loop_mem : loop ∈ atlas.loops
  support : HandoffHolonomySupport loop component

/-- The atlas has a nonempty source-ref handoff obstruction locus. -/
def HandoffObstructionLocusNonempty
    (atlas : SourceRefHandoffAtlas) : Prop :=
  Nonempty (HandoffObstructionPoint atlas)

/-- The atlas has empty source-ref handoff obstruction locus. -/
def HandoffObstructionLocusEmpty
    (atlas : SourceRefHandoffAtlas) : Prop :=
  Not (HandoffObstructionLocusNonempty atlas)

/--
Two handoff atlases have the same loop membership and the same failed
`(loop, component)` locus.
-/
def SameHandoffObstructionLocus
    (atlas₁ atlas₂ : SourceRefHandoffAtlas) : Prop :=
  (forall loop, loop ∈ atlas₁.loops <-> loop ∈ atlas₂.loops) /\
    (forall loop component,
      (loop ∈ atlas₁.loops /\ HandoffHolonomySupport loop component) <->
        (loop ∈ atlas₂.loops /\ HandoffHolonomySupport loop component))

/-- A locus point carries the Cycle 59 source-ref handoff failure object. -/
def HandoffObstructionPoint.toFailure
    {atlas : SourceRefHandoffAtlas}
    (point : HandoffObstructionPoint atlas) :
    SourceRefHandoffFailure point.loop.handoff :=
  sourceRefHandoffFailure_of_handoffHolonomySupport point.support

/-- A locus point carries the derived bridge obstruction. -/
def HandoffObstructionPoint.toBridgeObstruction
    {atlas : SourceRefHandoffAtlas}
    (point : HandoffObstructionPoint atlas) :
    BridgeObstruction point.loop.handoff.toBridgeCertificate :=
  sourceRefHandoffFailure_bridgeObstruction point.toFailure

/-- A locus point also carries the route-loop holonomy support. -/
theorem HandoffObstructionPoint.toLoopHolonomySupport
    {atlas : SourceRefHandoffAtlas}
    (point : HandoffObstructionPoint atlas) :
    HolonomySupport point.loop.toRouteLoop point.component :=
  (handoffHolonomySupport_iff_loopHolonomySupport
    point.loop point.component).mp point.support

/-! ## First selector as a report-facing projection -/

/--
No first handoff obstruction is found exactly when every listed loop is
handoff-holonomy clear.
-/
theorem firstHandoffObstructingLoop?_none_iff_holonomyVanishes :
    forall (loops : List SourceRefHandoffLoop),
      firstHandoffObstructingLoop? loops = none <->
        forall loop, loop ∈ loops -> HandoffHolonomyClear loop
  | [] => by
      constructor
      · intro _ loop hmem
        cases hmem
      · intro _h
        rfl
  | head :: rest => by
      constructor
      · intro hnone loop hmem
        by_cases hhead : handoffHolonomyClearBool head = true
        · have htail :
              firstHandoffObstructingLoop? rest = none := by
            simpa [firstHandoffObstructingLoop?, hhead] using hnone
          have hmem' : loop = head \/ loop ∈ rest := by
            simpa using hmem
          rcases hmem' with hloop | hmem
          · subst loop
            exact (handoffHolonomyClearBool_eq_true_iff head).mp hhead
          · exact
              (firstHandoffObstructingLoop?_none_iff_holonomyVanishes
                rest).mp htail loop hmem
        · simp [firstHandoffObstructingLoop?, hhead] at hnone
      · intro hclear
        have hhead_clear : handoffHolonomyClearBool head = true :=
          (handoffHolonomyClearBool_eq_true_iff head).mpr
            (hclear head (by simp))
        have htail :
            firstHandoffObstructingLoop? rest = none :=
          (firstHandoffObstructingLoop?_none_iff_holonomyVanishes
            rest).mpr
            (fun loop hmem => hclear loop (by simp [hmem]))
        simpa [firstHandoffObstructingLoop?, hhead_clear] using htail

/-- The ordered first selector returns a witness iff the protected locus is nonempty. -/
theorem firstHandoffObstructingLoop?_some_iff_locusNonempty
    (loops : List SourceRefHandoffLoop) :
    (exists loop, firstHandoffObstructingLoop? loops = some loop) <->
      HandoffObstructionLocusNonempty { loops := loops } := by
  constructor
  · intro hsome
    rcases hsome with ⟨loop, hfirst⟩
    rcases firstHandoffObstructingLoop?_some_nonemptySupport hfirst with
      ⟨component, hsupport⟩
    exact
      ⟨{ loop := loop,
          component := component,
          loop_mem := firstHandoffObstructingLoop?_some_mem hfirst,
          support := hsupport }⟩
  · intro hnonempty
    cases hfirst : firstHandoffObstructingLoop? loops with
    | none =>
        rcases hnonempty with ⟨point⟩
        have hclear :
            forall loop, loop ∈ loops -> HandoffHolonomyClear loop :=
          (firstHandoffObstructingLoop?_none_iff_holonomyVanishes
            loops).mp hfirst
        exact False.elim
          (point.support (hclear point.loop point.loop_mem point.component))
    | some loop =>
        exact ⟨loop, rfl⟩

/-- A returned first handoff obstruction is a projection from a locus point. -/
theorem firstHandoffObstructingLoop?_some_point
    {loops : List SourceRefHandoffLoop}
    {loop : SourceRefHandoffLoop}
    (hfirst : firstHandoffObstructingLoop? loops = some loop) :
    exists point : HandoffObstructionPoint { loops := loops },
      point.loop = loop := by
  rcases firstHandoffObstructingLoop?_some_nonemptySupport hfirst with
    ⟨component, hsupport⟩
  exact
    ⟨{ loop := loop,
        component := component,
        loop_mem := firstHandoffObstructingLoop?_some_mem hfirst,
        support := hsupport },
      rfl⟩

/-! ## Empty/nonempty locus criteria -/

/-- Empty handoff obstruction locus is exactly handoff holonomy vanishing. -/
theorem handoffObstructionLocus_empty_iff_holonomyVanishes
    (atlas : SourceRefHandoffAtlas) :
    HandoffObstructionLocusEmpty atlas <->
      HandoffAtlasHolonomyVanishes atlas := by
  constructor
  · intro hempty loop hmem component
    cases component with
    | support =>
        cases hcert : loop.handoff.supportCertified
        · have hsupport : HandoffHolonomySupport loop support :=
            (sourceRefHandoff_component_false_iff_lawFailure
              loop.handoff support).mp
              (by simp [SourceRefHandoff.component, hcert])
          exact False.elim
            (hempty
              ⟨{ loop := loop,
                  component := support,
                  loop_mem := hmem,
                  support := hsupport }⟩)
        · exact loop.handoff.supportCertified_iff.mp hcert
    | trace =>
        cases hcert : loop.handoff.traceCertified
        · have hsupport : HandoffHolonomySupport loop trace :=
            (sourceRefHandoff_component_false_iff_lawFailure
              loop.handoff trace).mp
              (by simp [SourceRefHandoff.component, hcert])
          exact False.elim
            (hempty
              ⟨{ loop := loop,
                  component := trace,
                  loop_mem := hmem,
                  support := hsupport }⟩)
        · exact loop.handoff.traceCertified_iff.mp hcert
    | repairFrontier =>
        cases hcert : loop.handoff.repairFrontierCertified
        · have hsupport : HandoffHolonomySupport loop repairFrontier :=
            (sourceRefHandoff_component_false_iff_lawFailure
              loop.handoff repairFrontier).mp
              (by simp [SourceRefHandoff.component, hcert])
          exact False.elim
            (hempty
              ⟨{ loop := loop,
                  component := repairFrontier,
                  loop_mem := hmem,
                  support := hsupport }⟩)
        · exact loop.handoff.repairFrontierCertified_iff.mp hcert
  · intro hvanish hnonempty
    rcases hnonempty with ⟨point⟩
    exact point.support
      (hvanish point.loop point.loop_mem point.component)

/-- Nonempty handoff obstruction locus is exactly failure of holonomy vanishing. -/
theorem handoffObstructionLocus_nonempty_iff_not_holonomyVanishes
    (atlas : SourceRefHandoffAtlas) :
    HandoffObstructionLocusNonempty atlas <->
      Not (HandoffAtlasHolonomyVanishes atlas) := by
  constructor
  · intro hnonempty hvanish
    rcases hnonempty with ⟨point⟩
    exact point.support
      (hvanish point.loop point.loop_mem point.component)
  · intro hnot
    cases hfirst : firstHandoffObstructingLoop? atlas.loops with
    | none =>
        have hvanish :
            HandoffAtlasHolonomyVanishes atlas :=
          (firstHandoffObstructingLoop?_none_iff_holonomyVanishes
            atlas.loops).mp hfirst
        exact False.elim (hnot hvanish)
    | some loop =>
        exact
          (firstHandoffObstructingLoop?_some_iff_locusNonempty
            atlas.loops).mp ⟨loop, hfirst⟩

/--
Under local exactness, atlas interaction exactness fails exactly when the
order-independent handoff obstruction locus is nonempty.
-/
theorem handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local
    {atlas : SourceRefHandoffAtlas}
    (hlocal : HandoffAtlasLocalExact atlas) :
    Not (HandoffAtlasInteractionExact atlas) <->
      HandoffObstructionLocusNonempty atlas := by
  constructor
  · intro hnot
    apply (handoffObstructionLocus_nonempty_iff_not_holonomyVanishes
      atlas).mpr
    intro hvanish
    exact hnot
      ((handoffAtlasInteractionExact_iff_localAndHandoffHolonomyClear
        atlas).mpr ⟨hlocal, hvanish⟩)
  · intro hnonempty hexact
    have hvanish :
        HandoffAtlasHolonomyVanishes atlas :=
      (handoffAtlasInteractionExact_iff_localAndHandoffHolonomyClear
        atlas).mp hexact |>.2
    exact
      ((handoffObstructionLocus_nonempty_iff_not_holonomyVanishes
        atlas).mp hnonempty) hvanish

/-! ## Preservation under membership-equivalent loci -/

/-- Same obstruction locus preserves locus nonemptiness. -/
theorem sameHandoffObstructionLocus_preserves_nonempty
    {atlas₁ atlas₂ : SourceRefHandoffAtlas}
    (hsame : SameHandoffObstructionLocus atlas₁ atlas₂) :
    HandoffObstructionLocusNonempty atlas₁ <->
      HandoffObstructionLocusNonempty atlas₂ := by
  constructor
  · intro hnonempty
    rcases hnonempty with ⟨point⟩
    have hlocus :=
      (hsame.2 point.loop point.component).mp
        ⟨point.loop_mem, point.support⟩
    exact
      ⟨{ loop := point.loop,
          component := point.component,
          loop_mem := hlocus.1,
          support := hlocus.2 }⟩
  · intro hnonempty
    rcases hnonempty with ⟨point⟩
    have hlocus :=
      (hsame.2 point.loop point.component).mpr
        ⟨point.loop_mem, point.support⟩
    exact
      ⟨{ loop := point.loop,
          component := point.component,
          loop_mem := hlocus.1,
          support := hlocus.2 }⟩

/-- Same obstruction locus preserves handoff holonomy vanishing. -/
theorem sameHandoffObstructionLocus_preserves_holonomyVanishes
    {atlas₁ atlas₂ : SourceRefHandoffAtlas}
    (hsame : SameHandoffObstructionLocus atlas₁ atlas₂) :
    HandoffAtlasHolonomyVanishes atlas₁ <->
      HandoffAtlasHolonomyVanishes atlas₂ := by
  constructor
  · intro hvanish loop hmem component
    exact hvanish loop ((hsame.1 loop).mpr hmem) component
  · intro hvanish loop hmem component
    exact hvanish loop ((hsame.1 loop).mp hmem) component

/-- Same obstruction locus preserves atlas local exactness. -/
theorem sameHandoffObstructionLocus_preserves_localExact
    {atlas₁ atlas₂ : SourceRefHandoffAtlas}
    (hsame : SameHandoffObstructionLocus atlas₁ atlas₂) :
    HandoffAtlasLocalExact atlas₁ <->
      HandoffAtlasLocalExact atlas₂ := by
  constructor
  · intro hlocal loop hmem
    exact hlocal loop ((hsame.1 loop).mpr hmem)
  · intro hlocal loop hmem
    exact hlocal loop ((hsame.1 loop).mp hmem)

/-- Same obstruction locus preserves atlas interaction exactness. -/
theorem sameHandoffObstructionLocus_preserves_interactionExact
    {atlas₁ atlas₂ : SourceRefHandoffAtlas}
    (hsame : SameHandoffObstructionLocus atlas₁ atlas₂) :
    HandoffAtlasInteractionExact atlas₁ <->
      HandoffAtlasInteractionExact atlas₂ := by
  constructor
  · intro hexact loop hmem
    exact hexact loop ((hsame.1 loop).mpr hmem)
  · intro hexact loop hmem
    exact hexact loop ((hsame.1 loop).mp hmem)

/--
Same obstruction locus preserves the local-exactness criterion for interaction
exactness.
-/
theorem sameHandoffObstructionLocus_preserves_interactionExact_of_local
    {atlas₁ atlas₂ : SourceRefHandoffAtlas}
    (hsame : SameHandoffObstructionLocus atlas₁ atlas₂)
    (hlocal₁ : HandoffAtlasLocalExact atlas₁)
    (hlocal₂ : HandoffAtlasLocalExact atlas₂) :
    Not (HandoffAtlasInteractionExact atlas₁) <->
      Not (HandoffAtlasInteractionExact atlas₂) := by
  rw [handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local
      hlocal₁,
    handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local
      hlocal₂]
  exact sameHandoffObstructionLocus_preserves_nonempty hsame

/-! ## Concrete mixed and aligned locus witnesses -/

/-- The mixed source-ref handoff atlas has nonempty protected obstruction locus. -/
theorem mixedSourceRefHandoffAtlas_locusNonempty :
    HandoffObstructionLocusNonempty mixedSourceRefHandoffAtlas := by
  exact
    (firstHandoffObstructingLoop?_some_iff_locusNonempty
      mixedSourceRefHandoffAtlas.loops).mp
      ⟨traceRenamedSourceRefHandoffLoop,
        mixedSourceRefHandoffAtlas_firstObstructingLoop⟩

/-- The aligned source-ref handoff atlas has empty protected obstruction locus. -/
theorem alignedSourceRefHandoffAtlas_locusEmpty :
    HandoffObstructionLocusEmpty alignedSourceRefHandoffAtlas := by
  exact (handoffObstructionLocus_empty_iff_holonomyVanishes
    alignedSourceRefHandoffAtlas).mpr
    (((handoffAtlasInteractionExact_iff_localAndHandoffHolonomyClear
      alignedSourceRefHandoffAtlas).mp
      alignedSourceRefHandoffAtlas_interactionExact).2)

/-- The mixed source-ref handoff atlas has nonempty locus iff it is not exact. -/
theorem mixedSourceRefHandoffAtlas_notExact_iff_locusNonempty :
    Not (HandoffAtlasInteractionExact mixedSourceRefHandoffAtlas) <->
      HandoffObstructionLocusNonempty mixedSourceRefHandoffAtlas :=
  handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local
    mixedSourceRefHandoffAtlas_localExact

/-! ## Theorem package -/

/--
Cycle-61 theorem package: the order-independent failed `(loop, component)`
locus is the protected object, while the first selector is a report-facing
projection from it.
-/
theorem sourceRefHandoffObstructionLocus_package :
    HandoffObstructionLocusEmpty alignedSourceRefHandoffAtlas /\
      HandoffObstructionLocusNonempty mixedSourceRefHandoffAtlas /\
      (exists point : HandoffObstructionPoint mixedSourceRefHandoffAtlas,
        (exists _failure : SourceRefHandoffFailure point.loop.handoff,
          True) /\
          (exists _obstruction :
            BridgeObstruction point.loop.handoff.toBridgeCertificate,
            True) /\
          HolonomySupport point.loop.toRouteLoop point.component) /\
      firstHandoffObstructingLoop? mixedSourceRefHandoffAtlas.loops =
        some traceRenamedSourceRefHandoffLoop /\
      (forall atlas,
        HandoffObstructionLocusEmpty atlas <->
          HandoffAtlasHolonomyVanishes atlas) /\
      (forall atlas,
        HandoffObstructionLocusNonempty atlas <->
          Not (HandoffAtlasHolonomyVanishes atlas)) /\
      (forall atlas,
        HandoffAtlasLocalExact atlas ->
          (Not (HandoffAtlasInteractionExact atlas) <->
            HandoffObstructionLocusNonempty atlas)) /\
      (forall loops,
        (exists loop, firstHandoffObstructingLoop? loops = some loop) <->
          HandoffObstructionLocusNonempty { loops := loops }) /\
      (forall loops,
        firstHandoffObstructingLoop? loops = none <->
          forall loop, loop ∈ loops -> HandoffHolonomyClear loop) /\
      (forall atlas₁ atlas₂,
        SameHandoffObstructionLocus atlas₁ atlas₂ ->
          (HandoffObstructionLocusNonempty atlas₁ <->
            HandoffObstructionLocusNonempty atlas₂) /\
          (HandoffAtlasHolonomyVanishes atlas₁ <->
            HandoffAtlasHolonomyVanishes atlas₂) /\
          (HandoffAtlasInteractionExact atlas₁ <->
            HandoffAtlasInteractionExact atlas₂)) := by
  rcases mixedSourceRefHandoffAtlas_locusNonempty with ⟨point⟩
  exact
    ⟨alignedSourceRefHandoffAtlas_locusEmpty,
      mixedSourceRefHandoffAtlas_locusNonempty,
      ⟨point,
        ⟨point.toFailure, trivial⟩,
        ⟨point.toBridgeObstruction, trivial⟩,
        point.toLoopHolonomySupport⟩,
      mixedSourceRefHandoffAtlas_firstObstructingLoop,
      handoffObstructionLocus_empty_iff_holonomyVanishes,
      handoffObstructionLocus_nonempty_iff_not_holonomyVanishes,
      fun _atlas hlocal =>
        handoffAtlas_not_interactionExact_iff_locus_nonempty_of_local
          hlocal,
      firstHandoffObstructingLoop?_some_iff_locusNonempty,
      firstHandoffObstructingLoop?_none_iff_holonomyVanishes,
      fun _atlas₁ _atlas₂ hsame =>
        ⟨sameHandoffObstructionLocus_preserves_nonempty hsame,
          sameHandoffObstructionLocus_preserves_holonomyVanishes hsame,
          sameHandoffObstructionLocus_preserves_interactionExact
            hsame⟩⟩

end SourceRefHandoffObstructionLocus
end QualitySurface
end ResearchLean.AG
