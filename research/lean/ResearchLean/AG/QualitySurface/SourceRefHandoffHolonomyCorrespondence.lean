import ResearchLean.AG.QualitySurface.RouteHolonomyObstructionSupport
import ResearchLean.AG.QualitySurface.SourceRefHandoffBridge

/-!
Cycle 60 evidence for `G-aat-quality-surface-01`.

This file packages a finite route atlas whose loops carry source-ref handoff
data.  The loop state bridge is required to be the bridge derived from the
handoff, so handoff component-law failure, bridge obstruction, holonomy
support, and interaction-exactness obstruction are the same bounded finite
certificate phenomenon.  The result is relative to the selected finite atlas
and supplied loop order.  It does not assert source extraction completeness,
ArchMap correctness, runtime repair synthesis, arbitrary route enumeration,
or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefHandoffHolonomyCorrespondence

open HeterogeneousRouteInteraction
open BridgeComponent
open RouteHolonomyObstructionSupport
open RouteLoopName
open SourceRefHandoffBridge

/-! ## Source-ref handoff loops -/

/--
A route loop whose bridge is derived from a bounded source-ref handoff.

The equality pins the route state bridge to `handoff.toBridgeCertificate`;
without it, handoff law failure and loop holonomy support would not be the
same locus.
-/
structure SourceRefHandoffLoop where
  name : RouteLoopName
  state : HeterogeneousRouteState
  handoff : SourceRefHandoff
  bridge_eq : state.bridge = handoff.toBridgeCertificate

/-- Forget the source-ref handoff and read the underlying route loop. -/
def SourceRefHandoffLoop.toRouteLoop
    (loop : SourceRefHandoffLoop) : RouteLoop where
  name := loop.name
  state := loop.state

/-- A finite source-ref handoff atlas with its supplied loop order. -/
structure SourceRefHandoffAtlas where
  loops : List SourceRefHandoffLoop

/-- Forget source-ref handoff data and read the supplied loops as a route atlas. -/
def SourceRefHandoffAtlas.toRouteAtlas
    (atlas : SourceRefHandoffAtlas) : RouteAtlas where
  loops := atlas.loops.map SourceRefHandoffLoop.toRouteLoop

/-! ## Handoff holonomy support -/

/-- Handoff holonomy support is failure of one source-ref handoff law. -/
def HandoffHolonomySupport
    (loop : SourceRefHandoffLoop) (component : BridgeComponent) : Prop :=
  Not (loop.handoff.ComponentLaw component)

/-- A source-ref handoff loop has nonempty handoff holonomy support. -/
def HasHandoffHolonomySupport
    (loop : SourceRefHandoffLoop) : Prop :=
  exists component, HandoffHolonomySupport loop component

/-- A source-ref handoff loop is clear when every handoff law holds. -/
def HandoffHolonomyClear
    (loop : SourceRefHandoffLoop) : Prop :=
  forall component, loop.handoff.ComponentLaw component

/--
Certified component failure is equivalent to failure of the underlying
source-ref handoff law.
-/
theorem sourceRefHandoff_component_false_iff_lawFailure
    (handoff : SourceRefHandoff)
    (component : BridgeComponent) :
    handoff.component component = false <->
      Not (handoff.ComponentLaw component) := by
  cases component with
  | support =>
      constructor
      · intro hfalse hlaw
        have htrue := handoff.supportCertified_iff.mpr hlaw
        rw [SourceRefHandoff.component, htrue] at hfalse
        cases hfalse
      · intro hfailure
        cases hcert : handoff.supportCertified
        · simp [SourceRefHandoff.component, hcert]
        · exact False.elim
            (hfailure (handoff.supportCertified_iff.mp hcert))
  | trace =>
      constructor
      · intro hfalse hlaw
        have htrue := handoff.traceCertified_iff.mpr hlaw
        rw [SourceRefHandoff.component, htrue] at hfalse
        cases hfalse
      · intro hfailure
        cases hcert : handoff.traceCertified
        · simp [SourceRefHandoff.component, hcert]
        · exact False.elim
            (hfailure (handoff.traceCertified_iff.mp hcert))
  | repairFrontier =>
      constructor
      · intro hfalse hlaw
        have htrue := handoff.repairFrontierCertified_iff.mpr hlaw
        rw [SourceRefHandoff.component, htrue] at hfalse
        cases hfalse
      · intro hfailure
        cases hcert : handoff.repairFrontierCertified
        · simp [SourceRefHandoff.component, hcert]
        · exact False.elim
            (hfailure (handoff.repairFrontierCertified_iff.mp hcert))

/-- A handoff law failure gives the failure object required by Cycle 59. -/
def sourceRefHandoffFailure_of_handoffHolonomySupport
    {loop : SourceRefHandoffLoop}
    {component : BridgeComponent}
    (hsupport : HandoffHolonomySupport loop component) :
    SourceRefHandoffFailure loop.handoff where
  component := component
  certifiedFalse :=
    (sourceRefHandoff_component_false_iff_lawFailure
      loop.handoff component).mpr hsupport
  lawFailure := hsupport

/--
For a handoff-derived route loop, source-ref handoff support is the same
locus as the loop holonomy support.
-/
theorem handoffHolonomySupport_iff_loopHolonomySupport
    (loop : SourceRefHandoffLoop)
    (component : BridgeComponent) :
    HandoffHolonomySupport loop component <->
      HolonomySupport loop.toRouteLoop component := by
  rw [HolonomySupport, SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq]
  rw [sourceRefHandoff_bridgeCertificate_component]
  exact (sourceRefHandoff_component_false_iff_lawFailure
    loop.handoff component).symm

/-- Handoff clearance and loop holonomy clearance are the same condition. -/
theorem handoffHolonomyClear_iff_loopHolonomyClear
    (loop : SourceRefHandoffLoop) :
    HandoffHolonomyClear loop <->
      LoopHolonomyClear loop.toRouteLoop := by
  constructor
  · intro hclear component
    cases component with
    | support =>
        have hcert :
            loop.handoff.supportCertified = true :=
          loop.handoff.supportCertified_iff.mpr (hclear support)
        simpa [BridgeCertificate.component,
          SourceRefHandoff.toBridgeCertificate,
          SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq] using hcert
    | trace =>
        have hcert :
            loop.handoff.traceCertified = true :=
          loop.handoff.traceCertified_iff.mpr (hclear trace)
        simpa [BridgeCertificate.component,
          SourceRefHandoff.toBridgeCertificate,
          SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq] using hcert
    | repairFrontier =>
        have hcert :
            loop.handoff.repairFrontierCertified = true :=
          loop.handoff.repairFrontierCertified_iff.mpr
            (hclear repairFrontier)
        simpa [BridgeCertificate.component,
          SourceRefHandoff.toBridgeCertificate,
          SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq] using hcert
  · intro hclear component
    cases component with
    | support =>
        have hcomponent := hclear support
        exact loop.handoff.supportCertified_iff.mp
          (by
            simpa [BridgeCertificate.component,
              SourceRefHandoff.toBridgeCertificate,
              SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq] using hcomponent)
    | trace =>
        have hcomponent := hclear trace
        exact loop.handoff.traceCertified_iff.mp
          (by
            simpa [BridgeCertificate.component,
              SourceRefHandoff.toBridgeCertificate,
              SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq] using hcomponent)
    | repairFrontier =>
        have hcomponent := hclear repairFrontier
        exact loop.handoff.repairFrontierCertified_iff.mp
          (by
            simpa [BridgeCertificate.component,
              SourceRefHandoff.toBridgeCertificate,
              SourceRefHandoffLoop.toRouteLoop, loop.bridge_eq] using hcomponent)

/-- Handoff clearance is equivalent to interaction exactness under local exactness. -/
theorem handoffLoopHolonomyClear_iff_interactionExact_of_local
    {loop : SourceRefHandoffLoop}
    (hlocal : ProductLocalExact loop.state) :
    HandoffHolonomyClear loop <-> InteractionExact loop.state :=
  Iff.trans (handoffHolonomyClear_iff_loopHolonomyClear loop)
    (routeLoopHolonomyClear_iff_interactionExact_of_local
      (loop := loop.toRouteLoop) hlocal)

/-! ## Atlas-level correspondence -/

/-- Every listed handoff loop is locally exact before reading handoff holonomy. -/
def HandoffAtlasLocalExact
    (atlas : SourceRefHandoffAtlas) : Prop :=
  forall loop, loop ∈ atlas.loops -> ProductLocalExact loop.state

/-- All listed handoff loops have vanishing source-ref handoff support. -/
def HandoffAtlasHolonomyVanishes
    (atlas : SourceRefHandoffAtlas) : Prop :=
  forall loop, loop ∈ atlas.loops -> HandoffHolonomyClear loop

/-- Atlas-level interaction exactness for source-ref handoff loops. -/
def HandoffAtlasInteractionExact
    (atlas : SourceRefHandoffAtlas) : Prop :=
  forall loop, loop ∈ atlas.loops -> InteractionExact loop.state

/-- Local exactness is preserved and reflected by the route-atlas projection. -/
theorem handoffAtlasLocalExact_iff_routeAtlasLocalExact
    (atlas : SourceRefHandoffAtlas) :
    HandoffAtlasLocalExact atlas <->
      AtlasLocalExact atlas.toRouteAtlas := by
  constructor
  · intro hlocal routeLoop hmem
    rcases List.mem_map.mp hmem with ⟨loop, hloop, hroute⟩
    subst hroute
    exact hlocal loop hloop
  · intro hlocal loop hmem
    exact hlocal loop.toRouteLoop
      (List.mem_map_of_mem (f := SourceRefHandoffLoop.toRouteLoop) hmem)

/-- Handoff holonomy vanishing is the same as route-atlas holonomy vanishing. -/
theorem handoffAtlasHolonomyVanishes_iff_routeAtlasHolonomyVanishes
    (atlas : SourceRefHandoffAtlas) :
    HandoffAtlasHolonomyVanishes atlas <->
      AtlasHolonomyVanishes atlas.toRouteAtlas := by
  constructor
  · intro hclear routeLoop hmem
    rcases List.mem_map.mp hmem with ⟨loop, hloop, hroute⟩
    subst hroute
    exact (handoffHolonomyClear_iff_loopHolonomyClear loop).mp
      (hclear loop hloop)
  · intro hclear loop hmem
    exact (handoffHolonomyClear_iff_loopHolonomyClear loop).mpr
      (hclear loop.toRouteLoop
        (List.mem_map_of_mem (f := SourceRefHandoffLoop.toRouteLoop) hmem))

/--
The source-ref handoff atlas and its underlying route atlas have the same
interaction-exact loops.
-/
theorem handoffAtlasInteractionExact_iff_routeAtlasInteractionExact
    (atlas : SourceRefHandoffAtlas) :
    HandoffAtlasInteractionExact atlas <->
      RouteAtlasInteractionExact atlas.toRouteAtlas := by
  constructor
  · intro hexact routeLoop hmem
    rcases List.mem_map.mp hmem with ⟨loop, hloop, hroute⟩
    subst hroute
    exact hexact loop hloop
  · intro hexact loop hmem
    exact hexact loop.toRouteLoop
      (List.mem_map_of_mem (f := SourceRefHandoffLoop.toRouteLoop) hmem)

/--
For a source-ref handoff atlas, interaction exactness is exactly local
exactness plus all-loop handoff holonomy vanishing.
-/
theorem handoffAtlasInteractionExact_iff_localAndHandoffHolonomyClear
    (atlas : SourceRefHandoffAtlas) :
    HandoffAtlasInteractionExact atlas <->
      HandoffAtlasLocalExact atlas /\
        HandoffAtlasHolonomyVanishes atlas := by
  constructor
  · intro hexact
    constructor
    · intro loop hmem
      exact (hexact loop hmem).1
    · intro loop hmem
      exact
        (handoffLoopHolonomyClear_iff_interactionExact_of_local
          (hexact loop hmem).1).mpr (hexact loop hmem)
  · intro hpair loop hmem
    exact
      (handoffLoopHolonomyClear_iff_interactionExact_of_local
        (hpair.1 loop hmem)).mp (hpair.2 loop hmem)

/-! ## First source-ref handoff obstruction -/

/-- Boolean clearance for the handoff laws on a loop. -/
def handoffHolonomyClearBool
    (loop : SourceRefHandoffLoop) : Bool :=
  loop.handoff.supportCertified &&
    loop.handoff.traceCertified &&
    loop.handoff.repairFrontierCertified

/-- The boolean clearance agrees with source-ref handoff holonomy clearance. -/
theorem handoffHolonomyClearBool_eq_true_iff
    (loop : SourceRefHandoffLoop) :
    handoffHolonomyClearBool loop = true <->
      HandoffHolonomyClear loop := by
  constructor
  · intro hclear component
    cases component with
    | support =>
        cases hsupport : loop.handoff.supportCertified <;>
          simp [handoffHolonomyClearBool, hsupport] at hclear
        exact loop.handoff.supportCertified_iff.mp hsupport
    | trace =>
        cases hsupport : loop.handoff.supportCertified <;>
          cases htrace : loop.handoff.traceCertified <;>
            simp [handoffHolonomyClearBool, hsupport, htrace] at hclear
        exact loop.handoff.traceCertified_iff.mp htrace
    | repairFrontier =>
        cases hsupport : loop.handoff.supportCertified <;>
          cases htrace : loop.handoff.traceCertified <;>
            cases hrepair : loop.handoff.repairFrontierCertified <;>
              simp [handoffHolonomyClearBool, hsupport, htrace,
                hrepair] at hclear
        exact loop.handoff.repairFrontierCertified_iff.mp hrepair
  · intro hclear
    have hsupport :
        loop.handoff.supportCertified = true :=
      loop.handoff.supportCertified_iff.mpr (hclear support)
    have htrace :
        loop.handoff.traceCertified = true :=
      loop.handoff.traceCertified_iff.mpr (hclear trace)
    have hrepair :
        loop.handoff.repairFrontierCertified = true :=
      loop.handoff.repairFrontierCertified_iff.mpr
        (hclear repairFrontier)
    simp [handoffHolonomyClearBool, hsupport, htrace, hrepair]

/-- A false handoff-clearance exposes nonempty source-ref handoff support. -/
theorem hasHandoffHolonomySupport_of_clearBool_false
    {loop : SourceRefHandoffLoop}
    (hclear : handoffHolonomyClearBool loop = false) :
    HasHandoffHolonomySupport loop := by
  cases hsupport : loop.handoff.supportCertified
  · exact ⟨support,
      (sourceRefHandoff_component_false_iff_lawFailure
        loop.handoff support).mp
        (by simp [SourceRefHandoff.component, hsupport])⟩
  · cases htrace : loop.handoff.traceCertified
    · exact ⟨trace,
        (sourceRefHandoff_component_false_iff_lawFailure
          loop.handoff trace).mp
          (by simp [SourceRefHandoff.component, htrace])⟩
    · cases hrepair : loop.handoff.repairFrontierCertified
      · exact ⟨repairFrontier,
          (sourceRefHandoff_component_false_iff_lawFailure
            loop.handoff repairFrontier).mp
            (by simp [SourceRefHandoff.component, hrepair])⟩
      · simp [handoffHolonomyClearBool, hsupport, htrace, hrepair]
          at hclear

/-- First listed loop whose source-ref handoff support is nonempty. -/
def firstHandoffObstructingLoop? :
    List SourceRefHandoffLoop -> Option SourceRefHandoffLoop
  | [] => none
  | loop :: rest =>
      if handoffHolonomyClearBool loop = true then
        firstHandoffObstructingLoop? rest
      else
        some loop

/-- A returned first handoff obstruction is listed in the supplied order. -/
theorem firstHandoffObstructingLoop?_some_mem :
    forall {loops : List SourceRefHandoffLoop} {loop : SourceRefHandoffLoop},
      firstHandoffObstructingLoop? loops = some loop ->
        loop ∈ loops
  | [], _loop, hsome => by
      cases hsome
  | head :: rest, loop, hsome => by
      by_cases hhead : handoffHolonomyClearBool head = true
      · have htail :
            firstHandoffObstructingLoop? rest = some loop := by
          simpa [firstHandoffObstructingLoop?, hhead] using hsome
        exact List.mem_cons_of_mem head
          (firstHandoffObstructingLoop?_some_mem htail)
      · have hloop : loop = head := by
          simpa [firstHandoffObstructingLoop?, hhead] using hsome.symm
        subst hloop
        simp

/-- A returned first handoff obstruction has nonempty handoff support. -/
theorem firstHandoffObstructingLoop?_some_nonemptySupport :
    forall {loops : List SourceRefHandoffLoop} {loop : SourceRefHandoffLoop},
      firstHandoffObstructingLoop? loops = some loop ->
        HasHandoffHolonomySupport loop
  | [], _loop, hsome => by
      cases hsome
  | head :: rest, loop, hsome => by
      by_cases hhead : handoffHolonomyClearBool head = true
      · have htail :
            firstHandoffObstructingLoop? rest = some loop := by
          simpa [firstHandoffObstructingLoop?, hhead] using hsome
        exact firstHandoffObstructingLoop?_some_nonemptySupport htail
      · have hloop : loop = head := by
          simpa [firstHandoffObstructingLoop?, hhead] using hsome.symm
        have hfalse : handoffHolonomyClearBool head = false := by
          cases hbool : handoffHolonomyClearBool head
          · rfl
          · exact False.elim (hhead hbool)
        simpa [hloop] using
          hasHandoffHolonomySupport_of_clearBool_false hfalse

/-- A returned first handoff obstruction carries a source-ref law failure. -/
theorem firstHandoffObstructingLoop?_some_failure
    {loops : List SourceRefHandoffLoop}
    {loop : SourceRefHandoffLoop}
    (hfirst : firstHandoffObstructingLoop? loops = some loop) :
    exists _failure : SourceRefHandoffFailure loop.handoff, True := by
  rcases firstHandoffObstructingLoop?_some_nonemptySupport hfirst with
    ⟨component, hsupport⟩
  exact
    ⟨sourceRefHandoffFailure_of_handoffHolonomySupport hsupport,
      trivial⟩

/-- A returned first handoff obstruction carries a derived bridge obstruction. -/
theorem firstHandoffObstructingLoop?_some_bridgeObstruction
    {loops : List SourceRefHandoffLoop}
    {loop : SourceRefHandoffLoop}
    (hfirst : firstHandoffObstructingLoop? loops = some loop) :
    exists _obstruction : BridgeObstruction loop.handoff.toBridgeCertificate,
      True := by
  rcases firstHandoffObstructingLoop?_some_failure hfirst with
    ⟨failure, _⟩
  exact ⟨sourceRefHandoffFailure_bridgeObstruction failure, trivial⟩

/-- A returned first handoff obstruction has nonempty loop holonomy support. -/
theorem firstHandoffObstructingLoop?_some_loopHolonomySupport
    {loops : List SourceRefHandoffLoop}
    {loop : SourceRefHandoffLoop}
    (hfirst : firstHandoffObstructingLoop? loops = some loop) :
    HasHolonomySupport loop.toRouteLoop := by
  rcases firstHandoffObstructingLoop?_some_nonemptySupport hfirst with
    ⟨component, hsupport⟩
  exact ⟨component,
    (handoffHolonomySupport_iff_loopHolonomySupport
      loop component).mp hsupport⟩

/-- A returned first handoff obstruction rules out atlas interaction exactness. -/
theorem firstHandoffObstructingLoop?_some_obstructs_atlasInteractionExact
    {loops : List SourceRefHandoffLoop}
    {loop : SourceRefHandoffLoop}
    (hfirst : firstHandoffObstructingLoop? loops = some loop) :
    Not (HandoffAtlasInteractionExact { loops := loops }) := by
  intro hexact
  rcases firstHandoffObstructingLoop?_some_failure hfirst with
    ⟨failure, _⟩
  exact
    sourceRefHandoffFailure_obstructs_interactionExact
      loop.bridge_eq failure
      (hexact loop (firstHandoffObstructingLoop?_some_mem hfirst))

/-! ## Concrete mixed and aligned source-ref handoff atlases -/

/-- Handoff-clear loop using the aligned source-ref handoff comparator. -/
def alignedSourceRefHandoffLoop : SourceRefHandoffLoop where
  name := stable
  state := alignedSourceRefHandoffState
  handoff := alignedSourceRefHandoff
  bridge_eq := rfl

/-- Handoff loop whose trace-token source-ref law is obstructed. -/
def traceRenamedSourceRefHandoffLoop : SourceRefHandoffLoop where
  name := handoff
  state := sourceRefHandoffBridgeBrokenState
  handoff := traceRenamedHandoff
  bridge_eq := rfl

@[simp] theorem alignedSourceRefHandoffLoop_clearBool :
    handoffHolonomyClearBool alignedSourceRefHandoffLoop = true :=
  rfl

@[simp] theorem traceRenamedSourceRefHandoffLoop_clearBool :
    handoffHolonomyClearBool traceRenamedSourceRefHandoffLoop = false :=
  rfl

/-- Mixed source-ref atlas: one aligned loop followed by one handoff obstruction. -/
def mixedSourceRefHandoffAtlas : SourceRefHandoffAtlas where
  loops := [alignedSourceRefHandoffLoop, traceRenamedSourceRefHandoffLoop]

/-- Positive comparator atlas: every listed handoff loop is aligned. -/
def alignedSourceRefHandoffAtlas : SourceRefHandoffAtlas where
  loops := [alignedSourceRefHandoffLoop]

/-- The mixed source-ref handoff atlas is locally exact on all listed loops. -/
theorem mixedSourceRefHandoffAtlas_localExact :
    HandoffAtlasLocalExact mixedSourceRefHandoffAtlas := by
  intro loop hmem
  simp [mixedSourceRefHandoffAtlas] at hmem
  rcases hmem with hloop | hloop
  · subst hloop
    exact alignedSourceRefHandoff_interactionExact.1
  · subst hloop
    exact sourceRefHandoffBridgeBroken_productLocalExact

/-- The mixed source-ref atlas selects the trace-renamed loop as first obstruction. -/
theorem mixedSourceRefHandoffAtlas_firstObstructingLoop :
    firstHandoffObstructingLoop? mixedSourceRefHandoffAtlas.loops =
      some traceRenamedSourceRefHandoffLoop := by
  simp [mixedSourceRefHandoffAtlas, firstHandoffObstructingLoop?]

/-- The mixed source-ref atlas is locally exact but not interaction exact. -/
theorem mixedSourceRefHandoffAtlas_not_interactionExact :
    HandoffAtlasLocalExact mixedSourceRefHandoffAtlas /\
      Not (HandoffAtlasInteractionExact mixedSourceRefHandoffAtlas) :=
  ⟨mixedSourceRefHandoffAtlas_localExact,
    firstHandoffObstructingLoop?_some_obstructs_atlasInteractionExact
      mixedSourceRefHandoffAtlas_firstObstructingLoop⟩

/-- The aligned source-ref handoff comparator atlas is interaction exact. -/
theorem alignedSourceRefHandoffAtlas_interactionExact :
    HandoffAtlasInteractionExact alignedSourceRefHandoffAtlas := by
  intro loop hmem
  simp [alignedSourceRefHandoffAtlas] at hmem
  subst hmem
  exact alignedSourceRefHandoff_interactionExact

/-! ## Theorem package -/

/--
Cycle-60 theorem package: source-ref handoff law failure, derived bridge
obstruction, loop holonomy support, first obstruction, and atlas interaction
failure are the same bounded finite correspondence.
-/
theorem sourceRefHandoffHolonomyCorrespondence_package :
    HandoffAtlasInteractionExact alignedSourceRefHandoffAtlas /\
      HandoffAtlasLocalExact mixedSourceRefHandoffAtlas /\
      HasHandoffHolonomySupport traceRenamedSourceRefHandoffLoop /\
      HasHolonomySupport traceRenamedSourceRefHandoffLoop.toRouteLoop /\
      firstHandoffObstructingLoop? mixedSourceRefHandoffAtlas.loops =
        some traceRenamedSourceRefHandoffLoop /\
      (exists _failure :
        SourceRefHandoffFailure traceRenamedSourceRefHandoffLoop.handoff,
        True) /\
      (exists _obstruction :
        BridgeObstruction traceRenamedSourceRefHandoffLoop.handoff.toBridgeCertificate,
        True) /\
      Not (HandoffAtlasInteractionExact mixedSourceRefHandoffAtlas) /\
      (forall loop component,
        HandoffHolonomySupport loop component <->
          HolonomySupport loop.toRouteLoop component) /\
      (forall loop,
        HandoffHolonomyClear loop <->
          LoopHolonomyClear loop.toRouteLoop) /\
      (forall atlas,
        HandoffAtlasLocalExact atlas <->
          AtlasLocalExact atlas.toRouteAtlas) /\
      (forall atlas,
        HandoffAtlasHolonomyVanishes atlas <->
          AtlasHolonomyVanishes atlas.toRouteAtlas) /\
      (forall atlas,
        HandoffAtlasInteractionExact atlas <->
          RouteAtlasInteractionExact atlas.toRouteAtlas) /\
      (forall atlas,
        HandoffAtlasInteractionExact atlas <->
          HandoffAtlasLocalExact atlas /\
            HandoffAtlasHolonomyVanishes atlas) /\
      (forall loops loop,
        firstHandoffObstructingLoop? loops = some loop ->
          loop ∈ loops /\
            HasHandoffHolonomySupport loop /\
            HasHolonomySupport loop.toRouteLoop /\
            (exists _failure :
              SourceRefHandoffFailure loop.handoff, True) /\
            (exists _obstruction :
              BridgeObstruction loop.handoff.toBridgeCertificate, True) /\
            Not (HandoffAtlasInteractionExact { loops := loops })) := by
  exact
    ⟨alignedSourceRefHandoffAtlas_interactionExact,
      mixedSourceRefHandoffAtlas_localExact,
      firstHandoffObstructingLoop?_some_nonemptySupport
        mixedSourceRefHandoffAtlas_firstObstructingLoop,
      firstHandoffObstructingLoop?_some_loopHolonomySupport
        mixedSourceRefHandoffAtlas_firstObstructingLoop,
      mixedSourceRefHandoffAtlas_firstObstructingLoop,
      firstHandoffObstructingLoop?_some_failure
        mixedSourceRefHandoffAtlas_firstObstructingLoop,
      firstHandoffObstructingLoop?_some_bridgeObstruction
        mixedSourceRefHandoffAtlas_firstObstructingLoop,
      mixedSourceRefHandoffAtlas_not_interactionExact.2,
      handoffHolonomySupport_iff_loopHolonomySupport,
      handoffHolonomyClear_iff_loopHolonomyClear,
      handoffAtlasLocalExact_iff_routeAtlasLocalExact,
      handoffAtlasHolonomyVanishes_iff_routeAtlasHolonomyVanishes,
      handoffAtlasInteractionExact_iff_routeAtlasInteractionExact,
      handoffAtlasInteractionExact_iff_localAndHandoffHolonomyClear,
      fun loops loop hfirst =>
        ⟨firstHandoffObstructingLoop?_some_mem hfirst,
          firstHandoffObstructingLoop?_some_nonemptySupport hfirst,
          firstHandoffObstructingLoop?_some_loopHolonomySupport hfirst,
          firstHandoffObstructingLoop?_some_failure hfirst,
          firstHandoffObstructingLoop?_some_bridgeObstruction hfirst,
          firstHandoffObstructingLoop?_some_obstructs_atlasInteractionExact
            hfirst⟩⟩

end SourceRefHandoffHolonomyCorrespondence
end QualitySurface
end ResearchLean.AG
