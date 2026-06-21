import Formal.AG.Research.QualitySurface.HeterogeneousRouteInteraction

/-!
Cycle 58 evidence for `G-aat-quality-surface-01`.

This file packages a finite selected route atlas as a closed-route holonomy
surface.  Holonomy support is read from the supplied bridge certificate
components, but atlas interaction exactness is defined separately as
interaction exactness on every listed loop.  The result is relative to the
selected finite atlas and supplied loop order.  It does not enumerate arbitrary
route systems, prove global canonical minimality, synthesize repairs, validate
ArchMap observations, or judge whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace RouteHolonomyObstructionSupport

open HeterogeneousRouteInteraction
open BridgeComponent

/-! ## Selected closed-route atlas -/

/-- Names for the selected closed-route loops in the finite atlas. -/
inductive RouteLoopName where
  | stable
  | handoff
  deriving DecidableEq

open RouteLoopName

/--
A selected closed-route loop carries a heterogeneous route state.  The loop
name is report-facing data; exactness is read from the state.
-/
structure RouteLoop where
  name : RouteLoopName
  state : HeterogeneousRouteState

/-- A finite route atlas with its supplied loop order. -/
structure RouteAtlas where
  loops : List RouteLoop

/-! ## Holonomy support -/

/-- Holonomy support records which bridge component fails on a route loop. -/
def HolonomySupport
    (loop : RouteLoop) (component : BridgeComponent) : Prop :=
  loop.state.bridge.component component = false

/-- A route loop has some protected holonomy support. -/
def HasHolonomySupport
    (loop : RouteLoop) : Prop :=
  ∃ component, HolonomySupport loop component

/-- A route loop is holonomy-clear when every bridge component is preserved. -/
def LoopHolonomyClear
    (loop : RouteLoop) : Prop :=
  ∀ component, loop.state.bridge.component component = true

/-- Boolean clearance used by the supplied ordered scan. -/
def loopHolonomyClearBool
    (loop : RouteLoop) : Bool :=
  loop.state.bridge.supportPreserved &&
    loop.state.bridge.tracePreserved &&
    loop.state.bridge.repairFrontierPreserved

/-- Holonomy clearance is the same bridge alignment law used by interaction exactness. -/
theorem bridgeHolonomyClear_iff_bridgeAligned
    (loop : RouteLoop) :
    LoopHolonomyClear loop ↔ BridgeAligned loop.state := by
  constructor
  · intro hclear
    exact ⟨hclear support, hclear trace, hclear repairFrontier⟩
  · intro haligned component
    rcases haligned with ⟨hsupport, htrace, hrepair⟩
    cases component with
    | support =>
        simpa [LoopHolonomyClear, BridgeCertificate.component] using hsupport
    | trace =>
        simpa [LoopHolonomyClear, BridgeCertificate.component] using htrace
    | repairFrontier =>
        simpa [LoopHolonomyClear, BridgeCertificate.component] using hrepair

/-- The boolean scan predicate agrees with propositional holonomy clearance. -/
theorem loopHolonomyClearBool_eq_true_iff
    (loop : RouteLoop) :
    loopHolonomyClearBool loop = true ↔ LoopHolonomyClear loop := by
  constructor
  · intro hclear component
    cases component with
    | support =>
        cases hsupport : loop.state.bridge.supportPreserved <;>
          simp [loopHolonomyClearBool, BridgeCertificate.component,
            hsupport] at hclear ⊢
    | trace =>
        cases hsupport : loop.state.bridge.supportPreserved <;>
          cases htrace : loop.state.bridge.tracePreserved <;>
            simp [loopHolonomyClearBool, BridgeCertificate.component,
              hsupport, htrace] at hclear ⊢
    | repairFrontier =>
        cases hsupport : loop.state.bridge.supportPreserved <;>
          cases htrace : loop.state.bridge.tracePreserved <;>
            cases hrepair : loop.state.bridge.repairFrontierPreserved <;>
              simp [loopHolonomyClearBool, BridgeCertificate.component,
                hsupport, htrace, hrepair] at hclear ⊢
  · intro hclear
    have hsupport : loop.state.bridge.supportPreserved = true := by
      simpa [BridgeCertificate.component] using hclear support
    have htrace : loop.state.bridge.tracePreserved = true := by
      simpa [BridgeCertificate.component] using hclear trace
    have hrepair :
        loop.state.bridge.repairFrontierPreserved = true := by
      simpa [BridgeCertificate.component] using hclear repairFrontier
    simp [loopHolonomyClearBool, hsupport, htrace, hrepair]

/-- A false boolean clearance exposes a nonempty holonomy support. -/
theorem hasHolonomySupport_of_clearBool_false
    {loop : RouteLoop}
    (hclear : loopHolonomyClearBool loop = false) :
    HasHolonomySupport loop := by
  cases hsupport : loop.state.bridge.supportPreserved
  · exact ⟨support, by
      simp [HolonomySupport, BridgeCertificate.component, hsupport]⟩
  · cases htrace : loop.state.bridge.tracePreserved
    · exact ⟨trace, by
        simp [HolonomySupport, BridgeCertificate.component, htrace]⟩
    · cases hrepair : loop.state.bridge.repairFrontierPreserved
      · exact ⟨repairFrontier, by
          simp [HolonomySupport, BridgeCertificate.component, hrepair]⟩
      · simp [loopHolonomyClearBool, hsupport, htrace, hrepair] at hclear

/-- Holonomy support is a bridge obstruction certificate. -/
def bridgeObstruction_of_holonomySupport
    {loop : RouteLoop}
    {component : BridgeComponent}
    (hsupport : HolonomySupport loop component) :
    BridgeObstruction loop.state.bridge where
  component := component
  fails := hsupport

/-! ## Atlas exactness and holonomy vanishing -/

/-- Every listed loop is locally exact before reading closed-route holonomy. -/
def AtlasLocalExact
    (atlas : RouteAtlas) : Prop :=
  ∀ loop, loop ∈ atlas.loops -> ProductLocalExact loop.state

/-- All listed loop holonomy supports vanish. -/
def AtlasHolonomyVanishes
    (atlas : RouteAtlas) : Prop :=
  ∀ loop, loop ∈ atlas.loops -> LoopHolonomyClear loop

/-- Atlas-level interaction exactness is interaction exactness on every listed loop. -/
def RouteAtlasInteractionExact
    (atlas : RouteAtlas) : Prop :=
  ∀ loop, loop ∈ atlas.loops -> InteractionExact loop.state

/--
With local exactness fixed, loop holonomy clearance is equivalent to
interaction exactness for that loop.
-/
theorem routeLoopHolonomyClear_iff_interactionExact_of_local
    {loop : RouteLoop}
    (hlocal : ProductLocalExact loop.state) :
    LoopHolonomyClear loop ↔ InteractionExact loop.state := by
  constructor
  · intro hclear
    exact ⟨hlocal, (bridgeHolonomyClear_iff_bridgeAligned loop).mp hclear⟩
  · intro hexact
    exact (bridgeHolonomyClear_iff_bridgeAligned loop).mpr hexact.2

/--
Atlas interaction exactness is equivalent to local exactness plus vanishing
holonomy support on every listed loop.
-/
theorem routeAtlasInteractionExact_iff_localAndHolonomyClear
    (atlas : RouteAtlas) :
    RouteAtlasInteractionExact atlas ↔
      AtlasLocalExact atlas ∧ AtlasHolonomyVanishes atlas := by
  constructor
  · intro hexact
    constructor
    · intro loop hmem
      exact (hexact loop hmem).1
    · intro loop hmem
      exact (bridgeHolonomyClear_iff_bridgeAligned loop).mpr
        (hexact loop hmem).2
  · intro hpair loop hmem
    exact ((routeLoopHolonomyClear_iff_interactionExact_of_local
      (hpair.1 loop hmem)).mp (hpair.2 loop hmem))

/-! ## Ordered first obstructing loop -/

/-- The first listed loop whose closed-route holonomy support is nonempty. -/
def firstObstructingLoop? : List RouteLoop -> Option RouteLoop
  | [] => none
  | loop :: rest =>
      if loopHolonomyClearBool loop = true then
        firstObstructingLoop? rest
      else
        some loop

/-- The first obstructing loop is a member of the supplied loop order. -/
theorem firstObstructingLoop?_some_mem :
    ∀ {loops : List RouteLoop} {loop : RouteLoop},
      firstObstructingLoop? loops = some loop ->
        loop ∈ loops
  | [], _loop, hsome => by
      cases hsome
  | head :: rest, loop, hsome => by
      by_cases hhead : loopHolonomyClearBool head = true
      · have htail :
            firstObstructingLoop? rest = some loop := by
          simpa [firstObstructingLoop?, hhead] using hsome
        exact List.mem_cons_of_mem head
          (firstObstructingLoop?_some_mem htail)
      · have hloop : loop = head := by
          simpa [firstObstructingLoop?, hhead] using hsome.symm
        subst hloop
        simp

/-- A returned loop has nonempty holonomy support. -/
theorem firstObstructingLoop?_some_nonemptySupport :
    ∀ {loops : List RouteLoop} {loop : RouteLoop},
      firstObstructingLoop? loops = some loop ->
        HasHolonomySupport loop
  | [], _loop, hsome => by
      cases hsome
  | head :: rest, loop, hsome => by
      by_cases hhead : loopHolonomyClearBool head = true
      · have htail :
            firstObstructingLoop? rest = some loop := by
          simpa [firstObstructingLoop?, hhead] using hsome
        exact firstObstructingLoop?_some_nonemptySupport htail
      · have hloop : loop = head := by
          simpa [firstObstructingLoop?, hhead] using hsome.symm
        have hfalse : loopHolonomyClearBool head = false := by
          cases hbool : loopHolonomyClearBool head
          · rfl
          · exact False.elim (hhead hbool)
        simpa [hloop] using hasHolonomySupport_of_clearBool_false hfalse

/-- A returned loop carries an explicit bridge obstruction certificate. -/
theorem firstObstructingLoop?_some_bridgeObstruction
    {loops : List RouteLoop}
    {loop : RouteLoop}
    (hfirst : firstObstructingLoop? loops = some loop) :
    ∃ _obstruction : BridgeObstruction loop.state.bridge, True := by
  rcases firstObstructingLoop?_some_nonemptySupport hfirst with
    ⟨component, hsupport⟩
  exact ⟨bridgeObstruction_of_holonomySupport hsupport, trivial⟩

/-- A returned first obstruction rules out atlas interaction exactness. -/
theorem firstObstructingLoop?_some_obstructs_atlasInteractionExact
    {loops : List RouteLoop}
    {loop : RouteLoop}
    (hfirst : firstObstructingLoop? loops = some loop) :
    ¬ RouteAtlasInteractionExact { loops := loops } := by
  intro hexact
  rcases firstObstructingLoop?_some_bridgeObstruction hfirst with
    ⟨obstruction, _⟩
  exact bridgeObstruction_obstructs_interactionExact obstruction
    (hexact loop (firstObstructingLoop?_some_mem hfirst))

/-- No first obstruction is equivalent to vanishing holonomy on the supplied order. -/
theorem firstObstructingLoop?_none_iff_holonomyVanishes :
    ∀ loops : List RouteLoop,
      firstObstructingLoop? loops = none ↔
        AtlasHolonomyVanishes { loops := loops }
  | [] => by
      constructor
      · intro _ loop hmem
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone loop hmem
        by_cases hhead : loopHolonomyClearBool head = true
        · have htail :
              firstObstructingLoop? rest = none := by
            simpa [firstObstructingLoop?, hhead] using hnone
          cases hmem with
          | head =>
              exact (loopHolonomyClearBool_eq_true_iff head).mp hhead
          | tail _ hlisted =>
              exact ((firstObstructingLoop?_none_iff_holonomyVanishes
                rest).mp htail) loop hlisted
        · have hsome :
              firstObstructingLoop? (head :: rest) = some head := by
            simp [firstObstructingLoop?, hhead]
          rw [hsome] at hnone
          cases hnone
      · intro hvans
        have hhead : loopHolonomyClearBool head = true :=
          (loopHolonomyClearBool_eq_true_iff head).mpr
            (hvans head (by simp))
        have htail :
            firstObstructingLoop? rest = none :=
          (firstObstructingLoop?_none_iff_holonomyVanishes rest).mpr
            (by
              intro loop hmem
              exact hvans loop (by simp [hmem]))
        simp [firstObstructingLoop?, hhead, htail]

/-! ## Concrete mixed and aligned atlases -/

/-- A holonomy-clear loop carrying the bridge-aligned comparator state. -/
def alignedLoop : RouteLoop where
  name := stable
  state := bridgeAlignedInteractionState

/-- A loop whose trace handoff bridge component is obstructed. -/
def bridgeBrokenLoop : RouteLoop where
  name := handoff
  state := productExactBridgeBrokenState

@[simp] theorem alignedLoop_clearBool :
    loopHolonomyClearBool alignedLoop = true :=
  rfl

@[simp] theorem bridgeBrokenLoop_clearBool :
    loopHolonomyClearBool bridgeBrokenLoop = false :=
  rfl

/-- The selected mixed atlas has one aligned loop followed by one obstructed loop. -/
def mixedHolonomyAtlas : RouteAtlas where
  loops := [alignedLoop, bridgeBrokenLoop]

/-- The positive comparator atlas has only the aligned loop. -/
def alignedHolonomyAtlas : RouteAtlas where
  loops := [alignedLoop]

/-- The mixed atlas is locally exact on every listed loop. -/
theorem mixedHolonomyAtlas_localExact :
    AtlasLocalExact mixedHolonomyAtlas := by
  intro loop hmem
  simp [mixedHolonomyAtlas] at hmem
  rcases hmem with hloop | hloop
  · subst hloop
    exact bridgeAlignedInteractionState_interactionExact.1
  · subst hloop
    exact productExactBridgeBroken_productLocalExact

/-- The mixed atlas has nonempty holonomy support on its handoff loop. -/
theorem mixedHolonomyAtlas_handoff_nonemptySupport :
    HasHolonomySupport bridgeBrokenLoop :=
  hasHolonomySupport_of_clearBool_false bridgeBrokenLoop_clearBool

/-- The ordered scan selects the handoff loop as the first obstruction. -/
theorem mixedHolonomyAtlas_firstObstructingLoop :
    firstObstructingLoop? mixedHolonomyAtlas.loops =
      some bridgeBrokenLoop := by
  simp [mixedHolonomyAtlas, firstObstructingLoop?]

/-- The first obstruction in the mixed atlas carries a bridge obstruction certificate. -/
theorem mixedHolonomyAtlas_firstObstructionCertificate :
    ∃ _obstruction : BridgeObstruction bridgeBrokenLoop.state.bridge, True :=
  firstObstructingLoop?_some_bridgeObstruction
    mixedHolonomyAtlas_firstObstructingLoop

/-- The mixed atlas is locally exact but not interaction exact. -/
theorem mixedHolonomyAtlas_not_interactionExact :
    AtlasLocalExact mixedHolonomyAtlas ∧
      ¬ RouteAtlasInteractionExact mixedHolonomyAtlas := by
  exact ⟨mixedHolonomyAtlas_localExact,
    firstObstructingLoop?_some_obstructs_atlasInteractionExact
      mixedHolonomyAtlas_firstObstructingLoop⟩

/-- The aligned comparator atlas is interaction exact. -/
theorem alignedHolonomyAtlas_interactionExact :
    RouteAtlasInteractionExact alignedHolonomyAtlas := by
  intro loop hmem
  simp [alignedHolonomyAtlas] at hmem
  subst hmem
  exact bridgeAlignedInteractionState_interactionExact

/-- The aligned comparator has vanishing holonomy. -/
theorem alignedHolonomyAtlas_holonomyVanishes :
    AtlasHolonomyVanishes alignedHolonomyAtlas :=
  (routeAtlasInteractionExact_iff_localAndHolonomyClear
    alignedHolonomyAtlas).mp alignedHolonomyAtlas_interactionExact |>.2

/-! ## Theorem package -/

/--
Cycle-58 theorem package: a finite selected route atlas has interaction
exactness exactly when local exactness and closed-route holonomy vanishing both
hold; a nonzero holonomy support yields a first obstructing loop and bridge
obstruction certificate.
-/
theorem routeAtlasHolonomyObstruction_package :
    RouteAtlasInteractionExact alignedHolonomyAtlas ∧
      AtlasLocalExact mixedHolonomyAtlas ∧
      HasHolonomySupport bridgeBrokenLoop ∧
      firstObstructingLoop? mixedHolonomyAtlas.loops =
        some bridgeBrokenLoop ∧
      (∃ _obstruction : BridgeObstruction bridgeBrokenLoop.state.bridge, True) ∧
      ¬ RouteAtlasInteractionExact mixedHolonomyAtlas ∧
      (∀ atlas : RouteAtlas,
        RouteAtlasInteractionExact atlas ↔
          AtlasLocalExact atlas ∧ AtlasHolonomyVanishes atlas) ∧
      (∀ loops loop,
        firstObstructingLoop? loops = some loop ->
          loop ∈ loops ∧
            HasHolonomySupport loop ∧
            (∃ _obstruction : BridgeObstruction loop.state.bridge, True) ∧
            ¬ RouteAtlasInteractionExact { loops := loops }) ∧
      (∀ loops,
        firstObstructingLoop? loops = none ↔
          AtlasHolonomyVanishes { loops := loops }) := by
  exact ⟨alignedHolonomyAtlas_interactionExact,
    mixedHolonomyAtlas_localExact,
    mixedHolonomyAtlas_handoff_nonemptySupport,
    mixedHolonomyAtlas_firstObstructingLoop,
    mixedHolonomyAtlas_firstObstructionCertificate,
    mixedHolonomyAtlas_not_interactionExact.2,
    routeAtlasInteractionExact_iff_localAndHolonomyClear,
    fun loops loop hfirst =>
      ⟨firstObstructingLoop?_some_mem hfirst,
        firstObstructingLoop?_some_nonemptySupport hfirst,
        firstObstructingLoop?_some_bridgeObstruction hfirst,
        firstObstructingLoop?_some_obstructs_atlasInteractionExact hfirst⟩,
    firstObstructingLoop?_none_iff_holonomyVanishes⟩

end RouteHolonomyObstructionSupport
end QualitySurface
end Formal.AG.Research
