import Formal.AG.Evolution.TemporalCoefficient

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R3 / AC7--AC8 state-transition presheaf surface.

The state-transition surface is relative to one selected temporal site.  It
separates architecture-context restriction from selected trace transport and
records the identity/composition laws needed by later temporal laws.
-/

/--
IX.§3 / AC7: state-transition presheaf `St_A` over the selected temporal site.

`restrictContext` is contravariant in the architecture context direction.
`transportTrace` is covariant along selected trace arrows.  The mixed square is
recorded explicitly so later laws can use the selected `Tr_E × X` product
surface without claiming an ambient runtime trace.
-/
structure StateTransitionPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    (T : TemporalSite S E) where
  State : T.Point -> Type (max u y)
  Transition : ∀ p : T.Point, State p -> State p -> Type (max u y)
  transitionId : ∀ p : T.Point, (x : State p) -> Transition p x x
  transitionComp :
    ∀ p : T.Point, {x y z' : State p} ->
      Transition p x y -> Transition p y z' -> Transition p x z'
  restrictContext :
    ∀ (t : E.trace.Obj) {i j : T.siteRegime.ContextIndex},
      T.siteRegime.contextLe i j -> State (t, j) -> State (t, i)
  restrictContext_id :
    ∀ (t : E.trace.Obj) (i : T.siteRegime.ContextIndex) (x : State (t, i)),
      restrictContext t (T.siteRegime.contextLe_refl i) x = x
  restrictContext_comp :
    ∀ (t : E.trace.Obj) {i j k : T.siteRegime.ContextIndex}
      (hij : T.siteRegime.contextLe i j) (hjk : T.siteRegime.contextLe j k)
      (x : State (t, k)),
      restrictContext t hij (restrictContext t hjk x) =
        restrictContext t (T.siteRegime.contextLe_trans hij hjk) x
  transportTrace :
    ∀ {t₀ t₁ : E.trace.Obj} (e : E.trace.Hom t₀ t₁),
      T.traceRegime.selectedArrow e ->
        (i : T.siteRegime.ContextIndex) -> State (t₀, i) -> State (t₁, i)
  transportTrace_id :
    ∀ (t : E.trace.Obj) (i : T.siteRegime.ContextIndex) (x : State (t, i)),
      transportTrace (E.trace.id t) (T.traceRegime.id_selected t) i x = x
  transportTrace_comp :
    ∀ {t₀ t₁ t₂ : E.trace.Obj} (e₀ : E.trace.Hom t₀ t₁)
      (e₁ : E.trace.Hom t₁ t₂) (he₀ : T.traceRegime.selectedArrow e₀)
      (he₁ : T.traceRegime.selectedArrow e₁) (i : T.siteRegime.ContextIndex)
      (x : State (t₀, i)),
      transportTrace e₁ he₁ i (transportTrace e₀ he₀ i x) =
        transportTrace (E.trace.comp e₀ e₁)
          (T.traceRegime.comp_selected he₀ he₁) i x
  restrict_transport_commute :
    ∀ {t₀ t₁ : E.trace.Obj} (e : E.trace.Hom t₀ t₁)
      (he : T.traceRegime.selectedArrow e)
      {i j : T.siteRegime.ContextIndex} (hij : T.siteRegime.contextLe i j)
      (x : State (t₀, j)),
      restrictContext t₁ hij (transportTrace e he j x) =
        transportTrace e he i (restrictContext t₀ hij x)

namespace StateTransitionPresheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}

/-- IX.§3 / AC7: readable alias for state at a selected temporal point. -/
abbrev StateAt (St : StateTransitionPresheaf T) (p : T.Point) : Type (max u y) :=
  St.State p

/-- IX.§3 / AC7: readable alias for transitions at a selected temporal point. -/
abbrev TransitionAt (St : StateTransitionPresheaf T) (p : T.Point)
    (x y' : St.StateAt p) : Type (max u y) :=
  St.Transition p x y'

/-- IX.§3 / AC7: restrict a state along a selected architecture-context leg. -/
def contextRestriction (St : StateTransitionPresheaf T)
    (t : E.trace.Obj) {i j : T.siteRegime.ContextIndex}
    (hij : T.siteRegime.contextLe i j) :
    St.State (t, j) -> St.State (t, i) :=
  St.restrictContext t hij

/-- IX.§3 / AC7: transport a state along a selected trace arrow. -/
def traceTransport (St : StateTransitionPresheaf T)
    {t₀ t₁ : E.trace.Obj} (e : E.trace.Hom t₀ t₁)
    (he : T.traceRegime.selectedArrow e) (i : T.siteRegime.ContextIndex) :
    St.State (t₀, i) -> St.State (t₁, i) :=
  St.transportTrace e he i

/-- IX.§3 / AC8: context restriction respects identity context legs. -/
theorem contextRestriction_identity (St : StateTransitionPresheaf T)
    (t : E.trace.Obj) (i : T.siteRegime.ContextIndex) (x : St.State (t, i)) :
    St.contextRestriction t (T.siteRegime.contextLe_refl i) x = x :=
  St.restrictContext_id t i x

/-- IX.§3 / AC8: context restriction respects composition of context legs. -/
theorem contextRestriction_composition (St : StateTransitionPresheaf T)
    (t : E.trace.Obj) {i j k : T.siteRegime.ContextIndex}
    (hij : T.siteRegime.contextLe i j) (hjk : T.siteRegime.contextLe j k)
    (x : St.State (t, k)) :
    St.contextRestriction t hij (St.contextRestriction t hjk x) =
      St.contextRestriction t (T.siteRegime.contextLe_trans hij hjk) x :=
  St.restrictContext_comp t hij hjk x

/-- IX.§3 / AC8: trace transport respects identity trace arrows. -/
theorem traceTransport_identity (St : StateTransitionPresheaf T)
    (t : E.trace.Obj) (i : T.siteRegime.ContextIndex) (x : St.State (t, i)) :
    St.traceTransport (E.trace.id t) (T.traceRegime.id_selected t) i x = x :=
  St.transportTrace_id t i x

/-- IX.§3 / AC8: trace transport respects selected trace composition. -/
theorem traceTransport_composition (St : StateTransitionPresheaf T)
    {t₀ t₁ t₂ : E.trace.Obj} (e₀ : E.trace.Hom t₀ t₁)
    (e₁ : E.trace.Hom t₁ t₂) (he₀ : T.traceRegime.selectedArrow e₀)
    (he₁ : T.traceRegime.selectedArrow e₁) (i : T.siteRegime.ContextIndex)
    (x : St.State (t₀, i)) :
    St.traceTransport e₁ he₁ i (St.traceTransport e₀ he₀ i x) =
      St.traceTransport (E.trace.comp e₀ e₁)
        (T.traceRegime.comp_selected he₀ he₁) i x :=
  St.transportTrace_comp e₀ e₁ he₀ he₁ i x

/-- IX.§3 / AC8: context restriction and trace transport form the selected square. -/
theorem context_trace_commutes (St : StateTransitionPresheaf T)
    {t₀ t₁ : E.trace.Obj} (e : E.trace.Hom t₀ t₁)
    (he : T.traceRegime.selectedArrow e)
    {i j : T.siteRegime.ContextIndex} (hij : T.siteRegime.contextLe i j)
    (x : St.State (t₀, j)) :
    St.contextRestriction t₁ hij (St.traceTransport e he j x) =
      St.traceTransport e he i (St.contextRestriction t₀ hij x) :=
  St.restrict_transport_commute e he hij x

end StateTransitionPresheaf

/--
IX.§3 / AC9: selected sheaf/descent predicate for a state-transition presheaf.

This records the selected descent predicate over a temporal cover.  It does not
construct a general sheafification.
-/
structure StateTransitionSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T) where
  cover : TemporalCover T
  CoverSection : Type (max u y)
  sectionAt :
    CoverSection -> (i : cover.Index) -> St.State (cover.chartTrace i, cover.chartContext i)
  selectedDescent : CoverSection -> Prop
  compatibleOnOverlaps : CoverSection -> Prop
  descent_implies_compatibility :
    ∀ s : CoverSection, selectedDescent s -> compatibleOnOverlaps s

namespace StateTransitionSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}

/-- IX.§3 / AC9: a selected descent section is overlap-compatible. -/
theorem descent_section_compatible (Sh : StateTransitionSheaf St)
    (s : Sh.CoverSection) (hs : Sh.selectedDescent s) :
    Sh.compatibleOnOverlaps s :=
  Sh.descent_implies_compatibility s hs

end StateTransitionSheaf

end Evolution
end AAT.AG
