import Formal.AG.Evolution.StateTransition

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
PRD-9 R3 / AC9 temporal law surface.

Temporal laws are selected predicates/equation packages over a fixed
state-transition presheaf.  They do not assert anything about unselected
runtime traces or future paths.
-/

/-- IX.§3 / AC9: selected temporal law vocabulary from PRD-9 R3. -/
inductive TemporalLawKind where
  | closedTemporalEquation
  | commutativeTemporalSquare
  | replayIdempotence
  | encodeDecodeCompatibility
  | compensationCompatibility
  | migrationCompatibility
  | descentTemporalLaw
  deriving DecidableEq, Repr

/--
IX.§3 / AC9: temporal law relative to a selected state-transition presheaf.

The law is a selected family of predicates/equations over states, local
transitions, and incidence legs of `Tr_E × X`.
-/
structure TemporalLaw {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T) where
  kind : TemporalLawKind
  Witness : Type (max u y)
  source : Witness -> T.Point
  target : Witness -> T.Point
  incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w)
  stateEquation :
    ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop
  transitionPredicate :
    ∀ w : Witness, {x y' : St.State (source w)} ->
      St.Transition (source w) x y' -> Prop
  descentPredicate :
    ∀ w : Witness, St.State (source w) -> Prop

namespace TemporalLaw

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}

/-- IX.§3 / AC9: read the selected incidence leg scoped by a temporal law witness. -/
def selectedIncidence (L : TemporalLaw St) (w : L.Witness) :
    T.IncidenceLeg (L.source w) (L.target w) :=
  L.incidence w

/-- IX.§3 / AC9: evaluate the selected state equation of a temporal law. -/
def holdsStateEquation (L : TemporalLaw St) (w : L.Witness)
    (x : St.State (L.source w)) (y' : St.State (L.target w)) : Prop :=
  L.stateEquation w x y'

/-- IX.§3 / AC9: evaluate the selected transition predicate of a temporal law. -/
def holdsTransition (L : TemporalLaw St) (w : L.Witness)
    {x y' : St.State (L.source w)}
    (tr : St.Transition (L.source w) x y') : Prop :=
  L.transitionPredicate w tr

/-- IX.§3 / AC9: evaluate the selected descent predicate of a temporal law. -/
def holdsDescent (L : TemporalLaw St) (w : L.Witness)
    (x : St.State (L.source w)) : Prop :=
  L.descentPredicate w x

end TemporalLaw

end Evolution
end AAT.AG
