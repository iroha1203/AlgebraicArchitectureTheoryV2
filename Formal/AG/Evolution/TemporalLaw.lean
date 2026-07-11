import Formal.AG.Evolution.StateTransition

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R3 / AC9 temporal law surface.

Temporal laws are selected predicates/equation packages over a fixed
state-transition presheaf.  They do not assert anything about unselected
runtime traces or future paths.
-/

/-- IX.§3 / AC9: selected temporal law vocabulary from Part IX R3. -/
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

/--
IX-4: canonical constructor for a temporal law whose load-bearing content is a
selected state equation. Transition and descent predicates are set to `True`,
so theorem users can see that this constructor contributes only the chosen
state equation and kind.
-/
def ofStateEquation
    (kind : TemporalLawKind)
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St where
  kind := kind
  Witness := Witness
  source := source
  target := target
  incidence := incidence
  stateEquation := stateEquation
  transitionPredicate := fun _w {_x _y} _tr => True
  descentPredicate := fun _w _x => True

/-- IX-4: canonical closed temporal-equation law. -/
def closedTemporalEquation
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .closedTemporalEquation Witness source target incidence stateEquation

/-- IX-4: canonical commutative temporal-square law. -/
def commutativeTemporalSquare
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .commutativeTemporalSquare Witness source target incidence stateEquation

/-- IX-4: canonical replay-idempotence law. -/
def replayIdempotence
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .replayIdempotence Witness source target incidence stateEquation

/-- IX-4: canonical encode/decode compatibility law. -/
def encodeDecodeCompatibility
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .encodeDecodeCompatibility Witness source target incidence stateEquation

/-- IX-4: canonical compensation compatibility law. -/
def compensationCompatibility
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .compensationCompatibility Witness source target incidence stateEquation

/-- IX-4: canonical migration compatibility law. -/
def migrationCompatibility
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .migrationCompatibility Witness source target incidence stateEquation

/-- IX-4: canonical descent temporal law. -/
def descentTemporalLaw
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    TemporalLaw St :=
  ofStateEquation .descentTemporalLaw Witness source target incidence stateEquation

@[simp] theorem ofStateEquation_kind
    (kind : TemporalLawKind)
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop) :
    (ofStateEquation (St := St) kind Witness source target incidence stateEquation).kind = kind :=
  rfl

@[simp] theorem ofStateEquation_holdsStateEquation
    (kind : TemporalLawKind)
    (Witness : Type (max u y))
    (source target : Witness -> T.Point)
    (incidence : ∀ w : Witness, T.IncidenceLeg (source w) (target w))
    (stateEquation :
      ∀ w : Witness, St.State (source w) -> St.State (target w) -> Prop)
    (w : Witness) (x : St.State (source w)) (y' : St.State (target w)) :
    (ofStateEquation (St := St) kind Witness source target incidence stateEquation).stateEquation
        w x y' =
      stateEquation w x y' :=
  rfl

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
