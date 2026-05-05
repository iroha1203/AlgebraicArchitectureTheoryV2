import Formal.Arch.Evolution.ArchitectureEvolution

namespace Formal.Arch

universe u v w

/--
An observation schema from architecture states to a signature domain.

The schema is intentionally generic in `Sig`: concrete `ArchitectureSignatureV1`
and dataset-facing signed measurements can be connected in later modules without
making this core depend on PRs, AI patch distributions, or report schemas.
-/
structure SignatureObservation (State : Type u) (Sig : Type v) where
  observe : State -> Sig
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace SignatureObservation

variable {State : Type u} {Sig : Type v}

/-- A state has the selected observed signature. -/
def Observes (O : SignatureObservation State Sig) (X : State) (sig : Sig) :
    Prop :=
  O.observe X = sig

/-- The observation package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (O : SignatureObservation State Sig) : Prop :=
  O.nonConclusions

end SignatureObservation

/--
An abstract delta operation on signatures.

No algebraic laws are assumed here. Endpoint and telescoping theorems can later
specialize this schema with additive or signed delta structure as needed.
-/
structure SignatureDelta (Sig : Type v) (Delta : Type w) where
  delta : Sig -> Sig -> Delta
  nonConclusions : Prop

namespace SignatureDelta

variable {Sig : Type v} {Delta : Type w}

/-- The selected abstract delta between two signatures. -/
def between (D : SignatureDelta Sig Delta) (source target : Sig) : Delta :=
  D.delta source target

/-- The delta package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (D : SignatureDelta Sig Delta) : Prop :=
  D.nonConclusions

end SignatureDelta

variable {State : Type u} {Sig : Type v} {Delta : Type w}

/--
Observe every state visited by an endpoint-indexed architecture evolution path.

For a path `X -> ... -> Y`, the resulting list starts with the observation of
`X` and ends with the observation of `Y`. The endpoint theorem is left as the
next proof obligation.
-/
def SignatureTrajectory (O : SignatureObservation State Sig) :
    {X Y : State} -> ArchitectureEvolution State X Y -> List Sig
  | X, _, ArchitecturePath.nil _ => [O.observe X]
  | X, _, ArchitecturePath.cons _step rest =>
      O.observe X :: SignatureTrajectory O rest

/--
Observe the per-step signature deltas along an architecture evolution path.

The list has one delta for each primitive transition. Net delta aggregation and
telescoping laws are intentionally deferred to the theorem package for #640.
-/
def SignatureDeltaSequence
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta) :
    {X Y : State} -> ArchitectureEvolution State X Y -> List Delta
  | _, _, ArchitecturePath.nil _ => []
  | X, _, ArchitecturePath.cons (Y := Y) _step rest =>
      D.between (O.observe X) (O.observe Y) ::
        SignatureDeltaSequence O D rest

end Formal.Arch
