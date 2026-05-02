namespace Formal.Arch

universe u v

/--
A finite architecture evolution path.

`Step X Y` is the chosen family of primitive architecture operations from state
`X` to state `Y`. The path index records both endpoints, so later preservation
theorems cannot confuse the start and target architecture states.
-/
inductive ArchitecturePath {State : Type u}
    (Step : State -> State -> Type v) : State -> State -> Type (max u v) where
  | nil (X : State) : ArchitecturePath Step X X
  | cons {X Y Z : State} :
      Step X Y -> ArchitecturePath Step Y Z -> ArchitecturePath Step X Z

namespace ArchitecturePath

variable {State : Type u} {Step : State -> State -> Type v}

/-- The endpoint obtained by applying a path to its starting state. -/
def ApplyPath (X : State) {Y : State}
    (_p : ArchitecturePath Step X Y) : State :=
  Y

/-- Number of primitive architecture steps in a finite path. -/
def length : {X Y : State} -> ArchitecturePath Step X Y -> Nat
  | _, _, nil _ => 0
  | _, _, cons _ rest => rest.length + 1

/-- Concatenate two architecture paths. -/
def append : {X Y Z : State} ->
    ArchitecturePath Step X Y -> ArchitecturePath Step Y Z ->
      ArchitecturePath Step X Z
  | _, _, _, nil _, q => q
  | _, _, _, cons step rest, q => cons step (append rest q)

/-- Appending an empty path on the right leaves a path unchanged. -/
@[simp] theorem append_nil {X Y : State} (p : ArchitecturePath Step X Y) :
    append p (nil Y) = p := by
  induction p with
  | nil X => rfl
  | cons step rest ih =>
      simp [append, ih]

/-- Appending a path to an empty path on the left leaves it unchanged. -/
@[simp] theorem nil_append {X Y : State} (p : ArchitecturePath Step X Y) :
    append (nil X) p = p :=
  rfl

/-- Architecture path append is associative. -/
@[simp] theorem append_assoc {W X Y Z : State}
    (p : ArchitecturePath Step W X) (q : ArchitecturePath Step X Y)
    (r : ArchitecturePath Step Y Z) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil W => rfl
  | cons step rest ih =>
      simp [append, ih]

/-- Path length is additive under append. -/
@[simp] theorem length_append {X Y Z : State}
    (p : ArchitecturePath Step X Y) (q : ArchitecturePath Step Y Z) :
    length (append p q) = length p + length q := by
  induction p with
  | nil X =>
      simp [append, length]
  | cons step rest ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_comm]

/-- `InvariantHolds I X` says architecture invariant `I` holds at state `X`. -/
def InvariantHolds (I : State -> Prop) (X : State) : Prop :=
  I X

/-- A primitive step preserves invariant `I` across its endpoints. -/
def StepPreservesInvariant (I : State -> Prop) {X Y : State}
    (_step : Step X Y) : Prop :=
  I X -> I Y

/-- Every primitive step in a finite path preserves invariant `I`. -/
def EveryStepPreserves : {X Y : State} ->
    ArchitecturePath Step X Y -> (State -> Prop) -> Prop
  | _, _, nil _, _I => True
  | _, _, cons step rest, I =>
      StepPreservesInvariant I step ∧ EveryStepPreserves rest I

/-- Stepwise invariant preservation over an appended path splits by segment. -/
@[simp] theorem everyStepPreserves_append {I : State -> Prop} {X Y Z : State}
    (p : ArchitecturePath Step X Y) (q : ArchitecturePath Step Y Z) :
    EveryStepPreserves (append p q) I ↔
      EveryStepPreserves p I ∧ EveryStepPreserves q I := by
  induction p with
  | nil X =>
      simp [append, EveryStepPreserves]
  | cons step rest ih =>
      simp [append, EveryStepPreserves, ih, and_assoc]

/-- If every step preserves an invariant, the whole path preserves it. -/
theorem pathPreservesInvariant {I : State -> Prop} :
    {X Y : State} -> (p : ArchitecturePath Step X Y) ->
      InvariantHolds I X -> EveryStepPreserves p I ->
        InvariantHolds I (ApplyPath X p)
  | _, _, nil _, hStart, _hEvery => hStart
  | _, _, cons step rest, hStart, hEvery => by
      exact pathPreservesInvariant rest (hEvery.1 hStart) hEvery.2

/--
Generated homotopy relation between finite architecture paths.

The three non-structural generators are parameters:
* an independent square swaps two adjacent steps when a commuting replacement
  square has been supplied;
* same-contract replacement swaps one step for another with the same endpoints;
* repair fill identifies paths once a later diagram-filling proof certifies it.
-/
inductive PathHomotopy
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop) :
    {X Y : State} -> ArchitecturePath Step X Y ->
      ArchitecturePath Step X Y -> Prop where
  | refl {X Y : State} (p : ArchitecturePath Step X Y) :
      PathHomotopy IndependentSquare SameExternalContract RepairFill p p
  | symm {X Y : State} {p q : ArchitecturePath Step X Y} :
      PathHomotopy IndependentSquare SameExternalContract RepairFill p q ->
        PathHomotopy IndependentSquare SameExternalContract RepairFill q p
  | trans {X Y : State} {p q r : ArchitecturePath Step X Y} :
      PathHomotopy IndependentSquare SameExternalContract RepairFill p q ->
        PathHomotopy IndependentSquare SameExternalContract RepairFill q r ->
          PathHomotopy IndependentSquare SameExternalContract RepairFill p r
  | swapIndependent {W X Y Z T : State}
      (a : Step W X) (b : Step X Z) (c : Step W Y) (d : Step Y Z)
      (rest : ArchitecturePath Step Z T) :
      IndependentSquare W X Y Z a b c d ->
        PathHomotopy IndependentSquare SameExternalContract RepairFill
          (cons a (cons b rest)) (cons c (cons d rest))
  | replaceBySameContract {X Y Z : State}
      (s t : Step X Y) (rest : ArchitecturePath Step Y Z) :
      SameExternalContract X Y s t ->
        PathHomotopy IndependentSquare SameExternalContract RepairFill
          (cons s rest) (cons t rest)
  | repairFill {X Y : State} {p q : ArchitecturePath Step X Y} :
      RepairFill X Y p q ->
        PathHomotopy IndependentSquare SameExternalContract RepairFill p q

/-- An invariant that is stable under the generated path homotopy relation. -/
def HomotopyInvariant
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    (I : State -> Prop) : Prop :=
  ∀ {X Y : State} (p q : ArchitecturePath Step X Y),
    PathHomotopy (Step := Step)
      IndependentSquare SameExternalContract RepairFill p q ->
      (I (ApplyPath X p) ↔ I (ApplyPath X q))

/-- Homotopy invariance specializes directly to any homotopic path pair. -/
theorem architectureHomotopyInvariance
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {I : State -> Prop}
    (hInvariant :
      HomotopyInvariant (Step := Step)
        IndependentSquare SameExternalContract RepairFill I)
    {X Y : State} {p q : ArchitecturePath Step X Y}
    (hHomotopy :
      PathHomotopy (Step := Step)
        IndependentSquare SameExternalContract RepairFill p q) :
    I (ApplyPath X p) ↔ I (ApplyPath X q) :=
  by
    have h := hInvariant p q
    exact h hHomotopy

end ArchitecturePath

end Formal.Arch
