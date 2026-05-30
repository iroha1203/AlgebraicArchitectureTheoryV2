import Formal.Arch.Evolution.DiagramFiller

/-!
Minimal measurement guardrails for ArchSig monodromy / boundary-holonomy
readings.

This module is deliberately bounded. It formalizes finite measured squares,
selected axes, axis-local defects, and nonnegative weighted aggregates used as
tooling claim boundaries. It does not assert all-path homotopy completeness,
all-axis semantic completeness, extractor completeness, or ArchSig correctness
in the wild.
-/

namespace Formal.Arch

universe u v w x

namespace MonodromyMeasurement

/-- A measured square is the selected pair of paths or operations compared by one reading. -/
structure MeasuredSquare (Path : Type u) where
  lhs : Path
  rhs : Path

/-- A selected axis observes only the path data chosen by a bounded measurement policy. -/
structure SelectedAxis (Path : Type u) (Observation : Type v) where
  observe : Path -> Observation

/--
An axis defect is a bounded measurement of one selected square on one selected
axis.

The sound fields record only safe readings:
* measured zero implies equality of the selected observations;
* measured nonzero implies a selected observation difference.
-/
structure AxisDefect {Path : Type u} {Observation : Type v}
    (axis : SelectedAxis Path Observation) (square : MeasuredSquare Path) where
  value : Nat
  zeroImpliesObservationEq :
    value = 0 -> axis.observe square.lhs = axis.observe square.rhs
  nonzeroImpliesObservationDiff :
    value ≠ 0 -> axis.observe square.lhs ≠ axis.observe square.rhs

namespace AxisDefect

/-- A measured nonzero defect can be read only as a selected observation difference. -/
theorem observationDiff_of_nonzero {Path : Type u} {Observation : Type v}
    {axis : SelectedAxis Path Observation} {square : MeasuredSquare Path}
    (defect : AxisDefect axis square) (hNonzero : defect.value ≠ 0) :
    axis.observe square.lhs ≠ axis.observe square.rhs :=
  defect.nonzeroImpliesObservationDiff hNonzero

/-- A measured zero defect gives local zero only on the selected axis and square. -/
theorem observationEq_of_zero {Path : Type u} {Observation : Type v}
    {axis : SelectedAxis Path Observation} {square : MeasuredSquare Path}
    (defect : AxisDefect axis square) (hZero : defect.value = 0) :
    axis.observe square.lhs = axis.observe square.rhs :=
  defect.zeroImpliesObservationEq hZero

end AxisDefect

/-- A finite family entry with a nonnegative natural weight. -/
structure WeightedAxisDefect {Path : Type u} {Observation : Type v}
    (axis : SelectedAxis Path Observation) where
  square : MeasuredSquare Path
  defect : AxisDefect axis square
  weight : Nat

/-- Finite measured-square family used by bounded aggregate reports. -/
abbrev FiniteMeasuredSquareFamily {Path : Type u} {Observation : Type v}
    (axis : SelectedAxis Path Observation) :=
  List (WeightedAxisDefect axis)

namespace WeightedAxisDefect

/-- Nonnegative weighted contribution of one selected defect. -/
def contribution {Path : Type u} {Observation : Type v}
    {axis : SelectedAxis Path Observation} (entry : WeightedAxisDefect axis) :
    Nat :=
  entry.weight * entry.defect.value

end WeightedAxisDefect

/-- Nonnegative weighted aggregate over a finite measured-square family. -/
def weightedAggregate {Path : Type u} {Observation : Type v}
    {axis : SelectedAxis Path Observation} :
    FiniteMeasuredSquareFamily axis -> Nat
  | [] => 0
  | entry :: rest =>
      WeightedAxisDefect.contribution entry + weightedAggregate rest

/--
Aggregate zero implies local zero for every positive-weight entry in the finite
measured family.

This is the bounded direction ArchSig reports may use. It does not say that a
zero aggregate covers unmeasured squares or zero-weight entries.
-/
theorem localZero_of_weightedAggregate_zero {Path : Type u} {Observation : Type v}
    {axis : SelectedAxis Path Observation}
    (family : FiniteMeasuredSquareFamily axis)
    (hAggregate : weightedAggregate family = 0)
    (entry : WeightedAxisDefect axis)
    (hEntry : entry ∈ family) (hPositiveWeight : entry.weight ≠ 0) :
    entry.defect.value = 0 := by
  induction family generalizing entry with
  | nil =>
      cases hEntry
  | cons head tail ih =>
      simp [weightedAggregate, WeightedAxisDefect.contribution] at hAggregate
      rcases hAggregate with ⟨hHeadZero, hTailZero⟩
      cases hEntry with
      | head =>
          rcases Nat.mul_eq_zero.mp hHeadZero with hWeightZero | hDefectZero
          · exact False.elim (hPositiveWeight hWeightZero)
          · exact hDefectZero
      | tail _ hTailEntry =>
          exact ih hTailZero entry hTailEntry hPositiveWeight

/--
Local zero from an aggregate-zero reading also yields equality of the selected
observations for that local square.
-/
theorem observationEq_of_weightedAggregate_zero {Path : Type u} {Observation : Type v}
    {axis : SelectedAxis Path Observation}
    (family : FiniteMeasuredSquareFamily axis)
    (hAggregate : weightedAggregate family = 0)
    (entry : WeightedAxisDefect axis)
    (hEntry : entry ∈ family) (hPositiveWeight : entry.weight ≠ 0) :
    axis.observe entry.square.lhs = axis.observe entry.square.rhs := by
  exact entry.defect.observationEq_of_zero
    (localZero_of_weightedAggregate_zero family hAggregate entry hEntry hPositiveWeight)

/-- Local selected-axis wrapper for an endpoint-indexed architecture-path observation. -/
def localSelectedAxis {State : Type u} {Step : State -> State -> Type v}
    {Observation : Type w}
    (Obs : {X Y : State} -> ArchitecturePath Step X Y -> Observation)
    (X Y : State) : SelectedAxis (ArchitecturePath Step X Y) Observation where
  observe := fun path => Obs path

/--
A nonzero defect on a selected architecture-path observation refutes selected
path homotopy whenever the existing homotopy API proves that homotopy preserves
that observation.
-/
theorem nonzero_refutes_selectedPathHomotopy {State : Type u}
    {Step : State -> State -> Type v} {Observation : Type w}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {Obs : {X Y : State} -> ArchitecturePath Step X Y -> Observation}
    (hIndependentSquare :
      ∀ {W X Y Z T : State}
        (a : Step W X) (b : Step X Z) (c : Step W Y) (d : Step Y Z)
        (rest : ArchitecturePath Step Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : State} (s t : Step X Y)
        (rest : ArchitecturePath Step Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : State} {p q : ArchitecturePath Step X Y},
        RepairFill X Y p q ->
          (suffix : ArchitecturePath Step Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : State} (step : Step X Y)
        {p q : ArchitecturePath Step Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {X Y : State} {square : MeasuredSquare (ArchitecturePath Step X Y)}
    (defect : AxisDefect (localSelectedAxis Obs X Y) square)
    (hNonzero : defect.value ≠ 0) :
    ¬ ArchitecturePath.PathHomotopy (Step := Step)
        IndependentSquare SameExternalContract RepairFill square.lhs square.rhs := by
  intro hHomotopy
  exact defect.observationDiff_of_nonzero hNonzero
    (ArchitecturePath.PathHomotopy.observation_eq
      (Step := Step) (Obs := Obs)
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      hHomotopy)

/--
A nonzero selected-axis defect on a diagram packages the existing
non-fillability witness API.
-/
theorem nonzero_nonFillabilityWitnessFor {State : Type u}
    {Step : State -> State -> Type v} {Observation : Type x}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {Obs : {X Y : State} -> ArchitecturePath Step X Y -> Observation}
    (hIndependentSquare :
      ∀ {W X Y Z T : State}
        (a : Step W X) (b : Step X Z) (c : Step W Y) (d : Step Y Z)
        (rest : ArchitecturePath Step Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : State} (s t : Step X Y)
        (rest : ArchitecturePath Step Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : State} {p q : ArchitecturePath Step X Y},
        RepairFill X Y p q ->
          (suffix : ArchitecturePath Step Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : State} (step : Step X Y)
        {p q : ArchitecturePath Step Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {X Y : State} {D : ArchitectureDiagram Step X Y}
    {Witness : Type w} (witness : Witness)
    (defect : AxisDefect (localSelectedAxis Obs X Y)
      { lhs := D.lhs, rhs := D.rhs })
    (hNonzero : defect.value ≠ 0) :
    NonFillabilityWitnessFor
      IndependentSquare SameExternalContract RepairFill D witness := by
  exact
    observationDifference_nonFillabilityWitnessFor
      (Step := Step) (Obs := Obs)
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      witness (defect.observationDiff_of_nonzero hNonzero)

/-- Claim boundary tracked by the minimal measurement package. -/
structure GuardrailBoundary where
  boundedFiniteFamily : Prop
  selectedAxisOnly : Prop
  noAllPathHomotopyCompleteness : Prop
  noAllAxisSemanticCompleteness : Prop
  noExtractorCompleteness : Prop

end MonodromyMeasurement

end Formal.Arch
