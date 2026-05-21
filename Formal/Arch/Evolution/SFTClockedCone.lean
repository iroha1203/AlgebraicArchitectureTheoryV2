import Formal.Arch.Evolution.SFTForecastCone

/-!
Clocked ForecastCone core for SFT descent.

`ClockedForecastCone` is the exact shared-clock object: membership means the
path length is exactly the selected horizon.  The upper-bound reading is kept
separately as `BoundedClockedForecastCone`.
-/

namespace Formal.Arch

universe u v

/--
One clock tick in an SFT field path.

An active tick stores an existing supported field step.  An idle tick leaves the
field state unchanged.
-/
inductive ClockedFieldStep
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation) :
    Field -> Field -> Type (max u v) where
  | active {source target : Field} :
      SupportedFieldStep support relation source target ->
        ClockedFieldStep support relation source target
  | idle (source : Field) :
      ClockedFieldStep support relation source source

/-- A finite clocked path whose ticks may be active or idle/stutter steps. -/
abbrev ClockedFieldPath
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation) :=
  ArchitecturePath (ClockedFieldStep support relation)

/-- A clocked field path uses exactly the selected shared-clock horizon. -/
def ExactClockedFieldPath
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field}
    (horizon : Nat)
    (path : ClockedFieldPath support relation source target) : Prop :=
  ArchitecturePath.length path = horizon

/-- A clocked field path has length bounded by the selected horizon. -/
def BoundedClockedFieldPath
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field}
    (horizon : Nat)
    (path : ClockedFieldPath support relation source target) : Prop :=
  ArchitecturePath.length path <= horizon

/-- Exact shared-clock ForecastCone membership. -/
def ClockedForecastCone
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat)
    (target : Field)
    (path : ClockedFieldPath support relation source target) : Prop :=
  ExactClockedFieldPath horizon path

/-- Bounded clocked cone membership, kept separate from exact clocked cones. -/
def BoundedClockedForecastCone
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat)
    (target : Field)
    (path : ClockedFieldPath support relation source target) : Prop :=
  BoundedClockedFieldPath horizon path

namespace ClockedForecastCone

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- Clocked cone membership exposes exact shared-clock length. -/
theorem length_eq_horizon
    {source target : Field} {horizon : Nat}
    {path : ClockedFieldPath support relation source target}
    (hCone :
      ClockedForecastCone support relation source horizon target path) :
    ArchitecturePath.length path = horizon :=
  hCone

/-- Exact shared-clock membership also gives the finite clock bound. -/
theorem length_le_horizon
    {source target : Field} {horizon : Nat}
    {path : ClockedFieldPath support relation source target}
    (hCone :
      ClockedForecastCone support relation source horizon target path) :
    ArchitecturePath.length path <= horizon := by
  rw [hCone]
  exact Nat.le_refl horizon

/-- The zero-length clocked path belongs to the zero-horizon clocked cone. -/
theorem nil_mem
    (source : Field) :
    ClockedForecastCone support relation source 0 source
      (ArchitecturePath.nil source) := by
  simp [ClockedForecastCone, ExactClockedFieldPath,
    ArchitecturePath.length]

/-- A single idle tick is admitted exactly at one clock tick. -/
theorem idle_mem_one
    (source : Field) :
    ClockedForecastCone support relation source 1 source
      (ArchitecturePath.cons (ClockedFieldStep.idle source)
        (ArchitecturePath.nil source)) := by
  simp [ClockedForecastCone, ExactClockedFieldPath,
    ArchitecturePath.length]

end ClockedForecastCone

namespace BoundedClockedForecastCone

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- Bounded clocked cone membership exposes the finite clock bound. -/
theorem length_le_horizon
    {source target : Field} {horizon : Nat}
    {path : ClockedFieldPath support relation source target}
    (hCone :
      BoundedClockedForecastCone support relation source horizon target path) :
    ArchitecturePath.length path <= horizon :=
  hCone

/-- Every exact clocked cone member is also a bounded clocked cone member. -/
theorem of_clockedForecastCone
    {source target : Field} {horizon : Nat}
    {path : ClockedFieldPath support relation source target}
    (hCone :
      ClockedForecastCone support relation source horizon target path) :
    BoundedClockedForecastCone support relation source horizon target path :=
  ClockedForecastCone.length_le_horizon hCone

/-- The zero-length clocked path belongs to every bounded clocked cone at its source. -/
theorem nil_mem
    (source : Field) {horizon : Nat} :
    BoundedClockedForecastCone support relation source horizon source
      (ArchitecturePath.nil source) := by
  simp [BoundedClockedForecastCone, BoundedClockedFieldPath,
    ArchitecturePath.length]

/-- Increasing the selected clock horizon preserves bounded clocked cone membership. -/
theorem monotone_horizon
    {source target : Field} {horizon₁ horizon₂ : Nat}
    {path : ClockedFieldPath support relation source target}
    (hCone :
      BoundedClockedForecastCone support relation source horizon₁ target path)
    (hLe : horizon₁ <= horizon₂) :
    BoundedClockedForecastCone support relation source horizon₂ target path :=
  Nat.le_trans hCone hLe

/-- A single idle tick is admitted whenever the bounded horizon allows one tick. -/
theorem idle_mem
    (source : Field) {horizon : Nat}
    (hTick : 1 <= horizon) :
    BoundedClockedForecastCone support relation source horizon source
      (ArchitecturePath.cons (ClockedFieldStep.idle source)
        (ArchitecturePath.nil source)) := by
  simpa [BoundedClockedForecastCone, BoundedClockedFieldPath,
    ArchitecturePath.length] using hTick

end BoundedClockedForecastCone

/-- Embed an ordinary supported path into the clocked path model. -/
def clockedFieldPathOfFieldPath
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation} :
    {source target : Field} ->
      FieldPath support relation source target ->
        ClockedFieldPath support relation source target
  | _, _, ArchitecturePath.nil source => ArchitecturePath.nil source
  | _, _, ArchitecturePath.cons step rest =>
      ArchitecturePath.cons (ClockedFieldStep.active step)
        (clockedFieldPathOfFieldPath rest)

/-- Clocking an ordinary field path preserves path length. -/
@[simp] theorem clockedFieldPathOfFieldPath_length
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation} :
    {source target : Field} ->
      (path : FieldPath support relation source target) ->
        ArchitecturePath.length (clockedFieldPathOfFieldPath path) =
          ArchitecturePath.length path
  | _, _, ArchitecturePath.nil _ => rfl
  | _, _, ArchitecturePath.cons _ rest => by
      simp [clockedFieldPathOfFieldPath, ArchitecturePath.length,
        clockedFieldPathOfFieldPath_length rest]

/-- A clocked path consisting of `ticks` idle/stutter steps at one field state. -/
def idleClockedFieldPath
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    (source : Field) : Nat ->
      ClockedFieldPath support relation source source
  | 0 => ArchitecturePath.nil source
  | Nat.succ ticks =>
      ArchitecturePath.cons (ClockedFieldStep.idle source)
        (idleClockedFieldPath source ticks)

/-- An idle clocked path has exactly the requested number of ticks. -/
@[simp] theorem idleClockedFieldPath_length
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    (source : Field) :
    (ticks : Nat) ->
      ArchitecturePath.length
        (idleClockedFieldPath
          (support := support) (relation := relation) source ticks) = ticks
  | 0 => rfl
  | Nat.succ ticks => by
      simp [idleClockedFieldPath, ArchitecturePath.length,
        idleClockedFieldPath_length source ticks]

/-- Pad a clocked reading of an ordinary field path with target-side idle ticks. -/
def paddedClockedFieldPathOfFieldPath
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field}
    (path : FieldPath support relation source target)
    (idleTicks : Nat) :
    ClockedFieldPath support relation source target :=
  ArchitecturePath.append (clockedFieldPathOfFieldPath path)
    (idleClockedFieldPath target idleTicks)

/-- Padding an ordinary field path adds exactly the selected idle ticks. -/
@[simp] theorem paddedClockedFieldPathOfFieldPath_length
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field}
    (path : FieldPath support relation source target)
    (idleTicks : Nat) :
    ArchitecturePath.length
      (paddedClockedFieldPathOfFieldPath path idleTicks) =
      ArchitecturePath.length path + idleTicks := by
  simp [paddedClockedFieldPathOfFieldPath]

/-- Every ordinary ForecastCone member has a bounded clocked reading at the same horizon. -/
theorem boundedClockedForecastCone_of_forecastCone
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field} {horizon : Nat}
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon target path) :
    BoundedClockedForecastCone support relation source horizon target
      (clockedFieldPathOfFieldPath path) := by
  simpa [BoundedClockedForecastCone, BoundedClockedFieldPath, ForecastCone,
    ReachableFieldPath] using hCone

/--
Every ordinary ForecastCone member can be padded with idle ticks into an exact
shared-clock `ClockedForecastCone` witness at the same horizon.
-/
theorem clockedForecastCone_of_forecastCone
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field} {horizon : Nat}
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon target path) :
    ClockedForecastCone support relation source horizon target
      (paddedClockedFieldPathOfFieldPath path
        (horizon - ArchitecturePath.length path)) := by
  have hLength :
      ArchitecturePath.length path +
          (horizon - ArchitecturePath.length path) = horizon :=
    Nat.add_sub_of_le hCone
  simpa [ClockedForecastCone, ExactClockedFieldPath,
    paddedClockedFieldPathOfFieldPath_length] using hLength

/-- A checked point of a selected clocked forecast cone. -/
structure ClockedConePoint
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  target : Field
  path : ClockedFieldPath support relation source target
  coneMember :
    ClockedForecastCone support relation source horizon target path

namespace ClockedConePoint

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- A clocked cone point exposes its horizon bound. -/
theorem length_le_horizon
    (point : ClockedConePoint support relation source horizon) :
    ArchitecturePath.length point.path <= horizon :=
  ClockedForecastCone.length_le_horizon point.coneMember

/-- A clocked cone point exposes its exact shared-clock length. -/
theorem length_eq_horizon
    (point : ClockedConePoint support relation source horizon) :
    ArchitecturePath.length point.path = horizon :=
  ClockedForecastCone.length_eq_horizon point.coneMember

/-- Turn an ordinary cone witness into a clocked cone point. -/
def ofForecastCone
    {target : Field}
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon target path) :
    ClockedConePoint support relation source horizon where
  target := target
  path :=
    paddedClockedFieldPathOfFieldPath path
      (horizon - ArchitecturePath.length path)
  coneMember := clockedForecastCone_of_forecastCone hCone

end ClockedConePoint

end Formal.Arch
