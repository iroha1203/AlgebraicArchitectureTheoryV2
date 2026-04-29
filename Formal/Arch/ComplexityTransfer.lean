namespace Formal.Arch

universe u v w z

/--
Selected target axes for bounded complexity-transfer witnesses.

The targets are diagnostic axes only.  They do not assert empirical cost
improvement, global conservation of complexity, or completeness outside the
selected witness universe.
-/
inductive ComplexityTransferTarget where
  | runtime
  | semantic
  | policy
  deriving DecidableEq, Repr

namespace ComplexityTransferTarget

/-- Documentation-facing label for a complexity-transfer target. -/
def label : ComplexityTransferTarget -> String
  | runtime => "runtime"
  | semantic => "semantic"
  | policy => "policy"

end ComplexityTransferTarget

/--
A bounded architecture transform schema.

`source` and `target` give the endpoints of a selected transform value.  The
schema records bounded-universe assumptions explicitly instead of claiming that
all architecture changes or extractor outputs have been enumerated.
-/
structure ArchitectureTransform (State : Type u) (Transform : Type v) where
  source : Transform -> State
  target : Transform -> State
  boundedUniverse : Prop
  nonConclusions : Prop

namespace ArchitectureTransform

variable {State : Type u} {Transform : Type v}

/-- The theorem package explicitly records transform-schema non-conclusions. -/
def RecordsNonConclusions
    (T : ArchitectureTransform State Transform) : Prop :=
  T.nonConclusions

end ArchitectureTransform

/--
A selected natural-valued complexity measure over architecture states.

The measure is intentionally bounded to its measurement universe.  It is not a
claim that every semantic, runtime, or policy cost has been measured.
-/
structure SelectedComplexityMeasure (State : Type u) where
  value : State -> Nat
  measuredUniverse : State -> Prop
  bounded : Prop
  nonConclusions : Prop

/-- A transform reduces the selected static complexity measure. -/
def ReducesStaticComplexity
    {State : Type u} {Transform : Type v}
    (T : ArchitectureTransform State Transform)
    (staticMeasure : SelectedComplexityMeasure State)
    (t : Transform) : Prop :=
  staticMeasure.value (T.target t) < staticMeasure.value (T.source t)

/--
Bounded requirement schema used by complexity-transfer theorem packages.

`PreservesRequirements` below is relative to the selected requirements, and
does not assert completeness of all possible stakeholder or semantic demands.
-/
structure RequirementSchema (State : Type u) (Requirement : Type w) where
  required : Requirement -> Prop
  satisfied : State -> Requirement -> Prop
  boundedUniverse : Prop
  nonConclusions : Prop

/-- The selected requirements have the same satisfaction truth at both states. -/
def PreservesRequirements
    {State : Type u} {Requirement : Type w}
    (R : RequirementSchema State Requirement)
    (source target : State) : Prop :=
  ∀ requirement, R.required requirement ->
    (R.satisfied source requirement ↔ R.satisfied target requirement)

/--
Selected proof-elimination and transfer-witness schema.

`transferWitness` is indexed by a diagnostic axis and a transform.  The
selected witness predicate is what keeps the package bounded.
-/
structure ComplexityTransferSchema
    (Transform : Type v) (Witness : Type z) where
  eliminatedByProof : Transform -> Prop
  transferWitness : ComplexityTransferTarget -> Transform -> Witness -> Prop
  selectedWitness : Witness -> Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

/-- The selected transform's static complexity was eliminated by proof. -/
def ComplexityEliminatedByProof
    {Transform : Type v} {Witness : Type z}
    (S : ComplexityTransferSchema Transform Witness)
    (t : Transform) : Prop :=
  S.eliminatedByProof t

/-- The selected transform transfers complexity to a diagnostic target axis. -/
def ComplexityTransferredTo
    {Transform : Type v} {Witness : Type z}
    (S : ComplexityTransferSchema Transform Witness)
    (target : ComplexityTransferTarget)
    (t : Transform) : Prop :=
  ∃ witness, S.selectedWitness witness ∧ S.transferWitness target t witness

/--
Transfer to one of the selected bounded diagnostic targets.

This keeps the conclusion at the runtime / semantic / policy axis level and
does not assert a global conservation law or lower bound.
-/
def ComplexityTransferredWithinSelectedTargets
    {Transform : Type v} {Witness : Type z}
    (S : ComplexityTransferSchema Transform Witness)
    (t : Transform) : Prop :=
  ComplexityTransferredTo S .runtime t ∨
    ComplexityTransferredTo S .semantic t ∨
    ComplexityTransferredTo S .policy t

/--
The bounded alternative returned by the complexity-transfer package.

Either the selected complexity was eliminated by proof, or it was transferred
to one of the selected bounded target axes.
-/
def ComplexityTransferAlternative
    {Transform : Type v} {Witness : Type z}
    (S : ComplexityTransferSchema Transform Witness)
    (t : Transform) : Prop :=
  ComplexityEliminatedByProof S t ∨
    ComplexityTransferredWithinSelectedTargets S t

/--
Residual gap for the bounded complexity-transfer schema.

This records that coverage or exactness is not closed.  It is a bounded
diagnostic predicate, not a theorem claiming global complexity conservation.
-/
def ComplexityTransferResidualGap
    {Transform : Type v} {Witness : Type z}
    (S : ComplexityTransferSchema Transform Witness) : Prop :=
  ¬ S.coverageAssumptions ∨ ¬ S.exactnessAssumptions

namespace ComplexityTransferredTo

variable {Transform : Type v} {Witness : Type z}
variable {S : ComplexityTransferSchema Transform Witness}
variable {target : ComplexityTransferTarget} {t : Transform}

/-- A transfer conclusion always exposes a selected witness. -/
theorem has_selectedWitness
    (hTransfer : ComplexityTransferredTo S target t) :
    ∃ witness, S.selectedWitness witness := by
  rcases hTransfer with ⟨witness, hSelected, _hAtTarget⟩
  exact ⟨witness, hSelected⟩

end ComplexityTransferredTo

/--
Bounded theorem package for complexity transfer.

Under a selected static-complexity reduction and selected requirement
preservation, the package returns either proof elimination or a selected
transfer witness on the runtime, semantic, or policy axis.  The package does
not claim empirical cost improvement, global complexity conservation, or
completeness outside the selected witness universe.
-/
structure BoundedComplexityTransferPackage
    {State : Type u} {Transform : Type v}
    {Requirement : Type w} {Witness : Type z}
    (T : ArchitectureTransform State Transform)
    (staticMeasure : SelectedComplexityMeasure State)
    (requirements : RequirementSchema State Requirement)
    (S : ComplexityTransferSchema Transform Witness) where
  transferAlternative :
    ∀ t,
      ReducesStaticComplexity T staticMeasure t ->
      PreservesRequirements requirements (T.source t) (T.target t) ->
        ComplexityEliminatedByProof S t ∨
          ComplexityTransferredTo S .runtime t ∨
          ComplexityTransferredTo S .semantic t ∨
          ComplexityTransferredTo S .policy t
  boundedAssumptions : Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

namespace BoundedComplexityTransferPackage

variable {State : Type u} {Transform : Type v}
variable {Requirement : Type w} {Witness : Type z}
variable {T : ArchitectureTransform State Transform}
variable {staticMeasure : SelectedComplexityMeasure State}
variable {requirements : RequirementSchema State Requirement}
variable {S : ComplexityTransferSchema Transform Witness}

/--
Complexity-transfer alternative for the selected transform.

This is the bounded version of the mathematical-design theorem: its conclusion
is relative to the selected measure, requirements, and transfer-witness schema.
-/
theorem complexityTransfer_alternative
    (pkg :
      BoundedComplexityTransferPackage T staticMeasure requirements S)
    (t : Transform)
    (hReduces : ReducesStaticComplexity T staticMeasure t)
    (hPreserves :
      PreservesRequirements requirements (T.source t) (T.target t)) :
    ComplexityEliminatedByProof S t ∨
      ComplexityTransferredTo S .runtime t ∨
      ComplexityTransferredTo S .semantic t ∨
      ComplexityTransferredTo S .policy t :=
  pkg.transferAlternative t hReduces hPreserves

/--
Bounded complexity-transfer alternative using the named selected-target
predicate.
-/
theorem complexityTransfer_selectedAlternative
    (pkg :
      BoundedComplexityTransferPackage T staticMeasure requirements S)
    (t : Transform)
    (hReduces : ReducesStaticComplexity T staticMeasure t)
    (hPreserves :
      PreservesRequirements requirements (T.source t) (T.target t)) :
    ComplexityTransferAlternative S t :=
  pkg.transferAlternative t hReduces hPreserves

/--
No-free-elimination corollary for the bounded package.

If selected static complexity decreases, selected requirements are preserved,
and proof elimination is not available, then the package must expose a selected
runtime, semantic, or policy transfer witness.
-/
theorem no_free_elimination_bounded
    (pkg :
      BoundedComplexityTransferPackage T staticMeasure requirements S)
    (t : Transform)
    (hReduces : ReducesStaticComplexity T staticMeasure t)
    (hPreserves :
      PreservesRequirements requirements (T.source t) (T.target t))
    (hNotEliminated : ¬ ComplexityEliminatedByProof S t) :
    ComplexityTransferredWithinSelectedTargets S t := by
  rcases complexityTransfer_selectedAlternative
      pkg t hReduces hPreserves with hEliminated | hTransferred
  · exact False.elim (hNotEliminated hEliminated)
  · exact hTransferred

/-- The theorem package explicitly records its non-conclusion clause. -/
def RecordsNonConclusions
    (pkg :
      BoundedComplexityTransferPackage T staticMeasure requirements S) :
    Prop :=
  pkg.nonConclusions

/-- The recorded non-conclusion predicate is exactly the schema field. -/
theorem records_nonConclusions_iff
    (pkg :
      BoundedComplexityTransferPackage T staticMeasure requirements S) :
    pkg.RecordsNonConclusions ↔ pkg.nonConclusions := by
  rfl

end BoundedComplexityTransferPackage

end Formal.Arch
