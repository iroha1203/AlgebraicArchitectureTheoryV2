namespace Formal.Arch

universe u v

/--
Finite witnesses that violate a supplied obstruction predicate.

The input list is the measured witness universe. Duplicates are intentionally
preserved, matching the executable metrics used elsewhere in the project.
-/
def violatingWitnesses {W : Type u} (bad : W -> Prop) [DecidablePred bad]
    (xs : List W) : List W :=
  xs.filter bad

/-- Count measured witnesses that violate a supplied obstruction predicate. -/
def violationCount {W : Type u} (bad : W -> Prop) [DecidablePred bad]
    (xs : List W) : Nat :=
  (violatingWitnesses bad xs).length

/--
One finite measured witness universe is included in another.

This is set-like inclusion over the measured list. It does not identify or
deduplicate witnesses, so duplicate-sensitive count monotonicity needs stronger
list-shape assumptions and is not encoded by this predicate.
-/
def WitnessUniverseIncluded {W : Type u} (small large : List W) : Prop :=
  ∀ w, w ∈ small -> w ∈ large

/-- There is a measured witness satisfying the obstruction predicate. -/
def MeasuredViolationExists {W : Type u} (bad : W -> Prop)
    (xs : List W) : Prop :=
  ∃ w, w ∈ xs ∧ bad w

/-- No measured witness in the supplied universe satisfies the obstruction predicate. -/
def NoMeasuredViolation {W : Type u} (bad : W -> Prop)
    (xs : List W) : Prop :=
  ∀ w, w ∈ xs -> ¬ bad w

/--
Membership in the violating witness list is exactly membership in the measured
universe plus the obstruction predicate.
-/
theorem mem_violatingWitnesses_iff {W : Type u} {bad : W -> Prop}
    [DecidablePred bad] {xs : List W} {w : W} :
    w ∈ violatingWitnesses bad xs ↔ w ∈ xs ∧ bad w := by
  simp [violatingWitnesses]

/--
Zero measured violations is equivalent to every measured witness being good.
-/
theorem violationCount_eq_zero_iff_forall_not_bad {W : Type u}
    {bad : W -> Prop} [DecidablePred bad] {xs : List W} :
    violationCount bad xs = 0 ↔ ∀ w, w ∈ xs -> ¬ bad w := by
  constructor
  · intro hZero w hMem hBad
    have hViolation : w ∈ violatingWitnesses bad xs := by
      rw [mem_violatingWitnesses_iff]
      exact ⟨hMem, hBad⟩
    have hPositive : 0 < violationCount bad xs := by
      unfold violationCount
      exact List.length_pos_of_mem hViolation
    exact (Nat.ne_of_gt hPositive) hZero
  · intro hNoBad
    unfold violationCount violatingWitnesses
    induction xs with
    | nil =>
        simp
    | cons x xs ih =>
        have hx : ¬ bad x := hNoBad x (by simp)
        have hxs : ∀ w, w ∈ xs -> ¬ bad w := by
          intro w hw
          exact hNoBad w (by simp [hw])
        simp [hx, ih hxs]

/--
If the measured universe is enlarged, an existing bad witness remains measured.
-/
theorem mem_violatingWitnesses_of_witnessUniverseIncluded {W : Type u}
    {bad : W -> Prop} [DecidablePred bad] {small large : List W}
    (hIncluded : WitnessUniverseIncluded small large) {w : W}
    (hMem : w ∈ violatingWitnesses bad small) :
    w ∈ violatingWitnesses bad large := by
  rw [mem_violatingWitnesses_iff] at hMem ⊢
  exact ⟨hIncluded w hMem.1, hMem.2⟩

/--
Witness existence is monotone under measured-universe enlargement.
-/
theorem measuredViolationExists_of_witnessUniverseIncluded {W : Type u}
    {bad : W -> Prop} {small large : List W}
    (hIncluded : WitnessUniverseIncluded small large)
    (hExists : MeasuredViolationExists bad small) :
    MeasuredViolationExists bad large := by
  rcases hExists with ⟨w, hMem, hBad⟩
  exact ⟨w, hIncluded w hMem, hBad⟩

/--
Absence of measured violations is contravariantly preserved by inclusion:
if the larger measured universe has no bad witness, neither does the smaller
one.
-/
theorem noMeasuredViolation_of_witnessUniverseIncluded {W : Type u}
    {bad : W -> Prop} {small large : List W}
    (hIncluded : WitnessUniverseIncluded small large)
    (hNoLarge : NoMeasuredViolation bad large) :
    NoMeasuredViolation bad small := by
  intro w hMem hBad
  exact hNoLarge w (hIncluded w hMem) hBad

/--
Zero measured violation count is contravariantly preserved by inclusion.

The direction is intentionally from larger zero to smaller zero. The converse
would require additional coverage assumptions and is not a global completeness
claim.
-/
theorem violationCount_eq_zero_of_witnessUniverseIncluded {W : Type u}
    {bad : W -> Prop} [DecidablePred bad] {small large : List W}
    (hIncluded : WitnessUniverseIncluded small large)
    (hZeroLarge : violationCount bad large = 0) :
    violationCount bad small = 0 := by
  exact violationCount_eq_zero_iff_forall_not_bad.mpr
    (noMeasuredViolation_of_witnessUniverseIncluded hIncluded
      (violationCount_eq_zero_iff_forall_not_bad.mp hZeroLarge))

/--
The measured witness list covers every required witness.

This one-way coverage is the part needed to turn measured-zero obstruction
counts into required-law statements. The measured list may contain additional
diagnostic witnesses.
-/
def CoversWitnesses {W : Type u} (required : W -> Prop) (measured : List W) :
    Prop :=
  ∀ w, required w -> w ∈ measured

/-- A finite list can be used as the required witness predicate it enumerates. -/
def RequiredByList {W : Type u} (required : List W) : W -> Prop :=
  fun w => w ∈ required

/--
If all witnesses in a required list occur in the measured list, the measured
list covers the finite required universe represented by that list.
-/
theorem coversWitnesses_of_requiredByList_subset {W : Type u}
    {required measured : List W}
    (hSubset : ∀ w, w ∈ required -> w ∈ measured) :
    CoversWitnesses (RequiredByList required) measured := by
  intro w hRequired
  exact hSubset w hRequired

/-- A finite required witness list covers itself. -/
theorem coversWitnesses_requiredByList_self {W : Type u}
    (required : List W) :
    CoversWitnesses (RequiredByList required) required := by
  exact coversWitnesses_of_requiredByList_subset (by
    intro w hRequired
    exact hRequired)

/-- A required equality diagram over an abstract expression type. -/
structure RequiredDiagram (Expr : Type u) where
  lhs : Expr
  rhs : Expr

/-- Semantics for interpreting diagram expressions as observable values. -/
structure Semantics (Expr : Type u) (Obs : Type v) where
  eval : Expr -> Obs

/-- A required diagram commutes when its two sides have equal semantics. -/
def DiagramCommutes {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) (d : RequiredDiagram Expr) : Prop :=
  sem.eval d.lhs = sem.eval d.rhs

/-- A diagram obstruction witness is a required diagram that does not commute. -/
def DiagramBad {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) (d : RequiredDiagram Expr) : Prop :=
  ¬ DiagramCommutes sem d

/-- Diagram obstruction witnesses are decidable when observations have decidable equality. -/
instance instDecidablePredDiagramBad {Expr : Type u} {Obs : Type v}
    [DecidableEq Obs] (sem : Semantics Expr Obs) :
    DecidablePred (DiagramBad sem) := by
  intro d
  unfold DiagramBad DiagramCommutes
  infer_instance

/-- Measured required diagrams whose two sides do not commute. -/
def diagramViolatingWitnesses {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) [DecidableEq Obs]
    (diagrams : List (RequiredDiagram Expr)) : List (RequiredDiagram Expr) :=
  violatingWitnesses (DiagramBad sem) diagrams

/-- Count measured diagram obstruction witnesses. -/
def diagramViolationCount {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) [DecidableEq Obs]
    (diagrams : List (RequiredDiagram Expr)) : Nat :=
  violationCount (DiagramBad sem) diagrams

/--
The measured diagram list covers every required diagram.

This is one-way on purpose: the measured list may contain additional diagrams,
but every required diagram must be present.
-/
def CoversRequired {Expr : Type u}
    (required : RequiredDiagram Expr -> Prop)
    (measured : List (RequiredDiagram Expr)) : Prop :=
  ∀ d, required d -> d ∈ measured

/-- A finite list can be used as the required diagram predicate it enumerates. -/
def RequiredDiagramsByList {Expr : Type u}
    (required : List (RequiredDiagram Expr)) :
    RequiredDiagram Expr -> Prop :=
  RequiredByList required

/--
If every required diagram listed by a finite diagram universe is measured, the
measured diagram list satisfies `CoversRequired`.
-/
theorem coversRequired_of_requiredDiagramsByList_subset {Expr : Type u}
    {required measured : List (RequiredDiagram Expr)}
    (hSubset : ∀ d, d ∈ required -> d ∈ measured) :
    CoversRequired (RequiredDiagramsByList required) measured := by
  exact coversWitnesses_of_requiredByList_subset hSubset

/-- A finite required diagram universe covers itself. -/
theorem coversRequired_requiredDiagramsByList_self {Expr : Type u}
    (required : List (RequiredDiagram Expr)) :
    CoversRequired (RequiredDiagramsByList required) required := by
  exact coversRequired_of_requiredDiagramsByList_subset (by
    intro d hRequired
    exact hRequired)

/--
Zero measured diagram violations constructively gives the absence of measured
diagram obstruction witnesses.
-/
theorem no_measured_DiagramBad_of_diagramViolationCount_eq_zero
    {Expr : Type u} {Obs : Type v} {sem : Semantics Expr Obs} [DecidableEq Obs]
    {measured : List (RequiredDiagram Expr)}
    (hZero : diagramViolationCount sem measured = 0) :
    ∀ d, d ∈ measured -> ¬ DiagramBad sem d := by
  rw [diagramViolationCount] at hZero
  exact (violationCount_eq_zero_iff_forall_not_bad.mp hZero)

/--
If every measured diagram commutes, the measured diagram violation count is
zero.
-/
theorem diagramViolationCount_eq_zero_of_forall_measured_DiagramCommutes
    {Expr : Type u} {Obs : Type v} {sem : Semantics Expr Obs} [DecidableEq Obs]
    {measured : List (RequiredDiagram Expr)}
    (hCommutes : ∀ d, d ∈ measured -> DiagramCommutes sem d) :
    diagramViolationCount sem measured = 0 := by
  rw [diagramViolationCount]
  exact violationCount_eq_zero_iff_forall_not_bad.mpr (by
    intro d hMem hBad
    exact hBad (hCommutes d hMem))

/--
With decidable semantic equality, zero measured diagram violations is equivalent
to every measured diagram commuting.
-/
theorem diagramViolationCount_eq_zero_iff_forall_measured_DiagramCommutes
    {Expr : Type u} {Obs : Type v} {sem : Semantics Expr Obs} [DecidableEq Obs]
    {measured : List (RequiredDiagram Expr)} :
    diagramViolationCount sem measured = 0 ↔
      ∀ d, d ∈ measured -> DiagramCommutes sem d := by
  constructor
  · intro hZero d hMem
    by_cases hCommutes : DiagramCommutes sem d
    · exact hCommutes
    · exact False.elim
        (no_measured_DiagramBad_of_diagramViolationCount_eq_zero hZero
          d hMem hCommutes)
  · intro hCommutes
    exact diagramViolationCount_eq_zero_of_forall_measured_DiagramCommutes
      hCommutes

/--
Under complete coverage, zero measured diagram violations constructively gives
the absence of required diagram obstruction witnesses.
-/
theorem no_required_DiagramBad_of_coversRequired_and_diagramViolationCount_eq_zero
    {Expr : Type u} {Obs : Type v} {sem : Semantics Expr Obs} [DecidableEq Obs]
    {required : RequiredDiagram Expr -> Prop}
    {measured : List (RequiredDiagram Expr)}
    (hCovers : CoversRequired required measured)
    (hZero : diagramViolationCount sem measured = 0) :
    ∀ d, required d -> ¬ DiagramBad sem d := by
  intro d hRequired
  exact no_measured_DiagramBad_of_diagramViolationCount_eq_zero hZero
    d (hCovers d hRequired)

/--
Under complete coverage and decidable semantic equality, zero measured diagram
violations implies every required diagram commutes.
-/
theorem requiredDiagramCommutes_of_coversRequired_and_diagramViolationCount_eq_zero
    {Expr : Type u} {Obs : Type v} {sem : Semantics Expr Obs} [DecidableEq Obs]
    {required : RequiredDiagram Expr -> Prop}
    {measured : List (RequiredDiagram Expr)}
    (hCovers : CoversRequired required measured)
    (hZero : diagramViolationCount sem measured = 0) :
    ∀ d, required d -> DiagramCommutes sem d := by
  intro d hRequired
  exact (diagramViolationCount_eq_zero_iff_forall_measured_DiagramCommutes.mp
    hZero) d (hCovers d hRequired)

end Formal.Arch
