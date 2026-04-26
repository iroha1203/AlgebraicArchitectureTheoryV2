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
