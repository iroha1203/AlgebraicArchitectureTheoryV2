import Formal.Arch.StateEffect

namespace Formal.Arch

universe u v

/--
A natural-number-valued distance on observations whose zero values exactly
separate equality.

This is the minimal numerical structure needed for the first curvature bridge:
zero numerical curvature should mean diagram commutativity, without committing
to weights, calibration, or an empirical cost model.
-/
structure ZeroSeparatingDistance (Obs : Type u) where
  distance : Obs -> Obs -> Nat
  distance_eq_zero_iff : ∀ x y, distance x y = 0 ↔ x = y

/--
Numerical curvature of a required diagram: the distance between the observable
semantics of its two sides.
-/
def numericalCurvature {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    (sem : Semantics Expr Obs) (d : RequiredDiagram Expr) : Nat :=
  metric.distance (sem.eval d.lhs) (sem.eval d.rhs)

/-- A diagram has numerical curvature obstruction when its curvature is nonzero. -/
def NumericalCurvatureObstruction {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    (sem : Semantics Expr Obs) (d : RequiredDiagram Expr) : Prop :=
  numericalCurvature metric sem d ≠ 0

/--
No required numerical curvature obstruction exists for the selected diagram
family.
-/
def NoNumericalCurvatureObstruction {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    (sem : Semantics Expr Obs)
    (required : RequiredDiagram Expr -> Prop) : Prop :=
  ∀ d, required d -> ¬ NumericalCurvatureObstruction metric sem d

/--
Total numerical curvature over a finite measured diagram universe.

Duplicates are counted as repeated measurements, matching the finite executable
metrics elsewhere in the signature layer.
-/
def totalCurvature {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    (sem : Semantics Expr Obs) : List (RequiredDiagram Expr) -> Nat
  | [] => 0
  | d :: ds => numericalCurvature metric sem d + totalCurvature metric sem ds

/--
No numerical curvature obstruction exists in the finite measured diagram
universe. This is intentionally list-scoped: it does not claim that every
semantic diagram has been measured.
-/
def NoMeasuredNumericalCurvatureObstruction {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    (sem : Semantics Expr Obs)
    (measured : List (RequiredDiagram Expr)) : Prop :=
  ∀ d, d ∈ measured -> ¬ NumericalCurvatureObstruction metric sem d

/--
Positive weights on the finite measured diagram universe.

This is the bounded exactness assumption needed to read a weighted aggregate
zero as zero curvature for every measured diagram. Diagrams outside the measured
list remain unclaimed.
-/
def PositiveCurvatureWeightOn {Expr : Type u}
    (measured : List (RequiredDiagram Expr))
    (weight : RequiredDiagram Expr -> Nat) : Prop :=
  ∀ d, d ∈ measured -> 0 < weight d

/--
Weighted numerical curvature over a finite measured diagram universe.

The weight function is supplied by the caller so that calibration and empirical
cost models stay outside the formal bridge.
-/
def totalWeightedCurvature {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    (sem : Semantics Expr Obs)
    (weight : RequiredDiagram Expr -> Nat) : List (RequiredDiagram Expr) -> Nat
  | [] => 0
  | d :: ds =>
      weight d * numericalCurvature metric sem d +
        totalWeightedCurvature metric sem weight ds

/--
Zero numerical curvature is exactly diagram commutativity.
-/
theorem numericalCurvature_eq_zero_iff_DiagramCommutes
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs} {d : RequiredDiagram Expr} :
    numericalCurvature metric sem d = 0 ↔ DiagramCommutes sem d := by
  exact metric.distance_eq_zero_iff (sem.eval d.lhs) (sem.eval d.rhs)

/-- Commuting diagrams have zero numerical curvature. -/
theorem numericalCurvature_eq_zero_of_DiagramCommutes
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs} {d : RequiredDiagram Expr}
    (hCommutes : DiagramCommutes sem d) :
    numericalCurvature metric sem d = 0 :=
  (numericalCurvature_eq_zero_iff_DiagramCommutes metric).mpr hCommutes

/-- Zero numerical curvature forces diagram commutativity. -/
theorem DiagramCommutes_of_numericalCurvature_eq_zero
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs} {d : RequiredDiagram Expr}
    (hZero : numericalCurvature metric sem d = 0) :
    DiagramCommutes sem d :=
  (numericalCurvature_eq_zero_iff_DiagramCommutes metric).mp hZero

/--
Numerical curvature obstruction is exactly the existing diagram obstruction
predicate, for a single diagram.
-/
theorem numericalCurvatureObstruction_iff_DiagramBad
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs} {d : RequiredDiagram Expr} :
    NumericalCurvatureObstruction metric sem d ↔ DiagramBad sem d := by
  constructor
  · intro hCurvature hCommutes
    exact hCurvature
      (numericalCurvature_eq_zero_of_DiagramCommutes metric hCommutes)
  · intro hBad hZero
    exact hBad
      (DiagramCommutes_of_numericalCurvature_eq_zero metric hZero)

/--
Absence of numerical curvature obstruction for one diagram is equivalent to
diagram commutativity.
-/
theorem not_numericalCurvatureObstruction_iff_DiagramCommutes
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs} {d : RequiredDiagram Expr} :
    ¬ NumericalCurvatureObstruction metric sem d ↔ DiagramCommutes sem d := by
  constructor
  · intro hNoObstruction
    by_cases hZero : numericalCurvature metric sem d = 0
    · exact DiagramCommutes_of_numericalCurvature_eq_zero metric hZero
    · exact False.elim (hNoObstruction hZero)
  · intro hCommutes hObstruction
    exact hObstruction
      (numericalCurvature_eq_zero_of_DiagramCommutes metric hCommutes)

/--
For a required diagram family, diagram lawfulness is exactly absence of
numerical curvature obstruction.
-/
theorem diagramLawful_iff_noNumericalCurvatureObstruction
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {required : RequiredDiagram Expr -> Prop} :
    DiagramLawful sem required ↔
      NoNumericalCurvatureObstruction metric sem required := by
  constructor
  · intro hLawful d hRequired hObstruction
    exact hObstruction
      (numericalCurvature_eq_zero_of_DiagramCommutes metric
        (hLawful d hRequired))
  · intro hNoObstruction d hRequired
    exact (not_numericalCurvatureObstruction_iff_DiagramCommutes metric).mp
      (hNoObstruction d hRequired)

/--
Total numerical curvature is zero exactly when every measured diagram has zero
curvature.
-/
theorem totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {measured : List (RequiredDiagram Expr)} :
    totalCurvature metric sem measured = 0 ↔
      ∀ d, d ∈ measured -> numericalCurvature metric sem d = 0 := by
  induction measured with
  | nil =>
      simp [totalCurvature]
  | cons d ds ih =>
      constructor
      · intro hZero d' hMem
        rw [totalCurvature] at hZero
        have hHead : numericalCurvature metric sem d = 0 :=
          Nat.eq_zero_of_add_eq_zero_right hZero
        have hTail : totalCurvature metric sem ds = 0 :=
          Nat.eq_zero_of_add_eq_zero_left hZero
        simp only [List.mem_cons] at hMem
        rcases hMem with hEq | hMem
        · cases hEq
          exact hHead
        · exact ih.mp hTail d' hMem
      · intro hAll
        rw [totalCurvature]
        have hHead : numericalCurvature metric sem d = 0 :=
          hAll d (by simp)
        have hTail : totalCurvature metric sem ds = 0 :=
          ih.mpr (by
            intro d' hMem
            exact hAll d' (by simp [hMem]))
        simp [hHead, hTail]

/--
Total numerical curvature is zero exactly when every measured diagram commutes.
-/
theorem totalCurvature_eq_zero_iff_forall_measured_DiagramCommutes
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {measured : List (RequiredDiagram Expr)} :
    totalCurvature metric sem measured = 0 ↔
      ∀ d, d ∈ measured -> DiagramCommutes sem d := by
  constructor
  · intro hZero d hMem
    exact (numericalCurvature_eq_zero_iff_DiagramCommutes metric).mp
      ((totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
        metric).mp hZero d hMem)
  · intro hCommutes
    exact
      (totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
        metric).mpr (by
          intro d hMem
          exact numericalCurvature_eq_zero_of_DiagramCommutes metric
            (hCommutes d hMem))

/--
Total numerical curvature is zero exactly when the measured diagram universe has
no numerical curvature obstruction.
-/
theorem totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {measured : List (RequiredDiagram Expr)} :
    totalCurvature metric sem measured = 0 ↔
      NoMeasuredNumericalCurvatureObstruction metric sem measured := by
  rw [totalCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero]
  constructor
  · intro hZero d hMem hObstruction
    exact hObstruction (hZero d hMem)
  · intro hNoObstruction d hMem
    by_cases hZero : numericalCurvature metric sem d = 0
    · exact hZero
    · exact False.elim (hNoObstruction d hMem hZero)

/--
Weighted total numerical curvature is zero exactly when every measured diagram
has zero curvature, provided every measured diagram has a positive weight.
-/
theorem totalWeightedCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {weight : RequiredDiagram Expr -> Nat}
    {measured : List (RequiredDiagram Expr)}
    (hPositive : PositiveCurvatureWeightOn measured weight) :
    totalWeightedCurvature metric sem weight measured = 0 ↔
      ∀ d, d ∈ measured -> numericalCurvature metric sem d = 0 := by
  induction measured with
  | nil =>
      simp [totalWeightedCurvature]
  | cons d ds ih =>
      constructor
      · intro hZero d' hMem
        rw [totalWeightedCurvature] at hZero
        have hHeadWeighted :
            weight d * numericalCurvature metric sem d = 0 :=
          Nat.eq_zero_of_add_eq_zero_right hZero
        have hTail :
            totalWeightedCurvature metric sem weight ds = 0 :=
          Nat.eq_zero_of_add_eq_zero_left hZero
        have hHead : numericalCurvature metric sem d = 0 := by
          have hWeightNe : weight d ≠ 0 :=
            Nat.ne_of_gt (hPositive d (by simp))
          rcases (Nat.mul_eq_zero.mp hHeadWeighted) with hWeightZero | hCurvatureZero
          · exact False.elim (hWeightNe hWeightZero)
          · exact hCurvatureZero
        have hPositiveTail : PositiveCurvatureWeightOn ds weight := by
          intro d'' hMemTail
          exact hPositive d'' (by simp [hMemTail])
        simp only [List.mem_cons] at hMem
        rcases hMem with hEq | hMem
        · cases hEq
          exact hHead
        · exact (ih hPositiveTail).mp hTail d' hMem
      · intro hAll
        rw [totalWeightedCurvature]
        have hHead : numericalCurvature metric sem d = 0 :=
          hAll d (by simp)
        have hTail :
            totalWeightedCurvature metric sem weight ds = 0 := by
          have hPositiveTail : PositiveCurvatureWeightOn ds weight := by
            intro d' hMem
            exact hPositive d' (by simp [hMem])
          exact (ih hPositiveTail).mpr (by
            intro d' hMem
            exact hAll d' (by simp [hMem]))
        simp [hHead, hTail]

/--
Weighted total numerical curvature is zero exactly when every measured diagram
commutes, under the same positive-weight boundedness assumption.
-/
theorem totalWeightedCurvature_eq_zero_iff_forall_measured_DiagramCommutes
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {weight : RequiredDiagram Expr -> Nat}
    {measured : List (RequiredDiagram Expr)}
    (hPositive : PositiveCurvatureWeightOn measured weight) :
    totalWeightedCurvature metric sem weight measured = 0 ↔
      ∀ d, d ∈ measured -> DiagramCommutes sem d := by
  constructor
  · intro hZero d hMem
    exact (numericalCurvature_eq_zero_iff_DiagramCommutes metric).mp
      ((totalWeightedCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
        metric hPositive).mp hZero d hMem)
  · intro hCommutes
    exact
      (totalWeightedCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
        metric hPositive).mpr (by
          intro d hMem
          exact numericalCurvature_eq_zero_of_DiagramCommutes metric
            (hCommutes d hMem))

/--
Weighted total numerical curvature is zero exactly when the measured diagram
universe has no numerical curvature obstruction, provided measured weights are
positive. This theorem remains list-scoped and does not assert unmeasured
diagram coverage or empirical cost correlation.
-/
theorem totalWeightedCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction
    {Expr : Type u} {Obs : Type v}
    (metric : ZeroSeparatingDistance Obs)
    {sem : Semantics Expr Obs}
    {weight : RequiredDiagram Expr -> Nat}
    {measured : List (RequiredDiagram Expr)}
    (hPositive : PositiveCurvatureWeightOn measured weight) :
    totalWeightedCurvature metric sem weight measured = 0 ↔
      NoMeasuredNumericalCurvatureObstruction metric sem measured := by
  rw [totalWeightedCurvature_eq_zero_iff_forall_measured_numericalCurvature_eq_zero
    metric hPositive]
  constructor
  · intro hZero d hMem hObstruction
    exact hObstruction (hZero d hMem)
  · intro hNoObstruction d hMem
    by_cases hZero : numericalCurvature metric sem d = 0
    · exact hZero
    · exact False.elim (hNoObstruction d hMem hZero)

end Formal.Arch
