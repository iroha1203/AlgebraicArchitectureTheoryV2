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

end Formal.Arch
