import Formal.AG.Atom.Obstruction

/-!
# Equation lawfulness and zero obstruction

This module formalizes Part I, Propositions 9.1--9.2 and Theorem 9.3 directly
for an `ArchitecturalEquationSystem`.

Implementation notes: valuation indices and required roles come from the same
equation system that defines residual vanishing.  The former predicate-valued
law surface is retained only by `Atom.LawfulnessZeroLegacy`.
-/

namespace AAT.AG

universe u

/-- I.命題9.1: equation-indexed obstruction soundness. -/
def EquationObstructionSound
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value) (index : E.Index) : Prop :=
  ∀ A : ArchitectureObject U, E.EquationHolds index A ->
    valuation.omega index A = valuation.domain.zero

/-- I.命題9.2: equation-indexed obstruction completeness. -/
def EquationObstructionComplete
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value) (index : E.Index) : Prop :=
  ∀ A : ArchitectureObject U, ¬ E.EquationHolds index A ->
    valuation.domain.positive (valuation.omega index A)

/--
I.命題9.1 / 9.2: soundness and completeness identify equation fulfillment
with zero obstruction value.

The material premises are precisely the soundness and completeness conditions
from Part I, Propositions 9.1 and 9.2.
-/
theorem equationHolds_iff_omega_zero
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value) (index : E.Index)
    (hsound : EquationObstructionSound valuation index)
    (hcomplete : EquationObstructionComplete valuation index)
    (A : ArchitectureObject U) :
    E.EquationHolds index A ↔
      valuation.omega index A = valuation.domain.zero := by
  constructor
  · intro hequation
    exact hsound A hequation
  · intro hzero
    by_cases hequation : E.EquationHolds index A
    · exact hequation
    · exact False.elim
        ((valuation.domain.noCancellationAtZero (hcomplete A hequation)) hzero)

/--
I.定理9.3: required equation lawfulness is equivalent to zero aggregate
obstruction value.

The material premises are the theorem's required-index soundness,
required-index completeness, and zero-reflecting aggregation.
-/
theorem equationLawful_iff_omegaE_zero
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex)
    (hsound :
      ∀ index : E.RequiredIndex,
        EquationObstructionSound valuation index.1)
    (hcomplete :
      ∀ index : E.RequiredIndex,
        EquationObstructionComplete valuation index.1)
    (A : ArchitectureObject U) :
    E.EquationLawful A ↔
      omegaE valuation aggregation A = valuation.domain.zero := by
  constructor
  · intro hlawful
    apply (omegaE_zero_iff_required valuation aggregation A).mpr
    intro index
    exact hsound index A (hlawful index.1 index.2)
  · intro hzero index hrequired
    let requiredIndex : E.RequiredIndex := ⟨index, hrequired⟩
    have hvalue :
        valuation.omega index A = valuation.domain.zero :=
      (omegaE_zero_iff_required valuation aggregation A).mp hzero requiredIndex
    exact (equationHolds_iff_omega_zero valuation index
      (hsound requiredIndex) (hcomplete requiredIndex) A).mpr hvalue

end AAT.AG
