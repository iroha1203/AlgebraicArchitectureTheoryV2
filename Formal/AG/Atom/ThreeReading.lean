import Formal.AG.Atom.Obstruction
import Formal.AG.Atom.Signature

/-!
# Equation lawfulness, finite circuits, and signature axes

This module formalizes the three readings following Part I, Theorem 9.3:
required residual vanishing, emptiness of required finite-circuit fibers, and
zero on the required equation signature axes.

Implementation notes: the circuit equivalence uses both detector soundness and
required completeness.  No equivalence conclusion is stored in a certificate
field, and all three readings are generated from one equation system.
-/

namespace AAT.AG

universe u

/-- Every required equation-indexed finite-circuit fiber is empty. -/
def NoRequiredEquationCircuit
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C}
    (R : EquationCircuitReading E) (A : ArchitectureObject U) : Prop :=
  ∀ index : E.Index, E.Required index -> IsEmpty (R.Circuit A index)

/--
Required equation lawfulness is equivalent to emptiness of required circuit
fibers when the selected detector is sound and required-complete.

The material premises are exactly `R.Sound` and `R.RequiredComplete` from Part I,
Definitions 8.2 and 8.2B.
-/
theorem equationLawful_iff_noRequiredEquationCircuit
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C}
    (R : EquationCircuitReading E) (hSound : R.Sound)
    (hComplete : R.RequiredComplete) (A : ArchitectureObject U) :
    E.EquationLawful A ↔ NoRequiredEquationCircuit R A := by
  constructor
  · intro hlawful index hrequired
    exact ⟨fun circuit =>
      (R.circuit_sound hSound A index circuit) (hlawful index hrequired)⟩
  · intro hnocircuit index hrequired
    exact Classical.byContradiction (fun hfailure => by
      obtain ⟨circuit⟩ := hComplete A index hrequired hfailure
      exact (hnocircuit index hrequired).false circuit)

/-- Canonical required signature axes generated from an equation system. -/
def requiredEquationSignatureAxes
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) : SignatureAxes U where
  Axis := E.RequiredIndex
  selected _ := True
  zero A index := E.EquationHolds index.1 A

/-- Equation lawfulness is zero on the canonical required equation axes. -/
theorem equationLawful_iff_requiredSignatureAxesZero
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) (A : ArchitectureObject U) :
    E.EquationLawful A ↔
      RequiredSignatureAxesZero A (requiredEquationSignatureAxes E) := by
  constructor
  · intro hlawful axis _hselected
    exact hlawful axis.1 axis.2
  · intro hzero index hrequired
    exact hzero ⟨index, hrequired⟩ trivial

/--
Part I, Theorem 9.3 continuation: the equation, finite-circuit, and canonical
signature readings agree under detector soundness and required completeness.
-/
theorem concreteThreeReadingAgreement
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C}
    (R : EquationCircuitReading E) (hSound : R.Sound)
    (hComplete : R.RequiredComplete) (A : ArchitectureObject U) :
    (E.EquationLawful A ↔ NoRequiredEquationCircuit R A) ∧
      (NoRequiredEquationCircuit R A ↔
        RequiredSignatureAxesZero A (requiredEquationSignatureAxes E)) ∧
        (E.EquationLawful A ↔
          RequiredSignatureAxesZero A (requiredEquationSignatureAxes E)) := by
  have hcircuit :=
    equationLawful_iff_noRequiredEquationCircuit R hSound hComplete A
  have hsignature := equationLawful_iff_requiredSignatureAxesZero E A
  exact ⟨hcircuit, hcircuit.symm.trans hsignature, hsignature⟩

end AAT.AG
