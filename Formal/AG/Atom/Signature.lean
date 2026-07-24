import Formal.AG.Atom.ArchitectureObject

/-!
# Selected architecture-signature axes

This module contains the Part I signature-axis reading shared by equation
lawfulness, representation analysis, and finite examples.

Implementation notes: signature axes are independent of the legacy
predicate-valued law display.  They remain a selected reading interface whose
exact comparison with an architectural equation system is stated by theorems
in the consumer modules.
-/

namespace AAT.AG

universe u

/-- I.定義10.3: selected signature axes and their object-indexed zero readings. -/
structure SignatureAxes (U : AtomCarrier.{u}) where
  Axis : Type u
  selected : Axis -> Prop
  zero : ArchitectureObject U -> Axis -> Prop

/-- Every selected signature axis reads as zero on the architecture object. -/
def RequiredSignatureAxesZero {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (S : SignatureAxes U) : Prop :=
  ∀ axis : S.Axis, S.selected axis -> S.zero A axis

/-- A required-axis-zero reading exposes zero on each selected axis. -/
theorem requiredSignatureAxesZero_axis {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : SignatureAxes U}
    (h : RequiredSignatureAxesZero A S) {axis : S.Axis}
    (hselected : S.selected axis) :
    S.zero A axis :=
  h axis hselected

end AAT.AG
