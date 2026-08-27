import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget

/-!
# G-112 semantic-global strong cartesian lift

This module records G-112 K2.  The mathematical construction is the reviewed
G-110 declaration `strongCartesianLiftOfTarget`; K2 fixes its unrestricted
semantic statement as the O7 wrapper and records how the realization-qualified
G-110 left branch is obtained by restriction.

## Implementation notes

The wrapper returns `HasStrongCartesianLift` rather than introducing a new lift
structure.  This keeps the predecessor construction visible in the proof term
and avoids adding a certificate field or a second choice of cartesian lift.
-/

namespace AAT.AG.DoctrineFiberProduct

open CrossStageCoherence

universe u

/--
G-112(c): every semantic exact-bottom arrow admits a strong cartesian lift to
every package in its target fiber, without a realization premise.
-/
theorem exactBottomSemanticGlobalStrongCartesianLift
    {U : AtomCarrier.{u}} (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    HasStrongCartesianLift input targetPackage := by
  exact ⟨strongCartesianLiftOfTarget input targetPackage⟩

/--
The G-110 realization-qualified global branch is the restriction of the G-112
semantic-global wrapper to `RealizableHom` inputs.
-/
theorem globalCartesianLift_of_exactBottomSemanticGlobalStrongCartesianLift :
    GlobalCartesianLift.{u} := by
  intro U _ input targetPackage
  exact exactBottomSemanticGlobalStrongCartesianLift
    input.semantic targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
