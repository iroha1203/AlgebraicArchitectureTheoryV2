import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Core-fiber lift axis API

This lightweight owner-adjacent module exposes the canonical lift's action on
signature axes so downstream exactness proofs do not unfold transport
constructors.
-/

namespace AAT.AG.CrossStageCoherence

universe u

open AtomFoundation

/-- The canonical core-fiber lift is the identity on signature axes. -/
theorem coreFiberLift_axisMap
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (package : CoreFiber X)
    (axis : package.1.reading.signatureReading.Axis) :
    (coreFiberLift base package).upper.axisMap axis = axis := by
  simp [coreFiberLift, transportAlongHom, transportAlongUpper]

#assert_standard_axioms_only AAT.AG.CrossStageCoherence

end AAT.AG.CrossStageCoherence
