import ResearchLean.AG.DoctrineFiberProduct.BCPastingClosure
import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchemaWitnesses

/-!
# Finite firing witnesses for pullback-pasting closure

The existing noninvertible horizontal and vertical seeds both fire the K4/E
closure package.  Their generated outer presentations have four source cells,
so the combined witness does not rely on an empty pasted presentation.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-- Executable equality for the concrete finite Atom carrier. -/
local instance finiteBCPastingClosureCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The concrete horizontal noninvertible seed fires the closure package. -/
theorem finiteHorizontalBCPastingClosure :
    BCPastingClosure (.horizontal finiteHorizontalBCPastingData) :=
  bcPastingClosure (.horizontal finiteHorizontalBCPastingData)

/-- The concrete vertical noninvertible seed fires the closure package. -/
theorem finiteVerticalBCPastingClosure :
    BCPastingClosure (.vertical finiteVerticalBCPastingData) :=
  bcPastingClosure (.vertical finiteVerticalBCPastingData)

/--
Horizontal and vertical closure fire simultaneously on named finite seeds, and
both generated outer presentations retain four source cells.
-/
theorem finiteBCPastingClosure_nonvacuous :
    BCPastingClosure (.horizontal finiteHorizontalBCPastingData) ∧
      BCPastingClosure (.vertical finiteVerticalBCPastingData) ∧
      readBCProjection (.cart .top .sourceCard)
          finiteHorizontalBCPastingData.pastePresentation = ULift.up 4 ∧
      readBCProjection (.cart .top .sourceCard)
          finiteVerticalBCPastingData.pastePresentation = ULift.up 4 ∧
      ¬ IsIso
          (toSemanticCart
            finiteHorizontalBCPastingData.bottomLeft.toPresentation).hom ∧
      ¬ IsIso
          (toSemanticCart
            finiteVerticalBCPastingData.bottom.toPresentation).hom := by
  exact ⟨finiteHorizontalBCPastingClosure,
    finiteVerticalBCPastingClosure,
    finiteHorizontalBCPasting_sourceCard,
    finiteVerticalBCPasting_sourceCard,
    finiteConstantPresentation_not_isIso,
    finiteConstantPresentation_not_isIso⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
