import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredComparisonNoGoWitnesses

/-!
# Cofork return-map barrier for a fixed authored target

Mathlib's `Cofork` makes the direction issue precise.  A coequalizing arrow for
an action and identity has type `Y ⟶ Q`; turning it into an endomorphism of the
fixed object `Y` requires an additional return map `Q ⟶ Y`.  If the action is
nonidentity, every such returned endomorphism is noninvertible.

The finite theorem below specializes the action to the actual lax authored
via-base residual.  It remains conditional on a supplied cofork and return map:
neither is promoted to the public K2 producer, and their input-generated
construction remains the next obligation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open CategoryTheory.Limits
open AtomFoundation CrossStageCoherence TransportCoherence

/--
A return from any cofork of a nonidentity endomorphism and identity cannot
produce an invertible endomorphism of the original object.
-/
theorem coforkReturn_not_isIso_of_ne
    {C : Type u} [Category.{v} C] {Y : C}
    (action : Y ⟶ Y) (cofork : Cofork action (𝟙 Y))
    (returnMap : cofork.pt ⟶ Y) (action_ne : action ≠ 𝟙 Y) :
    ¬ IsIso (cofork.π ≫ returnMap) := by
  intro composite_isIso
  letI : IsIso (cofork.π ≫ returnMap) := composite_isIso
  apply action_ne
  apply (cancel_mono (cofork.π ≫ returnMap)).1
  change action ≫ (cofork.π ≫ returnMap) =
    𝟙 Y ≫ (cofork.π ≫ returnMap)
  rw [← Category.assoc, cofork.condition]
  simp

/-- Identity supplies the positive control for the standard cofork API. -/
noncomputable def identityEndomorphismCofork
    {C : Type u} [Category.{v} C] (Y : C) : Cofork (𝟙 Y) (𝟙 Y) :=
  Cofork.ofπ (𝟙 Y) (by simp)

/-! ## Concrete nonidentity action -/

local instance finiteAuthoredQuotientNoGoAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Identity does not coequalize the fixed nonidentity via-base residual. -/
theorem finiteAxisFold_viaBase_identity_not_coequalizing :
    authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second) ≫
        𝟙 ((authoredSupportViaBaseRoute
          finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second)) ≠
      𝟙 ((authoredSupportViaBaseRoute
          finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second)) ≫
        𝟙 ((authoredSupportViaBaseRoute
          finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second)) := by
  simpa using finiteAxisFold_viaBaseRawDefect_second_ne_id

/--
For every cofork of the fixed lax via-base residual and identity, every explicit
return map gives a noninvertible endomorphism.  Existence and provenance of the
cofork and return remain deliberately unresolved.
-/
theorem finiteAxisFold_viaBase_coforkReturn_not_isIso
    (cofork : Cofork
      (authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second))
      (𝟙 ((authoredSupportViaBaseRoute
        finiteAxisFoldBCDatumSquare.context).obj
          (Discrete.mk DoubleDiamondTwoCell.second))))
    (returnMap : cofork.pt ⟶
      (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
        (Discrete.mk DoubleDiamondTwoCell.second)) :
    ¬ IsIso (cofork.π ≫ returnMap) :=
  coforkReturn_not_isIso_of_ne
    (authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second))
    cofork returnMap finiteAxisFold_viaBaseRawDefect_second_ne_id

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
