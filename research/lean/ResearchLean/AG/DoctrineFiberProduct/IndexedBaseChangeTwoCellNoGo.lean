import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses

/-!
# A two-cell base-congruence obstruction for indexed base change

Edgewise indexed square transport produces target packages, target total
morphisms, and their strongly cocartesian qualifications.  To reassemble an
arbitrary-source `AdmissibleTransportData`, however, a source two-cell base
equality must also generate equality of the two target path bases.

Pasting the edge squares gives equality only after precomposition by the
vertex transport index.  This module fixes a finite non-epimorphic transport
index showing that such precomposition cannot be cancelled on the full
`ExtractionInstance` domain.  Thus a generated base-congruence action is
additional data that the current F0 producer does not supply.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- The cancellation law needed to turn pasted edge squares into a target
two-cell base equality at one vertex transport index. -/
def IndexedTargetBaseCongruenceAt {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (index : source ⟶ target) : Prop :=
  ∀ (endpoint : ExtractionInstance U) (left right : target ⟶ endpoint),
    index ≫ left = index ≫ right → left = right

/-- The required target base-congruence law is exactly epimorphicity of the
vertex transport index. -/
theorem indexedTargetBaseCongruenceAt_iff_epi {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (index : source ⟶ target) :
    IndexedTargetBaseCongruenceAt index ↔ Epi index := by
  simpa [IndexedTargetBaseCongruenceAt] using
    (CategoryTheory.epi_iff_forall_injective index).symm

local instance g111FiniteModelCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The selected-point-preserving inclusion from the one-source finite
instance into the two-source finite instance. -/
def finiteOneToTwoPresentation :
    CartPresentationBetween finiteOneSourceInstance finiteTwoSourceInstance where
  sourceMap := fun _ => finiteTwoSourceZero
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- A constant endomorphism of the two-source finite instance fixing its
selected point. -/
def finiteTwoSourceConstantPresentation :
    CartPresentationBetween finiteTwoSourceInstance finiteTwoSourceInstance where
  sourceMap := fun _ => finiteTwoSourceZero
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- Semantic one-to-two transport index used by the no-go witness. -/
def finiteOneToTwoIndex :
    finiteOneSourceInstance.toSemantic ⟶ finiteTwoSourceInstance.toSemantic :=
  typedPresentationToSemantic finiteOneToTwoPresentation

/-- Semantic identity target path in the no-go witness. -/
def finiteTwoSourceIdentity :
    finiteTwoSourceInstance.toSemantic ⟶ finiteTwoSourceInstance.toSemantic :=
  𝟙 _

/-- Semantic constant target path in the no-go witness. -/
def finiteTwoSourceConstant :
    finiteTwoSourceInstance.toSemantic ⟶ finiteTwoSourceInstance.toSemantic :=
  typedPresentationToSemantic finiteTwoSourceConstantPresentation

/-- The transport index cannot distinguish the identity and constant target
paths after precomposition. -/
theorem finiteOneToTwo_comp_identity_eq_constant :
    finiteOneToTwoIndex ≫ finiteTwoSourceIdentity =
      finiteOneToTwoIndex ≫ finiteTwoSourceConstant := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The two target paths are nevertheless distinct. -/
theorem finiteTwoSourceIdentity_ne_constant :
    finiteTwoSourceIdentity ≠ finiteTwoSourceConstant := by
  intro equality
  have sourceEquality := congrArg
    (fun hom : finiteTwoSourceInstance.toSemantic ⟶
        finiteTwoSourceInstance.toSemantic =>
      hom.doctrineHom.sourceMap finiteTwoSourceOne) equality
  change finiteTwoSourceOne = finiteTwoSourceZero at sourceEquality
  have downEquality := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val)
    sourceEquality
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at downEquality

/-- The finite vertex transport index is not epimorphic in `ExtInst_U`. -/
theorem finiteOneToTwoIndex_not_epi : ¬ Epi finiteOneToTwoIndex := by
  intro epiIndex
  letI : Epi finiteOneToTwoIndex := epiIndex
  exact finiteTwoSourceIdentity_ne_constant
    ((cancel_epi finiteOneToTwoIndex).mp
      finiteOneToTwo_comp_identity_eq_constant)

/-- Full-domain edge-square data cannot supply the cancellation law required
to generate every target two-cell base equality. -/
theorem finiteOneToTwo_no_targetBaseCongruence :
    ¬ IndexedTargetBaseCongruenceAt finiteOneToTwoIndex := by
  rw [indexedTargetBaseCongruenceAt_iff_epi]
  exact finiteOneToTwoIndex_not_epi

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
