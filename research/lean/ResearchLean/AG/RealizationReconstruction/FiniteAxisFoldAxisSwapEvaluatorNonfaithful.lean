import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldComparisonCompletenessReduction
import Formal.Util.AssertStandardAxioms

/-!
# The current finite-axis-table evaluator is not faithful

The current source grammar contains one primitive leaf for every finite axis
table, but its generated congruence only records inverse-table laws.  In
particular, the primitive leaf carrying the identity table is not identified
with the categorical identity.

This file makes that candidate defect explicit.  A Boolean parity of primitive
axis-table leaves is invariant under every existing congruence constructor.  It
separates the identity-table leaf from the source identity, while both evaluate
to the same actual endpoint automorphism.  Consequently the current direct and
whole comparison evaluators are not injective.

This refutes only this particular congruence, not the fixed G-123 target.  A
repaired grammar may add source-derived table multiplication and identity laws;
it must still prove completeness for every actual endpoint automorphism without
using semantic equality as syntax congruence.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

local instance finiteAxisFoldAxisSwapEvaluatorNonfaithfulAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldAxisSwapSyntax

/-- Parity of primitive finite-axis-table leaves.  Normalization retains the
same source occurrence; old syntax contributes no new axis-table leaf. -/
def axisLeafParity {X Y} : FiniteAxisFoldAxisSwapSyntax X Y → Bool
  | .base _ => false
  | .axisDirect _ => true
  | .normalizeSectionDirect term => axisLeafParity term
  | .compose first second => xor (axisLeafParity first) (axisLeafParity second)

/-- Every law in the current source congruence preserves axis-leaf parity. -/
theorem axisLeafParity_eq_of_congruent {X Y}
    {first second : FiniteAxisFoldAxisSwapSyntax X Y}
    (relation : Congruent first second) :
    axisLeafParity first = axisLeafParity second := by
  induction relation with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | comp _ _ firstIH secondIH => simp [axisLeafParity, firstIH, secondIH]
  | base _ => rfl
  | base_comp _ _ => rfl
  | normalizeSectionDirect _ ih => simpa [axisLeafParity] using ih
  | id_comp _ => simp [axisLeafParity]
  | comp_id _ => simp [axisLeafParity]
  | assoc first second third =>
      cases axisLeafParity first <;>
        cases axisLeafParity second <;>
          cases axisLeafParity third <;> simp [axisLeafParity]
  | axisDirect_inv _ => rfl
  | normalizedAxisDirect_inv _ => rfl

/-- Even the identity finite table remains distinct from the categorical
identity in the current generated congruence. -/
theorem identityAxisDirect_not_congruent_identity :
    ¬ Congruent (.axisDirect (Equiv.refl (Fin 3)))
      (.base (.base (.identity (.direct finiteAxisFoldG122CellInput)))) := by
  intro relation
  have parityEquality := axisLeafParity_eq_of_congruent relation
  cases parityEquality

end FiniteAxisFoldAxisSwapSyntax

namespace FiniteAxisFoldAxisSwapPresentation

/-- The identity-table primitive gives a nonidentity displayed automorphism in
the current quotient. -/
theorem directIdentityAxisTableAut_ne_one :
    directAxisPermutationAut (Equiv.refl (Fin 3)) ≠ 1 := by
  intro equality
  have homEquality := congrArg Iso.hom equality
  have relation := Quotient.exact homEquality
  exact FiniteAxisFoldAxisSwapSyntax.identityAxisDirect_not_congruent_identity
    relation

/-- Nevertheless, the identity-table primitive evaluates to the actual
identity endpoint automorphism. -/
theorem directIdentityAxisTableAut_evaluation :
    directAutomorphismEvaluationHom
        (directAxisPermutationAut (Equiv.refl (Fin 3))) = 1 := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  change (finiteAxisFoldActualDirectPermutationAut
      (Equiv.refl (Fin 3))).hom.1 = _
  change (((geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).map
    ((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        (finiteAxisFoldSouthwestPermutationAut
          (Equiv.refl (Fin 3))).hom))).1 = _
  rw [show (finiteAxisFoldSouthwestPermutationAut
      (Equiv.refl (Fin 3))).hom = 𝟙 _ by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldPermutationGeometry_refl]
  have mappedIdentity :
      (geomFiberTransportFunctor
          finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).map
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (𝟙 finiteAxisFoldSouthwestGeometryFiber)) = 𝟙 _ := by
    calc
      _ = (geomFiberTransportFunctor
            finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).map
          (𝟙 _) := congrArg
            (fun f => (geomFiberTransportFunctor
              finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).map f)
            ((exactGeometryPullFunctor
              (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map_id _)
      _ = 𝟙 _ := (geomFiberTransportFunctor
        finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).map_id _
  exact congrArg Subtype.val mappedIdentity

/-- The current direct endpoint evaluator is therefore not faithful. -/
theorem directAutomorphismEvaluationHom_not_injective :
    ¬ Function.Injective directAutomorphismEvaluationHom := by
  intro injective
  apply directIdentityAxisTableAut_ne_one
  apply injective
  exact directIdentityAxisTableAut_evaluation.trans
    (map_one directAutomorphismEvaluationHom).symm

/-- By the exact Cycle 182 reduction, the current whole comparison evaluator
is not faithful either. -/
theorem comparisonEvaluationHom_not_injective :
    ¬ Function.Injective comparisonEvaluationHom := by
  intro comparisonInjective
  exact directAutomorphismEvaluationHom_not_injective
    (_root_.AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonCompletenessReduction.comparisonEvaluation_injective_iff_direct.mp
      comparisonInjective)

end FiniteAxisFoldAxisSwapPresentation

end

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
