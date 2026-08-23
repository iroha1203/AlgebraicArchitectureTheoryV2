import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredComparisonNoGo
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFoldWitnesses

/-!
# Finite firing witness for the authored factorization obstruction

The fixed lax double diamond makes the Cycle 43 transported raw residual
nonidentity at its second face.  Hence that exact factorization comparison is
concretely different from the canonical mate and its residual classification
fires without assuming a mismatch.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u₁ v₁

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteAuthoredNoGoAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The Cycle 43 transported raw residual is nonidentity on the lax second face. -/
theorem finiteAxisFold_viaBaseRawDefect_second_ne_id :
    authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      𝟙 ((authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
        (Discrete.mk DoubleDiamondTwoCell.second)) := by
  intro viaBase_eq
  let raw := authoredInitialRawDefectComponent finiteAxisFoldBCDatumSquare
    DoubleDiamondTwoCell.second
  let transported :=
    (coreFiberTransportFunctor
      (𝟙 finiteAuthoredSupportInstance.toSemantic)).map raw
  let reindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (idTypedPresentation finiteAuthoredSupportInstance))).map transported
  have reindexed_eq : reindexed = 𝟙 _ := by
    change authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) = 𝟙 _
    exact viaBase_eq
  have transported_eq : transported = 𝟙 _ :=
    eq_id_of_map_eq_id_of_natIso
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (idTypedPresentation finiteAuthoredSupportInstance)))
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      transported reindexed_eq
  have raw_eq : raw = 𝟙 _ :=
    eq_id_of_map_eq_id_of_natIso
      (coreFiberTransportFunctor
        (𝟙 finiteAuthoredSupportInstance.toSemantic))
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic)
      raw transported_eq
  have total_eq := congrArg
    (fun component => component.1) raw_eq
  change PackageFiberAut.hom
      (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        DoubleDiamondTwoCell.second) =
    PackageTotalHom.id finiteAxisFoldSupportPackage at total_eq
  have initial_eq :
      initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          DoubleDiamondTwoCell.second = finiteAxisFoldSwap := by
    simpa only [finiteAxisFold_toTransportData] using
      finiteAxisFold_initialRawDefect_second
  rw [initial_eq] at total_eq
  have axis_eq := congrArg
    (fun total => total.upper.axisMap (0 : Fin 3)) total_eq
  change (1 : Fin 3) = 0 at axis_eq
  exact Fin.zero_ne_one axis_eq.symm

/-- The exact Cycle 43 comparison is concretely noncanonical on the lax witness. -/
theorem finiteAxisFold_factorizationComparison_second_ne_canonical :
    authoredFactorizationComparisonComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second) := by
  intro equality
  rw [authoredFactorizationComparisonComponent_eq_canonical_comp_viaRawDefect]
    at equality
  have residual_eq :
      authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second) = 𝟙 _ := by
    apply (cancel_epi
      ((authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second))).1
    simpa using equality
  exact finiteAxisFold_viaBaseRawDefect_second_ne_id residual_eq

/-- The finite mismatch produces a nonidentity canonical-post-isomorphism residual. -/
theorem finiteAxisFold_factorizationComparison_second_has_nontrivial_residual :
    ∃ residual :
        (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second) ≅
          (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second),
      authoredFactorizationComparisonComponent finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second) =
          (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
              (Discrete.mk DoubleDiamondTwoCell.second) ≫ residual.hom ∧
        residual.hom ≠
          𝟙 ((authoredSupportViaBaseRoute
            finiteAxisFoldBCDatumSquare.context).obj
              (Discrete.mk DoubleDiamondTwoCell.second)) :=
  authoredFactorizationComparisonComponent_has_nontrivial_residual_of_ne
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    finiteAxisFold_factorizationComparison_second_ne_canonical

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
