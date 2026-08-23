import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticComparison
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFoldWitnesses

/-!
# Finite witnesses for the authored diagnostic comparison

The fixed lax double diamond refutes an auxiliary authored diagnostic throughout
its full reselection orbit.  The diagnostic retains the actual raw defect at
each supplied coordinate and then uses the internally generated direct-first,
pairwise-fallback fold.  The strict finite datum is the positive control.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u₁ v₁

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteAuthoredDiagnosticAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Every lax orbit coordinate supplies a noninvertible unified source fold. -/
theorem finiteAxisFold_generatedUnified_not_isIso
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    ¬ IsIso
      (show finiteAxisFoldSupportPackage ⟶ finiteAxisFoldSupportPackage from
        PackageFiberAut.generatedUnifiedAxisFoldTotalAt
          finiteAxisFoldBCDatumSquare.toTransportData
          (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
            reselection)
          DoubleDiamondTwoCell.second) :=
  PackageFiberAut.generatedUnifiedAxisFoldTotalAt_not_isIso
    finiteAxisFoldBCDatumSquare.toTransportData
    (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection)
    DoubleDiamondTwoCell.second
    (Or.inr (finiteAxisFold_input_pairwiseAvailable reselection))

/-- A functor naturally isomorphic to identity reflects isomorphisms. -/
private theorem isIso_of_map_isIso_of_natIso_id_authoredDiagnostic
    {C : Type u₁} [Category.{v₁} C] (functor : C ⥤ C)
    (unitor : functor ≅ 𝟭 C) {source target : C}
    (hom : source ⟶ target) [IsIso (functor.map hom)] : IsIso hom := by
  letI : IsIso (unitor.hom.app source ≫ hom) := by
    change IsIso (unitor.hom.app source ≫ (𝟭 C).map hom)
    rw [← unitor.hom.naturality hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (unitor.hom.app source) hom

/-- The via-base image of the selected unified fold stays noninvertible. -/
theorem finiteAxisFold_viaBaseUnified_not_isIso
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    ¬ IsIso
      (authoredViaBaseUnifiedAxisFoldComponentAtCochain
        finiteAxisFoldBCDatumSquare
        (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          reselection)
        (Discrete.mk DoubleDiamondTwoCell.second)) := by
  intro isIso
  let cochain := rawDefectCochain
    finiteAxisFoldBCDatumSquare.toTransportData reselection
  letI : IsIso
      (authoredViaBaseUnifiedAxisFoldComponentAtCochain
        finiteAxisFoldBCDatumSquare cochain
        (Discrete.mk DoubleDiamondTwoCell.second)) := isIso
  let fold := authoredUnifiedAxisFoldDecodedComponentAtCochain
    finiteAxisFoldBCDatumSquare cochain DoubleDiamondTwoCell.second
  let transported :=
    (coreFiberTransportFunctor
      (𝟙 finiteAuthoredSupportInstance.toSemantic)).map fold
  let reindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (idTypedPresentation finiteAuthoredSupportInstance))).map transported
  letI : IsIso reindexed := by
    change IsIso
      (authoredViaBaseUnifiedAxisFoldComponentAtCochain
        finiteAxisFoldBCDatumSquare cochain
        (Discrete.mk DoubleDiamondTwoCell.second))
    infer_instance
  letI : IsIso transported :=
    isIso_of_map_isIso_of_natIso_id_authoredDiagnostic
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (idTypedPresentation finiteAuthoredSupportInstance)))
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      transported
  letI : IsIso fold :=
    isIso_of_map_isIso_of_natIso_id_authoredDiagnostic
      (coreFiberTransportFunctor
        (𝟙 finiteAuthoredSupportInstance.toSemantic))
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic) fold
  letI : IsIso fold.1 := by
    change IsIso (CategoryTheory.Functor.Fiber.fiberInclusion.map fold)
    infer_instance
  have fold_heq : HEq fold.1
      (PackageFiberAut.generatedUnifiedAxisFoldTotalAt
        finiteAxisFoldBCDatumSquare.toTransportData cochain
        DoubleDiamondTwoCell.second) := by
    simpa only [fold] using
      (authoredUnifiedAxisFoldDecodedComponentAtCochain_val_heq
        finiteAxisFoldBCDatumSquare cochain DoubleDiamondTwoCell.second)
  have fold_eq : fold.1 =
      PackageFiberAut.generatedUnifiedAxisFoldTotalAt
        finiteAxisFoldBCDatumSquare.toTransportData cochain
        DoubleDiamondTwoCell.second :=
    eq_of_heq fold_heq
  apply finiteAxisFold_generatedUnified_not_isIso reselection
  rw [← fold_eq]
  infer_instance

/-- Every orbit-coordinate combined component differs from the canonical mate. -/
theorem finiteAxisFold_diagnosticComparison_ne_canonical
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    authoredDiagnosticComparisonComponentAtCochain
        finiteAxisFoldBCDatumSquare
        (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
          reselection)
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second) := by
  intro equality
  rw [authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold]
    at equality
  let canonical :=
    (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
      (Discrete.mk DoubleDiamondTwoCell.second)
  let raw := authoredViaBaseRawDefectComponentAtCochain
    finiteAxisFoldBCDatumSquare
    (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection)
    (Discrete.mk DoubleDiamondTwoCell.second)
  let fold := authoredViaBaseUnifiedAxisFoldComponentAtCochain
    finiteAxisFoldBCDatumSquare
    (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection)
    (Discrete.mk DoubleDiamondTwoCell.second)
  letI : IsIso canonical := by dsimp [canonical]; infer_instance
  letI : IsIso raw := by
    dsimp [raw]
    exact authoredViaBaseRawDefectComponentAtCochain_isIso
      finiteAxisFoldBCDatumSquare
      (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection)
      (Discrete.mk DoubleDiamondTwoCell.second)
  letI : IsIso (canonical ≫ raw) := inferInstance
  have composite_isIso : IsIso ((canonical ≫ raw) ≫ fold) := by
    rw [show (canonical ≫ raw) ≫ fold = canonical by
      simpa [canonical, raw, fold] using equality]
    infer_instance
  letI : IsIso ((canonical ≫ raw) ≫ fold) := composite_isIso
  letI : IsIso fold := IsIso.of_isIso_comp_left (canonical ≫ raw) fold
  apply finiteAxisFold_viaBaseUnified_not_isIso reselection
  simpa [fold] using (inferInstance : IsIso fold)

/-- The generated relation fails at every coordinate of the lax orbit. -/
theorem finiteAxisFold_not_mateCoherent
    (reselection : EdgeReselection
      finiteAxisFoldBCDatumSquare.toTransportData.lift) :
    ¬ GeneratedAuthoredDiagnosticMateCoherentAtCochain
      finiteAxisFoldBCDatumSquare
      (rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        reselection) := by
  apply AuthoredSupportComparison.not_agrees_of_app_ne
    (Discrete.mk DoubleDiamondTwoCell.second)
  exact finiteAxisFold_diagnosticComparison_ne_canonical reselection

/-- The mismatch is nonvanishing on the full G-106 reselection orbit. -/
theorem finiteAxisFold_not_mateCoherent_on_orbit
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (inOrbit : InReselectionOrbit
      finiteAxisFoldBCDatumSquare.toTransportData cochain) :
    ¬ GeneratedAuthoredDiagnosticMateCoherentAtCochain
      finiteAxisFoldBCDatumSquare cochain := by
  rcases inOrbit with ⟨reselection, rfl⟩
  exact finiteAxisFold_not_mateCoherent reselection

/-- The auxiliary initial-coordinate diagnostic fails on the fixed lax datum. -/
theorem finiteAxisFoldBCDatumSquare_not_generatedAuthoredDiagnosticMateCoherent :
    ¬ GeneratedAuthoredDiagnosticMateCoherentRel FiniteModel.carrier
      finiteAxisFoldBCDatumSquare := by
  rw [generatedAuthoredDiagnosticMateCoherentRel_apply,
    generatedAuthoredDiagnosticComparison_apply]
  exact finiteAxisFold_not_mateCoherent
    (1 : EdgeReselection finiteAxisFoldBCDatumSquare.toTransportData.lift)

/-- The strict finite datum fires the same auxiliary diagnostic relation. -/
theorem finiteAuthoredBCDatumSquare_generatedAuthoredDiagnosticMateCoherent :
    GeneratedAuthoredDiagnosticMateCoherentRel FiniteModel.carrier
      finiteAuthoredBCDatumSquare := by
  rw [generatedAuthoredDiagnosticMateCoherentRel_apply,
    generatedAuthoredDiagnosticComparison_apply]
  apply authoredDiagnosticComparisonAtCochain_eq_canonical
  · simpa [finiteAuthoredFactorization_toTransportData] using
      finiteAuthoredFactorization_initialRawDefect_eq_identity
  · intro supportCell
    exact finiteAuthored_pairwiseUnavailable
      (initialRawDefectCochain finiteAuthoredBCDatumSquare.toTransportData)
      supportCell

/-- The lax counterexample is tested on a genuinely nontrivial orbit. -/
theorem finiteAxisFold_authoredComparison_orbit_nontrivial :
    ∃ cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData,
      InReselectionOrbit finiteAxisFoldBCDatumSquare.toTransportData cochain ∧
        cochain ≠
          initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData :=
  finiteAxisFold_input_reselectionOrbit_nontrivial

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
