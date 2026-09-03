import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeCellProjector
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducerWitnesses

/-!
# G-116 raw failure locus

This module discharges G-116(g).  At every authored diagnostic cell, the
comparison is invertible exactly when its selected idempotent factor is
invertible, and an invertible idempotent is the identity.  The finite axis-fold
fixture then supplies an assumption-free noninvertible generated comparison.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteRawFailureLocusAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- An idempotent endomorphism is invertible exactly when it is the identity. -/
theorem isIso_iff_eq_id_of_comp_self_eq_self
    {C : Type u} [Category.{v} C] {X : C} (e : X ⟶ X)
    (idem : e ≫ e = e) :
    IsIso e ↔ e = 𝟙 X := by
  constructor
  · intro isIso
    letI : IsIso e := isIso
    exact (cancel_epi_id e).1 idem
  · rintro rfl
    infer_instance

/-- The actual comparison component is invertible exactly when its selected
cell projector is invertible. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    IsIso ((authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell) ↔
      IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell) := by
  rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  exact isIso_comp_left_iff _ _

/-- The selected cell projector is invertible exactly when it is the identity. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_isIso_iff_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell) ↔
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell =
        𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) :=
  isIso_iff_eq_id_of_comp_self_eq_self _
    (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp
      input cochain cell)

/-- G-116(g), cellwise raw failure locus.  The conjunction records the two
links in the chain `IsIso beta_c iff IsIso E_c iff E_c = 1` without relying on
the parsing convention for chained biconditionals. -/
theorem authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (IsIso ((authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell) ↔
      IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell)) ∧
    (IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell) ↔
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell =
        𝟙 ((authoredSupportViaBaseRoute input.context).obj cell)) :=
  ⟨authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff
      input cochain cell,
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_isIso_iff_eq_id
      input cochain cell⟩

/-- The outer links of the same cellwise raw failure chain. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    IsIso ((authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell) ↔
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell =
        𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) :=
  (authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff
    input cochain cell).trans
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_isIso_iff_eq_id
        input cochain cell)

/-- G-116(g), named fixture theorem: the generated comparison for the fixed
finite axis-fold datum is not an isomorphism. -/
theorem finiteAxisFold_generatedAuthoredDiagnosticObjectCollapseComparison_not_isIso :
    ¬ IsIso (generatedAuthoredDiagnosticObjectCollapseComparison
      finiteAxisFoldBCDatumSquare) := by
  intro comparisonIsIso
  letI : IsIso (generatedAuthoredDiagnosticObjectCollapseComparison
      finiteAxisFoldBCDatumSquare) := comparisonIsIso
  have betaIsIso : IsIso
      ((authoredDiagnosticObjectCollapseComparisonAtCochain
          finiteAxisFoldBCDatumSquare
          (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)).app
        (Discrete.mk DoubleDiamondTwoCell.second)) := by
    change IsIso
      ((generatedAuthoredDiagnosticObjectCollapseComparison
        finiteAxisFoldBCDatumSquare).app
          (Discrete.mk DoubleDiamondTwoCell.second))
    infer_instance
  have projectorIsIso : IsIso
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        finiteAxisFoldBCDatumSquare
        (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
        (Discrete.mk DoubleDiamondTwoCell.second)) :=
    (authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff
      finiteAxisFoldBCDatumSquare
      (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
      (Discrete.mk DoubleDiamondTwoCell.second)).1 betaIsIso
  apply finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso
    (initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    DoubleDiamondTwoCell.second
  · rw [finiteAxisFold_toTransportData,
      finiteAxisFold_initialRawDefect_second]
    intro equality
    have axisEquality := congrArg
      (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
        (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
    change (1 : Fin 3) = 0 at axisEquality
    exact Fin.zero_ne_one axisEquality.symm
  · exact projectorIsIso

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
