import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducer
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalizationWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapse
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticComparisonWitnesses

/-!
# Finite witnesses for the all-input diagnostic object-collapse producer

The strict fixture has identity raw diagnostic and satisfies the public
relation. On the lax double diamond, the package-selected canonical
normalization is admissible at every tagged face and specializes to the
reviewed Cycle 63 erasure. Every genuine G-106 reselection therefore selects a
noninvertible factor and violates the same public comparison equation.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteObjectCollapseProducerAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Every tagged lax support package satisfies the canonical-normalization
reading laws. -/
theorem finiteAxisFold_canonicalNormalizationAdmissibleAt
    (cell : finiteAxisFoldBCDatumSquare.context.square.semantic.diagnostic.TwoCell) :
    CanonicalObjectNormalizationAdmissible
      (finiteAxisFoldBCDatumSquare.context.supportPackage cell) := by
  simpa using finiteCanonicalObjectNormalization_admissible

/-- The package-selected canonical normalization on any tagged lax support
object. -/
noncomputable def finiteAxisFoldCanonicalNormalizationSupportComponent
    (cell : finiteAxisFoldBCDatumSquare.context.square.semantic.diagnostic.TwoCell) :
    finiteAxisFoldBCDatumSquare.context.supportObject cell ⟶
      finiteAxisFoldBCDatumSquare.context.supportObject cell :=
  authoredSupportCanonicalNormalizationComponent
    finiteAxisFoldBCDatumSquare cell
    (finiteAxisFold_canonicalNormalizationAdmissibleAt cell)

/-- The finite erasure remains noninvertible in the southwest fiber. -/
theorem finiteAxisFoldCanonicalNormalizationSupportComponent_not_isIso
    (cell : finiteAxisFoldBCDatumSquare.context.square.semantic.diagnostic.TwoCell) :
    ¬ IsIso (finiteAxisFoldCanonicalNormalizationSupportComponent cell) := by
  intro fiberIsIso
  letI : IsIso (finiteAxisFoldCanonicalNormalizationSupportComponent cell) :=
    fiberIsIso
  have selectedIsIso : IsIso
      (show finiteAxisFoldSupportPackage ⟶ finiteAxisFoldSupportPackage from
        canonicalObjectNormalizationTotal finiteAxisFoldSupportPackage
          (finiteAxisFold_canonicalNormalizationAdmissibleAt cell)) := by
    change IsIso (CategoryTheory.Functor.Fiber.fiberInclusion.map
      (finiteAxisFoldCanonicalNormalizationSupportComponent cell))
    infer_instance
  have total_eq := canonicalObjectNormalizationTotal_proof_irrel
    finiteAxisFoldSupportPackage
    (finiteAxisFold_canonicalNormalizationAdmissibleAt cell)
    finiteCanonicalObjectNormalization_admissible
  rw [total_eq] at selectedIsIso
  exact finiteCanonicalObjectNormalizationTotal_not_isIso selectedIsIso

/-- A firing lax component makes the all-input selected southwest factor
noninvertible. -/
theorem finiteAxisFold_generatedObjectCollapseComponent_not_isIso
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit)
    (fires : cochain cell ≠ 1) :
    ¬ IsIso (authoredDiagnosticObjectCollapseComponentAtCochain
      finiteAxisFoldBCDatumSquare cochain cell) := by
  rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
    finiteAxisFoldBCDatumSquare cochain cell fires
      (finiteAxisFold_canonicalNormalizationAdmissibleAt cell)]
  exact finiteAxisFoldCanonicalNormalizationSupportComponent_not_isIso cell

/-- The firing selected factor remains noninvertible on the public via-base
route of the finite identity presentation. -/
theorem finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit)
    (fires : cochain cell ≠ 1) :
    ¬ IsIso (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
      finiteAxisFoldBCDatumSquare cochain (Discrete.mk cell)) := by
  intro imageIsIso
  letI : IsIso
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        finiteAxisFoldBCDatumSquare cochain (Discrete.mk cell)) := imageIsIso
  let factor := authoredDiagnosticObjectCollapseComponentAtCochain
    finiteAxisFoldBCDatumSquare cochain cell
  let transported :=
    (coreFiberTransportFunctor
      (𝟙 finiteAuthoredSupportInstance.toSemantic)).map factor
  let reindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (idTypedPresentation finiteAuthoredSupportInstance))).map transported
  letI : IsIso reindexed := by
    change IsIso
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        finiteAxisFoldBCDatumSquare cochain (Discrete.mk cell))
    infer_instance
  letI : IsIso transported :=
    isIso_of_map_isIso_of_natIso
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (idTypedPresentation finiteAuthoredSupportInstance)))
      (selectedCoreFiberReindexUnitor finiteAuthoredSupportInstance).symm
      transported
  letI : IsIso factor :=
    isIso_of_map_isIso_of_natIso
      (coreFiberTransportFunctor
        (𝟙 finiteAuthoredSupportInstance.toSemantic))
      (coreFiberUnitor finiteAuthoredSupportInstance.toSemantic) factor
  exact finiteAxisFold_generatedObjectCollapseComponent_not_isIso
    cochain cell fires (by change IsIso factor; infer_instance)

/-- A firing selected factor makes the all-input comparison differ from the
canonical mate at that tagged component. -/
theorem finiteAxisFold_generatedObjectCollapseComparison_app_ne_canonical
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit)
    (fires : cochain cell ≠ 1) :
    (authoredDiagnosticObjectCollapseComparisonAtCochain
        finiteAxisFoldBCDatumSquare cochain).app (Discrete.mk cell) ≠
      (authoredSupportCanonicalMate
        finiteAxisFoldBCDatumSquare.context).app (Discrete.mk cell) := by
  intro equality
  rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app] at equality
  have factor_eq :
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          finiteAxisFoldBCDatumSquare cochain (Discrete.mk cell) =
        𝟙 ((authoredSupportViaBaseRoute
          finiteAxisFoldBCDatumSquare.context).obj (Discrete.mk cell)) := by
    apply (cancel_epi
      ((authoredSupportCanonicalMate
        finiteAxisFoldBCDatumSquare.context).app (Discrete.mk cell))).1
    simpa using equality
  apply finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso
    cochain cell fires
  rw [factor_eq]
  infer_instance

/-- The same firing component still separates the generated comparison from
the canonical mate after changing only the genuine G-106 edge
trivializations. -/
theorem finiteAxisFold_reselectEdges_generatedComparison_app_ne_canonical
    (reselection : EdgeReselection finiteAxisFoldBCDatumSquare.context.lift)
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (cell : DoubleDiamondTwoCell PUnit)
    (fires : cochain cell ≠ 1) :
    (authoredDiagnosticObjectCollapseComparisonAtCochain
        (finiteAxisFoldBCDatumSquare.reselectEdges reselection) cochain).app
          (Discrete.mk cell) ≠
      (authoredSupportCanonicalMate
        (finiteAxisFoldBCDatumSquare.reselectEdges reselection).context).app
          (Discrete.mk cell) := by
  simpa [AuthoredBCDatumSquare.reselectEdges,
    AuthoredSupportContext.supportPackage,
    AuthoredSupportContext.supportObject,
    AuthoredSupportContext.supportFunctor,
    authoredSupportCanonicalMate,
    authoredSupportViaBaseRoute,
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain] using
    finiteAxisFold_generatedObjectCollapseComparison_app_ne_canonical
      cochain cell fires

/-- Cochain-indexed form of the fixed public comparison equation. -/
def MateCoherentAtCochain
    (input : AuthoredBCDatumSquare FiniteModel.carrier)
    (cochain : DefectCochain input.toTransportData) : Prop :=
  AuthoredSupportComparison.Agrees
    (authoredDiagnosticObjectCollapseComparisonAtCochain input cochain)
    (authoredSupportCanonicalMate input.context)

/-- The auxiliary cochain-indexed equation holds on the strict fixture at the
identity diagnostic cochain. -/
theorem finiteAuthoredBCDatumSquare_mateCoherentAtIdentityCochain :
    MateCoherentAtCochain finiteAuthoredBCDatumSquare
      (identityDefectCochain finiteAuthoredBCDatumSquare.toTransportData) := by
  exact authoredDiagnosticObjectCollapseComparisonAtCochain_eq_canonical
    finiteAuthoredBCDatumSquare _ rfl

/-- The all-input non-twist comparison mismatch survives every genuine G-106
reselection of the lax fixture. -/
theorem finiteAxisFold_not_mateCoherentAtCochain_on_orbit
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (inOrbit : InReselectionOrbit
      finiteAxisFoldBCDatumSquare.toTransportData cochain) :
    ¬ MateCoherentAtCochain finiteAxisFoldBCDatumSquare cochain := by
  rcases inOrbit with ⟨reselection, rfl⟩
  have cochain_ne :
      rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection ≠
        identityDefectCochain finiteAxisFoldBCDatumSquare.toTransportData := by
    intro equality
    apply finiteAxisFold_not_coherentizable
    exact ⟨reselection,
      (coherentAt_iff_rawDefectCochain_eq_identity
        finiteAxisFoldBCDatumSquare.toTransportData reselection).2 equality⟩
  have fires : ∃ cell,
      rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        reselection cell ≠ 1 := by
    by_contra none
    apply cochain_ne
    funext cell
    by_contra component_ne
    exact none ⟨cell, component_ne⟩
  rcases fires with ⟨cell, fires⟩
  apply AuthoredSupportComparison.not_agrees_of_app_ne (Discrete.mk cell)
  exact finiteAxisFold_generatedObjectCollapseComparison_app_ne_canonical
    _ cell fires

/-- Every genuine edge-reselection representative of the finite lax datum
fails the same fixed public `MateCoherentRel`. -/
theorem finiteAxisFold_reselectEdges_not_mateCoherentRel
    (reselection : EdgeReselection finiteAxisFoldBCDatumSquare.context.lift) :
    ¬ MateCoherentRel FiniteModel.carrier
      (finiteAxisFoldBCDatumSquare.reselectEdges reselection) := by
  rw [MateCoherentRel_apply,
    generatedAuthoredDiagnosticObjectCollapseComparison_apply]
  rw [finiteAxisFoldBCDatumSquare.initialRawDefectCochain_reselectEdges
    reselection]
  have cochain_ne :
      rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData reselection ≠
        identityDefectCochain finiteAxisFoldBCDatumSquare.toTransportData := by
    intro equality
    apply finiteAxisFold_not_coherentizable
    exact ⟨reselection,
      (coherentAt_iff_rawDefectCochain_eq_identity
        finiteAxisFoldBCDatumSquare.toTransportData reselection).2 equality⟩
  have fires : ∃ cell,
      rawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData
        reselection cell ≠ 1 := by
    by_contra none
    apply cochain_ne
    funext cell
    by_contra component_ne
    exact none ⟨cell, component_ne⟩
  rcases fires with ⟨cell, fires⟩
  apply AuthoredSupportComparison.not_agrees_of_app_ne (Discrete.mk cell)
  exact finiteAxisFold_reselectEdges_generatedComparison_app_ne_canonical
    reselection _ cell fires

/-- Every cochain in the actual G-106 reselection orbit is realized as the
initial raw diagnostic of a datum on which the same fixed public relation
fails. -/
theorem finiteAxisFold_public_not_mateCoherentRel_on_orbit
    (cochain : DefectCochain finiteAxisFoldBCDatumSquare.toTransportData)
    (inOrbit : InReselectionOrbit
      finiteAxisFoldBCDatumSquare.toTransportData cochain) :
    ∃ reselection : EdgeReselection finiteAxisFoldBCDatumSquare.context.lift,
      initialRawDefectCochain
          (finiteAxisFoldBCDatumSquare.reselectEdges reselection).toTransportData =
        cochain ∧
      ¬ MateCoherentRel FiniteModel.carrier
        (finiteAxisFoldBCDatumSquare.reselectEdges reselection) := by
  rcases inOrbit with ⟨reselection, rfl⟩
  exact ⟨reselection,
    finiteAxisFoldBCDatumSquare.initialRawDefectCochain_reselectEdges reselection,
    finiteAxisFold_reselectEdges_not_mateCoherentRel reselection⟩

/-- The fixed lax datum refutes the public `MateCoherentRel`. -/
theorem finiteAxisFoldBCDatumSquare_not_mateCoherentRel :
    ¬ MateCoherentRel FiniteModel.carrier finiteAxisFoldBCDatumSquare := by
  rw [MateCoherentRel_apply,
    generatedAuthoredDiagnosticObjectCollapseComparison_apply]
  apply AuthoredSupportComparison.not_agrees_of_app_ne
    (Discrete.mk DoubleDiamondTwoCell.second)
  apply finiteAxisFold_generatedObjectCollapseComparison_app_ne_canonical
  rw [finiteAxisFold_toTransportData,
    finiteAxisFold_initialRawDefect_second]
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  exact Fin.zero_ne_one axisEquality.symm

/-- The existing strict datum satisfies the same public relation. -/
theorem finiteAuthoredBCDatumSquare_mateCoherentRel :
    MateCoherentRel FiniteModel.carrier finiteAuthoredBCDatumSquare := by
  apply mateCoherentRel_of_initialRawDefect_eq_identity
  simpa [finiteAuthoredFactorization_toTransportData] using
    finiteAuthoredFactorization_initialRawDefect_eq_identity

/-- Presentation replacement preserves the lax public counterexample. -/
theorem finiteAxisFold_replacePresentation_not_mateCoherentRel
    (replacement : BCRealizationProvenance
      finiteAxisFoldBCDatumSquare.context.square.semantic) :
    ¬ MateCoherentRel FiniteModel.carrier
      (finiteAxisFoldBCDatumSquare.replacePresentation replacement) := by
  rw [mateCoherentRel_replacePresentation_iff]
  exact finiteAxisFoldBCDatumSquare_not_mateCoherentRel

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
