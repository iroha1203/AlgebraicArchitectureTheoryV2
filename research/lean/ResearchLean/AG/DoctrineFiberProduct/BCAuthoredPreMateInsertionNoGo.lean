import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredComparisonNoGoWitnesses

/-!
# Natural diagnostic insertion before the Beck--Chevalley mate

This module tests a non-Cofork route for G-110: insert the actual diagnostic
endomorphism before the generated unit--square--counit mate rather than append
an independently chosen fold.  Naturality gives a decisive normalization.
Every such source-derived insertion slides through the complete mate and
becomes the canonical mate followed by the via-base image of the same
endomorphism.  In particular, an invertible diagnostic input remains exactly
a canonical post-isomorphism twist.

The generic classification quantifies a source diagnostic.  The authored
specialization fixes that value to the actual G-106 residual and accepts no
intermediate endomorphism, comparison, equality, quotient, return map, or
noninvertibility certificate from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-! ## Generic unit--square--counit insertion -/

/--
Insert a source-fiber endomorphism immediately before the generated canonical
mate.  Expanding the mate places this endomorphism before its right unit and
therefore inside the unit--square--counit construction path.
-/
noncomputable def coreBeckChevalleyPreMateInsertion
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage) :
    (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcLeftPresentation presentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).obj sourcePackage ⟶
      (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation)) ⋙
          selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcRightPresentation presentation))).obj sourcePackage :=
  (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcLeftPresentation presentation)) ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation presentation))).map diagnostic ≫
    (coreBeckChevalleyMate presentation).app sourcePackage

/--
Naturality moves the pre-mate diagnostic through the whole generated
unit--square--counit composite.  The result is precisely a postcomposition by
the via-base image of that same diagnostic.
-/
theorem coreBeckChevalleyPreMateInsertion_eq_post
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage) :
    coreBeckChevalleyPreMateInsertion presentation diagnostic =
      (coreBeckChevalleyMate presentation).app sourcePackage ≫
        (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation)) ⋙
            selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcRightPresentation presentation))).map diagnostic :=
  (coreBeckChevalleyMate presentation).naturality diagnostic

/-- An invertible diagnostic cannot become a noninvertible interior factor. -/
theorem coreBeckChevalleyPreMateInsertion_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage)
    [IsIso diagnostic] :
    IsIso (coreBeckChevalleyPreMateInsertion presentation diagnostic) := by
  letI : IsIso (coreBeckChevalleyMate presentation) :=
    coreBeckChevalleyMate_isIso presentation
  rw [coreBeckChevalleyPreMateInsertion_eq_post]
  infer_instance

/-! ## Specialization to the authored G-106 residual -/

/--
The actual initial G-106 residual inserted before the mate on one authored
support component.  The definition consumes the decoded residual itself; it
does not accept an endomorphism or completed comparison as an argument.
-/
noncomputable def authoredPreMateDiagnosticComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    (authoredSupportDirectRoute input.context).obj cell ⟶
      (authoredSupportViaBaseRoute input.context).obj cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  exact coreBeckChevalleyPreMateInsertion presentation
    (authoredInitialRawDefectComponent normalizedInput cell.as)

/--
The authored interior-insertion route is exactly the canonical mate followed
by the already reviewed via-base raw residual.
-/
theorem authoredPreMateDiagnosticComponent_eq_canonical_comp_viaRawDefect
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    authoredPreMateDiagnosticComponent input cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseRawDefectComponent input cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact coreBeckChevalleyPreMateInsertion_eq_post presentation
    (authoredInitialRawDefectComponent
      ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
        lift, endpoint_eq⟩, twoCellBase, authored⟩ cell.as)

/-- Every authored pre-mate insertion component remains invertible. -/
theorem authoredPreMateDiagnosticComponent_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    IsIso (authoredPreMateDiagnosticComponent input cell) := by
  letI : IsIso (authoredViaBaseRawDefectComponent input cell) :=
    authoredViaBaseRawDefectComponent_isIso input cell
  rw [authoredPreMateDiagnosticComponent_eq_canonical_comp_viaRawDefect]
  infer_instance

/--
Consequently the natural unit-interior route belongs to the forbidden
canonical post-isomorphism class; it cannot be the required non-twist K2
producer.
-/
theorem authoredPreMateDiagnosticComponent_isCanonicalPostIsoTwist
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    ∃ residual :
        (authoredSupportViaBaseRoute input.context).obj cell ≅
          (authoredSupportViaBaseRoute input.context).obj cell,
      authoredPreMateDiagnosticComponent input cell =
        (authoredSupportCanonicalMate input.context).app cell ≫ residual.hom := by
  letI : IsIso (authoredViaBaseRawDefectComponent input cell) :=
    authoredViaBaseRawDefectComponent_isIso input cell
  exact ⟨asIso (authoredViaBaseRawDefectComponent input cell),
    authoredPreMateDiagnosticComponent_eq_canonical_comp_viaRawDefect input cell⟩

/-! ## Concrete lax firing -/

local instance finitePreMateInsertionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/--
The natural insertion is genuinely noncanonical on the fixed lax second face;
the mismatch is derived from the actual transported adjacent-swap residual.
-/
theorem finiteAxisFold_preMateDiagnostic_second_ne_canonical :
    authoredPreMateDiagnosticComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) ≠
      (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second) := by
  intro equality
  rw [authoredPreMateDiagnosticComponent_eq_canonical_comp_viaRawDefect]
    at equality
  have residual_eq :
      authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second) = 𝟙 _ := by
    apply (cancel_epi
      ((authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
        (Discrete.mk DoubleDiamondTwoCell.second))).1
    simpa using equality
  exact finiteAxisFold_viaBaseRawDefect_second_ne_id residual_eq

/--
The concrete mismatch therefore has the actual nonidentity via-base residual
as an invertible postfactor.  It is a finite firing of the route obstruction,
not a K2 negative witness.
-/
theorem finiteAxisFold_preMateDiagnostic_has_nontrivial_postIsoResidual :
    ∃ residual :
        (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second) ≅
          (authoredSupportViaBaseRoute finiteAxisFoldBCDatumSquare.context).obj
            (Discrete.mk DoubleDiamondTwoCell.second),
      authoredPreMateDiagnosticComponent finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second) =
          (authoredSupportCanonicalMate finiteAxisFoldBCDatumSquare.context).app
              (Discrete.mk DoubleDiamondTwoCell.second) ≫ residual.hom ∧
        residual.hom ≠
          𝟙 ((authoredSupportViaBaseRoute
            finiteAxisFoldBCDatumSquare.context).obj
              (Discrete.mk DoubleDiamondTwoCell.second)) := by
  letI : IsIso
      (authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)) :=
    authoredViaBaseRawDefectComponent_isIso finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
  refine ⟨asIso
      (authoredViaBaseRawDefectComponent finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)),
    authoredPreMateDiagnosticComponent_eq_canonical_comp_viaRawDefect
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second), ?_⟩
  exact finiteAxisFold_viaBaseRawDefect_second_ne_id

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
