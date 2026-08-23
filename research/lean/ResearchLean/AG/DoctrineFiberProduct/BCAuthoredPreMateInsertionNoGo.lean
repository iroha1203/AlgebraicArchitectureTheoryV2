import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredComparisonNoGoWitnesses

/-!
# Natural diagnostic insertion before the Beck--Chevalley mate

This module tests a non-Cofork route for G-110: insert the actual diagnostic
endomorphism at each natural boundary of the generated
unit--square--counit mate rather than append an independently chosen fold.
The unit, square comparison, and counit naturality laws separately identify
the placements before the unit, after the unit, after the square, and after
the counit.  Every such source-derived insertion therefore becomes the
canonical mate followed by the via-base image of the same endomorphism.  In
particular, an invertible diagnostic input remains exactly a canonical
post-isomorphism twist.

The generic classification quantifies a source diagnostic.  The authored
specialization fixes that value to the actual G-106 residual and accepts no
intermediate endomorphism, comparison, equality, quotient, return map, or
noninvertibility certificate from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 3000000

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
The same source diagnostic placed after the right-adjunction unit and before
the generated square comparison.  Its endomorphism at that boundary is forced
by the right transport and reindex functors.
-/
noncomputable def coreBeckChevalleyPostUnitInsertion
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
              (bcRightPresentation presentation))).obj sourcePackage := by
  let leftReindex := selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcLeftPresentation presentation))
  let topTransport := coreFiberTransportFunctor
    (typedPresentationToSemantic (bcTopPresentation presentation))
  let rightTransport := coreFiberTransportFunctor
    (typedPresentationToSemantic (bcRightPresentation presentation))
  let rightReindex := selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcRightPresentation presentation))
  let bottomTransport := coreFiberTransportFunctor
    (typedPresentationToSemantic (bcBottomPresentation presentation))
  let directMap := topTransport.map (leftReindex.map diagnostic)
  let unitApp := (bcRightAdjunction presentation).unit.app
    (topTransport.obj (leftReindex.obj sourcePackage))
  let squareApp := (bcCoreTransportSquareIso presentation).hom.app
    (leftReindex.obj sourcePackage)
  let counitApp := (bcLeftAdjunction presentation).counit.app sourcePackage
  exact unitApp ≫ rightReindex.map (rightTransport.map directMap) ≫
    rightReindex.map squareApp ≫
    rightReindex.map (bottomTransport.map counitApp)

/--
The same source diagnostic placed after the generated square comparison and
before the mapped left-adjunction counit.
-/
noncomputable def coreBeckChevalleyPostSquareInsertion
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
              (bcRightPresentation presentation))).obj sourcePackage := by
  let leftReindex := selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcLeftPresentation presentation))
  let topTransport := coreFiberTransportFunctor
    (typedPresentationToSemantic (bcTopPresentation presentation))
  let rightReindex := selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcRightPresentation presentation))
  let bottomTransport := coreFiberTransportFunctor
    (typedPresentationToSemantic (bcBottomPresentation presentation))
  let leftTransport := coreFiberTransportFunctor
    (typedPresentationToSemantic (bcLeftPresentation presentation))
  let unitApp := (bcRightAdjunction presentation).unit.app
    (topTransport.obj (leftReindex.obj sourcePackage))
  let squareApp := (bcCoreTransportSquareIso presentation).hom.app
    (leftReindex.obj sourcePackage)
  let counitApp := (bcLeftAdjunction presentation).counit.app sourcePackage
  exact unitApp ≫ rightReindex.map squareApp ≫
    rightReindex.map
      (bottomTransport.map (leftTransport.map (leftReindex.map diagnostic))) ≫
    rightReindex.map (bottomTransport.map counitApp)

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

/-- Unit naturality identifies the entrance placement with the post-unit one. -/
theorem coreBeckChevalleyPreMateInsertion_eq_postUnit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage) :
    coreBeckChevalleyPreMateInsertion presentation diagnostic =
      coreBeckChevalleyPostUnitInsertion presentation diagnostic := by
  rw [coreBeckChevalleyPreMateInsertion,
    coreBeckChevalleyPostUnitInsertion,
    coreBeckChevalleyMate_app]
  simp only [Functor.comp_obj, Functor.comp_map]
  have unit_naturality :
      (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcTopPresentation presentation))).map
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcLeftPresentation presentation))).map
        diagnostic) ≫
        (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).obj sourcePackage)) =
      (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).obj sourcePackage)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcRightPresentation presentation))).map
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcTopPresentation presentation))).map
              ((selectedCoreFiberReindexFunctor
                (typedRealizableHom
                  (bcLeftPresentation presentation))).map diagnostic))) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (bcRightAdjunction presentation).unit.naturality
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation presentation))).map
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcLeftPresentation presentation))).map
          diagnostic))
  rw [← Category.assoc, unit_naturality, Category.assoc]

/--
Square-comparison naturality identifies the post-unit placement with the
post-square placement.
-/
theorem coreBeckChevalleyPostUnitInsertion_eq_postSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage) :
    coreBeckChevalleyPostUnitInsertion presentation diagnostic =
      coreBeckChevalleyPostSquareInsertion presentation diagnostic := by
  rw [coreBeckChevalleyPostUnitInsertion,
    coreBeckChevalleyPostSquareInsertion]
  have square_naturality :
      (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).map
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).map diagnostic)) ≫
        (bcCoreTransportSquareIso presentation).hom.app
          ((selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcLeftPresentation presentation))).obj sourcePackage) =
      (bcCoreTransportSquareIso presentation).hom.app
          ((selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcLeftPresentation presentation))).obj sourcePackage) ≫
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcLeftPresentation presentation))).map
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).map diagnostic)) := by
    simpa only [Functor.comp_map] using
      (bcCoreTransportSquareIso presentation).hom.naturality
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation presentation))).map diagnostic)
  have mapped_square_naturality := congrArg
    (fun hom =>
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation presentation))).map hom)
    square_naturality
  simp only [Functor.map_comp] at mapped_square_naturality
  simpa only [Category.assoc] using congrArg
    (fun hom =>
      (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).obj sourcePackage)) ≫
        hom ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((bcLeftAdjunction presentation).counit.app sourcePackage)))
    mapped_square_naturality

/--
Counit naturality identifies the post-square placement with postcomposition by
the via-base image.  Together with the two preceding theorems, this covers all
three internal boundaries of the generated unit--square--counit formula.
-/
theorem coreBeckChevalleyPostSquareInsertion_eq_post
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage) :
    coreBeckChevalleyPostSquareInsertion presentation diagnostic =
      (coreBeckChevalleyMate presentation).app sourcePackage ≫
        (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation)) ⋙
            selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcRightPresentation presentation))).map diagnostic := by
  rw [coreBeckChevalleyPostSquareInsertion,
    coreBeckChevalleyMate_app]
  have counit_naturality :
      (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation presentation))).map
          ((selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcLeftPresentation presentation))).map diagnostic) ≫
        (bcLeftAdjunction presentation).counit.app sourcePackage =
      (bcLeftAdjunction presentation).counit.app sourcePackage ≫
        diagnostic := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (bcLeftAdjunction presentation).counit.naturality diagnostic
  have mapped_counit_naturality := congrArg
    (fun hom =>
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation presentation))).map
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation))).map hom))
    counit_naturality
  simp only [Functor.comp_map, Functor.map_comp] at mapped_counit_naturality ⊢
  simpa only [Category.assoc] using congrArg
    (fun hom =>
      (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).obj sourcePackage)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((bcCoreTransportSquareIso presentation).hom.app
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation presentation))).obj sourcePackage)) ≫
        hom)
    mapped_counit_naturality

/--
Complete boundary normalization for a source-derived diagnostic: before the
unit, after the unit, after the square, and after the counit are the same
component.  The three equalities consume unit, square, and counit naturality
separately.
-/
theorem coreBeckChevalleyNaturalInsertionBoundary_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {sourcePackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (diagnostic : sourcePackage ⟶ sourcePackage) :
    coreBeckChevalleyPreMateInsertion presentation diagnostic =
        coreBeckChevalleyPostUnitInsertion presentation diagnostic ∧
      coreBeckChevalleyPostUnitInsertion presentation diagnostic =
        coreBeckChevalleyPostSquareInsertion presentation diagnostic ∧
      coreBeckChevalleyPostSquareInsertion presentation diagnostic =
        (coreBeckChevalleyMate presentation).app sourcePackage ≫
          (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation)) ⋙
              selectedCoreFiberReindexFunctor
                (typedRealizableHom
                  (bcRightPresentation presentation))).map diagnostic :=
  ⟨coreBeckChevalleyPreMateInsertion_eq_postUnit presentation diagnostic,
    coreBeckChevalleyPostUnitInsertion_eq_postSquare presentation diagnostic,
    coreBeckChevalleyPostSquareInsertion_eq_post presentation diagnostic⟩

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
