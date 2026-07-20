import Formal.AG.Examples.StandardGeometryReferenceModels

/-!
Executable statement contract for the SD0–SD7 public surface of the standard
geometry reference models.

Each example fixes one approved declaration type and refers directly to its
implementation.  This file introduces no new mathematical declarations.
-/

set_option maxErrors 1000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section
example : Type :=
  AmbientRing

example : Type :=
  ReferenceRawCoordinate

example : AmbientRing = MvPolynomial Unit Int :=
  ambientRing_eq

example : referenceSite.category :=
  baseContext

example : CommRingCat.of (referenceRaw.rawAlgebra baseContext) ≅
      CommRingCat.of AmbientRing :=
  baseRawAlgebraIso

example : baseRawAlgebraIso.hom (rawCoordinate baseContext) = coordinate :=
  baseRawAlgebraIso_coordinate

example : SheafifiedSectionRing referenceRaw baseContext ≅
      CommRingCat.of AmbientRing :=
  baseSectionRingIso

example : (referenceRelationFamily baseContext).JStruct =
      Ideal.span {rawLeftInverse baseContext, rawRightInverse baseContext} :=
  base_JStruct_eq

example : ∀ (W : referenceSite.category),
    IsIso (referenceRaw.toRingedSite.canonical.app (op W)) :=
  canonical_component_isIso

example : ∀ (i : AAT.AG.FiniteModel.TwoPatchContextIndex),
    referenceSite.category :=
  context

example : ∀ (i : AAT.AG.FiniteModel.TwoPatchContextIndex),
    (context i).ctx = AAT.AG.FiniteModel.twoPatchContext i :=
  context_ctx

example : ∀ (i j : AAT.AG.FiniteModel.TwoPatchContextIndex),
    Nonempty (context i ⟶ context j) ↔
      AAT.AG.FiniteModel.twoPatchContextIndexLe i j :=
  context_hom_iff

example : AmbientRing :=
  coordinate

example : coordinate = MvPolynomial.X () :=
  coordinate_eq

example : Bool → AmbientRing :=
  coverGenerator

example : coverGenerator false = leftGenerator :=
  coverGenerator_false

example : Ideal.span (Set.range coverGenerator) = ⊤ :=
  coverGenerator_span_eq_top

example : coverGenerator true = rightGenerator :=
  coverGenerator_true

example : referenceSite.category :=
  leftContext

example : AmbientRing :=
  leftGenerator

example : leftGenerator ∣ overlapGenerator :=
  leftGenerator_dvd_overlap

example : leftGenerator = coordinate :=
  leftGenerator_eq

example : IsUnit
      (algebraMap AmbientRing (Localization.Away overlapGenerator)
        leftGenerator) :=
  leftGenerator_isUnit_on_overlap

example : ∀ (W : referenceSite.category),
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  leftInverseRelation

example : ∀ (W : referenceSite.category),
    leftInverseRelation W = rawX W * rawLeftInverse W - 1 :=
  leftInverseRelation_eq

example : ∀ (W : referenceSite.category),
    Prop :=
  leftIsInverted

example : ¬ leftIsInverted baseContext :=
  leftIsInverted_base

example : ∀ (W : referenceSite.category),
    leftIsInverted W ↔ W = leftContext ∨ W = overlapContext :=
  leftIsInverted_iff

example : leftIsInverted leftContext :=
  leftIsInverted_left

example : leftIsInverted overlapContext :=
  leftIsInverted_overlap

example : ¬ leftIsInverted rightContext :=
  leftIsInverted_right

example : CommRingCat.of (referenceRaw.rawAlgebra leftContext) ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  leftRawAlgebraIso

example : leftRawAlgebraIso.hom (rawCoordinate leftContext) =
      algebraMap AmbientRing (Localization.Away leftGenerator) coordinate :=
  leftRawAlgebraIso_coordinate

example : SheafifiedSectionRing referenceRaw leftContext ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  leftSectionRingIso

example : leftContext ⟶ baseContext :=
  leftToBase

example : Localization.Away leftGenerator →+*
      Localization.Away overlapGenerator :=
  leftToOverlapRingHom

example : leftToOverlapRingHom.comp
        (algebraMap AmbientRing (Localization.Away leftGenerator)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) :=
  leftToOverlapRingHom_comp_algebraMap

example : (referenceRelationFamily leftContext).JStruct =
      Ideal.span
        {leftInverseRelation leftContext, rawRightInverse leftContext} :=
  left_JStruct_eq

example : baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase ≫
        leftSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away leftGenerator)) :=
  left_restriction_is_localization

example : ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) :=
  left_restriction_not_isIso

example : referenceSite.category :=
  overlapContext

example : AmbientRing :=
  overlapGenerator

example : overlapGenerator = leftGenerator * rightGenerator :=
  overlapGenerator_eq

example : CommRingCat.of (referenceRaw.rawAlgebra overlapContext) ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  overlapRawAlgebraIso

example : overlapRawAlgebraIso.hom (rawCoordinate overlapContext) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate :=
  overlapRawAlgebraIso_coordinate

example : SheafifiedSectionRing referenceRaw overlapContext ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  overlapSectionRingIso

example : overlapContext ⟶ leftContext :=
  overlapToLeft

example : overlapContext ⟶ rightContext :=
  overlapToRight

example : (referenceRelationFamily overlapContext).JStruct =
      Ideal.span
        {leftInverseRelation overlapContext,
          rightInverseRelation overlapContext} :=
  overlap_JStruct_eq

example : leftSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToLeft ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom leftToOverlapRingHom :=
  overlap_left_restriction_is_localization

example : rightSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToRight ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom rightToOverlapRingHom :=
  overlap_right_restriction_is_localization

example : ∀ (W : referenceSite.category),
    referenceRaw.rawAlgebra W :=
  rawCoordinate

example : ∀ (W : referenceSite.category),
    rawCoordinate W =
      (referenceRelationFamily W).quotientMap (rawX W) :=
  rawCoordinate_eq

example : ∀ {source target : referenceSite.category}
    (f : source ⟶ target),
    (referenceRaw.restrictionStable f).quotientDesc
        (rawCoordinate target) =
      rawCoordinate source :=
  rawCoordinate_restrict

example : ∀ (W : referenceSite.category),
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawLeftInverse

example : ∀ (W : referenceSite.category),
    rawLeftInverse W = rawVariable W .leftInverse :=
  rawLeftInverse_eq

example : ∀ (W : referenceSite.category),
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawRightInverse

example : ∀ (W : referenceSite.category),
    rawRightInverse W = rawVariable W .rightInverse :=
  rawRightInverse_eq

example : ∀ (W : referenceSite.category)
    (c : ReferenceRawCoordinate),
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable

example : ∀ (W : referenceSite.category)
    (c : ReferenceRawCoordinate),
    rawVariable W c = MvPolynomial.X c :=
  rawVariable_eq

example : ∀ (W : referenceSite.category),
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawX

example : ∀ (W : referenceSite.category),
    rawX W = rawVariable W .coordinate :=
  rawX_eq

example : Site.ContextPreorderCategory
      AAT.AG.FiniteModel.corePackage.object :=
  referenceContextPreorder

example : ∀ (W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object),
    referenceContextPreorder.le W V ↔
      W = V ∨
        ∃ i j : AAT.AG.FiniteModel.TwoPatchContextIndex,
          W = AAT.AG.FiniteModel.twoPatchContext i ∧
          V = AAT.AG.FiniteModel.twoPatchContext j ∧
          AAT.AG.FiniteModel.twoPatchContextIndexLe i j :=
  referenceContextPreorder_le_iff

example : ∀ (W : referenceSite.category),
    CoordinateFamily W.ctx :=
  referenceCoordinateFamily

example : ∀ (W : referenceSite.category),
    (referenceCoordinateFamily W).Coord = ReferenceRawCoordinate :=
  referenceCoordinateFamily_coord

example : ∀ (W : referenceSite.category)
    (c : ReferenceRawCoordinate),
    (referenceCoordinateFamily W).label c = CoordinateLabel.semantic :=
  referenceCoordinateFamily_label

example : ∀ (W : referenceSite.category)
    (c : ReferenceRawCoordinate),
    (referenceCoordinateFamily W).LocalData c = PUnit :=
  referenceCoordinateFamily_localData

example : Site.AATCoverageFamily
      referenceSite.requirements referenceSite.overlap baseContext :=
  referenceCover

example : referenceCover.Index ≃ AAT.AG.FiniteModel.TwoPatchCoverIndex :=
  referenceCoverIndexEquiv

example : ∀ (i : AAT.AG.FiniteModel.TwoPatchCoverIndex),
    referenceCover.patch (referenceCoverIndexEquiv.symm i) =
      AAT.AG.FiniteModel.twoPatchCoverPatch i :=
  referenceCover_patch

example : referenceCover.presieve =
      Presieve.ofArrows
        (fun i : AAT.AG.FiniteModel.TwoPatchCoverIndex =>
          context (AAT.AG.FiniteModel.twoPatchCoverContextIndex i))
        (fun i => match i with
          | AAT.AG.FiniteModel.TwoPatchCoverIndex.left => leftToBase
          | AAT.AG.FiniteModel.TwoPatchCoverIndex.right => rightToBase) :=
  referenceCover_presieve

example : Sieve.generate referenceCover.presieve ∈
      referenceSite.topology baseContext :=
  referenceCover_topologyCover

example : Site.CoverageRequirements
      AAT.AG.FiniteModel.corePackage.object
      AAT.AG.FiniteModel.corePackage.algebra.lawReading.lawUniverse
      AAT.AG.FiniteModel.corePackage.algebra.signatureReading :=
  referenceCoverageRequirements

example : referenceCoverageRequirements =
      AAT.AG.FiniteModel.twoPatchCoverageRequirements :=
  referenceCoverageRequirements_eq

example : Site.ContextOverlapPullback referenceContextPreorder :=
  referenceOverlap

example : ∀ (base left right : AAT.AG.FiniteModel.TwoPatchContextIndex),
    referenceOverlap.overlap
        (AAT.AG.FiniteModel.twoPatchContext base)
        (AAT.AG.FiniteModel.twoPatchContext left)
        (AAT.AG.FiniteModel.twoPatchContext right) =
      AAT.AG.FiniteModel.twoPatchContext
        (AAT.AG.FiniteModel.twoPatchContextMeet left right) :=
  referenceOverlap_selected

example : RawAmbientRestrictionSystem referenceSite Int :=
  referenceRaw

example : ∀ (c : ReferenceRawCoordinate),
    c = .coordinate ∨ c = .leftInverse ∨ c = .rightInverse :=
  referenceRawCoordinate_cases

example : ∀ (W : referenceSite.category),
    referenceRaw.coordFamily W = referenceCoordinateFamily W :=
  referenceRaw_coordFamily

example : Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf :=
  referenceRaw_isSheaf

example : ∀ (W : referenceSite.category),
    referenceRaw.relationFamily W = referenceRelationFamily W :=
  referenceRaw_relationFamily

example : ∀ {source target : referenceSite.category}
    (f : source ⟶ target),
    referenceRaw.restrictionStable f = referenceRestrictionStable f :=
  referenceRaw_restrictionStable

example : ∀ (W : referenceSite.category),
    StructuralRelationFamily (referenceCoordinateFamily W) Int :=
  referenceRelationFamily

example : ∀ (W : referenceSite.category)
    (r : Bool),
    (referenceRelationFamily W).polynomial r =
      referenceRelationPolynomial W r :=
  referenceRelationFamily_polynomial

example : ∀ (W : referenceSite.category),
    (referenceRelationFamily W).Relation = Bool :=
  referenceRelationFamily_relation

example : ∀ (W : referenceSite.category),
    Bool →
      FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  referenceRelationPolynomial

example : ∀ (W : referenceSite.category),
    referenceRelationPolynomial W false =
      if leftIsInverted W then leftInverseRelation W else rawLeftInverse W :=
  referenceRelationPolynomial_false

example : ∀ (W : referenceSite.category),
    referenceRelationPolynomial W true =
      if rightIsInverted W then rightInverseRelation W else rawRightInverse W :=
  referenceRelationPolynomial_true

example : ∀ {source target : referenceSite.category}
    (f : source ⟶ target),
    RestrictionStableStructuralRelations
      (referenceRelationFamily source)
      (referenceRelationFamily target)
      (referenceSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) :=
  referenceRestrictionStable

example : ∀ {X Y Z : referenceSite.category}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    (referenceRestrictionStable (f ≫ g)).restriction.polynomialMap =
      ((referenceRestrictionStable f).restriction.polynomialMap).comp
        ((referenceRestrictionStable g).restriction.polynomialMap) :=
  referenceRestrictionStable_comp

example : ∀ (W : referenceSite.category),
    (referenceRestrictionStable (𝟙 W)).restriction.polynomialMap =
      RingHom.id (FreeTypedCommAlg (referenceCoordinateFamily W) Int) :=
  referenceRestrictionStable_identity

example : Site.SelectedGeometryReading AAT.AG.FiniteModel.corePackage :=
  referenceSelectedGeometryReading

example : referenceSelectedGeometryReading =
      { contextPreorder := referenceContextPreorder
        requirements := referenceCoverageRequirements
        overlap := referenceOverlap } :=
  referenceSelectedGeometryReading_eq

example : Site.AATSite AAT.AG.FiniteModel.corePackage.object :=
  referenceSite

example : referenceSite = referenceSelectedGeometryReading.toAATSite :=
  referenceSite_eq

example : HasSheafify referenceSite.topology (AATCommAlgCat Int) :=
  referenceSite_hasSheafifyInt

example : HasSheafify referenceSite.topology
      (AATCommAlgCat (Polynomial Int)) :=
  referenceSite_hasSheafifyPolynomialInt

example : ∀ {source target : referenceSite.category}
    (f : source ⟶ target),
    TypedCoordinateRestriction
      (referenceCoordinateFamily source)
      (referenceCoordinateFamily target) Int
      (referenceSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) :=
  referenceTypedRestriction

example : ∀ {source target : referenceSite.category}
    (f : source ⟶ target)
    (p : FreeTypedCommAlg (referenceCoordinateFamily target) Int)
    (hp : p ∈ (referenceRelationFamily target).JStruct),
    (referenceTypedRestriction f).polynomialMap p ∈
      (referenceRelationFamily source).JStruct :=
  referenceTypedRestriction_maps_JStruct

example : ∀ {source target : referenceSite.category}
    (f : source ⟶ target)
    (c : ReferenceRawCoordinate),
    (referenceTypedRestriction f).variableImage c =
      match c with
      | .coordinate => rawX source
      | .leftInverse =>
          if leftIsInverted target then rawLeftInverse source
          else if leftIsInverted source then leftInverseRelation source
          else rawLeftInverse source
      | .rightInverse =>
          if rightIsInverted target then rawRightInverse source
          else if rightIsInverted source then rightInverseRelation source
          else rawRightInverse source :=
  referenceTypedRestriction_variableImage

example : referenceSite.category :=
  rightContext

example : AmbientRing :=
  rightGenerator

example : rightGenerator ∣ overlapGenerator :=
  rightGenerator_dvd_overlap

example : rightGenerator = 1 - coordinate :=
  rightGenerator_eq

example : IsUnit
      (algebraMap AmbientRing (Localization.Away overlapGenerator)
        rightGenerator) :=
  rightGenerator_isUnit_on_overlap

example : ∀ (W : referenceSite.category),
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rightInverseRelation

example : ∀ (W : referenceSite.category),
    rightInverseRelation W = (1 - rawX W) * rawRightInverse W - 1 :=
  rightInverseRelation_eq

example : ∀ (W : referenceSite.category),
    Prop :=
  rightIsInverted

example : ¬ rightIsInverted baseContext :=
  rightIsInverted_base

example : ∀ (W : referenceSite.category),
    rightIsInverted W ↔ W = rightContext ∨ W = overlapContext :=
  rightIsInverted_iff

example : ¬ rightIsInverted leftContext :=
  rightIsInverted_left

example : rightIsInverted overlapContext :=
  rightIsInverted_overlap

example : rightIsInverted rightContext :=
  rightIsInverted_right

example : CommRingCat.of (referenceRaw.rawAlgebra rightContext) ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  rightRawAlgebraIso

example : rightRawAlgebraIso.hom (rawCoordinate rightContext) =
      algebraMap AmbientRing (Localization.Away rightGenerator) coordinate :=
  rightRawAlgebraIso_coordinate

example : SheafifiedSectionRing referenceRaw rightContext ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  rightSectionRingIso

example : rightContext ⟶ baseContext :=
  rightToBase

example : Localization.Away rightGenerator →+*
      Localization.Away overlapGenerator :=
  rightToOverlapRingHom

example : rightToOverlapRingHom.comp
        (algebraMap AmbientRing (Localization.Away rightGenerator)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) :=
  rightToOverlapRingHom_comp_algebraMap

example : (referenceRelationFamily rightContext).JStruct =
      Ideal.span
        {rawLeftInverse rightContext, rightInverseRelation rightContext} :=
  right_JStruct_eq

example : baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase ≫
        rightSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away rightGenerator)) :=
  right_restriction_is_localization

example : ¬ IsIso (sheafifiedRestriction referenceRaw rightToBase) :=
  right_restriction_not_isIso

example : AlgebraicGeometry.Scheme := ambientScheme
example : ambientScheme = AlgebraicGeometry.Spec (CommRingCat.of AmbientRing) := ambientScheme_eq
example : architectureChartSpec referenceRaw baseContext ≅ ambientScheme := baseChartDomainIso
example : baseChartDomainIso = AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.symm.op := baseChartDomainIso_eq
example : architectureChartSpec referenceRaw leftContext ≅
    AlgebraicGeometry.Spec (CommRingCat.of (Localization.Away leftGenerator)) := leftChartDomainIso
example : leftChartDomainIso = AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.symm.op := leftChartDomainIso_eq
example : architectureChartSpec referenceRaw rightContext ≅
    AlgebraicGeometry.Spec (CommRingCat.of (Localization.Away rightGenerator)) := rightChartDomainIso
example : rightChartDomainIso = AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.symm.op := rightChartDomainIso_eq
example : architectureChartSpec referenceRaw overlapContext ≅
    AlgebraicGeometry.Spec (CommRingCat.of (Localization.Away overlapGenerator)) := overlapChartDomainIso
example : overlapChartDomainIso = AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.symm.op := overlapChartDomainIso_eq
example : AATReadingDecoration referenceRaw ambientScheme := ambientDecoration
example : ambientDecoration = AATReadingDecoration.pullback referenceRaw baseChartDomainIso.inv
    (AATReadingDecoration.ofContext referenceRaw baseContext) := ambientDecoration_eq
example : ArchitectureAffineChart referenceRaw ambientScheme ambientDecoration := leftChart
example : ArchitectureAffineChart referenceRaw ambientScheme ambientDecoration := rightChart
example : ArchitectureAffineAtlas referenceRaw ambientScheme ambientDecoration := referenceAtlas
example : IsArchitectureAffineAtlas referenceRaw referenceAtlas := referenceAtlas_valid
example : ArchitectureOverlapPresentation referenceRaw referenceAtlas := referenceOverlapPresentation
example : IsArchitectureOverlapPresentation referenceRaw referenceOverlapPresentation := referenceOverlapPresentation_valid
example : StandardArchitectureScheme referenceRaw := referenceScheme
example : referenceScheme = StandardArchitectureScheme.ofPresentation
    referenceRaw ambientScheme ambientDecoration referenceAtlas referenceAtlas_valid
    referenceOverlapPresentation referenceOverlapPresentation_valid := referenceScheme_eq
example : referenceScheme.atlas.Index := leftIndex
example : referenceScheme.atlas.Index := rightIndex
example : leftIndex ≠ rightIndex := leftIndex_ne_rightIndex
example : ∀ i : referenceScheme.atlas.Index, i = leftIndex ∨ i = rightIndex := index_cases
example : referenceScheme.underlying = ambientScheme := referenceScheme_underlying
example : (referenceScheme.atlas.chart leftIndex).context = leftContext := left_chart_context
example : (referenceScheme.atlas.chart rightIndex).context = rightContext := right_chart_context
example : (referenceScheme.atlas.chart leftIndex).context ≠
    (referenceScheme.atlas.chart rightIndex).context := chart_contexts_ne
example : (referenceScheme.atlas.chart leftIndex).map = leftChartDomainIso.hom ≫
    AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away leftGenerator))).op := left_chart_map
example : (referenceScheme.atlas.chart rightIndex).map = rightChartDomainIso.hom ≫
    AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away rightGenerator))).op := right_chart_map
example : AlgebraicGeometry.IsOpenImmersion
    (referenceScheme.atlas.chart leftIndex).map := left_chart_isOpenImmersion
example : AlgebraicGeometry.IsOpenImmersion
    (referenceScheme.atlas.chart rightIndex).map := right_chart_isOpenImmersion
example : ⨆ i, ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange = ⊤ := twoChart_jointlyCovers
example : ¬ IsIso (referenceScheme.atlas.chart leftIndex).map := left_chart_not_isIso
example : ¬ IsIso (referenceScheme.atlas.chart rightIndex).map := right_chart_not_isIso
example : referenceScheme.atlas.pairContext referenceRaw leftIndex rightIndex = overlapContext := pair_context
example : referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex ≅
    AlgebraicGeometry.Spec (CommRingCat.of (Localization.Away overlapGenerator)) := actualOverlapIso
example : actualOverlapIso =
    (referenceScheme.overlap_is_actual_pullback referenceRaw leftIndex rightIndex).symm ≪≫
      eqToIso (by rw [pair_context]) ≪≫ overlapChartDomainIso := actualOverlapIso_eq
example : Nonempty (referenceScheme.atlas.actualOverlap
    referenceRaw leftIndex rightIndex) := actualOverlap_nonempty
example : sheafifiedRestriction referenceRaw
      (referenceScheme.atlas.pairToLeft referenceRaw leftIndex rightIndex ≫
        (referenceScheme.atlas.chart leftIndex).contextHom) =
    sheafifiedRestriction referenceRaw
      (referenceScheme.atlas.pairToRight referenceRaw leftIndex rightIndex ≫
        (referenceScheme.atlas.chart rightIndex).contextHom) := decoration_overlap
example : ∀ i j l : referenceScheme.atlas.Index,
    referenceScheme.atlas.actualTripleToLeft referenceRaw i j l ≫
        (referenceScheme.atlas.chart i).map =
      referenceScheme.atlas.actualTripleToMiddle referenceRaw i j l ≫
        (referenceScheme.atlas.chart j).map ∧
    referenceScheme.atlas.actualTripleToMiddle referenceRaw i j l ≫
        (referenceScheme.atlas.chart j).map =
      referenceScheme.atlas.actualTripleToRight referenceRaw i j l ≫
        (referenceScheme.atlas.chart l).map := actual_triple_cocycle


/-! ## SD2-SD3 executable statement contracts -/

example : SemanticLawEquationWitnessIdealCore referenceSite :=
  weakLawEquationCore

example : SemanticLawEquationWitnessIdealCore referenceSite :=
  strongLawEquationCore

example : SemanticLawEquationWitnessIdealCore referenceSite :=
  rigidLawEquationCore

example : ∀ (W : referenceSite.category),
weakLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  weakLawEquationCore_observable

example : ∀ (W : referenceSite.category),
strongLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  strongLawEquationCore_observable

example : ∀ (W : referenceSite.category),
rigidLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rigidLawEquationCore_observable

example : ∀ (W : referenceSite.category),
weakLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  weakLawEquationCore_observableCommRing

example : ∀ (W : referenceSite.category),
strongLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  strongLawEquationCore_observableCommRing

example : ∀ (W : referenceSite.category),
rigidLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rigidLawEquationCore_observableCommRing

example : ∀ {source target : referenceSite.category} (f : source ⟶ target),
weakLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  weakLawEquationCore_restrict

example : ∀ {source target : referenceSite.category} (f : source ⟶ target),
strongLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  strongLawEquationCore_restrict

example : ∀ {source target : referenceSite.category} (f : source ⟶ target),
rigidLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rigidLawEquationCore_restrict

example : ∀ (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom),
weakLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else 0 :=
  weakViolationWitness_eq

example : ∀ (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom),
strongLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else 0 :=
  strongViolationWitness_eq

example : ∀ (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom),
rigidLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        algebraMap Int (referenceRaw.rawAlgebra W) 2
      else 0 :=
  rigidViolationWitness_eq

example : weakLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  weakLawEquationCore_supportAtom

example : strongLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  strongLawEquationCore_supportAtom

example : rigidLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rigidLawEquationCore_supportAtom

example : weakLawEquationCore.supportLawIndex = PUnit.unit :=
  weakLawEquationCore_supportLawIndex

example : strongLawEquationCore.supportLawIndex = PUnit.unit :=
  strongLawEquationCore_supportLawIndex

example : rigidLawEquationCore.supportLawIndex = PUnit.unit :=
  rigidLawEquationCore_supportLawIndex

example : SemanticLawEquationSchemeBridge referenceRaw weakLawEquationCore :=
  weakSchemeBridge

example : SemanticLawEquationSchemeBridge referenceRaw strongLawEquationCore :=
  strongSchemeBridge

example : SemanticLawEquationSchemeBridge referenceRaw rigidLawEquationCore :=
  rigidSchemeBridge

example : ∀ (W : referenceSite.category),
weakSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  weakSchemeBridge_toRawPresentation

example : ∀ (W : referenceSite.category),
strongSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  strongSchemeBridge_toRawPresentation

example : ∀ (W : referenceSite.category),
rigidSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rigidSchemeBridge_toRawPresentation

example : IsSemanticLawEquationSchemeBridge
      referenceRaw weakLawEquationCore weakSchemeBridge :=
  weakSchemeBridge_valid

example : IsSemanticLawEquationSchemeBridge
      referenceRaw strongLawEquationCore strongSchemeBridge :=
  strongSchemeBridge_valid

example : IsSemanticLawEquationSchemeBridge
      referenceRaw rigidLawEquationCore rigidSchemeBridge :=
  rigidSchemeBridge_valid

example : ClosedEquationalLawReading referenceRaw referenceScheme :=
  weakReading

example : weakReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge :=
  weakReading_eq

example : ClosedEquationalLawReading referenceRaw referenceScheme :=
  strongReading

example : strongReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge :=
  strongReading_eq

example : ClosedEquationalLawReading referenceRaw referenceScheme :=
  rigidReading

example : rigidReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge :=
  rigidReading_eq

example : IsClosedEquationalLawReading referenceRaw referenceScheme weakReading :=
  weakReading_valid

example : IsClosedEquationalLawReading referenceRaw referenceScheme strongReading :=
  strongReading_valid

example : IsClosedEquationalLawReading referenceRaw referenceScheme rigidReading :=
  rigidReading_valid

example : RequiredClosed referenceRaw referenceScheme weakReading :=
  weakReading_requiredClosed

example : RequiredClosed referenceRaw referenceScheme strongReading :=
  strongReading_requiredClosed

example : RequiredClosed referenceRaw referenceScheme rigidReading :=
  rigidReading_requiredClosed

example : RequiredLawIdealExact referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed :=
  weakReading_requiredLawIdealExact

example : RequiredLawIdealExact referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed :=
  strongReading_requiredLawIdealExact

example : RequiredLawIdealExact referenceRaw referenceScheme
      rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rigidReading_requiredLawIdealExact

example : referenceScheme.underlying.IdealSheafData :=
  weakIdealSheaf

example : weakIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  weakIdealSheaf_eq

example : referenceScheme.underlying.IdealSheafData :=
  strongIdealSheaf

example : strongIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  strongIdealSheaf_eq

example : referenceScheme.underlying.IdealSheafData :=
  rigidIdealSheaf

example : rigidIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rigidIdealSheaf_eq

example : AlgebraicGeometry.Scheme :=
  weakLocus

example : weakLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  weakLocus_eq

example : AlgebraicGeometry.Scheme :=
  strongLocus

example : strongLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  strongLocus_eq

example : AlgebraicGeometry.Scheme :=
  rigidLocus

example : rigidLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rigidLocus_eq

example : weakLocus ⟶ referenceScheme.underlying :=
  weakImmersion

example : weakImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  weakImmersion_eq

example : strongLocus ⟶ referenceScheme.underlying :=
  strongImmersion

example : strongImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  strongImmersion_eq

example : rigidLocus ⟶ referenceScheme.underlying :=
  rigidImmersion

example : rigidImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rigidImmersion_eq

example : Γ(referenceScheme.underlying, ⊤) ≅
      CommRingCat.of AmbientRing :=
  ambientGlobalSectionsIso

example : ambientGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing) :=
  ambientGlobalSectionsIso_eq

example : ∀ (a : AAT.AG.FiniteModel.carrier.Atom),
ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else 0 :=
  weakGlobalEquation_eq

example : ∀ (a : AAT.AG.FiniteModel.carrier.Atom),
ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else 0 :=
  strongGlobalEquation_eq

example : ∀ (a : AAT.AG.FiniteModel.carrier.Atom),
ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          rigidLawEquationCore rigidSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        MvPolynomial.C 2
      else 0 :=
  rigidGlobalEquation_eq

example : Ideal AmbientRing :=
  weakAmbientIdeal

example : weakAmbientIdeal =
      Ideal.span {coordinate * (coordinate - 1)} :=
  weakAmbientIdeal_eq

example : Ideal AmbientRing :=
  strongAmbientIdeal

example : strongAmbientIdeal = Ideal.span {coordinate} :=
  strongAmbientIdeal_eq

example : Ideal AmbientRing :=
  rigidAmbientIdeal

example : rigidAmbientIdeal =
      Ideal.span {coordinate, MvPolynomial.C 2} :=
  rigidAmbientIdeal_eq

example : Ideal (Localization.Away leftGenerator) :=
  weakLeftIdeal

example : weakLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away leftGenerator)
          (coordinate * (coordinate - 1))} :=
  weakLeftIdeal_eq

example : Ideal (Localization.Away rightGenerator) :=
  weakRightIdeal

example : weakRightIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away rightGenerator)
          (coordinate * (coordinate - 1))} :=
  weakRightIdeal_eq

example : Ideal (Localization.Away overlapGenerator) :=
  weakOverlapIdeal

example : weakOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away overlapGenerator)
          (coordinate * (coordinate - 1))} :=
  weakOverlapIdeal_eq

example : Ideal (Localization.Away leftGenerator) :=
  strongLeftIdeal

example : strongLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away leftGenerator) coordinate} :=
  strongLeftIdeal_eq

example : Ideal (Localization.Away rightGenerator) :=
  strongRightIdeal

example : strongRightIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate} :=
  strongRightIdeal_eq

example : Ideal (Localization.Away overlapGenerator) :=
  strongOverlapIdeal

example : strongOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate} :=
  strongOverlapIdeal_eq

example : Γ(leftChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  leftChartGlobalSectionsIso

example : leftChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext) ≪≫
        leftSectionRingIso :=
  leftChartGlobalSectionsIso_eq

example : Γ(rightChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  rightChartGlobalSectionsIso

example : rightChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext) ≪≫
        rightSectionRingIso :=
  rightChartGlobalSectionsIso_eq

example : Γ(referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex, ⊤) ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  actualOverlapGlobalSectionsIso

example : actualOverlapGlobalSectionsIso =
      (asIso actualOverlapIso.inv.appTop) ≪≫
        AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (Localization.Away overlapGenerator)) :=
  actualOverlapGlobalSectionsIso_eq

example : referenceScheme.underlying.affineOpens :=
  ambientTopAffineOpen

example : ambientTopAffineOpen.1 = ⊤ :=
  ambientTopAffineOpen_obj

example : Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) =
      weakAmbientIdeal :=
  weakIdeal_top_eq

example : Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) =
      strongAmbientIdeal :=
  strongIdeal_top_eq

example : Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) =
      rigidAmbientIdeal :=
  rigidIdeal_top_eq

example : Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      weakLeftIdeal :=
  weakIdeal_left_eq

example : Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      weakRightIdeal :=
  weakIdeal_right_eq

example : Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap
              referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      weakOverlapIdeal :=
  weakIdeal_overlap_eq

example : Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      strongLeftIdeal :=
  strongIdeal_left_eq

example : Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      strongRightIdeal :=
  strongIdeal_right_eq

example : Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap
              referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      strongOverlapIdeal :=
  strongIdeal_overlap_eq

example : (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) :=
  weakIdeal_overlap_agrees

example : (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) :=
  strongIdeal_overlap_agrees

example : weakAmbientIdeal ≠ ⊥ :=
  weakAmbientIdeal_ne_bot

example : weakAmbientIdeal ≠ ⊤ :=
  weakAmbientIdeal_ne_top

example : strongAmbientIdeal ≠ ⊥ :=
  strongAmbientIdeal_ne_bot

example : strongAmbientIdeal ≠ ⊤ :=
  strongAmbientIdeal_ne_top

example : rigidAmbientIdeal ≠ ⊥ :=
  rigidAmbientIdeal_ne_bot

example : rigidAmbientIdeal ≠ ⊤ :=
  rigidAmbientIdeal_ne_top

example : weakIdealSheaf < strongIdealSheaf :=
  weakIdeal_lt_strongIdeal

example : strongIdealSheaf < rigidIdealSheaf :=
  strongIdeal_lt_rigidIdeal

example : Nonempty weakLocus :=
  weakLocus_nonempty

example : Nonempty strongLocus :=
  strongLocus_nonempty

example : Nonempty rigidLocus :=
  rigidLocus_nonempty

example : ¬ IsIso weakImmersion :=
  weakImmersion_not_isIso

example : ¬ IsIso strongImmersion :=
  strongImmersion_not_isIso

example : ¬ IsIso rigidImmersion :=
  rigidImmersion_not_isIso

example : weakImmersion.ker = weakIdealSheaf :=
  weakImmersion_ker

example : strongImmersion.ker = strongIdealSheaf :=
  strongImmersion_ker

example : Set.range weakImmersion = weakIdealSheaf.support :=
  weakImmersion_zeroLocus

example : Set.range strongImmersion = strongIdealSheaf.support :=
  strongImmersion_zeroLocus

example : AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            weakIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      weakLocus :=
  weakAffineQuotientChart

example : AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            strongIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      strongLocus :=
  strongAffineQuotientChart

example : IsIso weakAffineQuotientChart :=
  weakAffineQuotientChart_isIso

example : IsIso strongAffineQuotientChart :=
  strongAffineQuotientChart_isIso

example : ∀ (n : Int),
AmbientRing →+* Int :=
  evaluationRingHom

example : ∀ (n : Int),
evaluationRingHom n =
      MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n) :=
  evaluationRingHom_eq

example : ∀ (n : Int),
AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint

example : ∀ (n : Int),
evaluationPoint n =
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom (evaluationRingHom n)).op :=
  evaluationPoint_eq

example : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  zeroPoint

example : zeroPoint = evaluationPoint 0 :=
  zeroPoint_eq

example : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  onePoint

example : onePoint = evaluationPoint 1 :=
  onePoint_eq

example : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  twoPoint

example : twoPoint = evaluationPoint 2 :=
  twoPoint_eq

example : ∀ {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying),
(SemanticLawfulAlong referenceRaw referenceScheme weakReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          weakReading weakReading_valid weakReading_requiredClosed s)) :=
  weak_correspondence

example : ∀ {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying),
(SemanticLawfulAlong referenceRaw referenceScheme strongReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          strongReading strongReading_valid strongReading_requiredClosed s)) :=
  strong_correspondence

example : SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed zeroPoint) :=
  zeroPoint_fires

example : SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed onePoint) :=
  onePoint_fires

example : ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed twoPoint) :=
  twoPoint_fires

example : AAT.AG.FiniteModel.carrier.Atom →
    AAT.AG.FiniteModel.carrier.Atom :=
  weakToStrongAtomMap

example : ∀ (a : AAT.AG.FiniteModel.carrier.Atom),
    weakToStrongAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else
        AAT.AG.FiniteModel.FiniteAtom.componentC :=
  weakToStrongAtomMap_eq

example : ClosedEquationalLawInclusion
    referenceRaw referenceScheme weakReading strongReading :=
  weakToStrong

example : weakToStrong.lawMap = id :=
  weakToStrong_lawMap

example : weakToStrong.atomMap PUnit.unit = weakToStrongAtomMap :=
  weakToStrong_atomMap

example : IsClosedEquationalLawInclusion
    referenceRaw referenceScheme weakToStrong :=
  weakToStrong_valid

example : strongLocus ⟶ weakLocus :=
  lawComparison

example : lawComparison =
    lawfulClosedSubschemeMap
      referenceRaw referenceScheme
      weakReading_valid strongReading_valid
      weakReading_requiredClosed strongReading_requiredClosed
      weakToStrong weakToStrong_valid :=
  lawComparison_eq

example : AlgebraicGeometry.IsClosedImmersion lawComparison :=
  lawComparison_isClosedImmersion

example : lawComparison ≫ weakImmersion = strongImmersion :=
  lawComparison_immersion

example : ¬ IsIso lawComparison :=
  lawComparison_not_isIso

example : AAT.AG.FiniteModel.carrier.Atom →
    AAT.AG.FiniteModel.carrier.Atom :=
  strongToRigidAtomMap

example : ∀ (a : AAT.AG.FiniteModel.carrier.Atom),
    strongToRigidAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        AAT.AG.FiniteModel.FiniteAtom.componentB
      else
        AAT.AG.FiniteModel.FiniteAtom.dependsAB :=
  strongToRigidAtomMap_eq

example : ClosedEquationalLawInclusion
    referenceRaw referenceScheme strongReading rigidReading :=
  strongToRigid

example : strongToRigid.lawMap = id :=
  strongToRigid_lawMap

example : strongToRigid.atomMap PUnit.unit = strongToRigidAtomMap :=
  strongToRigid_atomMap

example : IsClosedEquationalLawInclusion
    referenceRaw referenceScheme strongToRigid :=
  strongToRigid_valid

example : rigidLocus ⟶ strongLocus :=
  strongToRigidComparison

example : strongToRigidComparison =
    lawfulClosedSubschemeMap
      referenceRaw referenceScheme
      strongReading_valid rigidReading_valid
      strongReading_requiredClosed rigidReading_requiredClosed
      strongToRigid strongToRigid_valid :=
  strongToRigidComparison_eq

example : AlgebraicGeometry.IsClosedImmersion strongToRigidComparison :=
  strongToRigidComparison_isClosedImmersion

example : strongToRigidComparison ≫ strongImmersion = rigidImmersion :=
  strongToRigidComparison_immersion

example : ¬ IsIso strongToRigidComparison :=
  strongToRigidComparison_not_isIso

example : ClosedEquationalLawInclusion
    referenceRaw referenceScheme weakReading rigidReading :=
  weakToRigid

example : weakToRigid =
    weakToStrong.comp referenceRaw referenceScheme strongToRigid :=
  weakToRigid_eq

example : IsClosedEquationalLawInclusion
    referenceRaw referenceScheme weakToRigid :=
  weakToRigid_valid

example : rigidLocus ⟶ weakLocus :=
  weakToRigidComparison

example : weakToRigidComparison =
    lawfulClosedSubschemeMap
      referenceRaw referenceScheme
      weakReading_valid rigidReading_valid
      weakReading_requiredClosed rigidReading_requiredClosed
      weakToRigid weakToRigid_valid :=
  weakToRigidComparison_eq

example :
    lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid weakReading_valid
        weakReading_requiredClosed weakReading_requiredClosed
        (ClosedEquationalLawInclusion.refl
          referenceRaw referenceScheme weakReading)
        (ClosedEquationalLawInclusion.refl_valid
          referenceRaw referenceScheme weakReading) =
      𝟙 weakLocus :=
  lawComparison_id_fires

example : strongToRigidComparison ≫ lawComparison = weakToRigidComparison :=
  lawComparison_comp_fires

example : FlatCoefficientChange Int (Polynomial Int) :=
  coefficientChange

example : coefficientChange.hom = Polynomial.C :=
  coefficientChange_hom

example : ¬ Function.Surjective coefficientChange.hom :=
  coefficientChange_not_surjective

example : referenceSite.topology.HasSheafCompose
    (coefficientChange.coefficientExtension :
      AATCommAlgCat.{0, 0} Int ⥤
        AATCommAlgCat.{0, 0} (Polynomial Int)) :=
  coefficientChange_hasSheafCompose

example : StandardArchitectureScheme
    (referenceRaw.baseChange coefficientChange.hom) :=
  coefficientChangedScheme

example : coefficientChangedScheme =
    referenceScheme.baseChange referenceRaw coefficientChange :=
  coefficientChangedScheme_eq

example : ClosedEquationalLawReading
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme :=
  coefficientChangedWeakReading

example : coefficientChangedWeakReading =
    ClosedEquationalLawReading.baseChangeOfSemanticCore
      referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge coefficientChange :=
  coefficientChangedWeakReading_eq

example : ClosedEquationalLawReading
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme :=
  coefficientChangedStrongReading

example : coefficientChangedStrongReading =
    ClosedEquationalLawReading.baseChangeOfSemanticCore
      referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge coefficientChange :=
  coefficientChangedStrongReading_eq

example : IsClosedEquationalLawReading
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakReading :=
  coefficientChangedWeakReading_valid

example : IsClosedEquationalLawReading
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedStrongReading :=
  coefficientChangedStrongReading_valid

example : RequiredClosed
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakReading :=
  coefficientChangedWeakReading_requiredClosed

example : RequiredClosed
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedStrongReading :=
  coefficientChangedStrongReading_requiredClosed

example : Scheme.IdealSheafData.comap weakIdealSheaf
      (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
    lawGeneratedIdealSheaf
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading
      coefficientChangedWeakReading_valid
      coefficientChangedWeakReading_requiredClosed :=
  weakIdeal_baseChange

example : Scheme.IdealSheafData.comap strongIdealSheaf
      (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
    lawGeneratedIdealSheaf
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading
      coefficientChangedStrongReading_valid
      coefficientChangedStrongReading_requiredClosed :=
  strongIdeal_baseChange

example : IsPullback
    ((referenceScheme.baseChangedAtlas
        referenceRaw coefficientChange).chart
      (cast
        (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm leftIndex)).map
    (referenceScheme.baseChangedChartMap
      referenceRaw coefficientChange leftIndex)
    (referenceScheme.baseChangeMap referenceRaw coefficientChange)
    (referenceScheme.atlas.chart leftIndex).map :=
  leftChart_baseChange_isPullback

example : IsPullback
    ((referenceScheme.baseChangedAtlas
        referenceRaw coefficientChange).chart
      (cast
        (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm rightIndex)).map
    (referenceScheme.baseChangedChartMap
      referenceRaw coefficientChange rightIndex)
    (referenceScheme.baseChangeMap referenceRaw coefficientChange)
    (referenceScheme.atlas.chart rightIndex).map :=
  rightChart_baseChange_isPullback

example : lawGeneratedIdealSheaf
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading
      coefficientChangedWeakReading_valid
      coefficientChangedWeakReading_requiredClosed <
    lawGeneratedIdealSheaf
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading
      coefficientChangedStrongReading_valid
      coefficientChangedStrongReading_requiredClosed :=
  coefficientChanged_ideal_strict

example : ClosedEquationalLawInclusion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading coefficientChangedStrongReading :=
  coefficientChangedWeakToStrong

example : coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap :=
  coefficientChangedWeakToStrong_lawMap

example : coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap :=
  coefficientChangedWeakToStrong_atomMap

example : IsClosedEquationalLawInclusion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakToStrong :=
  coefficientChangedWeakToStrong_valid

example : lawfulClosedSubscheme
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading
      coefficientChangedStrongReading_valid
      coefficientChangedStrongReading_requiredClosed ⟶
    lawfulClosedSubscheme
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading
      coefficientChangedWeakReading_valid
      coefficientChangedWeakReading_requiredClosed :=
  coefficientChangedLawComparison

example : coefficientChangedLawComparison =
    lawfulClosedSubschemeMap
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme
      coefficientChangedWeakReading_valid
      coefficientChangedStrongReading_valid
      coefficientChangedWeakReading_requiredClosed
      coefficientChangedStrongReading_requiredClosed
      coefficientChangedWeakToStrong
      coefficientChangedWeakToStrong_valid :=
  coefficientChangedLawComparison_eq

example : AlgebraicGeometry.IsClosedImmersion
    coefficientChangedLawComparison :=
  coefficientChangedLawComparison_isClosedImmersion

example : coefficientChangedLawComparison ≫
      lawfulClosedImmersion
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed =
    lawfulClosedImmersion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading
      coefficientChangedStrongReading_valid
      coefficientChangedStrongReading_requiredClosed :=
  coefficientChangedLawComparison_immersion

example : ¬ IsIso coefficientChangedLawComparison :=
  coefficientChangedLawComparison_not_isIso

example : coefficientChangedLawComparison ≫
      lawfulClosedSubschemeBaseChangeMap
        referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge coefficientChange =
    lawfulClosedSubschemeBaseChangeMap
        referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge coefficientChange ≫
      lawComparison :=
  coefficient_law_comparison_square

example : ¬ IsIso
    (referenceScheme.baseChangeMap referenceRaw coefficientChange) :=
  coefficientChange_schemeMap_not_isIso

/-! ## SD6 negative fixtures -/

example : ArchitectureAffineAtlas referenceRaw
    referenceScheme.underlying referenceScheme.decoration :=
  duplicateLeftAtlas

example (i : Bool) : duplicateLeftAtlas.chart i = leftChart :=
  duplicateLeftAtlas_chart i

example : ¬ ∃ lift : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
    leftChart.domain, lift ≫ leftChart.map = zeroPoint :=
  zeroPoint_not_factors_through_leftChart

example : ¬ IsArchitectureAffineAtlas referenceRaw duplicateLeftAtlas :=
  duplicateLeftAtlas_not_valid

example : AmbientRing ≃+* AmbientRing :=
  coordinateReflection

example : coordinateReflection coordinate = rightGenerator :=
  coordinateReflection_coordinate

example : coordinateReflection rightGenerator = coordinate :=
  coordinateReflection_rightGenerator

example : AmbientRing →+* Localization.Away rightGenerator :=
  reflectedRightRingHom

example : reflectedRightRingHom coordinate =
    algebraMap AmbientRing (Localization.Away rightGenerator) rightGenerator :=
  reflectedRightRingHom_coordinate

example : ArchitectureAffineChart referenceRaw
    referenceScheme.underlying referenceScheme.decoration :=
  brokenRightChart

example : brokenRightChart.context = rightContext :=
  brokenRightChart_context

example : brokenRightChart.map =
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom reflectedRightRingHom).op :=
  brokenRightChart_map

example : AlgebraicGeometry.IsOpenImmersion brokenRightChart.map :=
  brokenRightChart_isOpenImmersion

example : sheafifiedRestriction referenceRaw brokenRightChart.contextHom ≠
    referenceScheme.decoration.interpretation ≫
      brokenRightChart.map.appTop ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw brokenRightChart.context)).hom :=
  brokenRightChart_interpretation_ne

example : ¬ IsArchitectureAffineChart referenceRaw brokenRightChart :=
  brokenRightChart_not_valid

example : ClosedEquationalLawReading referenceRaw referenceScheme :=
  collapsedStrongReading

example : collapsedStrongReading = weakReading :=
  collapsedStrongReading_eq

example : ¬ lawGeneratedIdealSheaf
      referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed <
    lawGeneratedIdealSheaf
      referenceRaw referenceScheme
      collapsedStrongReading weakReading_valid weakReading_requiredClosed :=
  collapsedIdeal_not_strict

example : referenceScheme.underlying.IdealSheafData :=
  unitIdealFixture

example : unitIdealFixture = ⊤ :=
  unitIdealFixture_eq

example : IsEmpty unitIdealFixture.subscheme :=
  unitIdealFixture_subscheme_empty

example : Int →+* ZMod 2 :=
  nonFlatCoefficientMap

example : nonFlatCoefficientMap = Int.castRingHom (ZMod 2) :=
  nonFlatCoefficientMap_eq

example : ¬ nonFlatCoefficientMap.Flat :=
  nonFlatCoefficientMap_not_flat

/-! ## SD7 integrated firing theorem -/

example :
    Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf ∧
    (∀ W : referenceSite.category,
      IsIso (referenceRaw.toRingedSite.canonical.app (op W))) ∧
    (⨆ i, ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange = ⊤) ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map ∧
    Nonempty (referenceScheme.atlas.actualOverlap
      referenceRaw leftIndex rightIndex) ∧
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) = weakAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) = strongAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) = rigidAmbientIdeal ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
      weakLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
      weakRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      weakOverlapIdeal ∧
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
      strongLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
      strongRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      strongOverlapIdeal ∧
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    weakAmbientIdeal ≠ ⊥ ∧ weakAmbientIdeal ≠ ⊤ ∧
    strongAmbientIdeal ≠ ⊥ ∧ strongAmbientIdeal ≠ ⊤ ∧
    weakIdealSheaf < strongIdealSheaf ∧
    rigidAmbientIdeal ≠ ⊥ ∧ rigidAmbientIdeal ≠ ⊤ ∧
    strongIdealSheaf < rigidIdealSheaf ∧
    weakImmersion.ker = weakIdealSheaf ∧
    strongImmersion.ker = strongIdealSheaf ∧
    Set.range weakImmersion = weakIdealSheaf.support ∧
    Set.range strongImmersion = strongIdealSheaf.support ∧
    IsIso weakAffineQuotientChart ∧ IsIso strongAffineQuotientChart ∧
    Nonempty weakLocus ∧ Nonempty strongLocus ∧ Nonempty rigidLocus ∧
    ¬ IsIso weakImmersion ∧ ¬ IsIso strongImmersion ∧ ¬ IsIso rigidImmersion ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint) ∧
    AlgebraicGeometry.IsClosedImmersion lawComparison ∧
    lawComparison ≫ weakImmersion = strongImmersion ∧
    ¬ IsIso lawComparison ∧
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison ∧
    strongToRigidComparison ≫ strongImmersion = rigidImmersion ∧
    ¬ IsIso strongToRigidComparison ∧
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison ∧
    ¬ Function.Surjective coefficientChange.hom ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas referenceRaw coefficientChange).chart
        (cast (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas referenceRaw coefficientChange).chart
        (cast (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map ∧
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedWeakReading coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed ∧
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedStrongReading coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedWeakReading coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedStrongReading coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    AlgebraicGeometry.IsClosedImmersion coefficientChangedLawComparison ∧
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap ∧
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap ∧
    ¬ IsIso coefficientChangedLawComparison ∧
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison ∧
    ¬ IsIso (referenceScheme.baseChangeMap referenceRaw coefficientChange) :=
  standardGeometryReference_fires

end

end AAT.AG.Examples.StandardGeometryReferenceModels
