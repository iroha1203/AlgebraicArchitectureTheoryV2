import Formal.AG.Examples.StandardGeometryReferenceModels

/-!
Executable statement contract for the SD0 public surface of the standard
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

end

end AAT.AG.Examples.StandardGeometryReferenceModels
