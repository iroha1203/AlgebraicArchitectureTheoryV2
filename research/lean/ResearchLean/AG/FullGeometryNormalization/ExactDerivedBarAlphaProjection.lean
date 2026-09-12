import ResearchLean.AG.FullGeometryNormalization.ExactDerivedBarAlphaTriangle
import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement
import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonFactorization

/-!
# Exact projection of the authored derived Beck--Chevalley comparison

This module identifies the projection of the exact authored `barAlpha`
comparison with the canonical support-level Beck--Chevalley mate.  The proof
normalizes the realized presentation, compares both routes after the selected
right cartesian lift, and cancels first that lift and then the projected top
cocartesian lift.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 6000000

/-- The semantic Beck--Chevalley mate followed by the selected right lift
factors through the selected left lift and the bottom core transport. -/
theorem coreBeckChevalleyMate_app_iterated_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (sourcePackage : CoreFiber
      presentation.1.cospan.firstSource.toSemantic) :
    coreFiberLift (typedPresentationToSemantic
          (bcTopPresentation presentation))
        ((selectedCoreFiberReindexFunctor
          (bcLeftInput presentation)).obj sourcePackage) ≫
      ((coreBeckChevalleyMate presentation).app sourcePackage).1 ≫
      (selectedCoreFiberCartesianLift (bcRightInput presentation)
        ((coreFiberTransportFunctor (typedPresentationToSemantic
          (bcBottomPresentation presentation))).obj sourcePackage)).hom =
    (selectedCoreFiberCartesianLift (bcLeftInput presentation)
        sourcePackage).hom ≫
      coreFiberLift (typedPresentationToSemantic
        (bcBottomPresentation presentation)) sourcePackage := by
  let selectedLeft := (selectedCoreFiberReindexFunctor
    (bcLeftInput presentation)).obj sourcePackage
  have hsquare :
      bcCoreTransportSquareIso presentation =
        bcSemanticCoreTransportSquareIso (toSemanticBC presentation) :=
    bcProvenanceCoreTransportSquareIso_eq_semantic
      ({ presentation := presentation, realization_eq := rfl } :
        BCRealizationProvenance (toSemanticBC presentation))
  have mateFac := coreBeckChevalleyMate_app_selectedLift_fac
    presentation sourcePackage
  rw [hsquare] at mateFac
  have squareFac := bcSemanticCoreTransportSquareIso_hom_fac
    (toSemanticBC presentation) selectedLeft
  have squareFac' :
      coreFiberIteratedLift
          (typedPresentationToSemantic (bcTopPresentation presentation))
          (typedPresentationToSemantic (bcRightPresentation presentation))
          selectedLeft ≫
        ((bcSemanticCoreTransportSquareIso
          (toSemanticBC presentation)).hom.app selectedLeft).1 =
      coreFiberIteratedLift
        (typedPresentationToSemantic (bcLeftPresentation presentation))
        (typedPresentationToSemantic (bcBottomPresentation presentation))
        selectedLeft := by
    simpa only using squareFac
  have bottomMapFac := coreFiberTransportMap_fac
    (typedPresentationToSemantic (bcBottomPresentation presentation))
      ((bcLeftAdjunction presentation).counit.app sourcePackage)
  have leftCounitFac := coreTransportReindexCounit_app_fac
    (bcLeftInput presentation) sourcePackage
  have squareCounitBase :
      (((bcSemanticCoreTransportSquareIso
          (toSemanticBC presentation)).hom.app selectedLeft) ≫
        (coreFiberTransportFunctor (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
          ((bcLeftAdjunction presentation).counit.app sourcePackage)).1 =
      ((bcSemanticCoreTransportSquareIso
        (toSemanticBC presentation)).hom.app selectedLeft).1 ≫
        ((coreFiberTransportFunctor (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
          ((bcLeftAdjunction presentation).counit.app sourcePackage)).1 := rfl
  have mateFac' :
      ((coreBeckChevalleyMate presentation).app sourcePackage).1 ≫
          (selectedCoreFiberCartesianLift (bcRightInput presentation)
            ((coreFiberTransportFunctor (typedPresentationToSemantic
              (bcBottomPresentation presentation))).obj sourcePackage)).hom =
        coreFiberLift (typedPresentationToSemantic
            (bcRightPresentation presentation))
            ((coreFiberTransportFunctor (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj selectedLeft) ≫
          (((bcSemanticCoreTransportSquareIso
            (toSemanticBC presentation)).hom.app selectedLeft).1 ≫
            ((coreFiberTransportFunctor (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
              ((bcLeftAdjunction presentation).counit.app sourcePackage)).1) :=
    mateFac.trans (congrArg
      (fun h => coreFiberLift (typedPresentationToSemantic
        (bcRightPresentation presentation))
        ((coreFiberTransportFunctor (typedPresentationToSemantic
          (bcTopPresentation presentation))).obj selectedLeft) ≫ h)
      squareCounitBase)
  calc
    _ = coreFiberLift (typedPresentationToSemantic
            (bcTopPresentation presentation)) selectedLeft ≫
        (coreFiberLift (typedPresentationToSemantic
            (bcRightPresentation presentation))
            ((coreFiberTransportFunctor (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj selectedLeft) ≫
          (((bcSemanticCoreTransportSquareIso
            (toSemanticBC presentation)).hom.app selectedLeft).1 ≫
            ((coreFiberTransportFunctor (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
              ((bcLeftAdjunction presentation).counit.app sourcePackage)).1)) :=
      congrArg (fun h => coreFiberLift (typedPresentationToSemantic
        (bcTopPresentation presentation)) selectedLeft ≫ h) mateFac'
    _ = (coreFiberIteratedLift
          (typedPresentationToSemantic (bcTopPresentation presentation))
          (typedPresentationToSemantic (bcRightPresentation presentation))
          selectedLeft ≫
        ((bcSemanticCoreTransportSquareIso
          (toSemanticBC presentation)).hom.app selectedLeft).1) ≫
        ((coreFiberTransportFunctor (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
          ((bcLeftAdjunction presentation).counit.app sourcePackage)).1 := by
      simp only [coreFiberIteratedLift, Category.assoc]
    _ = coreFiberIteratedLift
          (typedPresentationToSemantic (bcLeftPresentation presentation))
          (typedPresentationToSemantic (bcBottomPresentation presentation))
          selectedLeft ≫
        ((coreFiberTransportFunctor (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
          ((bcLeftAdjunction presentation).counit.app sourcePackage)).1 :=
      congrArg (fun h => h ≫
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation))).map
          ((bcLeftAdjunction presentation).counit.app sourcePackage)).1)
        squareFac'
    _ = coreFiberLift (typedPresentationToSemantic
          (bcLeftPresentation presentation)) selectedLeft ≫
        (coreFiberLift (typedPresentationToSemantic
            (bcBottomPresentation presentation))
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcLeftPresentation presentation))).obj selectedLeft) ≫
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((bcLeftAdjunction presentation).counit.app sourcePackage)).1) := by
      simp only [coreFiberIteratedLift, Category.assoc]
    _ = coreFiberLift (typedPresentationToSemantic
          (bcLeftPresentation presentation)) selectedLeft ≫
        (((bcLeftAdjunction presentation).counit.app sourcePackage).1 ≫
          coreFiberLift (typedPresentationToSemantic
            (bcBottomPresentation presentation))
            sourcePackage) :=
      congrArg (fun h => coreFiberLift
        (typedPresentationToSemantic (bcLeftPresentation presentation))
          selectedLeft ≫ h) bottomMapFac
    _ = (coreFiberLift (typedPresentationToSemantic
          (bcLeftPresentation presentation)) selectedLeft ≫
        ((bcLeftAdjunction presentation).counit.app sourcePackage).1) ≫
          coreFiberLift (typedPresentationToSemantic
            (bcBottomPresentation presentation)) sourcePackage :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun h => h ≫ coreFiberLift
      (typedPresentationToSemantic (bcBottomPresentation presentation))
        sourcePackage) leftCounitFac

/-- After the projected top lift, the authored `barAlpha` route through the
base has the common bottom-transport composite. -/
theorem authoredExactBarAlpha_left_post_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    let sourceCore := (geometryFiberProjection
      A.context.square.semantic.square.southwest).obj
        (authoredSouthwestGeometryFiberAt A z k g)
    let rightLift := selectedCoreFiberCartesianLift
      (authoredExactRightInput A)
      ((coreFiberTransportFunctor
        A.context.square.semantic.square.bottom).obj sourceCore)
    ((geometryProjection U).map
          (geomFiberLift A.context.square.semantic.square.top
            (authoredExactLeftPulledGeometryAt A z k g)) ≫
        ((geometryFiberProjection
          A.context.square.semantic.square.northeast).map
            (authoredExactBarAlphaIsoAt A z k g).hom).1) ≫
      ((authoredExactViaBaseGeometryCoreIsoAt A z k g).hom.1 ≫
        rightLift.hom) =
    (geometryProjection U).map
        (exactGeometryPullLift (authoredExactLeftInput A)
          (authoredSouthwestGeometryFiberAt A z k g)) ≫
      coreFiberLift A.context.square.semantic.square.bottom sourceCore := by
  dsimp only
  let sourceCore := (geometryFiberProjection
    A.context.square.semantic.square.southwest).obj
      (authoredSouthwestGeometryFiberAt A z k g)
  let rightLift := selectedCoreFiberCartesianLift
    (authoredExactRightInput A)
    ((coreFiberTransportFunctor
      A.context.square.semantic.square.bottom).obj sourceCore)
  have hvia :
      (authoredExactViaBaseGeometryCoreIsoAt A z k g).hom.1 ≫
          rightLift.hom =
        (geometryProjection U).map
            (exactGeometryPullLift (authoredExactRightInput A)
              (authoredExactTargetGeometryAt A z k g)) ≫
          (towerTransportComparisonApp
            A.context.square.semantic.square.bottom
              (authoredSouthwestGeometryFiberAt A z k g)).hom.1 := by
    unfold authoredExactViaBaseGeometryCoreIsoAt
    let tower := towerTransportComparisonApp
      A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g)
    let projectedPull := (geometryFiberProjection
      A.context.square.semantic.square.southeast).obj
        (authoredExactTargetGeometryAt A z k g)
    have reindexFac :
        ((selectedCoreFiberReindexFunctor
          (authoredExactRightInput A)).map tower.hom).1 ≫
            (selectedCoreFiberCartesianLift (authoredExactRightInput A)
              ((coreFiberTransportFunctor
                A.context.square.semantic.square.bottom).obj sourceCore)).hom =
          (selectedCoreFiberCartesianLift
            (authoredExactRightInput A) projectedPull).hom ≫ tower.hom.1 := by
      simpa only [tower, projectedPull, sourceCore] using
        selectedCoreFiberReindexFunctor_map_fac
          (authoredExactRightInput A) tower.hom
    change
      (exactGeometryPullProjectionIsoApp (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g)).hom.1 ≫
        ((selectedCoreFiberReindexFunctor
          (authoredExactRightInput A)).map tower.hom).1 ≫
        (selectedCoreFiberCartesianLift (authoredExactRightInput A)
          ((coreFiberTransportFunctor
            A.context.square.semantic.square.bottom).obj sourceCore)).hom = _
    rw [reindexFac]
    have projectionFac := exactGeometryPullProjectionIsoApp_hom_fac
      (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g)
    exact congrArg (fun h => h ≫ tower.hom.1)
      (by simpa only [projectedPull] using projectionFac)
  have hbar :
      (geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.top
              (authoredExactLeftPulledGeometryAt A z k g)) ≫
          ((geometryFiberProjection
            A.context.square.semantic.square.northeast).map
              (authoredExactBarAlphaIsoAt A z k g).hom).1 ≫
          (geometryProjection U).map
            (exactGeometryPullLift (authoredExactRightInput A)
              (authoredExactTargetGeometryAt A z k g)) =
        (geometryProjection U).map
            (exactGeometryPullLift (authoredExactLeftInput A)
              (authoredSouthwestGeometryFiberAt A z k g)) ≫
          (geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.bottom
              (authoredSouthwestGeometryFiberAt A z k g)) := by
    simpa only [Functor.map_comp] using congrArg
      (geometryProjection U).map
        (authoredExactBarAlphaIsoAt_triangle A z k g)
  have hbottom :
      (geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.bottom
              (authoredSouthwestGeometryFiberAt A z k g)) ≫
          (towerTransportComparisonApp
            A.context.square.semantic.square.bottom
              (authoredSouthwestGeometryFiberAt A z k g)).hom.1 =
        coreFiberLift A.context.square.semantic.square.bottom sourceCore := by
    simpa only [sourceCore] using towerTransportComparisonApp_hom_fac
      A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g)
  rw [hvia]
  have hbar' :
      ((geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.top
              (authoredExactLeftPulledGeometryAt A z k g)) ≫
          ((geometryFiberProjection
            A.context.square.semantic.square.northeast).map
              (authoredExactBarAlphaIsoAt A z k g).hom).1) ≫
        (geometryProjection U).map
          (exactGeometryPullLift (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g)) =
      (geometryProjection U).map
          (exactGeometryPullLift (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)) ≫
        (geometryProjection U).map
          (geomFiberLift A.context.square.semantic.square.bottom
            (authoredSouthwestGeometryFiberAt A z k g)) :=
    (Category.assoc _ _ _).trans hbar
  rw [← Category.assoc, hbar', Category.assoc, hbottom]
  /-
  calc
    _ = ((geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.top
              (authoredExactLeftPulledGeometryAt A z k g)) ≫
          ((geometryFiberProjection
            A.context.square.semantic.square.northeast).map
              (authoredExactBarAlphaIsoAt A z k g).hom).1) ≫
        ((geometryProjection U).map
            (exactGeometryPullLift (authoredExactRightInput A)
              (authoredExactTargetGeometryAt A z k g)) ≫
          (towerTransportComparisonApp
            A.context.square.semantic.square.bottom
              (authoredSouthwestGeometryFiberAt A z k g)).hom.1) :=
      congrArg (fun h =>
        ((geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.top
              (authoredExactLeftPulledGeometryAt A z k g)) ≫
          ((geometryFiberProjection
            A.context.square.semantic.square.northeast).map
              (authoredExactBarAlphaIsoAt A z k g).hom).1) ≫ h) hvia
    _ = ((geometryProjection U).map
            (exactGeometryPullLift (authoredExactLeftInput A)
              (authoredSouthwestGeometryFiberAt A z k g)) ≫
          (geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.bottom
              (authoredSouthwestGeometryFiberAt A z k g))) ≫
        (towerTransportComparisonApp
          A.context.square.semantic.square.bottom
            (authoredSouthwestGeometryFiberAt A z k g)).hom.1 := by
      simpa only [Category.assoc] using congrArg
        (fun h => h ≫ (towerTransportComparisonApp
          A.context.square.semantic.square.bottom
            (authoredSouthwestGeometryFiberAt A z k g)).hom.1) hbar
    _ = _ := by rw [Category.assoc, hbottom]
  -/

/-- The direct geometry-core comparison after the projected top lift is the
selected left core lift followed by top transport. -/
theorem authoredExactDirectGeometryCoreIsoAt_top_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    let sourceCore := (geometryFiberProjection
      A.context.square.semantic.square.southwest).obj
        (authoredSouthwestGeometryFiberAt A z k g)
    (geometryProjection U).map
        (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g)) ≫
      (authoredExactDirectGeometryCoreIsoAt A z k g).hom.1 =
    (exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g)).hom.1 ≫
      coreFiberLift A.context.square.semantic.square.top
        ((selectedCoreFiberReindexFunctor
          (authoredExactLeftInput A)).obj sourceCore) := by
  dsimp only
  unfold authoredExactDirectGeometryCoreIsoAt
  change
    (geometryProjection U).map
        (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g)) ≫
      (towerTransportComparisonApp A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g)).hom.1 ≫
      ((coreFiberTransportFunctor
        A.context.square.semantic.square.top).map
          (exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)).hom).1 = _
  have towerFac :
      (geometryProjection U).map
          (geomFiberLift A.context.square.semantic.square.top
            (authoredExactLeftPulledGeometryAt A z k g)) ≫
        (towerTransportComparisonApp A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g)).hom.1 =
      coreFiberLift A.context.square.semantic.square.top
        ((geometryFiberProjection
          A.context.square.semantic.square.northwest).obj
            (authoredExactLeftPulledGeometryAt A z k g)) := by
    simpa only using towerTransportComparisonApp_hom_fac
      A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g)
  rw [← Category.assoc, towerFac]
  simpa only using coreFiberTransportMap_fac
    A.context.square.semantic.square.top
      (exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g)).hom


/-- Equality after a strongly cartesian right lift and the projected strongly
cocartesian top lift implies equality of the two support-fiber morphisms. -/
theorem authoredExactBarAlpha_projection_of_post_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (Q : AATCorePackage U)
    (rightHom : ((authoredSupportViaBaseRoute A.context).obj z).1 ⟶ Q)
    [rightCart : (packageProjection U).IsStronglyCartesian
      A.context.square.semantic.square.right rightHom]
    (hpost :
      let lhs :=
        (geometryFiberProjection
          A.context.square.semantic.square.northeast).map
            (authoredExactBarAlphaIsoAt A z k g).hom ≫
          (authoredExactViaBaseSupportCoreIsoAt A z k g).hom
      let rhs := (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
        (authoredSupportCanonicalMate A.context).app z
      let topLift := (geometryProjection U).map
        (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g))
      topLift ≫ lhs.1 ≫ rightHom =
        topLift ≫ rhs.1 ≫ rightHom) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).map
          (authoredExactBarAlphaIsoAt A z k g).hom ≫
        (authoredExactViaBaseSupportCoreIsoAt A z k g).hom =
      (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
        (authoredSupportCanonicalMate A.context).app z := by
  let lhs :=
    (geometryFiberProjection
      A.context.square.semantic.square.northeast).map
        (authoredExactBarAlphaIsoAt A z k g).hom ≫
      (authoredExactViaBaseSupportCoreIsoAt A z k g).hom
  let rhs := (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
    (authoredSupportCanonicalMate A.context).app z
  change lhs = rhs
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast) lhs.1 := lhs.2
  letI : (packageProjection U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast) rhs.1 := rhs.2
  change lhs.1 = rhs.1
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) A.context.square.semantic.square.right rightHom
    (𝟙 A.context.square.semantic.square.northeast)
    (ψ := lhs.1) (ψ' := rhs.1)
  let topLift := (geometryProjection U).map
    (geomFiberLift A.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt A z k g))
  letI : (packageProjection U).IsStronglyCocartesian
      A.context.square.semantic.square.top topLift :=
    projectedGeomFiberLift_isStronglyCocartesian
      A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g)
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) A.context.square.semantic.square.top topLift
    A.context.square.semantic.square.right
    (ψ := lhs.1 ≫ rightHom) (ψ' := rhs.1 ≫ rightHom)
  simpa only [lhs, rhs, topLift] using hpost

/-! ## Implementation notes for presentation normalization

The cancellation theorem above is stated for the semantic square generated
definitionally by a `BCPresentation`.  An arbitrary `AuthoredBCDatumSquare`
instead stores its semantic square together with `realization_eq`.  We
eliminate that existing provenance equality, retain precisely the authored
lift and two-cell fields below, and reassemble a definitionally normalized
datum so that all endpoint transports remain visible to the simplifier.

Accepting a pre-normalized datum or an endpoint equality from the caller was
rejected: either would add a premise absent from G-122(B), whereas the datum
already contains the required realization provenance.
-/

/-- The authored fields remaining after replacing a realized semantic square
by the semantic square generated from its presentation. -/
structure ExactBarAlphaNormalizedFields
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) where
  supportLift : TransportCoherence.AdmissibleLiftData
    (toSemanticBC presentation).diagnostic U
  endpoint_eq : ∀ cell : (toSemanticBC presentation).diagnostic.TwoCell,
    (packageProjection U).obj
      (supportLift.package
        ((toSemanticBC presentation).diagnostic.twoTarget cell)) =
      (toSemanticBC presentation).square.southwest
  twoCellBase : ∀ cell : (toSemanticBC presentation).diagnostic.TwoCell,
    (supportLift.pathLift
      ((toSemanticBC presentation).diagnostic.twoLeft cell)).base =
    (supportLift.pathLift
      ((toSemanticBC presentation).diagnostic.twoRight cell)).base
  authored : AuthoredBC2CellPresentation (fun cell =>
    supportLift.package
      ((toSemanticBC presentation).diagnostic.twoTarget cell))

/-- Reassemble normalized authored fields into an authored datum whose semantic
square is definitionally generated by the presentation. -/
noncomputable def ExactBarAlphaNormalizedFields.datum
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {presentation : BCPresentation U}
    (fields : ExactBarAlphaNormalizedFields presentation) :
    AuthoredBCDatumSquare U :=
  ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
      fields.supportLift, fields.endpoint_eq⟩,
    fields.twoCellBase, fields.authored⟩

/-- In a presentation-normalized authored datum, the direct route followed by
the semantic mate and selected right lift is the common bottom composite. -/
theorem normalizedAuthoredExactBarAlpha_right_post_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (fields : ExactBarAlphaNormalizedFields presentation) :
    let A := fields.datum
    ∀ (z : A.context.Category) (k : Type v) [CommRing k]
      (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k),
      let sourceCore := (geometryFiberProjection
        A.context.square.semantic.square.southwest).obj
          (authoredSouthwestGeometryFiberAt A z k g)
      let rightLift := selectedCoreFiberCartesianLift
        (authoredExactRightInput A)
        ((coreFiberTransportFunctor
          A.context.square.semantic.square.bottom).obj sourceCore)
      ((geometryProjection U).map
            (geomFiberLift A.context.square.semantic.square.top
              (authoredExactLeftPulledGeometryAt A z k g)) ≫
          (authoredExactDirectGeometryCoreIsoAt A z k g).hom.1) ≫
        (((coreBeckChevalleyMate presentation).app sourceCore).1 ≫
          rightLift.hom) =
      (geometryProjection U).map
          (exactGeometryPullLift (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)) ≫
        coreFiberLift A.context.square.semantic.square.bottom sourceCore := by
  dsimp only
  intro z k _ g
  let A : AuthoredBCDatumSquare U := fields.datum
  let sourceCore := (geometryFiberProjection
    A.context.square.semantic.square.southwest).obj
      (authoredSouthwestGeometryFiberAt A z k g)
  let rightLift := selectedCoreFiberCartesianLift
    (authoredExactRightInput A)
    ((coreFiberTransportFunctor
      A.context.square.semantic.square.bottom).obj sourceCore)
  let selectedLeft := (selectedCoreFiberReindexFunctor
    (authoredExactLeftInput A)).obj sourceCore
  have hdirect := authoredExactDirectGeometryCoreIsoAt_top_fac A z k g
  have hcanonical :
      coreFiberLift A.context.square.semantic.square.top selectedLeft ≫
          ((coreBeckChevalleyMate presentation).app sourceCore).1 ≫
          rightLift.hom =
        (selectedCoreFiberCartesianLift
          (authoredExactLeftInput A) sourceCore).hom ≫
          coreFiberLift A.context.square.semantic.square.bottom sourceCore := by
    simpa only [selectedLeft, rightLift, sourceCore, A,
      ExactBarAlphaNormalizedFields.datum, authoredExactLeftInput,
      authoredExactRightInput] using
        coreBeckChevalleyMate_app_iterated_fac presentation sourceCore
  have hprojection := exactGeometryPullProjectionIsoApp_hom_fac
    (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
  calc
    _ = ((exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)).hom.1 ≫
          coreFiberLift A.context.square.semantic.square.top selectedLeft) ≫
        (((coreBeckChevalleyMate presentation).app sourceCore).1 ≫
          rightLift.hom) := congrArg (fun h => h ≫
            (((coreBeckChevalleyMate presentation).app sourceCore).1 ≫
              rightLift.hom)) (by simpa only [selectedLeft, sourceCore] using hdirect)
    _ = (exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)).hom.1 ≫
        (coreFiberLift A.context.square.semantic.square.top selectedLeft ≫
          (((coreBeckChevalleyMate presentation).app sourceCore).1 ≫
            rightLift.hom)) := by simp only [Category.assoc]
    _ = (exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)).hom.1 ≫
        ((selectedCoreFiberCartesianLift
            (authoredExactLeftInput A) sourceCore).hom ≫
          coreFiberLift A.context.square.semantic.square.bottom sourceCore) :=
      congrArg (fun h => (exactGeometryPullProjectionIsoApp
        (authoredExactLeftInput A)
          (authoredSouthwestGeometryFiberAt A z k g)).hom.1 ≫ h) hcanonical
    _ = ((exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g)).hom.1 ≫
          (selectedCoreFiberCartesianLift
            (authoredExactLeftInput A) sourceCore).hom) ≫
        coreFiberLift A.context.square.semantic.square.bottom sourceCore :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun h => h ≫ coreFiberLift
      A.context.square.semantic.square.bottom sourceCore)
      (by simpa only [sourceCore] using hprojection)


/-- Projection of composition in a package fiber is composition of the
underlying package morphisms. -/
@[simp]
theorem packageFiber_comp_fst
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {S : ExtractionInstance U}
    {X Y Z : CategoryTheory.Functor.Fiber (packageProjection U) S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- Projection of an identity in a package fiber is the underlying identity. -/
@[simp]
theorem packageFiber_id_fst
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {S : ExtractionInstance U}
    (X : CategoryTheory.Functor.Fiber (packageProjection U) S) :
    (𝟙 X : X ⟶ X).1 = 𝟙 X.1 := rfl

set_option maxHeartbeats 6000000 in
/-- The projection of the exact authored `barAlpha` comparison followed by the
via-base support comparison equals the direct comparison followed by the
canonical support Beck--Chevalley mate. -/
theorem authoredExactBarAlphaIsoAt_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).map
          (authoredExactBarAlphaIsoAt A z k g).hom ≫
        (authoredExactViaBaseSupportCoreIsoAt A z k g).hom =
      (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
        (authoredSupportCanonicalMate A.context).app z := by
  rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    supportLift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let fields : ExactBarAlphaNormalizedFields presentation :=
    ⟨supportLift, endpoint_eq, twoCellBase, authored⟩
  let A : AuthoredBCDatumSquare U := fields.datum
  change
    (geometryFiberProjection A.context.square.semantic.square.northeast).map
          (authoredExactBarAlphaIsoAt A z k g).hom ≫
        (authoredExactViaBaseSupportCoreIsoAt A z k g).hom =
      (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
        (authoredSupportCanonicalMate A.context).app z
  let target := (coreFiberTransportFunctor
    A.context.square.semantic.square.bottom).obj
      ((AuthoredSupportContext.supportFunctor A.context).obj z)
  let rightLift := selectedCoreFiberCartesianLift
    (authoredExactRightInput A) target
  letI : (packageProjection U).IsStronglyCartesian
      A.context.square.semantic.square.right rightLift.hom :=
    rightLift.isStronglyCartesian
  apply authoredExactBarAlpha_projection_of_post_fac
    A z k g target.1 rightLift.hom
  let sourceCore := (geometryFiberProjection
    A.context.square.semantic.square.southwest).obj
      (authoredSouthwestGeometryFiberAt A z k g)
  unfold authoredExactViaBaseSupportCoreIsoAt
    authoredExactDirectSupportCoreIsoAt authoredSupportCanonicalMate
  dsimp only [A]
  simp only [Iso.trans_hom, Iso.refl_hom, packageFiber_comp_fst,
    packageFiber_id_fst, Functor.whiskerLeft_app]
  have hleft := authoredExactBarAlpha_left_post_fac A z k g
  have hright := normalizedAuthoredExactBarAlpha_right_post_fac presentation fields z k g
  dsimp only [A, sourceCore, target, rightLift] at hleft hright ⊢
  dsimp only [fields, ExactBarAlphaNormalizedFields.datum] at hleft hright ⊢
  dsimp only [AuthoredSupportContext.supportFunctor,
    AuthoredSupportContext.supportObject,
    AuthoredSupportContext.supportPackage,
    authoredSouthwestGeometryFiberAt,
    FixedCoefficientGeometryAt.package,
    Discrete.functor, geometryFiberProjection] at hleft hright ⊢
  dsimp only [Function.comp_apply,
    AuthoredSupportContext.supportObject,
    AuthoredSupportContext.supportPackage] at hleft hright ⊢
  simp only [Category.assoc, Category.comp_id] at hleft hright ⊢
  rw [hleft, hright]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
