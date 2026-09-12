import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFactorization
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedBarAlphaProjection
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducer

/-!
# Projection of the exact selected complete-geometry comparison
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct TransportCoherence

set_option maxHeartbeats 6000000

/-- Projection of the source normalization is the G-116 diagnostic projector. -/
private theorem sourceNormalization_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (geometryFiberProjection A.context.square.semantic.square.southwest).map
        (canonicalGeometryFiberNormalization
          (authoredSouthwestGeometryFiberAt A z k g) admissible) =
      authoredSupportCanonicalNormalizationComponent A z.as admissible := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  rfl

/-- Under the explicit exact-derived endpoint comparison, projection of
`barD` is literally the existing G-116 selected via-base projector. -/
theorem authoredExactBarDAt_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).map
          (authoredExactBarDAt A z omega k g) ≫
        (authoredExactViaBaseSupportCoreIsoAt A z k g).hom =
      (authoredExactViaBaseSupportCoreIsoAt A z k g).hom ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          A omega z := by
  classical
  by_cases selected : omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)
  · rw [authoredExactBarDAt_eq_normalization_route A z omega k g selected]
    rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
    cases realization_eq
    let normalizedContext : AuthoredSupportContext U :=
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
    let normalizedA : AuthoredBCDatumSquare U :=
      ⟨normalizedContext, twoCellBase, authored⟩
    let source := authoredSouthwestGeometryFiberAt normalizedA z k g
    let n := canonicalGeometryFiberNormalization source selected.2
    let pushed := (geomFiberTransportFunctor
      normalizedA.context.square.semantic.square.bottom).map n
    let pullComparison := exactGeometryPullProjectionIsoApp
      (authoredExactRightInput normalizedA)
      (authoredExactTargetGeometryAt normalizedA z k g)
    let towerComparison := towerTransportComparisonApp
      normalizedA.context.square.semantic.square.bottom source
    have hpull := exactGeometryPullProjectionIso_naturality
      (authoredExactRightInput normalizedA) pushed
    have hpull' :
        (geometryFiberProjection
          normalizedA.context.square.semantic.square.northeast).map
            ((exactGeometryPullFunctor
              (authoredExactRightInput normalizedA)).map pushed) ≫
            pullComparison.hom =
          pullComparison.hom ≫
            (selectedCoreFiberReindexFunctor
              (authoredExactRightInput normalizedA)).map
                ((geometryFiberProjection
                  normalizedA.context.square.semantic.square.southeast).map
                    pushed) := by
      simpa only [pullComparison, pushed, source,
        authoredExactTargetGeometryAt] using hpull
    have htower := towerTransportComparison_naturality
      normalizedA.context.square.semantic.square.bottom n
    have htower' :
        (geometryFiberProjection
          normalizedA.context.square.semantic.square.southeast).map pushed ≫
            towerComparison.hom =
          towerComparison.hom ≫
            (coreFiberTransportFunctor
              normalizedA.context.square.semantic.square.bottom).map
                ((geometryFiberProjection
                  normalizedA.context.square.semantic.square.southwest).map n) := by
      simpa only [pushed, towerComparison] using htower
    have hsource := sourceNormalization_projection normalizedA z k g selected.2
    change
      (geometryFiberProjection
        normalizedA.context.square.semantic.square.northeast).map
          ((exactGeometryPullFunctor
            (authoredExactRightInput normalizedA)).map pushed) ≫
          (pullComparison.hom ≫
            (selectedCoreFiberReindexFunctor
              (authoredExactRightInput normalizedA)).map towerComparison.hom) =
        (pullComparison.hom ≫
          (selectedCoreFiberReindexFunctor
            (authoredExactRightInput normalizedA)).map towerComparison.hom) ≫
          (selectedCoreFiberReindexFunctor
            (authoredExactRightInput normalizedA)).map
            ((coreFiberTransportFunctor
              normalizedA.context.square.semantic.square.bottom).map
                (authoredDiagnosticObjectCollapseComponentAtCochain
                  normalizedA omega z.as))
    rw [← Category.assoc, hpull']
    rw [Category.assoc, ← Functor.map_comp, htower', Functor.map_comp,
      hsource,
      authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
        normalizedA omega z.as selected.1 selected.2]
    simp only [Category.assoc]
  · rw [authoredExactBarDAt_eq_id A z omega k g selected]
    have hraw :
        authoredDiagnosticObjectCollapseComponentAtCochain A omega z.as =
          𝟙 _ := by
      by_cases vanishes : omega z.as = 1
      · exact authoredDiagnosticObjectCollapseComponentAtCochain_eq_id
          A omega z.as vanishes
      · have inadmissible : ¬ CanonicalObjectNormalizationAdmissible
            (A.context.supportPackage z.as) := by
          intro admissible
          exact selected ⟨vanishes, admissible⟩
        simp [authoredDiagnosticObjectCollapseComponentAtCochain,
          vanishes, inadmissible]
    rw [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance,
      hraw]
    have mapIdentity :
        (bcProvenanceViaBaseRoute A.context.realizationProvenance).map
            (𝟙 (A.context.supportObject z.as)) =
          𝟙 ((bcProvenanceViaBaseRoute
            A.context.realizationProvenance).obj
              (A.context.supportObject z.as)) :=
      (bcProvenanceViaBaseRoute
        A.context.realizationProvenance).map_id _
    rw [mapIdentity]
    have hprovenance :
        (authoredSupportViaBaseRouteProvenanceIso A.context).hom.app z ≫
            (authoredSupportViaBaseRouteProvenanceIso A.context).inv.app z =
          𝟙 ((authoredSupportViaBaseRoute A.context).obj z) := by
      simp
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id,
      Category.assoc] using (congrArg
        (fun morphism =>
          (authoredExactViaBaseSupportCoreIsoAt A z k g).hom ≫ morphism)
        hprovenance).symm

/-- Projection of `barBeta = barAlpha ≫ barD` is the existing G-116 raw
comparison, with both exact-derived endpoint transports displayed. -/
theorem authoredExactBarBetaAt_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).map
          (authoredExactBarBetaAt A z omega k g) ≫
        (authoredExactViaBaseSupportCoreIsoAt A z k g).hom =
      (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
        (authoredDiagnosticObjectCollapseComparisonAtCochain A omega).app z := by
  rw [authoredExactBarBetaAt, Functor.map_comp, Category.assoc,
    authoredExactBarDAt_projection,
    ← Category.assoc, authoredExactBarAlphaIsoAt_projection,
    authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  simp only [Category.assoc]

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
