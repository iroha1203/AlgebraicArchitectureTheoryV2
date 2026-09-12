import ResearchLean.AG.FullGeometryNormalization.ExactDerivedEndpointGeometry
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate

/-!
# Exact-derived complete endpoints on authored support

This module identifies the core projections of the two exact-derived complete
geometry endpoints with the corresponding authored-support Beck--Chevalley
routes.  The endpoint comparison is reconstructed from the realization
provenance of the authored square; no object equality or endpoint cast is
accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The projected direct complete-geometry endpoint is the authored-support
direct core route at the same cell. -/
noncomputable def authoredExactDirectSupportCoreIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).obj
        (authoredExactDirectGeometryAt A z k g) ≅
      (authoredSupportDirectRoute A.context).obj z := by
  refine authoredExactDirectGeometryCoreIsoAt A z k g ≪≫ ?_
  rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact Iso.refl _

/-- The projected via-base complete-geometry endpoint is the authored-support
via-base core route at the same cell. -/
noncomputable def authoredExactViaBaseSupportCoreIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).obj
        (authoredExactViaBaseGeometryAt A z k g) ≅
      (authoredSupportViaBaseRoute A.context).obj z := by
  refine authoredExactViaBaseGeometryCoreIsoAt A z k g ≪≫ ?_
  rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact Iso.refl _

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
