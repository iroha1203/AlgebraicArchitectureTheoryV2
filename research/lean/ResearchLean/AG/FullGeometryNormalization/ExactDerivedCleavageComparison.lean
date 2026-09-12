import ResearchLean.AG.FullGeometryNormalization.ExactDerivedGeneratedMate
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointExactIsos

/-!
# Direct-to-generated cleavage comparisons for G-122

This support layer exposes the literal exact iterated pullback legs and the
source-point isomorphisms that compare their authored northwest fibers with
the G-118 generated mixed-pullback fibers.  The source isomorphisms are built
from the realization-proven pullback comparison and endpoint incidence; no
comparison or certificate is accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The literal two-step exact base route from the direct `B_z` endpoint to
`q_z`; this is the authored comparison leg later matched to the generated
canonical route by Cartesian uniqueness. -/
noncomputable def authoredExactDirectBaseRouteLegAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateSourceGeometryAt A z k g).1 ⟶
      (authoredExactTargetGeometryAt A z k g).1 :=
  exactGeometryPullLift (authoredExactLeftInput A)
      (authoredExactBottomPulledTargetGeometryAt A z k g) ≫
    exactGeometryPullLift (authoredExactBottomInput A)
      (authoredExactTargetGeometryAt A z k g)

/-- The exact pointed comparison from the direct northwest package point to
the generated mixed-pullback package point. -/
noncomputable def authoredExactBaseRouteSourcePointIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    packagePoint (authoredExactGeneratedMateSourceGeometryAt A z k g).1.core ≅
      packagePoint (authoredExactGeneratedBaseRouteFiberAt A z k g).1.core :=
  eqToIso (authoredExactGeneratedMateSourceGeometryAt A z k g).2 ≪≫
    (authoredExactPullbackSourceIso A).symm ≪≫
    eqToIso (authoredExactGeneratedBaseRouteFiberAt A z k g).2.symm

/-- The exact pointed comparison from the direct northwest package point to
the generated pulled-route mixed-pullback package point. -/
noncomputable def authoredExactPulledRouteSourcePointIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    packagePoint (authoredExactGeneratedMateTargetGeometryAt A z k g).1.core ≅
      packagePoint (authoredExactGeneratedPulledRouteFiberAt A z k g).1.core :=
  eqToIso (authoredExactGeneratedMateTargetGeometryAt A z k g).2 ≪≫
    (authoredExactPullbackSourceIso A).symm ≪≫
    eqToIso (authoredExactGeneratedPulledRouteFiberAt A z k g).2.symm

/-- The literal direct pulled-first exact route from `T_z` to `q_z`. -/
noncomputable def authoredExactDirectPulledRouteLegAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateTargetGeometryAt A z k g).1 ⟶
      (authoredExactTargetGeometryAt A z k g).1 :=
  exactGeometryPullLift (authoredExactTopInput A)
      (authoredExactViaBaseGeometryAt A z k g) ≫
    exactGeometryPullLift (authoredExactRightInput A)
      (authoredExactTargetGeometryAt A z k g)

/-! ## Canonical-authored route endpoints in the exact-derived fibers -/

/-- The G-118 canonical-authored base normalization, retaining its generated
mixed-pullback incidence. -/
noncomputable def authoredExactCanonicalBaseRouteFiberAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber
      ((authoredExactRefinementBCConfiguration A).pullbackSourceAt
        (authoredExactRefinementBCCompatibleSource A)) := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  refine ⟨input.canonicalAuthoredBaseRouteGeometryAt PUnit.unit, ?_⟩
  change packagePoint
      (input.canonicalAuthoredBaseRouteGeometryAt PUnit.unit).core = _
  rw [input.canonicalAuthoredBaseRouteGeometryAt_core]
  exact UpperGeometryCleavage.baseRouteGeometry_packagePoint_eq
    (authoredExactRefinementBCContextAt A z k g)
    (input.sourceTargetGeometryAt PUnit.unit)

/-- The G-118 canonical-authored pulled normalization, retaining its generated
mixed-pullback incidence. -/
noncomputable def authoredExactCanonicalPulledRouteFiberAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber
      ((authoredExactRefinementBCConfiguration A).pullbackSourceAt
        (authoredExactRefinementBCCompatibleSource A)) := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  refine ⟨input.canonicalAuthoredPulledRouteGeometryAt PUnit.unit, ?_⟩
  change packagePoint
      (input.canonicalAuthoredPulledRouteGeometryAt PUnit.unit).core = _
  rw [input.canonicalAuthoredPulledRouteGeometryAt_core]
  exact UpperGeometryCleavage.pulledRouteGeometry_packagePoint_eq
    (authoredExactRefinementBCContextAt A z k g)
    (input.sourceTargetGeometryAt PUnit.unit)

/-- The exact endpoint comparison lifted to the generated mixed-pullback
fiber. -/
noncomputable def authoredExactCanonicalBaseToGeneratedFiberIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactCanonicalBaseRouteFiberAt A z k g ≅
      authoredExactGeneratedBaseRouteFiberAt A z k g := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  let e := input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
    PUnit.unit
  refine
    { hom := ⟨show
          (authoredExactCanonicalBaseRouteFiberAt A z k g).1 ⟶
            (authoredExactGeneratedBaseRouteFiberAt A z k g).1 from by
          simpa [authoredExactCanonicalBaseRouteFiberAt,
            authoredExactGeneratedBaseRouteFiberAt, input, e] using e.hom, ?_⟩
      inv := ⟨show
          (authoredExactGeneratedBaseRouteFiberAt A z k g).1 ⟶
            (authoredExactCanonicalBaseRouteFiberAt A z k g).1 from by
          simpa [authoredExactCanonicalBaseRouteFiberAt,
            authoredExactGeneratedBaseRouteFiberAt, input, e] using e.inv, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.IsHomLift.of_fac'
      (crossStageProjection.{u, v} U) (𝟙 _) _
      (authoredExactCanonicalBaseRouteFiberAt A z k g).2
      (authoredExactGeneratedBaseRouteFiberAt A z k g).2
    rw [crossStageProjection_map]
    simp [e, input, authoredExactCanonicalBaseRouteFiberAt,
      authoredExactGeneratedBaseRouteFiberAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt]
    rfl
  · apply CategoryTheory.IsHomLift.of_fac'
      (crossStageProjection.{u, v} U) (𝟙 _) _
      (authoredExactGeneratedBaseRouteFiberAt A z k g).2
      (authoredExactCanonicalBaseRouteFiberAt A z k g).2
    rw [crossStageProjection_map]
    simp [e, input, authoredExactCanonicalBaseRouteFiberAt,
      authoredExactGeneratedBaseRouteFiberAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt]
    rfl
  · apply CategoryTheory.Functor.Fiber.hom_ext
    simpa [authoredExactCanonicalBaseRouteFiberAt,
      authoredExactGeneratedBaseRouteFiberAt, input, e] using e.hom_inv_id
  · apply CategoryTheory.Functor.Fiber.hom_ext
    simpa [authoredExactCanonicalBaseRouteFiberAt,
      authoredExactGeneratedBaseRouteFiberAt, input, e] using e.inv_hom_id

/-- The exact pulled endpoint comparison lifted to the generated
mixed-pullback fiber. -/
noncomputable def authoredExactCanonicalPulledToGeneratedFiberIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactCanonicalPulledRouteFiberAt A z k g ≅
      authoredExactGeneratedPulledRouteFiberAt A z k g := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  let e := input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
    PUnit.unit
  refine
    { hom := ⟨show
          (authoredExactCanonicalPulledRouteFiberAt A z k g).1 ⟶
            (authoredExactGeneratedPulledRouteFiberAt A z k g).1 from by
          simpa [authoredExactCanonicalPulledRouteFiberAt,
            authoredExactGeneratedPulledRouteFiberAt, input, e] using e.hom, ?_⟩
      inv := ⟨show
          (authoredExactGeneratedPulledRouteFiberAt A z k g).1 ⟶
            (authoredExactCanonicalPulledRouteFiberAt A z k g).1 from by
          simpa [authoredExactCanonicalPulledRouteFiberAt,
            authoredExactGeneratedPulledRouteFiberAt, input, e] using e.inv, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.IsHomLift.of_fac'
      (crossStageProjection.{u, v} U) (𝟙 _) _
      (authoredExactCanonicalPulledRouteFiberAt A z k g).2
      (authoredExactGeneratedPulledRouteFiberAt A z k g).2
    rw [crossStageProjection_map]
    simp [e, input, authoredExactCanonicalPulledRouteFiberAt,
      authoredExactGeneratedPulledRouteFiberAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt]
    rfl
  · apply CategoryTheory.IsHomLift.of_fac'
      (crossStageProjection.{u, v} U) (𝟙 _) _
      (authoredExactGeneratedPulledRouteFiberAt A z k g).2
      (authoredExactCanonicalPulledRouteFiberAt A z k g).2
    rw [crossStageProjection_map]
    simp [e, input, authoredExactCanonicalPulledRouteFiberAt,
      authoredExactGeneratedPulledRouteFiberAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt,
      UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt]
    rfl
  · apply CategoryTheory.Functor.Fiber.hom_ext
    simpa [authoredExactCanonicalPulledRouteFiberAt,
      authoredExactGeneratedPulledRouteFiberAt, input, e] using e.hom_inv_id
  · apply CategoryTheory.Functor.Fiber.hom_ext
    simpa [authoredExactCanonicalPulledRouteFiberAt,
      authoredExactGeneratedPulledRouteFiberAt, input, e] using e.inv_hom_id

/-- The canonical-authored base normalization transported to the original
northwest fiber. -/
noncomputable def authoredExactCanonicalBaseRouteNorthwestAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northwest :=
  (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).obj
    (authoredExactCanonicalBaseRouteFiberAt A z k g)

/-- The canonical-authored pulled normalization transported to the original
northwest fiber. -/
noncomputable def authoredExactCanonicalPulledRouteNorthwestAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northwest :=
  (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).obj
    (authoredExactCanonicalPulledRouteFiberAt A z k g)

/-- Transport of the exact base endpoint comparison to the authored
northwest fiber. -/
noncomputable def authoredExactCanonicalBaseToGeneratedNorthwestIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactCanonicalBaseRouteNorthwestAt A z k g ≅
      authoredExactGeneratedBaseRouteNorthwestAt A z k g :=
  (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).mapIso
    (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g)

/-- Transport of the exact pulled endpoint comparison to the authored
northwest fiber. -/
noncomputable def authoredExactCanonicalPulledToGeneratedNorthwestIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactCanonicalPulledRouteNorthwestAt A z k g ≅
      authoredExactGeneratedPulledRouteNorthwestAt A z k g :=
  (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).mapIso
    (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g)

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
