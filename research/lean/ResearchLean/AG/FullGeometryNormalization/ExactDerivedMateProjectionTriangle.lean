import ResearchLean.AG.FullGeometryNormalization.ExactDerivedMateComposite
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedDirectCanonicalBridgeLaws
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionContracts

/-!
# Exact-derived mate projection triangle

This module moves the actual G-118 mate through the realization-generated
endpoint comparisons and proves its exact two-route triangle.  The proof uses
the generated full-geometry triangle and the independently proved Cartesian
factor laws; no mate, factorization equation, or endpoint certificate is
accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

theorem authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt A z k g).hom.1 =
      (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
        geomFiberLift (authoredExactPullbackSourceIso A).hom
          (authoredExactCanonicalBaseRouteFiberAt A z k g) := by
  rfl

theorem authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt A z k g).hom.1 =
      (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom ≫
        geomFiberLift (authoredExactPullbackSourceIso A).hom
          (authoredExactCanonicalPulledRouteFiberAt A z k g) := by
  rfl

noncomputable def authoredExactCanonicalMateInMixedFiberAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactCanonicalBaseRouteFiberAt A z k g ⟶
      authoredExactCanonicalPulledRouteFiberAt A z k g :=
  (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).hom ≫
    authoredExactGeneratedMateInMixedFiberAt A z k g ≫
    (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g).inv

theorem authoredExactCanonicalMateNorthwest_decomposition
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g).hom ≫
        authoredExactGeneratedMateNorthwestAt A z k g ≫
        (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g).hom =
      (authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
          A z k g).hom ≫
        (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).map
          (authoredExactCanonicalMateInMixedFiberAt A z k g) ≫
        (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
          A z k g).inv := by
  simp [authoredExactBToGeneratedBaseNorthwestIsoAt,
    authoredExactGeneratedPulledToTargetNorthwestIsoAt,
    authoredExactGeneratedMateNorthwestAt,
    authoredExactCanonicalBaseToGeneratedNorthwestIsoAt,
    authoredExactCanonicalPulledToGeneratedNorthwestIsoAt,
    authoredExactCanonicalMateInMixedFiberAt, Functor.map_comp]

theorem authoredExactCanonicalMateInMixedFiberAt_toRefinement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (exactGeometryToRefinementGeometry U).map
        (authoredExactCanonicalMateInMixedFiberAt A z k g).1 =
      (authoredExactCompatibleProblemDataAt A z k g
        ).canonicalAuthoredUpperGeometryMateRefinementAt PUnit.unit := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  change (exactGeometryToRefinementGeometry U).map
      ((authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).hom.1 ≫
        (authoredExactGeneratedMateInMixedFiberAt A z k g).1 ≫
        (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g).inv.1) = _
  simp only [Functor.map_comp]
  rw [show (exactGeometryToRefinementGeometry U).map
          (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).hom.1 =
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
          PUnit.unit).hom from
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement
        PUnit.unit]
  rw [show (exactGeometryToRefinementGeometry U).map
          (authoredExactGeneratedMateInMixedFiberAt A z k g).1 =
        (exactGeometryToRefinementGeometry U).map
          (input.generatedCompatibleUpperGeometryMateAt PUnit.unit) from rfl]
  rw [show (exactGeometryToRefinementGeometry U).map
          (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g).inv.1 =
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
          PUnit.unit).inv from
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement
        PUnit.unit]
  rfl

theorem authoredExactDirectEndpointMate_triangle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((authoredExactBToGeneratedBaseNorthwestIsoAt A z k g).hom ≫
        authoredExactGeneratedMateNorthwestAt A z k g ≫
        (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g).hom).1 ≫
      authoredExactDirectPulledRouteLegAt A z k g =
    authoredExactDirectBaseRouteLegAt A z k g := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  let sigma := (authoredExactPullbackSourceIso A).hom
  let pulledFiber := authoredExactCanonicalPulledRouteFiberAt A z k g
  let pulledLift := geomFiberLift sigma pulledFiber
  letI hpulledLiftStrong : (crossStageProjection U).IsStronglyCocartesian
      sigma pulledLift := by
    simpa [sigma, pulledLift, pulledFiber] using
      geomFiberLift_isStronglyCocartesian sigma pulledFiber
  letI hpulledLiftIso : IsIso pulledLift :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (crossStageProjection U) sigma pulledLift
  have htargetInv :
      (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
          A z k g).inv.1 ≫
        (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom =
      inv pulledLift := by
    apply (cancel_mono pulledLift).1
    rw [Category.assoc,
      ← authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt_hom]
    change ((authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).inv ≫
        (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
          A z k g).hom).1 = _
    simp
    rfl
  have htarget :
      (exactGeometryToRefinementGeometry U).map
          (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
            A z k g).inv.1 ≫
        (exactGeometryToRefinementGeometry U).map
          (authoredExactDirectPulledRouteLegAt A z k g) =
      (exactGeometryToRefinementGeometry U).map (inv pulledLift) ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit := by
    rw [← authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_fac]
    rw [← Category.assoc, ← Functor.map_comp, htargetInv]
  have htransport :
      (authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
          A z k g).hom.1 ≫
        (geomFiberTransportMap sigma
          (authoredExactCanonicalMateInMixedFiberAt A z k g)).1 ≫
        inv pulledLift =
      (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
        (authoredExactCanonicalMateInMixedFiberAt A z k g).1 := by
    rw [authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt_hom]
    have hfac := geomFiberTransportMap_fac sigma
      (authoredExactCanonicalMateInMixedFiberAt A z k g)
    calc
      ((authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
          geomFiberLift sigma
            (authoredExactCanonicalBaseRouteFiberAt A z k g)) ≫
          (geomFiberTransportMap sigma
            (authoredExactCanonicalMateInMixedFiberAt A z k g)).1 ≫ inv pulledLift =
        (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
          ((geomFiberLift sigma
              (authoredExactCanonicalBaseRouteFiberAt A z k g) ≫
            (geomFiberTransportMap sigma
              (authoredExactCanonicalMateInMixedFiberAt A z k g)).1) ≫
            inv pulledLift) := by simp only [Category.assoc]
      _ = (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
          (((authoredExactCanonicalMateInMixedFiberAt A z k g).1 ≫
            geomFiberLift sigma pulledFiber) ≫ inv pulledLift) := by
          rw [hfac]
      _ = (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
          (authoredExactCanonicalMateInMixedFiberAt A z k g).1 := by
          dsimp only [pulledLift]
          simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [authoredExactCanonicalMateNorthwest_decomposition]
  apply (exactGeometryToRefinementGeometry U).map_injective
  simp only [Functor.map_comp]
  change (exactGeometryToRefinementGeometry U).map
      ((authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
          A z k g).hom.1 ≫
        (geomFiberTransportMap sigma
          (authoredExactCanonicalMateInMixedFiberAt A z k g)).1 ≫
        (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
          A z k g).inv.1) ≫
      (exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g) = _
  simp only [Functor.map_comp, Category.assoc]
  rw [htarget]
  have htransportMapped := congrArg
    (fun f => (exactGeometryToRefinementGeometry U).map f) htransport
  simp only [Functor.map_comp] at htransportMapped
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
        (exactGeometryToRefinementGeometry U).map
          (authoredExactCanonicalMateInMixedFiberAt A z k g).1) ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit := by
      rw [← htransportMapped]
      simp only [Category.assoc]
    _ = _ := by
      rw [authoredExactCanonicalMateInMixedFiberAt_toRefinement]
      rw [← input.canonicalAuthoredUpperGeometryMateAt_toRefinement]
      simp only [Category.assoc]
      have htriangle := input.canonicalAuthoredUpperGeometryMateAt_triangle
        PUnit.unit
      change (exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredUpperGeometryMateAt PUnit.unit) ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit =
          input.canonicalAuthoredBaseRouteGeometryHomAt PUnit.unit at htriangle
      rw [htriangle]
      exact authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_fac A z k g

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
