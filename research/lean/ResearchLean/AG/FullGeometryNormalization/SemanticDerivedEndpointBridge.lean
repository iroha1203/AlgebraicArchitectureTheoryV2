import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedGeneratedMate
import ResearchLean.AG.FullGeometryNormalization.SemanticExactGeometryTransportAdjunction

/-!
# Semantic derived complete-geometry endpoints and comparison

All four literal endpoints are generated from an exact semantic square and a
single southwest geometry. The comparison with the G-118 generated routes is
proved from the square's pullback property and the exact Cartesian cleavages.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable local instance semanticDerivedEndpointAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _


/-! ## Literal semantic endpoints -/

/-- The southeast geometry transported from the selected southwest geometry. -/
noncomputable def semanticDerivedTargetGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.southeast :=
  semanticDerivedTargetGeometry input
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)

/-- The first exact pullback along the left edge. -/
noncomputable def semanticDerivedLeftPulledGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.northwest :=
  (semanticGeometryPullFunctor input.square.left).obj
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)

/-- The literal direct endpoint, top transport after left pullback. -/
noncomputable def semanticDerivedDirectGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.northeast :=
  (geomFiberTransportFunctor input.square.top).obj
    (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)

/-- The literal via-base endpoint, right pullback after bottom transport. -/
noncomputable def semanticDerivedViaBaseGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.northeast :=
  (semanticGeometryPullFunctor input.square.right).obj
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)

/-- The southwest endpoint of the bottom adjunction unit. -/
noncomputable def semanticDerivedBottomPulledTargetGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.southwest :=
  (semanticGeometryPullFunctor input.square.bottom).obj
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)

/-- The literal northwest source of the five-factor mate. -/
noncomputable def semanticDerivedBGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.northwest :=
  (semanticGeometryPullFunctor input.square.left).obj
    (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)

/-- The literal northwest target of the five-factor mate. -/
noncomputable def semanticDerivedTGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber input.square.northwest :=
  (semanticGeometryPullFunctor input.square.top).obj
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)

/-! ## Literal two-edge Cartesian routes -/

/-- The two exact pull lifts from `B` to the southeast geometry. -/
noncomputable def semanticDerivedDirectBaseRouteLegAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (semanticDerivedBGeometryAt input Q k g endpoint_eq).1 ⟶
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).1 :=
  semanticGeometryPullLift input.square.left
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq) ≫
    semanticGeometryPullLift input.square.bottom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)

/-- The two exact pull lifts from `T` to the southeast geometry. -/
noncomputable def semanticDerivedDirectPulledRouteLegAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (semanticDerivedTGeometryAt input Q k g endpoint_eq).1 ⟶
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).1 :=
  semanticGeometryPullLift input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq) ≫
    semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)

private theorem semanticDerivedDirectBaseRouteLegAt_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (crossStageProjection U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq) =
      eqToHom (semanticDerivedBGeometryAt input Q k g endpoint_eq).2 ≫
        input.square.left ≫ input.square.bottom ≫
        eqToHom (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm := by
  simp only [semanticDerivedDirectBaseRouteLegAt, Functor.map_comp,
    semanticGeometryPullLift_crossStageProjection,
    semanticGeometryPullBaseHom, Category.assoc]
  simp

private theorem semanticDerivedDirectPulledRouteLegAt_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (crossStageProjection U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq) =
      eqToHom (semanticDerivedTGeometryAt input Q k g endpoint_eq).2 ≫
        input.square.top ≫ input.square.right ≫
        eqToHom (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm := by
  simp only [semanticDerivedDirectPulledRouteLegAt, Functor.map_comp,
    semanticGeometryPullLift_crossStageProjection,
    semanticGeometryPullBaseHom, Category.assoc]
  simp

private theorem semanticDerivedDirectBaseRouteLegAt_isStronglyCartesian
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq))
      (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq) := by
  let first := semanticGeometryPullLift input.square.left
    (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
  let second := semanticGeometryPullLift input.square.bottom
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  letI hfirst : (crossStageProjection U).IsStronglyCartesian
      first.base.base first := by
    simpa [first] using semanticGeometryPullLift_crossStageStronglyCartesian_map
      input.square.left
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
  letI hsecond : (crossStageProjection U).IsStronglyCartesian
      second.base.base second := by
    simpa [second] using semanticGeometryPullLift_crossStageStronglyCartesian_map
      input.square.bottom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  simpa [semanticDerivedDirectBaseRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (crossStageProjection U)

private theorem semanticDerivedDirectPulledRouteLegAt_isStronglyCartesian
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq))
      (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq) := by
  let first := semanticGeometryPullLift input.square.top
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  let second := semanticGeometryPullLift input.square.right
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  letI hfirst : (crossStageProjection U).IsStronglyCartesian
      first.base.base first := by
    simpa [first] using semanticGeometryPullLift_crossStageStronglyCartesian_map
      input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  letI hsecond : (crossStageProjection U).IsStronglyCartesian
      second.base.base second := by
    simpa [second] using semanticGeometryPullLift_crossStageStronglyCartesian_map
      input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  simpa [semanticDerivedDirectPulledRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (crossStageProjection U)

/-- The two literal sources have the same northwest point after their stored
fiber incidences are taken into account. -/
noncomputable def semanticDerivedLiteralSourcePointIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    packagePoint (semanticDerivedBGeometryAt input Q k g endpoint_eq).1.core ≅
      packagePoint (semanticDerivedTGeometryAt input Q k g endpoint_eq).1.core :=
  eqToIso (semanticDerivedBGeometryAt input Q k g endpoint_eq).2 ≪≫
    eqToIso (semanticDerivedTGeometryAt input Q k g endpoint_eq).2.symm

private theorem semanticDerivedLiteralRoutes_base_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (crossStageProjection U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq) =
      (semanticDerivedLiteralSourcePointIsoAt input Q k g endpoint_eq).hom ≫
        (crossStageProjection U).map
          (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq) := by
  rw [semanticDerivedDirectBaseRouteLegAt_projection,
    semanticDerivedDirectPulledRouteLegAt_projection]
  simp only [semanticDerivedLiteralSourcePointIsoAt, Iso.trans_hom,
    eqToIso.hom, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ eqToHom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm)
    input.square.commutes

/-- Cartesian uniqueness compares the two literal exact pullback routes in
the original northwest fiber. -/
noncomputable def semanticDerivedLiteralMateNorthwestIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedBGeometryAt input Q k g endpoint_eq ≅
      semanticDerivedTGeometryAt input Q k g endpoint_eq := by
  let baseLeg := semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq
  let pulledLeg := semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq
  let pointIso := semanticDerivedLiteralSourcePointIsoAt input Q k g endpoint_eq
  letI hbase : (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map baseLeg) baseLeg := by
    simpa [baseLeg] using
      semanticDerivedDirectBaseRouteLegAt_isStronglyCartesian
        input Q k g endpoint_eq
  letI hpulled : (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map pulledLeg) pulledLeg := by
    simpa [pulledLeg] using
      semanticDerivedDirectPulledRouteLegAt_isStronglyCartesian
        input Q k g endpoint_eq
  have baseFac : (crossStageProjection U).map baseLeg =
      pointIso.hom ≫ (crossStageProjection U).map pulledLeg := by
    simpa [baseLeg, pulledLeg, pointIso] using
      semanticDerivedLiteralRoutes_base_fac input Q k g endpoint_eq
  let e := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := crossStageProjection U) (g := pointIso)
    (f := (crossStageProjection U).map pulledLeg)
    (f' := (crossStageProjection U).map baseLeg)
    baseFac pulledLeg baseLeg
  have hprojection : (crossStageProjection U).map e.hom = pointIso.hom := by
    letI hmap : (crossStageProjection U).IsHomLift pointIso.hom e.hom := by
      dsimp [e]
      exact CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
        (p := crossStageProjection U)
        (f := (crossStageProjection U).map pulledLeg)
        (φ := pulledLeg) (g := pointIso.hom)
        (f' := (crossStageProjection U).map baseLeg)
        baseFac baseLeg
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (p := crossStageProjection.{u, v} U)
      (a := (semanticDerivedBGeometryAt input Q k g endpoint_eq).1)
      (b := (semanticDerivedTGeometryAt input Q k g endpoint_eq).1)
      (f := pointIso.hom) (φ := e.hom)).symm
  let forward : semanticDerivedBGeometryAt input Q k g endpoint_eq ⟶
      semanticDerivedTGeometryAt input Q k g endpoint_eq :=
    ⟨e.hom, by
      apply CategoryTheory.IsHomLift.of_fac'
        (crossStageProjection U) (𝟙 input.square.northwest) e.hom
        (semanticDerivedBGeometryAt input Q k g endpoint_eq).2
        (semanticDerivedTGeometryAt input Q k g endpoint_eq).2
      rw [hprojection]
      simp [pointIso, semanticDerivedLiteralSourcePointIsoAt]⟩
  letI : IsIso forward := semanticGeomFiberHom_isIso_of_total_isIso forward
  exact asIso forward

/-! ## The semantic complete-geometry comparison -/


/-- The bottom adjunction unit, pulled left and pushed across the top. -/
noncomputable def semanticDerivedUnitTopPushIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedDirectGeometryAt input Q k g endpoint_eq ≅
      (geomFiberTransportFunctor input.square.top).obj
        (semanticDerivedBGeometryAt input Q k g endpoint_eq) := by
  let unit : semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq ⟶
      semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq :=
    (semanticGeometryTransportPullUnit input.square.bottom).app
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  letI : IsIso unit := semanticGeometryTransportPullUnit_app_isIso
    input.square.bottom
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  let pullLeft := semanticGeometryPullFunctor.{u, v} input.square.left
  let pushTop := geomFiberTransportFunctor input.square.top
  exact pushTop.mapIso (pullLeft.mapIso (asIso unit))

/-- The top adjunction counit at the literal via-base endpoint. -/
noncomputable def semanticDerivedTopCounitIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (geomFiberTransportFunctor input.square.top).obj
        (semanticDerivedTGeometryAt input Q k g endpoint_eq) ≅
      semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq := by
  let counit :
      (geomFiberTransportFunctor input.square.top).obj
        (semanticDerivedTGeometryAt input Q k g endpoint_eq) ⟶
      semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq :=
    (semanticGeometryTransportPullCounit input.square.top).app
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  letI : IsIso counit := semanticGeometryTransportPullCounit_app_isIso
    input.square.top
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  exact asIso counit

/-- The complete semantic Beck--Chevalley comparison between the literal
direct and via-base geometries. Its middle factor is the uniquely determined
exact Cartesian mate of the two literal routes. -/
noncomputable def semanticDerivedBarAlphaIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (_square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedDirectGeometryAt input Q k g endpoint_eq ≅
      semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq :=
  semanticDerivedUnitTopPushIsoAt input Q k g endpoint_eq ≪≫
    (geomFiberTransportFunctor input.square.top).mapIso
      (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq) ≪≫
    semanticDerivedTopCounitIsoAt input Q k g endpoint_eq

/-- The comparison hom is the stated unit, Cartesian mate, counit composite. -/
theorem semanticDerivedBarAlphaIsoAt_hom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq square_isPullback).hom =
      (semanticDerivedUnitTopPushIsoAt input Q k g endpoint_eq).hom ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq).hom ≫
      (semanticDerivedTopCounitIsoAt input Q k g endpoint_eq).hom := by
  rfl

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
