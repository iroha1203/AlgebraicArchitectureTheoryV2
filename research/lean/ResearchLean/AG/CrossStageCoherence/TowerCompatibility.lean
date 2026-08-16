import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Pseudonatural compatibility of the geometry and core stages

The geometry projection induces a functor between the fibers over each pointed
extraction instance.  This module compares projection-after-geometry-transport
with core-transport-after-projection by a natural isomorphism generated from
the two canonical lifts.  It also proves compatibility with both compositor
and unitor cells by comparing the actual composite routes.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport

set_option maxHeartbeats 2000000

/-- Projection from the geometry fiber to the core fiber over the same point. -/
noncomputable def geometryFiberProjection {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) :
    GeomFiber.{u, v} X ⥤ CoreFiber X where
  obj G := ⟨G.1.core, G.2⟩
  map {G H} f := ⟨f.1.base, by
    letI : (crossStageProjection.{u, v} U).IsHomLift (𝟙 X) f.1 := f.2
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (𝟙 X) f.1.base G.2 H.2
    simpa only [crossStageProjection_map, packageProjection_map] using
      (CategoryTheory.IsHomLift.commSq
        (crossStageProjection.{u, v} U) (𝟙 X) f.1).w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projected geometry lift is the canonical lower-stage lift. -/
theorem projectedGeomFiberLift_eq_coreFiberLift {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    (G : GeomFiber.{u, v} X) :
    (geomFiberLift σ G).base =
      coreFiberLift σ ((geometryFiberProjection X).obj G) :=
  rfl

/-- Projected geometry transport lands at the projected target-fiber object. -/
theorem projectedGeomFiberTransportObj_eq {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    (G : GeomFiber.{u, v} X) :
    ((geometryFiberProjection Y).obj
      ((geomFiberTransportFunctor σ).obj G)).1 =
      ((coreFiberTransportFunctor σ).obj
        ((geometryFiberProjection X).obj G)).1 :=
  rfl

/-- The projected geometry lift is strong for the core projection. -/
theorem projectedGeomFiberLift_isStronglyCocartesian
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (σ : X ⟶ Y) (G : GeomFiber.{u, v} X) :
    (packageProjection U).IsStronglyCocartesian σ
      (geomFiberLift σ G).base := by
  rw [projectedGeomFiberLift_eq_coreFiberLift]
  exact coreFiberLift_isStronglyCocartesian σ
    ((geometryFiberProjection X).obj G)

/-- Projection preserves the factorization equation for vertical transport. -/
theorem projectedGeomFiberTransportMap_fac {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    {G H : GeomFiber.{u, v} X} (f : G ⟶ H) :
    (geometryProjection U).map (geomFiberLift σ G) ≫
        (geometryProjection U).map (geomFiberTransportMap σ f).1 =
      (geometryProjection U).map f.1 ≫
        (geometryProjection U).map (geomFiberLift σ H) := by
  have h := congrArg (geometryProjection U).map
    (geomFiberTransportMap_fac σ f)
  simpa only [Functor.map_comp, geometryProjection_map] using h

/-- The comparison component between projected geometry and core transport. -/
noncomputable def towerTransportComparisonApp {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    (G : GeomFiber.{u, v} X) :
    ((geomFiberTransportFunctor σ ⋙ geometryFiberProjection Y).obj G) ≅
      ((geometryFiberProjection X ⋙ coreFiberTransportFunctor σ).obj G) := by
  letI : (packageProjection U).IsStronglyCocartesian σ
      (geomFiberLift σ G).base :=
    projectedGeomFiberLift_isStronglyCocartesian σ G
  letI : (packageProjection U).IsStronglyCocartesian σ
      (coreFiberLift σ ((geometryFiberProjection X).obj G)) :=
    coreFiberLift_isStronglyCocartesian σ
      ((geometryFiberProjection X).obj G)
  exact strongLiftComparisonIso (packageProjection U) σ
    (geomFiberLift σ G).base
    (coreFiberLift σ ((geometryFiberProjection X).obj G))

/-- The tower comparison factors the projected lift as the core lift. -/
theorem towerTransportComparisonApp_hom_fac {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    (G : GeomFiber.{u, v} X) :
    (geomFiberLift σ G).base ≫
        (towerTransportComparisonApp σ G).hom.1 =
      coreFiberLift σ ((geometryFiberProjection X).obj G) := by
  letI : (packageProjection U).IsStronglyCocartesian σ
      (geomFiberLift σ G).base :=
    projectedGeomFiberLift_isStronglyCocartesian σ G
  letI : (packageProjection U).IsStronglyCocartesian σ
      (coreFiberLift σ ((geometryFiberProjection X).obj G)) :=
    coreFiberLift_isStronglyCocartesian σ
      ((geometryFiberProjection X).obj G)
  exact strongLiftComparisonHom_fac (packageProjection U) σ
    (B := (geomFiberTransportFunctor σ ⋙ geometryFiberProjection Y).obj G)
    (C := (geometryFiberProjection X ⋙ coreFiberTransportFunctor σ).obj G)
    (geomFiberLift σ G).base
    (coreFiberLift σ ((geometryFiberProjection X).obj G))

/-- The tower comparison is natural on every vertical geometry morphism. -/
theorem towerTransportComparison_naturality {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y)
    {G H : GeomFiber.{u, v} X} (f : G ⟶ H) :
    (geomFiberTransportFunctor σ ⋙ geometryFiberProjection Y).map f ≫
        (towerTransportComparisonApp σ H).hom =
      (towerTransportComparisonApp σ G).hom ≫
        (geometryFiberProjection X ⋙ coreFiberTransportFunctor σ).map f := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian σ
      (geomFiberLift σ G).base :=
    projectedGeomFiberLift_isStronglyCocartesian σ G
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) σ (geomFiberLift σ G).base (𝟙 Y)
  change (geomFiberLift σ G).base ≫
      ((geomFiberTransportMap σ f).1.base ≫
        (towerTransportComparisonApp σ H).hom.1) =
    (geomFiberLift σ G).base ≫
      ((towerTransportComparisonApp σ G).hom.1 ≫
        (coreFiberTransportMap σ ((geometryFiberProjection X).map f)).1)
  calc
    _ = ((geomFiberLift σ G).base ≫
        (geomFiberTransportMap σ f).1.base) ≫
          (towerTransportComparisonApp σ H).hom.1 :=
      (Category.assoc _ _ _).symm
    _ = (f.1.base ≫ (geomFiberLift σ H).base) ≫
          (towerTransportComparisonApp σ H).hom.1 := by
      exact congrArg
        (fun k => k ≫ (towerTransportComparisonApp σ H).hom.1)
        (show (geomFiberLift σ G).base ≫
          (geomFiberTransportMap σ f).1.base =
        f.1.base ≫ (geomFiberLift σ H).base by
        simpa only [geometryProjection_map] using
          projectedGeomFiberTransportMap_fac σ f)
    _ = f.1.base ≫ ((geomFiberLift σ H).base ≫
          (towerTransportComparisonApp σ H).hom.1) := Category.assoc _ _ _
    _ = f.1.base ≫ coreFiberLift σ
          ((geometryFiberProjection X).obj H) := by
      rw [towerTransportComparisonApp_hom_fac]
    _ = coreFiberLift σ ((geometryFiberProjection X).obj G) ≫
        (coreFiberTransportMap σ ((geometryFiberProjection X).map f)).1 :=
      (coreFiberTransportMap_fac σ ((geometryFiberProjection X).map f)).symm
    _ = ((geomFiberLift σ G).base ≫
          (towerTransportComparisonApp σ G).hom.1) ≫
        (coreFiberTransportMap σ ((geometryFiberProjection X).map f)).1 := by
      rw [towerTransportComparisonApp_hom_fac]
    _ = _ := Category.assoc _ _ _

/-- Pseudonatural comparison for a fixed pointed base arrow. -/
noncomputable def towerTransportComparison {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y) :
    geomFiberTransportFunctor.{u, v} σ ⋙ geometryFiberProjection Y ≅
      geometryFiberProjection X ⋙ coreFiberTransportFunctor σ :=
  NatIso.ofComponents (towerTransportComparisonApp σ)
    (fun f => towerTransportComparison_naturality σ f)

/-- Projection carries the geometry compositor factorization to the core stage. -/
theorem projectedGeomFiberCompositor_fac {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    (geomFiberLift (σ ≫ τ) G).base ≫
        ((geometryFiberProjection Z).map
          (geomFiberCompositorApp σ τ G).hom).1 =
      (geomFiberLift σ G).base ≫
        (geomFiberLift τ ((geomFiberTransportFunctor σ).obj G)).base := by
  have h := congrArg (geometryProjection U).map
    (geomFiberCompositorApp_hom_fac σ τ G)
  simpa only [Functor.map_comp, geometryProjection_map,
    geomFiberIteratedLift] using h

/-- Route through the comparison for the composite arrow and the core compositor. -/
noncomputable def towerCompositorDirectRoute {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    (geometryFiberProjection Z).obj
        ((geomFiberTransportFunctor (σ ≫ τ)).obj G) ⟶
      (coreFiberTransportFunctor τ).obj
        ((coreFiberTransportFunctor σ).obj
          ((geometryFiberProjection X).obj G)) :=
  (towerTransportComparisonApp (σ ≫ τ) G).hom ≫
    (coreFiberCompositorApp σ τ
      ((geometryFiberProjection X).obj G)).hom

/-- Route obtained by projecting the geometry compositor and comparing each leg. -/
noncomputable def towerCompositorStagedRoute {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    (geometryFiberProjection Z).obj
        ((geomFiberTransportFunctor (σ ≫ τ)).obj G) ⟶
      (coreFiberTransportFunctor τ).obj
        ((coreFiberTransportFunctor σ).obj
          ((geometryFiberProjection X).obj G)) :=
  (geometryFiberProjection Z).map (geomFiberCompositorApp σ τ G).hom ≫
    (towerTransportComparisonApp τ
      ((geomFiberTransportFunctor σ).obj G)).hom ≫
    (coreFiberTransportFunctor τ).map
      (towerTransportComparisonApp σ G).hom

/-- The direct compositor route factors the projected lift as the iterated core lift. -/
theorem towerCompositorDirectRoute_fac {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    (geomFiberLift (σ ≫ τ) G).base ≫
        (towerCompositorDirectRoute σ τ G).1 =
      coreFiberIteratedLift σ τ ((geometryFiberProjection X).obj G) := by
  change (geomFiberLift (σ ≫ τ) G).base ≫
      ((towerTransportComparisonApp (σ ≫ τ) G).hom.1 ≫
        (coreFiberCompositorApp σ τ
          ((geometryFiberProjection X).obj G)).hom.1) = _
  calc
    _ = ((geomFiberLift (σ ≫ τ) G).base ≫
        (towerTransportComparisonApp (σ ≫ τ) G).hom.1) ≫
          (coreFiberCompositorApp σ τ
            ((geometryFiberProjection X).obj G)).hom.1 :=
      (Category.assoc _ _ _).symm
    _ = coreFiberLift (σ ≫ τ) ((geometryFiberProjection X).obj G) ≫
          (coreFiberCompositorApp σ τ
            ((geometryFiberProjection X).obj G)).hom.1 := by
      rw [towerTransportComparisonApp_hom_fac]
    _ = _ := coreFiberCompositorApp_hom_fac σ τ
      ((geometryFiberProjection X).obj G)

/-- The staged compositor route has the same canonical factorization. -/
theorem towerCompositorStagedRoute_fac {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    (geomFiberLift (σ ≫ τ) G).base ≫
        (towerCompositorStagedRoute σ τ G).1 =
      coreFiberIteratedLift σ τ ((geometryFiberProjection X).obj G) := by
  change (geomFiberLift (σ ≫ τ) G).base ≫
      (((geometryFiberProjection Z).map
          (geomFiberCompositorApp σ τ G).hom).1 ≫
        (towerTransportComparisonApp τ
          ((geomFiberTransportFunctor σ).obj G)).hom.1 ≫
        (coreFiberTransportMap τ
          (towerTransportComparisonApp σ G).hom).1) = _
  calc
    _ = ((geomFiberLift (σ ≫ τ) G).base ≫
          ((geometryFiberProjection Z).map
            (geomFiberCompositorApp σ τ G).hom).1) ≫
        ((towerTransportComparisonApp τ
          ((geomFiberTransportFunctor σ).obj G)).hom.1 ≫
          (coreFiberTransportMap τ
            (towerTransportComparisonApp σ G).hom).1) := by
      simp only [Category.assoc]
    _ = ((geomFiberLift σ G).base ≫
          (geomFiberLift τ
            ((geomFiberTransportFunctor σ).obj G)).base) ≫
        ((towerTransportComparisonApp τ
          ((geomFiberTransportFunctor σ).obj G)).hom.1 ≫
          (coreFiberTransportMap τ
            (towerTransportComparisonApp σ G).hom).1) := by
      rw [projectedGeomFiberCompositor_fac]
    _ = (geomFiberLift σ G).base ≫
        ((geomFiberLift τ
            ((geomFiberTransportFunctor σ).obj G)).base ≫
          ((towerTransportComparisonApp τ
            ((geomFiberTransportFunctor σ).obj G)).hom.1 ≫
            (coreFiberTransportMap τ
              (towerTransportComparisonApp σ G).hom).1)) :=
      Category.assoc _ _ _
    _ = (geomFiberLift σ G).base ≫
        (((geomFiberLift τ
            ((geomFiberTransportFunctor σ).obj G)).base ≫
          (towerTransportComparisonApp τ
            ((geomFiberTransportFunctor σ).obj G)).hom.1) ≫
          (coreFiberTransportMap τ
            (towerTransportComparisonApp σ G).hom).1) := by
      rw [Category.assoc]
    _ = (geomFiberLift σ G).base ≫
        (coreFiberLift τ
            ((geometryFiberProjection Y).obj
              ((geomFiberTransportFunctor σ).obj G)) ≫
          (coreFiberTransportMap τ
            (towerTransportComparisonApp σ G).hom).1) := by
      rw [towerTransportComparisonApp_hom_fac]
    _ = (geomFiberLift σ G).base ≫
        ((towerTransportComparisonApp σ G).hom.1 ≫
          coreFiberLift τ
            ((geometryFiberProjection X ⋙
              coreFiberTransportFunctor σ).obj G)) := by
      rw [coreFiberTransportMap_fac]
    _ = ((geomFiberLift σ G).base ≫
          (towerTransportComparisonApp σ G).hom.1) ≫
        coreFiberLift τ
          ((geometryFiberProjection X ⋙
            coreFiberTransportFunctor σ).obj G) :=
      (Category.assoc _ _ _).symm
    _ = coreFiberLift σ ((geometryFiberProjection X).obj G) ≫
        coreFiberLift τ
          ((geometryFiberProjection X ⋙
            coreFiberTransportFunctor σ).obj G) := by
      rw [towerTransportComparisonApp_hom_fac]
    _ = _ := rfl

/-- The tower comparison respects compositor cells. -/
theorem towerTransportComparison_compositor {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    towerCompositorDirectRoute σ τ G =
      towerCompositorStagedRoute σ τ G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian (σ ≫ τ)
      (geomFiberLift (σ ≫ τ) G).base :=
    projectedGeomFiberLift_isStronglyCocartesian (σ ≫ τ) G
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (σ ≫ τ) (geomFiberLift (σ ≫ τ) G).base (𝟙 Z)
  change (geomFiberLift (σ ≫ τ) G).base ≫
      (towerCompositorDirectRoute σ τ G).1 =
    (geomFiberLift (σ ≫ τ) G).base ≫
      (towerCompositorStagedRoute σ τ G).1
  rw [towerCompositorDirectRoute_fac, towerCompositorStagedRoute_fac]

/-- Projection carries the geometry unitor factorization to the core stage. -/
theorem projectedGeomFiberUnitor_fac {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    (geomFiberLift (𝟙 X) G).base ≫
        ((geometryFiberProjection X).map
          (geomFiberUnitorApp X G).hom).1 = 𝟙 G.1.core := by
  have h := congrArg (geometryProjection U).map
    (geomFiberUnitorApp_hom_fac X G)
  simpa only [Functor.map_comp, Functor.map_id, geometryProjection_map] using h

/-- Unit route through the tower comparison and the core unitor. -/
noncomputable def towerUnitorComparisonRoute {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    (geometryFiberProjection X).obj
        ((geomFiberTransportFunctor (𝟙 X)).obj G) ⟶
      (geometryFiberProjection X).obj G :=
  (towerTransportComparisonApp (𝟙 X) G).hom ≫
    (coreFiberUnitorApp X ((geometryFiberProjection X).obj G)).hom

/-- Unit route obtained by projecting the geometry unitor. -/
noncomputable def towerUnitorProjectedRoute {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    (geometryFiberProjection X).obj
        ((geomFiberTransportFunctor (𝟙 X)).obj G) ⟶
      (geometryFiberProjection X).obj G :=
  (geometryFiberProjection X).map (geomFiberUnitorApp X G).hom

/-- The comparison-and-core-unitor route factors to the identity. -/
theorem towerUnitorComparisonRoute_fac {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    (geomFiberLift (𝟙 X) G).base ≫
        (towerUnitorComparisonRoute X G).1 = 𝟙 G.1.core := by
  change (geomFiberLift (𝟙 X) G).base ≫
      ((towerTransportComparisonApp (𝟙 X) G).hom.1 ≫
        (coreFiberUnitorApp X
          ((geometryFiberProjection X).obj G)).hom.1) = _
  calc
    _ = ((geomFiberLift (𝟙 X) G).base ≫
        (towerTransportComparisonApp (𝟙 X) G).hom.1) ≫
          (coreFiberUnitorApp X
            ((geometryFiberProjection X).obj G)).hom.1 :=
      (Category.assoc _ _ _).symm
    _ = coreFiberLift (𝟙 X) ((geometryFiberProjection X).obj G) ≫
          (coreFiberUnitorApp X
            ((geometryFiberProjection X).obj G)).hom.1 := by
      rw [towerTransportComparisonApp_hom_fac]
    _ = _ := coreFiberUnitorApp_hom_fac X
      ((geometryFiberProjection X).obj G)

/-- The projected geometry-unitor route has the same identity factorization. -/
theorem towerUnitorProjectedRoute_fac {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    (geomFiberLift (𝟙 X) G).base ≫
        (towerUnitorProjectedRoute X G).1 = 𝟙 G.1.core :=
  projectedGeomFiberUnitor_fac X G

/-- The tower comparison respects unitor cells. -/
theorem towerTransportComparison_unitor {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) (G : GeomFiber.{u, v} X) :
    towerUnitorComparisonRoute X G = towerUnitorProjectedRoute X G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian (𝟙 X)
      (geomFiberLift (𝟙 X) G).base :=
    projectedGeomFiberLift_isStronglyCocartesian (𝟙 X) G
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (𝟙 X) (geomFiberLift (𝟙 X) G).base (𝟙 X)
  change (geomFiberLift (𝟙 X) G).base ≫
      (towerUnitorComparisonRoute X G).1 =
    (geomFiberLift (𝟙 X) G).base ≫
      (towerUnitorProjectedRoute X G).1
  rw [towerUnitorComparisonRoute_fac, towerUnitorProjectedRoute_fac]

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
