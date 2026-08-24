import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceAssociator

/-!
# G-106/G-109 three-arrow route bridge

This module identifies both actual G-109 pentagon routes with the corresponding
endpoint-casted G-106 adjacent paths.  The final fiber-functor compositor
equality is then derived through `transportAlong_comp_coherence`; the existing
G-109 pentagon equality is not used to establish either route identification.

This discharges the package-to-fiber compositor bridge portion of G-110(E),
not the remaining Beck--Chevalley, diagnostic, pullback, or K4 pasting laws.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

set_option maxHeartbeats 2000000

theorem coreFiberTripleIteratedPackageEq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    ((coreFiberTransportFunctor upsilon).obj
      ((coreFiberTransportFunctor tau).obj
        ((coreFiberTransportFunctor sigma).obj G))).1 =
      transportAlong
        (transportAlong
          (transportAlong G.1 (coreFiberBaseHom sigma G).doctrineHom)
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom)
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom := rfl

noncomputable def coreFiberG106LeftRouteHom {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberTransportObject ((sigma ≫ tau) ≫ upsilon) G ⟶
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).1 :=
  eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
    transportAlongLeftAdjacentCompHom G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom ≫
    eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm

noncomputable def coreFiberG106RightRouteHom {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberTransportObject ((sigma ≫ tau) ≫ upsilon) G ⟶
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).1 :=
  eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
    (transportAlong_assocFiberIso G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv ≫
    transportAlongAdjacentCompHom G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom ≫
    eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm

/-- The left actual route with both components replaced by the reviewed bridges. -/
noncomputable def coreFiberG106LeftComponentRoute {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G ⟶
      (coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G)) :=
  coreFiberG106CompositorHom (sigma ≫ tau) upsilon G ≫
    coreFiberG106WhiskeredCompositorHom sigma tau upsilon G

/-- The right actual route with its associator and binary components replaced. -/
noncomputable def coreFiberG106RightComponentRoute {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G ⟶
      (coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G)) :=
  coreFiberG106AssociatorHom sigma tau upsilon G ≫
    coreFiberG106CompositorHom sigma (tau ≫ upsilon) G ≫
    coreFiberG106CompositorHom tau upsilon
      ((coreFiberTransportFunctor sigma).obj G)

/-- The actual left route is the componentwise G-106 bridge composition. -/
theorem coreFiberPentagonLeftRoute_eq_components {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberPentagonLeftRoute sigma tau upsilon G =
      coreFiberG106LeftComponentRoute sigma tau upsilon G := by
  change (coreFiberCompositorApp (sigma ≫ tau) upsilon G).hom ≫
      (coreFiberTransportFunctor upsilon).map
        (coreFiberCompositorApp sigma tau G).hom =
    coreFiberG106CompositorHom (sigma ≫ tau) upsilon G ≫
      coreFiberG106WhiskeredCompositorHom sigma tau upsilon G
  rw [coreFiberCompositorApp_hom_eq_g106,
    coreFiberCompositor_whiskered_eq_g106]

/-- The actual right route is the componentwise G-106 bridge composition. -/
theorem coreFiberPentagonRightRoute_eq_components {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberPentagonRightRoute sigma tau upsilon G =
      coreFiberG106RightComponentRoute sigma tau upsilon G := by
  change coreFiberAssociatorCast sigma tau upsilon G ≫
      (coreFiberCompositorApp sigma (tau ≫ upsilon) G).hom ≫
      (coreFiberCompositorApp tau upsilon
        ((coreFiberTransportFunctor sigma).obj G)).hom =
    coreFiberG106AssociatorHom sigma tau upsilon G ≫
      coreFiberG106CompositorHom sigma (tau ≫ upsilon) G ≫
      coreFiberG106CompositorHom tau upsilon
        ((coreFiberTransportFunctor sigma).obj G)
  rw [coreFiberAssociatorCast_eq_g106,
    coreFiberCompositorApp_hom_eq_g106,
    coreFiberCompositorApp_hom_eq_g106]

theorem coreFiberG106RouteHom_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberG106LeftRouteHom sigma tau upsilon G =
      coreFiberG106RightRouteHom sigma tau upsilon G := by
  let f := (coreFiberBaseHom sigma G).doctrineHom
  let g := (coreFiberBaseHom tau
    ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
  let h := (coreFiberBaseHom upsilon
    ((coreFiberTransportFunctor tau).obj
      ((coreFiberTransportFunctor sigma).obj G))).doctrineHom
  have hassoc :
      (transportAlong_assocFiberIso G.1 f g h).iso.inv ≫
          transportAlongAdjacentCompHom G.1 f g h =
        transportAlongLeftAdjacentCompHom G.1 f g h := by
    rw [transportAlong_comp_coherence]
    change (transportAlong_assocFiberIso G.1 f g h).iso.inv ≫
        ((transportAlong_assocFiberIso G.1 f g h).iso.hom ≫
          transportAlongLeftAdjacentCompHom G.1 f g h) = _
    simp
  change eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
      transportAlongLeftAdjacentCompHom G.1 f g h ≫
      eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm =
    eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
      (transportAlong_assocFiberIso G.1 f g h).iso.inv ≫
      transportAlongAdjacentCompHom G.1 f g h ≫
      eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm
  rw [← hassoc]
  simp only [Category.assoc]

theorem coreFiberG106LeftRouteHom_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
        coreFiberG106LeftRouteHom sigma tau upsilon G =
      coreFiberTripleIteratedLift sigma tau upsilon G := by
  change coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
      (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
        transportAlongLeftAdjacentCompHom G.1
          (coreFiberBaseHom sigma G).doctrineHom
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom ≫
        eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm) = _
  rw [← Category.assoc, coreFiberTripleLeftLift_cast_fac]
  rw [← Category.assoc]
  change ((transportAlongHom G.1
      (((coreFiberBaseHom sigma G).doctrineHom.comp
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom).comp
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)).comp
      (transportAlongLeftAdjacentCompHom G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)).comp
      (eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm) = _
  rw [transportAlongLeftAdjacentCompHom_fac]
  rfl

theorem coreFiberG106LeftComponentRoute_hom_eq_path {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberG106LeftComponentRoute sigma tau upsilon G).1 =
      coreFiberG106LeftRouteHom sigma tau upsilon G := by
  let rhs := coreFiberG106LeftRouteHom sigma tau upsilon G
  letI : (packageProjection U).IsStronglyCocartesian
      ((sigma ≫ tau) ≫ upsilon)
      (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) :=
    coreFiberLift_isStronglyCocartesian ((sigma ≫ tau) ≫ upsilon) G
  letI : (packageProjection U).IsHomLift (𝟙 Z)
      (coreFiberG106LeftComponentRoute sigma tau upsilon G).1 :=
    (coreFiberG106LeftComponentRoute sigma tau upsilon G).2
  letI : (packageProjection U).IsHomLift (𝟙 Z) rhs := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (𝟙 Z) rhs
      ((coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G).2
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2
    change (packageProjection U).map
        (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
          transportAlongLeftAdjacentCompHom G.1
            (coreFiberBaseHom sigma G).doctrineHom
            (coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom ≫
          eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm) ≫
        eqToHom ((coreFiberTransportFunctor upsilon).obj
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).2 =
      eqToHom ((coreFiberTransportFunctor
        ((sigma ≫ tau) ≫ upsilon)).obj G).2 ≫ 𝟙 Z
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
      packageProjection_map]
    rw [transportAlongLeftAdjacentCompHom_base]
    simp only [Category.comp_id]
    exact eqToHom_comp4
      (congrArg (packageProjection U).obj
        (coreFiberTripleLeftPackageEq sigma tau upsilon G))
      (transportAlong_leftTriple_point G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)
      (congrArg (packageProjection U).obj
        (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm)
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2
      ((coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G).2
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) ((sigma ≫ tau) ≫ upsilon)
    (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) (𝟙 Z)
  have hcomponent :
      coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          (coreFiberG106LeftComponentRoute sigma tau upsilon G).1 =
        coreFiberTripleIteratedLift sigma tau upsilon G := by
    calc
      _ = coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          (coreFiberPentagonLeftRoute sigma tau upsilon G).1 :=
        congrArg (fun q => coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫ q.1)
          (coreFiberPentagonLeftRoute_eq_components sigma tau upsilon G).symm
      _ = _ := coreFiberPentagonLeftRoute_fac sigma tau upsilon G
  exact hcomponent.trans
    (coreFiberG106LeftRouteHom_fac sigma tau upsilon G).symm

/-- The actual left route is the componentwise bridge followed by the G-106 path. -/
theorem coreFiberPentagonLeftRoute_hom_eq_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberPentagonLeftRoute sigma tau upsilon G).1 =
      coreFiberG106LeftRouteHom sigma tau upsilon G :=
  (congrArg (fun q => q.1)
    (coreFiberPentagonLeftRoute_eq_components sigma tau upsilon G)).trans
    (coreFiberG106LeftComponentRoute_hom_eq_path sigma tau upsilon G)

theorem eqToHom_comp5 {C : Type u} [Category C]
    {A B C' D E F : C} (hAB : A = B) (hBC : B = C')
    (hCD : C' = D) (hDE : D = E) (hEF : E = F) (hAF : A = F) :
    ((((eqToHom hAB : A ⟶ B) ≫ eqToHom hBC) ≫ eqToHom hCD) ≫
      eqToHom hDE) ≫ eqToHom hEF = eqToHom hAF := by
  subst hAB
  subst hBC
  subst hCD
  subst hDE
  subst hEF
  simp

theorem coreFiberG106RightRouteHom_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
        coreFiberG106RightRouteHom sigma tau upsilon G =
      coreFiberTripleIteratedLift sigma tau upsilon G := by
  let f := (coreFiberBaseHom sigma G).doctrineHom
  let g := (coreFiberBaseHom tau
    ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
  let h := (coreFiberBaseHom upsilon
    ((coreFiberTransportFunctor tau).obj
      ((coreFiberTransportFunctor sigma).obj G))).doctrineHom
  change coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
      (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
        (transportAlong_assocFiberIso G.1 f g h).iso.inv ≫
        transportAlongAdjacentCompHom G.1 f g h ≫
        eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm) = _
  rw [← Category.assoc, coreFiberTripleLeftLift_cast_fac]
  rw [← Category.assoc, transportAlong_assocFiberIso_inv_fac]
  rw [← Category.assoc]
  change ((transportAlongHom G.1 (f.comp (g.comp h))).comp
      (transportAlongAdjacentCompHom G.1 f g h)).comp
      (eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm) = _
  rw [transportAlongAdjacentCompHom_fac]
  rfl

theorem coreFiberG106RightComponentRoute_hom_eq_path {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberG106RightComponentRoute sigma tau upsilon G).1 =
      coreFiberG106RightRouteHom sigma tau upsilon G := by
  let f := (coreFiberBaseHom sigma G).doctrineHom
  let g := (coreFiberBaseHom tau
    ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
  let h := (coreFiberBaseHom upsilon
    ((coreFiberTransportFunctor tau).obj
      ((coreFiberTransportFunctor sigma).obj G))).doctrineHom
  let rhs := coreFiberG106RightRouteHom sigma tau upsilon G
  letI : (packageProjection U).IsStronglyCocartesian
      ((sigma ≫ tau) ≫ upsilon)
      (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) :=
    coreFiberLift_isStronglyCocartesian ((sigma ≫ tau) ≫ upsilon) G
  letI : (packageProjection U).IsHomLift (𝟙 Z)
      (coreFiberG106RightComponentRoute sigma tau upsilon G).1 :=
    (coreFiberG106RightComponentRoute sigma tau upsilon G).2
  letI : (packageProjection U).IsHomLift (𝟙 Z) rhs := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (𝟙 Z) rhs
      ((coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G).2
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2
    change (packageProjection U).map
        (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
          (transportAlong_assocFiberIso G.1 f g h).iso.inv ≫
          transportAlongAdjacentCompHom G.1 f g h ≫
          eqToHom (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm) ≫
        eqToHom ((coreFiberTransportFunctor upsilon).obj
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).2 =
      eqToHom ((coreFiberTransportFunctor
        ((sigma ≫ tau) ≫ upsilon)).obj G).2 ≫ 𝟙 Z
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map, packageProjection_map]
    rw [(transportAlong_assocFiberIso G.1 f g h).inv_base_eq]
    rw [packageProjection_map]
    rw [transportAlongAdjacentCompHom_base]
    simp only [Category.comp_id]
    exact eqToHom_comp5
      (congrArg (packageProjection U).obj
        (coreFiberTripleLeftPackageEq sigma tau upsilon G))
      (transportAlong_assoc_point G.1 f g h).symm
      (transportAlong_triple_point G.1 f g h)
      (congrArg (packageProjection U).obj
        (coreFiberTripleIteratedPackageEq sigma tau upsilon G).symm)
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2
      ((coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G).2
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) ((sigma ≫ tau) ≫ upsilon)
    (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) (𝟙 Z)
  have hcomponent :
      coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          (coreFiberG106RightComponentRoute sigma tau upsilon G).1 =
        coreFiberTripleIteratedLift sigma tau upsilon G := by
    calc
      _ = coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          (coreFiberPentagonRightRoute sigma tau upsilon G).1 :=
        congrArg (fun q => coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫ q.1)
          (coreFiberPentagonRightRoute_eq_components sigma tau upsilon G).symm
      _ = _ := coreFiberPentagonRightRoute_fac sigma tau upsilon G
  exact hcomponent.trans
    (coreFiberG106RightRouteHom_fac sigma tau upsilon G).symm

/-- The actual right route is the componentwise bridge followed by the G-106 path. -/
theorem coreFiberPentagonRightRoute_hom_eq_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberPentagonRightRoute sigma tau upsilon G).1 =
      coreFiberG106RightRouteHom sigma tau upsilon G :=
  (congrArg (fun q => q.1)
    (coreFiberPentagonRightRoute_eq_components sigma tau upsilon G)).trans
    (coreFiberG106RightComponentRoute_hom_eq_path sigma tau upsilon G)

noncomputable def coreFiberG106LeftRoute {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G ⟶
      (coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G)) := by
  refine ⟨coreFiberG106LeftRouteHom sigma tau upsilon G, ?_⟩
  rw [← coreFiberPentagonLeftRoute_hom_eq_g106]
  exact (coreFiberPentagonLeftRoute sigma tau upsilon G).2

noncomputable def coreFiberG106RightRoute {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G ⟶
      (coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G)) := by
  refine ⟨coreFiberG106RightRouteHom sigma tau upsilon G, ?_⟩
  rw [← coreFiberPentagonRightRoute_hom_eq_g106]
  exact (coreFiberPentagonRightRoute sigma tau upsilon G).2

theorem coreFiberPentagonLeftRoute_eq_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberPentagonLeftRoute sigma tau upsilon G =
      coreFiberG106LeftRoute sigma tau upsilon G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact coreFiberPentagonLeftRoute_hom_eq_g106 sigma tau upsilon G

theorem coreFiberPentagonRightRoute_eq_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberPentagonRightRoute sigma tau upsilon G =
      coreFiberG106RightRoute sigma tau upsilon G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact coreFiberPentagonRightRoute_hom_eq_g106 sigma tau upsilon G

theorem coreFiberG106Route_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberG106LeftRoute sigma tau upsilon G =
      coreFiberG106RightRoute sigma tau upsilon G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact coreFiberG106RouteHom_eq sigma tau upsilon G

/-- G-109 compositor coherence obtained through the named G-106 path equality. -/
theorem coreFiberCompositor_assoc_via_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberPentagonLeftRoute sigma tau upsilon G =
      coreFiberPentagonRightRoute sigma tau upsilon G := by
  calc
    _ = coreFiberG106LeftRoute sigma tau upsilon G :=
      coreFiberPentagonLeftRoute_eq_g106 sigma tau upsilon G
    _ = coreFiberG106RightRoute sigma tau upsilon G :=
      coreFiberG106Route_eq sigma tau upsilon G
    _ = _ := (coreFiberPentagonRightRoute_eq_g106 sigma tau upsilon G).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
