import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceWhiskeredIso

/-!
# Direct G-106/G-109 associator bridge

This module retains both direct-transport endpoint casts and identifies the
G-109 left-to-right associator cast with the inverse of the named G-106
`transportAlong_assocFiberIso`.  The inverse is required because the G-106
forward leg aligns the right-associated direct transport with the
left-associated one.

The two complete three-arrow route identifications and the resulting use of
`transportAlong_comp_coherence` remain later G-110(E) obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

set_option maxHeartbeats 2000000

theorem transportAlong_assocFiberIso_inv_fac {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {D E F : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine D)
    (g : ExactDoctrineHom D E)
    (h : ExactDoctrineHom E F) :
    transportAlongHom P ((f.comp g).comp h) ≫
        (transportAlong_assocFiberIso P f g h).iso.inv =
      transportAlongHom P (f.comp (g.comp h)) := by
  rw [← transportAlong_assocFiberIso_hom_fac P f g h]
  change (transportAlongHom P (f.comp (g.comp h)) ≫
      (transportAlong_assocFiberIso P f g h).iso.hom) ≫
    (transportAlong_assocFiberIso P f g h).iso.inv = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem coreFiberTripleLeftBaseHom_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberBaseHom ((sigma ≫ tau) ≫ upsilon) G).doctrineHom =
      ((coreFiberBaseHom sigma G).doctrineHom.comp
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom).comp
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom := by
  rw [coreFiberBaseHom_comp_doctrineHom (sigma ≫ tau) upsilon G]
  rw [coreFiberBaseHom_comp_doctrineHom sigma tau G]
  rw [coreFiberWhiskeringBaseHom_eq sigma tau upsilon G]

theorem coreFiberTripleRightBaseHom_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberBaseHom (sigma ≫ (tau ≫ upsilon)) G).doctrineHom =
      (coreFiberBaseHom sigma G).doctrineHom.comp
        ((coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom) := by
  rw [coreFiberBaseHom_comp_doctrineHom sigma (tau ≫ upsilon) G]
  rw [coreFiberBaseHom_comp_doctrineHom tau upsilon
    ((coreFiberTransportFunctor sigma).obj G)]

theorem coreFiberTripleLeftPackageEq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberTransportObject ((sigma ≫ tau) ≫ upsilon) G =
      transportAlong G.1
        (((coreFiberBaseHom sigma G).doctrineHom.comp
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom).comp
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom) :=
  congrArg (transportAlong G.1)
    (coreFiberTripleLeftBaseHom_eq sigma tau upsilon G)

theorem coreFiberTripleRightPackageEq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberTransportObject (sigma ≫ (tau ≫ upsilon)) G =
      transportAlong G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          ((coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)) :=
  congrArg (transportAlong G.1)
    (coreFiberTripleRightBaseHom_eq sigma tau upsilon G)

theorem coreFiberTripleLeftLift_cast_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
        eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) =
      transportAlongHom G.1
        (((coreFiberBaseHom sigma G).doctrineHom.comp
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom).comp
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom) :=
  transportAlongHom_eqToHom_congrArg G.1 _ _
    (coreFiberTripleLeftBaseHom_eq sigma tau upsilon G)

theorem coreFiberTripleRightLift_cast_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    transportAlongHom G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          ((coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)) ≫
      eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm =
    coreFiberLift (sigma ≫ (tau ≫ upsilon)) G :=
  transportAlongHom_eqToHom_congrArg G.1 _ _
    (coreFiberTripleRightBaseHom_eq sigma tau upsilon G).symm

theorem eqToHom_comp4 {C : Type u} [Category C]
    {A B C' D E : C} (hAB : A = B) (hBC : B = C')
    (hCD : C' = D) (hDE : D = E) (hAE : A = E) :
    (((eqToHom hAB : A ⟶ B) ≫ eqToHom hBC) ≫ eqToHom hCD) ≫
      eqToHom hDE = eqToHom hAE := by
  subst hAB
  subst hBC
  subst hCD
  subst hDE
  simp

theorem coreFiberAssociatorCast_hom_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberAssociatorCast sigma tau upsilon G).1 =
      (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
        (transportAlong_assocFiberIso G.1
          (coreFiberBaseHom sigma G).doctrineHom
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
        eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm := by
  let rhs :=
    (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
      (transportAlong_assocFiberIso G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
      eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm
  letI : (packageProjection U).IsStronglyCocartesian
      (((sigma ≫ tau) ≫ upsilon))
      (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) :=
    coreFiberLift_isStronglyCocartesian ((sigma ≫ tau) ≫ upsilon) G
  letI : (packageProjection U).IsHomLift (𝟙 Z)
      (coreFiberAssociatorCast sigma tau upsilon G).1 :=
    (coreFiberAssociatorCast sigma tau upsilon G).2
  letI : (packageProjection U).IsHomLift (𝟙 Z) rhs := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (𝟙 Z) rhs
      ((coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G).2
      ((coreFiberTransportFunctor (sigma ≫ (tau ≫ upsilon))).obj G).2
    change (packageProjection U).map
        ((eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
          (transportAlong_assocFiberIso G.1
            (coreFiberBaseHom sigma G).doctrineHom
            (coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
          eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm) ≫
        eqToHom ((coreFiberTransportFunctor
          (sigma ≫ (tau ≫ upsilon))).obj G).2 =
      eqToHom ((coreFiberTransportFunctor
        ((sigma ≫ tau) ≫ upsilon)).obj G).2 ≫ 𝟙 Z
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
      packageProjection_map]
    rw [(transportAlong_assocFiberIso G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).inv_base_eq]
    simp only [Category.comp_id]
    exact eqToHom_comp4
      (congrArg (packageProjection U).obj
        (coreFiberTripleLeftPackageEq sigma tau upsilon G))
      (transportAlong_assoc_point G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).symm
      (congrArg (packageProjection U).obj
        (coreFiberTripleRightPackageEq sigma tau upsilon G).symm)
      ((coreFiberTransportFunctor (sigma ≫ (tau ≫ upsilon))).obj G).2
      ((coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G).2
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (((sigma ≫ tau) ≫ upsilon))
    (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) (𝟙 Z)
  have hactual :
      coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          (coreFiberAssociatorCast sigma tau upsilon G).1 =
        coreFiberLift (sigma ≫ (tau ≫ upsilon)) G := by
    exact coreFiberLift_eqCast_fac (Category.assoc sigma tau upsilon) G
  have hrhs : coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫ rhs =
      coreFiberLift (sigma ≫ (tau ≫ upsilon)) G := by
    change coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
      ((eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
        (transportAlong_assocFiberIso G.1
          (coreFiberBaseHom sigma G).doctrineHom
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
        eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm) = _
    calc
      _ = (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
            (transportAlong_assocFiberIso G.1
              (coreFiberBaseHom sigma G).doctrineHom
              (coreFiberBaseHom tau
                ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
              (coreFiberBaseHom upsilon
                ((coreFiberTransportFunctor tau).obj
                  ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv)) ≫
          eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm :=
        (Category.assoc _ _ _).symm
      _ = ((coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
          eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G)) ≫
            (transportAlong_assocFiberIso G.1
              (coreFiberBaseHom sigma G).doctrineHom
              (coreFiberBaseHom tau
                ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
              (coreFiberBaseHom upsilon
                ((coreFiberTransportFunctor tau).obj
                  ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
          eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm := by
        exact congrArg (fun q => q ≫
          eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm)
          (Category.assoc _ _ _).symm
      _ = (transportAlongHom G.1
          (((coreFiberBaseHom sigma G).doctrineHom.comp
            (coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom).comp
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom) ≫
            (transportAlong_assocFiberIso G.1
              (coreFiberBaseHom sigma G).doctrineHom
              (coreFiberBaseHom tau
                ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
              (coreFiberBaseHom upsilon
                ((coreFiberTransportFunctor tau).obj
                  ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
          eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm := by
        rw [coreFiberTripleLeftLift_cast_fac]
      _ = transportAlongHom G.1
          ((coreFiberBaseHom sigma G).doctrineHom.comp
            ((coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)) ≫
          eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm := by
        rw [transportAlong_assocFiberIso_inv_fac]
      _ = _ := coreFiberTripleRightLift_cast_fac sigma tau upsilon G
  exact hactual.trans hrhs.symm

noncomputable def coreFiberG106AssociatorHom {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor ((sigma ≫ tau) ≫ upsilon)).obj G ⟶
      (coreFiberTransportFunctor (sigma ≫ (tau ≫ upsilon))).obj G := by
  refine ⟨
    (eqToHom (coreFiberTripleLeftPackageEq sigma tau upsilon G) ≫
      (transportAlong_assocFiberIso G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.inv) ≫
      eqToHom (coreFiberTripleRightPackageEq sigma tau upsilon G).symm, ?_⟩
  rw [← coreFiberAssociatorCast_hom_eq]
  exact (coreFiberAssociatorCast sigma tau upsilon G).2

theorem coreFiberAssociatorCast_eq_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberAssociatorCast sigma tau upsilon G =
      coreFiberG106AssociatorHom sigma tau upsilon G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact coreFiberAssociatorCast_hom_eq sigma tau upsilon G

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
