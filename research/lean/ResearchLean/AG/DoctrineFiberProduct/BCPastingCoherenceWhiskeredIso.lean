import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceWhiskering

/-!
# Direct G-106/G-109 whiskered-component bridge

This module constructs the endpoint cast omitted by the first whiskering
factorization and identifies the transported G-109 compositor component with
the named G-106 `transportAlong_whiskeredCompFiberIso` comparison.  Package
and third-arrow data are transported together as a dependent pair, so neither
the source package nor its exact morphism is hidden by a false definitional
equality.

Associator compatibility and the resulting three-arrow route identification
remain later G-110(E) obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The third exact doctrine morphism is independent of the two fiber realizations. -/
theorem coreFiberWhiskeringBaseHom_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberBaseHom upsilon
      ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).doctrineHom =
    (coreFiberBaseHom upsilon
      ((coreFiberTransportFunctor tau).obj
        ((coreFiberTransportFunctor sigma).obj G))).doctrineHom := by
  change (extInstToDoctrine U).map
      (eqToHom ((coreFiberTransportFunctor (sigma ≫ tau)).obj G).2 ≫ upsilon) =
    (extInstToDoctrine U).map
      (eqToHom ((coreFiberTransportFunctor tau).obj
        ((coreFiberTransportFunctor sigma).obj G)).2 ≫ upsilon)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]

/--
The source of the transported G-109 component equals the G-106 whiskered
source after transporting the package and its third exact morphism together.
-/
theorem coreFiberWhiskeredSourcePackageEq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberTransportObject upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G) =
      transportAlong
        (transportAlong G.1
          ((coreFiberBaseHom sigma G).doctrineHom.comp
            (coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom))
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom := by
  change transportAlong
      (coreFiberTransportObject (sigma ≫ tau) G)
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).doctrineHom = _
  let left : Σ Q : AATCorePackage U,
      ExactDoctrineHom Q.reading.doctrine Z.doctrine :=
    ⟨coreFiberTransportObject (sigma ≫ tau) G,
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).doctrineHom⟩
  let right : Σ Q : AATCorePackage U,
      ExactDoctrineHom Q.reading.doctrine Z.doctrine :=
    ⟨transportAlong G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom),
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom⟩
  have hpair : left = right := by
    apply Sigma.ext (coreFiberDirectPackageEq sigma tau G)
    exact heq_of_eq (coreFiberWhiskeringBaseHom_eq sigma tau upsilon G)
  exact congrArg (fun qh => transportAlong qh.1 qh.2) hpair

/-- Canonical lifts commute with equality transport of a package/exact-hom pair. -/
theorem transportAlongSigmaHom_eqToHom {U : AtomCarrier.{u}}
    {Z : ExtractionDoctrine U}
    (left right : Σ Q : AATCorePackage U,
      ExactDoctrineHom Q.reading.doctrine Z)
    (h : left = right) :
    transportAlongHom left.1 left.2 ≫
        eqToHom (congrArg (fun qh => transportAlong qh.1 qh.2) h) =
      eqToHom (congrArg Sigma.fst h) ≫
        transportAlongHom right.1 right.2 := by
  subst h
  simp

/-- The endpoint cast carries the G-109 third lift to the G-106 third lift. -/
theorem coreFiberWhiskeredSourceLift_cast_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G) ≫
      eqToHom (coreFiberWhiskeredSourcePackageEq sigma tau upsilon G) =
    eqToHom (coreFiberDirectPackageEq sigma tau G) ≫
      transportAlongHom
        (transportAlong G.1
          ((coreFiberBaseHom sigma G).doctrineHom.comp
            (coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom))
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom := by
  let left : Σ Q : AATCorePackage U,
      ExactDoctrineHom Q.reading.doctrine Z.doctrine :=
    ⟨coreFiberTransportObject (sigma ≫ tau) G,
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).doctrineHom⟩
  let right : Σ Q : AATCorePackage U,
      ExactDoctrineHom Q.reading.doctrine Z.doctrine :=
    ⟨transportAlong G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom),
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom⟩
  have hpair : left = right := by
    apply Sigma.ext (coreFiberDirectPackageEq sigma tau G)
    exact heq_of_eq (coreFiberWhiskeringBaseHom_eq sigma tau upsilon G)
  have heq : congrArg (fun qh => transportAlong qh.1 qh.2) hpair =
      coreFiberWhiskeredSourcePackageEq sigma tau upsilon G :=
    Subsingleton.elim _ _
  rw [← heq]
  have hfst : congrArg Sigma.fst hpair =
      coreFiberDirectPackageEq sigma tau G := Subsingleton.elim _ _
  rw [← hfst]
  exact transportAlongSigmaHom_eqToHom left right hpair

/--
The transported G-109 compositor component is the endpoint-casted named G-106
whiskered comparison as an equality of package morphisms.
-/
theorem coreFiberCompositor_whiskered_hom_eq {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    ((coreFiberTransportFunctor upsilon).map
      (coreFiberCompositorApp sigma tau G).hom).1 =
    eqToHom (coreFiberWhiskeredSourcePackageEq sigma tau upsilon G) ≫
      (transportAlong_whiskeredCompFiberIso G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.hom := by
  let rhs := eqToHom
      (coreFiberWhiskeredSourcePackageEq sigma tau upsilon G) ≫
    (transportAlong_whiskeredCompFiberIso G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.hom
  letI : (packageProjection U).IsStronglyCocartesian upsilon
      (coreFiberLift upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)) :=
    coreFiberLift_isStronglyCocartesian upsilon
      ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)
  letI : (packageProjection U).IsHomLift (𝟙 Z)
      ((coreFiberTransportFunctor upsilon).map
        (coreFiberCompositorApp sigma tau G).hom).1 :=
    ((coreFiberTransportFunctor upsilon).map
      (coreFiberCompositorApp sigma tau G).hom).2
  letI : (packageProjection U).IsHomLift (𝟙 Z) rhs := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (𝟙 Z) rhs
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).2
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2
    change (packageProjection U).map
        (eqToHom
          (coreFiberWhiskeredSourcePackageEq sigma tau upsilon G) ≫
        (transportAlong_whiskeredCompFiberIso G.1
          (coreFiberBaseHom sigma G).doctrineHom
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.hom) ≫
      eqToHom ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2 =
      eqToHom ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).2 ≫ 𝟙 Z
    rw [Functor.map_comp, eqToHom_map, packageProjection_map]
    rw [(transportAlong_whiskeredCompFiberIso G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).hom_base_eq]
    simp only [Category.comp_id]
    exact eqToHom_comp3
      (congrArg (packageProjection U).obj
        (coreFiberWhiskeredSourcePackageEq sigma tau upsilon G))
      (transportAlong_whiskeredComp_point G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
        (coreFiberBaseHom upsilon
          ((coreFiberTransportFunctor tau).obj
            ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).2
      ((coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)).2
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) upsilon
    (coreFiberLift upsilon
      ((coreFiberTransportFunctor (sigma ≫ tau)).obj G)) (𝟙 Z)
  rw [coreFiberCompositor_whiskered_g106_fac]
  rw [← Category.assoc, coreFiberWhiskeredSourceLift_cast_fac]
  rw [Category.assoc]
  change _ = (eqToHom (coreFiberDirectPackageEq sigma tau G) ≫
    ((transportAlongHom
      (transportAlong G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom))
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).comp
    (transportAlong_whiskeredCompFiberIso G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.hom))
  rw [transportAlong_whiskeredCompFiberIso_hom_fac]
  rfl

/-- The endpoint-casted G-106 whiskered comparison as a target-fiber morphism. -/
noncomputable def coreFiberG106WhiskeredCompositorHom {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G) ⟶
      (coreFiberTransportFunctor upsilon).obj
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G)) := by
  refine ⟨eqToHom
      (coreFiberWhiskeredSourcePackageEq sigma tau upsilon G) ≫
    (transportAlong_whiskeredCompFiberIso G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).iso.hom, ?_⟩
  rw [← coreFiberCompositor_whiskered_hom_eq]
  exact ((coreFiberTransportFunctor upsilon).map
    (coreFiberCompositorApp sigma tau G).hom).2

/-- The transported G-109 component is the casted G-106 whiskered component in the fiber. -/
theorem coreFiberCompositor_whiskered_eq_g106 {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    (coreFiberTransportFunctor upsilon).map
        (coreFiberCompositorApp sigma tau G).hom =
      coreFiberG106WhiskeredCompositorHom sigma tau upsilon G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact coreFiberCompositor_whiskered_hom_eq sigma tau upsilon G

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
