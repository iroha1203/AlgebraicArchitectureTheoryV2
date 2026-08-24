import ResearchLean.AG.DoctrineFiberProduct.BCPastingClosure
import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor
import ResearchLean.AG.TransportCoherence.CanonicalCoherence

/-!
# Package-to-fiber compositor coherence bridge

This module constructs the G-106/G-109 bridge required by G-110(E).  The two
G-109 three-arrow compositor routes are forgotten to package morphisms and
precomposed with the same canonical composite lift.  Their resulting package
paths are identified with the two sides of G-106
`transportAlong_comp_coherence`.  The final fiber equality is then derived by
strongly cocartesian uniqueness while consuming that G-106 equality in the
proof term.

The theorem does not obtain the result by pairing two already independent
coherence statements.  The left and right factorization lemmas below are the
explicit compatibility maps between package-level and fiber-level paths.
Comparison and diagnostic compatibility with a pasted BC square remain later
K4 obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

set_option maxHeartbeats 2000000

/-- A core-fiber canonical lift is definitionally the underlying G-106 package lift. -/
theorem coreFiberLift_as_transportAlongHom {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (sigma : X ⟶ Y) (G : CoreFiber X) :
    coreFiberLift sigma G =
      transportAlongHom G.1 (coreFiberBaseHom sigma G).doctrineHom := rfl

/--
The G-106 three-step package lift obtained from the three pointed base arrows
used by G-109 core-fiber transport.
-/
noncomputable def coreFiberPackageTripleHom {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :=
  transportAlongTripleHom G.1
    (coreFiberBaseHom sigma G).doctrineHom
    (coreFiberBaseHom tau
      ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
    (coreFiberBaseHom upsilon
      ((coreFiberTransportFunctor tau).obj
        ((coreFiberTransportFunctor sigma).obj G))).doctrineHom

/-- The G-109 fully iterated lift is the right-associated G-106 package lift. -/
theorem coreFiberTripleIteratedLift_eq_package {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberTripleIteratedLift sigma tau upsilon G =
      coreFiberPackageTripleHom sigma tau upsilon G := by
  simp only [coreFiberTripleIteratedLift, coreFiberIteratedLift,
    coreFiberPackageTripleHom, transportAlongTripleHom,
    transportAlongCompHom, coreFiberLift_as_transportAlongHom,
    coreFiberTransportFunctor, coreFiberTransportObj,
    coreFiberTransportObject]
  exact (Category.assoc _ _ _).symm

/--
The left G-109 compositor route, after the canonical lift, is the right-side
G-106 adjacent-comparison path.
-/
theorem coreFiberPentagonLeftRoute_package_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
        (coreFiberPentagonLeftRoute sigma tau upsilon G).1 =
      (transportAlongHom G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          ((coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom))).comp
        (transportAlongAdjacentCompHom G.1
          (coreFiberBaseHom sigma G).doctrineHom
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom) := by
  rw [coreFiberPentagonLeftRoute_fac]
  rw [coreFiberTripleIteratedLift_eq_package]
  exact (transportAlongAdjacentCompHom_fac G.1
    (coreFiberBaseHom sigma G).doctrineHom
    (coreFiberBaseHom tau
      ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
    (coreFiberBaseHom upsilon
      ((coreFiberTransportFunctor tau).obj
        ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).symm

/--
The right G-109 compositor route, after the same canonical lift, is the
left-aligned G-106 comparison path.
-/
theorem coreFiberPentagonRightRoute_package_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
        (coreFiberPentagonRightRoute sigma tau upsilon G).1 =
      (transportAlongHom G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          ((coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom))).comp
        (transportAlongLeftAlignedCompHom G.1
          (coreFiberBaseHom sigma G).doctrineHom
          (coreFiberBaseHom tau
            ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
          (coreFiberBaseHom upsilon
            ((coreFiberTransportFunctor tau).obj
              ((coreFiberTransportFunctor sigma).obj G))).doctrineHom) := by
  rw [coreFiberPentagonRightRoute_fac]
  rw [coreFiberTripleIteratedLift_eq_package]
  exact (transportAlongLeftAlignedCompHom_fac G.1
    (coreFiberBaseHom sigma G).doctrineHom
    (coreFiberBaseHom tau
      ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
    (coreFiberBaseHom upsilon
      ((coreFiberTransportFunctor tau).obj
        ((coreFiberTransportFunctor sigma).obj G))).doctrineHom).symm

/--
The G-109 fiber compositor associativity equation derived through the explicit
G-106 package bridge.  The proof term consumes
`transportAlong_comp_coherence` between the two package factorizations before
applying strong-lift uniqueness in the target fiber.
-/
theorem coreFiberCompositor_assoc_from_transportAlong_comp_coherence
    {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberPentagonLeftRoute sigma tau upsilon G =
      coreFiberPentagonRightRoute sigma tau upsilon G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      ((sigma ≫ tau) ≫ upsilon)
      (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) :=
    coreFiberLift_isStronglyCocartesian ((sigma ≫ tau) ≫ upsilon) G
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) ((sigma ≫ tau) ≫ upsilon)
    (coreFiberLift ((sigma ≫ tau) ≫ upsilon) G) (𝟙 Z)
  change coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
      (coreFiberPentagonLeftRoute sigma tau upsilon G).1 =
    coreFiberLift ((sigma ≫ tau) ≫ upsilon) G ≫
      (coreFiberPentagonRightRoute sigma tau upsilon G).1
  rw [coreFiberPentagonLeftRoute_package_fac,
    coreFiberPentagonRightRoute_package_fac]
  exact congrArg
    (fun comparison =>
      (transportAlongHom G.1
        ((coreFiberBaseHom sigma G).doctrineHom.comp
          ((coreFiberBaseHom tau
              ((coreFiberTransportFunctor sigma).obj G)).doctrineHom.comp
            (coreFiberBaseHom upsilon
              ((coreFiberTransportFunctor tau).obj
                ((coreFiberTransportFunctor sigma).obj G))).doctrineHom))).comp
        comparison)
    (transportAlong_comp_coherence G.1
      (coreFiberBaseHom sigma G).doctrineHom
      (coreFiberBaseHom tau
        ((coreFiberTransportFunctor sigma).obj G)).doctrineHom
      (coreFiberBaseHom upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G))).doctrineHom)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
