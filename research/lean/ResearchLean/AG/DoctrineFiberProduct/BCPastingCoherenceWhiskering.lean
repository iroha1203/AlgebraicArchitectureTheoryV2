import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridge

/-!
# First whiskering compatibility for the package-to-fiber bridge

This module advances the G-110(E) G-106/G-109 bridge from a binary component
to its first whiskering factorization.  Transporting the G-109 compositor
along a third pointed arrow factors as the explicitly casted G-106 binary
comparison followed by the next canonical lift.

This checkpoint does not yet identify the transported component with
`transportAlong_whiskeredCompFiberIso`: endpoint casts and the associator
comparison remain required before the three-arrow routes can be fixed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

set_option maxHeartbeats 2000000

/--
The first G-109 whiskering factorization exposes the corresponding casted
G-106 binary comparison as its actual first package factor.
-/
theorem coreFiberCompositor_whiskered_g106_fac {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (sigma : W ⟶ X) (tau : X ⟶ Y) (upsilon : Y ⟶ Z)
    (G : CoreFiber W) :
    coreFiberLift upsilon
        ((coreFiberTransportFunctor (sigma ≫ tau)).obj G) ≫
      ((coreFiberTransportFunctor upsilon).map
        (coreFiberCompositorApp sigma tau G).hom).1 =
    (eqToHom (coreFiberDirectPackageEq sigma tau G) ≫
      (transportAlong_compFiberIso G.1
        (coreFiberBaseHom sigma G).doctrineHom
        (coreFiberBaseHom tau
          ((coreFiberTransportFunctor sigma).obj G)).doctrineHom).iso.hom) ≫
      coreFiberLift upsilon
        ((coreFiberTransportFunctor tau).obj
          ((coreFiberTransportFunctor sigma).obj G)) := by
  rw [show ((coreFiberTransportFunctor upsilon).map
      (coreFiberCompositorApp sigma tau G).hom).1 =
      (coreFiberTransportMap upsilon
        (coreFiberCompositorApp sigma tau G).hom).1 from rfl]
  rw [coreFiberTransportMap_fac]
  rw [coreFiberCompositorApp_hom_eq_transportAlong_compFiberIso]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
