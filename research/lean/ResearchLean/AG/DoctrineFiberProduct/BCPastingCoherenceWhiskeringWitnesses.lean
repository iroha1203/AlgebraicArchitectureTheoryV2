import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceWhiskering
import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridgeWitnesses

/-!
# Finite control for the first whiskering compatibility

The universal three-arrow factorization is instantiated on the reviewed finite
G-106 package and identity arrows.  This checks the dependent endpoints only;
it is not a nondegeneracy result.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-- The first whiskering factorization elaborates on the finite control. -/
theorem finiteCoreFiberCompositorWhiskeredG106_identity_control :
    coreFiberLift (𝟙 (packagePoint finiteWitnessTargetPackage))
        ((coreFiberTransportFunctor
          ((𝟙 (packagePoint finiteWitnessTargetPackage)) ≫
            𝟙 (packagePoint finiteWitnessTargetPackage))).obj
          finitePackageCompositorBridgeObject) ≫
      ((coreFiberTransportFunctor
        (𝟙 (packagePoint finiteWitnessTargetPackage))).map
        (coreFiberCompositorApp
          (𝟙 (packagePoint finiteWitnessTargetPackage))
          (𝟙 (packagePoint finiteWitnessTargetPackage))
          finitePackageCompositorBridgeObject).hom).1 =
    (eqToHom (coreFiberDirectPackageEq
      (𝟙 (packagePoint finiteWitnessTargetPackage))
      (𝟙 (packagePoint finiteWitnessTargetPackage))
      finitePackageCompositorBridgeObject) ≫
      (transportAlong_compFiberIso finiteWitnessTargetPackage
        (coreFiberBaseHom
          (𝟙 (packagePoint finiteWitnessTargetPackage))
          finitePackageCompositorBridgeObject).doctrineHom
        (coreFiberBaseHom
          (𝟙 (packagePoint finiteWitnessTargetPackage))
          ((coreFiberTransportFunctor
            (𝟙 (packagePoint finiteWitnessTargetPackage))).obj
            finitePackageCompositorBridgeObject)).doctrineHom).iso.hom) ≫
      coreFiberLift (𝟙 (packagePoint finiteWitnessTargetPackage))
        ((coreFiberTransportFunctor
          (𝟙 (packagePoint finiteWitnessTargetPackage))).obj
          ((coreFiberTransportFunctor
            (𝟙 (packagePoint finiteWitnessTargetPackage))).obj
            finitePackageCompositorBridgeObject)) :=
  coreFiberCompositor_whiskered_g106_fac
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
