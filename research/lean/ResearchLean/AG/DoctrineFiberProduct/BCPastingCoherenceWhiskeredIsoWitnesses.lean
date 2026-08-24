import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceWhiskeredIso
import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridgeWitnesses

/-!
# Finite control for the direct whiskered-component bridge

The universal endpoint-cast theorem is instantiated on the reviewed finite
G-106 package and identity arrows.  This is an elaboration control, not a
nondegeneracy theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-- The direct whiskered-component bridge elaborates on the finite control. -/
theorem finiteCoreFiberWhiskeredCompositorG106_identity_control :
    (coreFiberTransportFunctor
      (𝟙 (packagePoint finiteWitnessTargetPackage))).map
        (coreFiberCompositorApp
          (𝟙 (packagePoint finiteWitnessTargetPackage))
          (𝟙 (packagePoint finiteWitnessTargetPackage))
          finitePackageCompositorBridgeObject).hom =
      coreFiberG106WhiskeredCompositorHom
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        finitePackageCompositorBridgeObject :=
  coreFiberCompositor_whiskered_eq_g106
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
