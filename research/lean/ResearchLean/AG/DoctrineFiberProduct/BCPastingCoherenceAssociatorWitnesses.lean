import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceAssociator
import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridgeWitnesses

/-!
# Finite control for the direct associator bridge

The universal associator comparison is instantiated on the reviewed finite
G-106 package and identity arrows.  This checks elaboration only and is not a
nondegeneracy theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-- The direct associator bridge elaborates on the finite identity control. -/
theorem finiteCoreFiberAssociatorG106_identity_control :
    coreFiberAssociatorCast
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        finitePackageCompositorBridgeObject =
      coreFiberG106AssociatorHom
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        finitePackageCompositorBridgeObject :=
  coreFiberAssociatorCast_eq_g106
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
