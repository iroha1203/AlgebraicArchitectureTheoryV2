import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceRoutes
import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridgeWitnesses

/-!
# Finite control for the G-106/G-109 route bridge

The universal route bridge is instantiated on the reviewed finite G-106
package and identity arrows.  This is an elaboration control and does not
assert nondegeneracy.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-- The route bridge and G-106-derived compositor equality elaborate finitely. -/
theorem finiteCoreFiberCompositorAssocViaG106_identity_control :
    coreFiberPentagonLeftRoute
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        finitePackageCompositorBridgeObject =
      coreFiberPentagonRightRoute
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        (𝟙 (packagePoint finiteWitnessTargetPackage))
        finitePackageCompositorBridgeObject :=
  coreFiberCompositor_assoc_via_g106
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
