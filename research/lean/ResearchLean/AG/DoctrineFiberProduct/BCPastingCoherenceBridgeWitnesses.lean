import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridge
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Finite control for the package-to-fiber coherence bridge

The universal bridge is instantiated on the reviewed finite G-106 target
package and its three identity base arrows.  This is a finite elaboration
control for the package/fiber casts; it does not restrict the universal theorem
to identity arrows and is not used as a nondegeneracy claim.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-- The reviewed finite G-106 target package as a core-fiber object. -/
noncomputable def finitePackageCompositorBridgeObject :
    CoreFiber (packagePoint finiteWitnessTargetPackage) :=
  ⟨finiteWitnessTargetPackage, rfl⟩

/-- The package-derived fiber compositor theorem fires on the finite control. -/
theorem finiteCoreFiberCompositorPackageBridge_identity_control :
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
  coreFiberCompositor_assoc_from_transportAlong_comp_coherence
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
