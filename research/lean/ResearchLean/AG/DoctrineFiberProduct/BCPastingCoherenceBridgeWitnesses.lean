import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceBridge
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Finite control for the package-to-fiber coherence bridge

The universal binary component bridge is instantiated on the reviewed finite
G-106 target package and two identity base arrows.  This is a finite elaboration
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

/-- The component-level binary bridge fires on the finite control. -/
theorem finiteCoreFiberBinaryCompositorBridge_identity_control :
    (coreFiberCompositorApp
      (𝟙 (packagePoint finiteWitnessTargetPackage))
      (𝟙 (packagePoint finiteWitnessTargetPackage))
      finitePackageCompositorBridgeObject).hom =
    coreFiberG106CompositorHom
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject :=
  coreFiberCompositorApp_hom_eq_g106
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    (𝟙 (packagePoint finiteWitnessTargetPackage))
    finitePackageCompositorBridgeObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
