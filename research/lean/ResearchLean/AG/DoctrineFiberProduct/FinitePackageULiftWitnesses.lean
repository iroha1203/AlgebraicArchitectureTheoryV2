import ResearchLean.AG.DoctrineFiberProduct.FinitePackageULift

/-!
# Concrete witnesses for finite-package universe lifting

This module specializes the canonical finite-package universe-lift API to the
reviewed `FiniteModel.corePackage`.  The witnesses retain positive and negative
family information, a nontrivial identification, configuration round trips,
and the visible Atom-map graph of the existing collapse homomorphism.

No predicate, certificate, package, or homomorphism is accepted as input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-! ## Lifted family and configuration content -/

/-- The canonically lifted finite core family still contains `componentA`. -/
theorem finiteModelLiftCorePackage_componentA_mem :
    (finiteModelLiftAtomFamily.{u} FiniteModel.corePackage.family).mem
      (ULift.up FiniteModel.FiniteAtom.componentA) := by
  simpa [finiteModelLiftAtomFamily] using
    FiniteModel.corePackage_componentA_mem

/-- The canonically lifted finite core family still excludes `componentC`. -/
theorem finiteModelLiftCorePackage_componentC_not_mem :
    ¬ (finiteModelLiftAtomFamily.{u} FiniteModel.corePackage.family).mem
      (ULift.up FiniteModel.FiniteAtom.componentC) := by
  simpa [finiteModelLiftAtomFamily] using
    FiniteModel.corePackage_componentC_not_mem

/-- The concrete `componentA`-`componentB` identification survives universe lifting. -/
theorem finiteModelLiftCorePackage_componentA_identified_componentB :
    (finiteModelLiftAtomConfiguration.{u}
        FiniteModel.corePackage.object.configuration).identification
      (ULift.up FiniteModel.FiniteAtom.componentA)
      (ULift.up FiniteModel.FiniteAtom.componentB) := by
  simpa [finiteModelLiftAtomConfiguration] using
    FiniteModel.corePackage_componentA_identified_componentB

/-- Reflecting the lifted concrete core configuration recovers it exactly. -/
theorem finiteModelCorePackage_configuration_lift_reflect :
    finiteModelReflectAtomConfiguration.{u}
        (finiteModelLiftAtomConfiguration.{u}
          FiniteModel.corePackage.object.configuration) =
      FiniteModel.corePackage.object.configuration :=
  finiteModelReflectAtomConfiguration_lift.{u} _

/-! ## Concrete collapse homomorphism -/

/-- Canonical universe lift of the reviewed nonidentity collapse homomorphism. -/
def finiteModelLiftCollapseConfigurationHom :
    ConfigurationHom
      (finiteModelLiftAtomConfiguration.{u}
        FiniteModel.corePackage.object.configuration)
      (finiteModelLiftAtomConfiguration.{u}
        (FiniteModel.mappedConfiguration
          FiniteModel.corePackage.object.configuration)) :=
  finiteModelLiftConfigurationHom.{u}
    (FiniteModel.collapseConfigurationHom
      FiniteModel.corePackage.object.configuration)

/-- The lifted collapse Atom map is the same visible constant map to `componentB`. -/
theorem finiteModelLiftCollapseConfigurationHom_atomMap_graph
    (atom : finiteModelLiftCarrier.{u}.Atom) :
    finiteModelLiftCollapseConfigurationHom.{u}.atomMap atom =
      ULift.up FiniteModel.FiniteAtom.componentB := by
  rcases atom with ⟨atom⟩
  rfl

/-- Reflecting the lifted concrete collapse homomorphism recovers the base homomorphism. -/
theorem finiteModelLiftCollapseConfigurationHom_roundtrip :
    castConfigurationHom
        (finiteModelReflectAtomConfiguration_lift.{u}
          FiniteModel.corePackage.object.configuration)
        (finiteModelReflectAtomConfiguration_lift.{u}
          (FiniteModel.mappedConfiguration
            FiniteModel.corePackage.object.configuration))
        (finiteModelReflectConfigurationHom.{u}
          finiteModelLiftCollapseConfigurationHom.{u}) =
      FiniteModel.collapseConfigurationHom
        FiniteModel.corePackage.object.configuration :=
  finiteModelReflectConfigurationHom_lift.{u} _

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
