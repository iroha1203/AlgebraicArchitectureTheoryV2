import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticBaseChangeAutomorphism
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFoldWitnesses

/-!
# Finite witness for the diagnostic endpoint action

The identity core-fiber functor on the finite axis-fold support sends the
concrete adjacent swap to itself.  Its endpoint action therefore separates
that swap from the identity automorphism.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The finite lax support as an object of its own core fiber. -/
noncomputable def finiteAxisFoldSupportFiberObject :
    CoreFiber (packagePoint finiteAxisFoldSupportPackage) :=
  ⟨finiteAxisFoldSupportPackage, rfl⟩

/-- The identity action on the finite lax support fiber. -/
noncomputable def finiteAxisFoldIdentityCoreFiberFunctor :
    CoreFiber (packagePoint finiteAxisFoldSupportPackage) ⥤
      CoreFiber (packagePoint finiteAxisFoldSupportPackage) :=
  𝟭 _

/-- The identity core-fiber action sends the concrete adjacent swap to itself. -/
theorem finiteAxisFold_identityEndpointAction_swap :
    coreFiberFunctorPackageAutHom
        finiteAxisFoldIdentityCoreFiberFunctor
        finiteAxisFoldSupportFiberObject finiteAxisFoldSwap =
      finiteAxisFoldSwap := by
  rfl

/-- The concrete d2 endpoint action is nonconstant. -/
theorem finiteAxisFold_identityEndpointAction_nonconstant :
    coreFiberFunctorPackageAutHom
        finiteAxisFoldIdentityCoreFiberFunctor
        finiteAxisFoldSupportFiberObject finiteAxisFoldSwap ≠
      coreFiberFunctorPackageAutHom
        finiteAxisFoldIdentityCoreFiberFunctor
        finiteAxisFoldSupportFiberObject 1 := by
  rw [finiteAxisFold_identityEndpointAction_swap,
    coreFiberFunctorPackageAutHom_one]
  exact finiteAxisFoldSwap_ne_one

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
