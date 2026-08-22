import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperAssembly

/-!
# Generated upper composition: first computational fields

This module reads the upper equality of the actual normalized high-factor
triangle and descends its Atom and architecture-object components to the
generated finite-model domains.  The high equation-transport component is
also retained as a dependent equality obtained from that same triangle.

No low factor, canonical-factor equality, caller comparison, or cartesian
certificate is accepted here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/--
The upper component of the actual normalized high-factor triangle.  This is
the proof source for the component descents below, rather than a reconstructed
low factorization equality.
-/
theorem finiteGeneratedNormalizedHighFactor_upper_fac
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedNormalizedHighFactor input lift base).upper.comp
        input.highGeneratedLift.hom.upper =
      (finiteGeneratedOuterInput input base).highGeneratedLift.hom.upper :=
  congrArg PackageTotalHom.upper
    (finiteGeneratedNormalizedHighFactor_fac input lift base)

/--
The reflected actual-high upper followed by the generated low upper has the
same primitive Atom equivalence as the outer generated upper.
-/
theorem finiteGeneratedReflectedUpper_comp_atomEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper).atomEquiv =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.atomEquiv := by
  apply Equiv.ext
  intro atom
  apply finiteModelLiftCarrierEquiv.{u}.atom.injective
  let outer := finiteGeneratedOuterInput input base
  have hHigh :
      input.highPackageHomFromLowData.upper.atomEquiv
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
            (finiteModelLiftCarrierEquiv.{u}.atom atom)) =
        outer.highPackageHomFromLowData.upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
    have h := congrArg
      (fun upper => upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom))
      (finiteGeneratedNormalizedHighFactor_upper_fac input lift base)
    change
      input.highPackageHomFromLowData.upper.atomEquiv
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
            (finiteModelLiftCarrierEquiv.{u}.atom atom)) =
        outer.highPackageHomFromLowData.upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) at h
    exact h
  change
    finiteModelLiftCarrierEquiv.{u}.atom
        (input.lowGeneratedLift.hom.upper.atomEquiv
          (finiteGeneratedReflectedUpperAtomEquiv input lift base atom)) =
      finiteModelLiftCarrierEquiv.{u}.atom
        (outer.lowGeneratedLift.hom.upper.atomEquiv atom)
  calc
    _ = input.highPackageHomFromLowData.upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom
            (finiteGeneratedReflectedUpperAtomEquiv input lift base atom)) := by
      rw [input.lowGeneratedLift_upper_atomEquiv]
      exact (input.highPackageHomFromLowData_upper_atom_graph _).symm
    _ = input.highPackageHomFromLowData.upper.atomEquiv
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
            (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
      rw [finiteGeneratedReflectedUpperAtomEquiv_high_graph]
    _ = outer.highPackageHomFromLowData.upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) := hHigh
    _ = finiteModelLiftCarrierEquiv.{u}.atom
          (outer.hom.doctrineHom.atomEquiv atom) :=
      outer.highPackageHomFromLowData_upper_atom_graph atom
    _ = finiteModelLiftCarrierEquiv.{u}.atom
          (outer.lowGeneratedLift.hom.upper.atomEquiv atom) := by
      rw [outer.lowGeneratedLift_upper_atomEquiv]

/--
The first Atom equality, expressed only through the reflected Atom producer
and the two generated low arrows.  This form is used by object transport.
-/
theorem finiteGeneratedReflectedUpper_comp_atomEquiv_explicit
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedReflectedUpperAtomEquiv input lift base).trans
        input.hom.doctrineHom.atomEquiv =
      (finiteGeneratedOuterInput input base).hom.doctrineHom.atomEquiv := by
  simpa [SignedExactCoreReadingHom.comp,
    input.lowGeneratedLift_upper_atomEquiv,
    (finiteGeneratedOuterInput input base).lowGeneratedLift_upper_atomEquiv] using
      finiteGeneratedReflectedUpper_comp_atomEquiv input lift base

/--
The reflected actual-high object map followed by the generated low object map
equals the outer generated object map on every architecture object.
-/
theorem finiteGeneratedReflectedUpper_comp_objectMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper).objectMap =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.objectMap := by
  funext object
  let outer := finiteGeneratedOuterInput input base
  change
    input.lowGeneratedLift.hom.upper.objectMap
        (finiteGeneratedReflectedArchitectureObject input lift base object) =
      outer.lowGeneratedLift.hom.upper.objectMap object
  rw [finiteGeneratedReflectedArchitectureObject_transport]
  rw [input.lowGeneratedLift_upper_objectMap,
    outer.lowGeneratedLift_upper_objectMap]
  rw [← transportArchitectureObject_trans]
  rw [finiteGeneratedReflectedUpper_comp_atomEquiv_explicit input lift base]

private theorem equationTransport_heq_of_eq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {f g : SignedExactCoreReadingHom P Q} (h : f = g) :
    HEq f.equationTransport g.equationTransport := by
  cases h
  rfl

/--
The equation-transport projection of the actual high upper triangle.  Because
the field type depends on both `atomEquiv` and `objectMap`, the projection is
recorded as `HEq` after eliminating the actual upper equality.
-/
theorem finiteGeneratedNormalizedHighFactor_upper_fac_equationTransport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    HEq
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.comp
        input.highGeneratedLift.hom.upper).equationTransport
      (finiteGeneratedOuterInput input base).highGeneratedLift.hom.upper.equationTransport := by
  exact equationTransport_heq_of_eq
    (finiteGeneratedNormalizedHighFactor_upper_fac input lift base)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
