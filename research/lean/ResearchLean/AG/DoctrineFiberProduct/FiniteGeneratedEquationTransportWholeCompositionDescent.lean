import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableCompositionDescent

/-!
# Whole generated equation-transport composition descent

This module assembles the complete equation-system component of the reflected
generated upper triangle.  The Atom map, complete object map, context
equivalence, equation-index equivalence, and dependent observable family are
all obtained from the actual normalized high factorization before the
proposition-valued laws are removed by proof irrelevance.

No known low factorization, canonical-factor equality, caller comparison, or
ambient cartesianness proof is used.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/--
Exact equation transports with the same computational context, index, and
observable fields are equal.  Their remaining fields are propositions.
-/
private theorem equationSystemExactTransport_ext
    {U : AtomCarrier.{u}}
    {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {first second :
      EquationSystemExactTransport E F atomEquiv objectMap}
    (hContext : first.contextEquivalence = second.contextEquivalence)
    (hEquation : first.equationEquiv = second.equationEquiv)
    (hObservable : HEq first.observableEquiv second.observableEquiv) :
    first = second := by
  cases first
  cases second
  cases hContext
  cases hEquation
  cases hObservable
  rfl

/--
Aligning the Atom and object indices reduces heterogeneous equality of exact
equation transports to equality of their three computational fields.
-/
private theorem equationSystemExactTransport_heq
    {U : AtomCarrier.{u}}
    {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {firstAtom secondAtom : U.Atom ≃ U.Atom}
    {firstObject secondObject :
      ArchitectureObject U → ArchitectureObject U}
    {first :
      EquationSystemExactTransport E F firstAtom firstObject}
    {second :
      EquationSystemExactTransport E F secondAtom secondObject}
    (hAtom : firstAtom = secondAtom)
    (hObject : firstObject = secondObject)
    (hContext : first.contextEquivalence = second.contextEquivalence)
    (hEquation : first.equationEquiv = second.equationEquiv)
    (hObservable : HEq first.observableEquiv second.observableEquiv) :
    HEq first second := by
  cases hAtom
  cases hObject
  exact heq_of_eq
    (equationSystemExactTransport_ext hContext hEquation hObservable)

/--
The complete equation transport of the reflected generated upper followed by
the inner generated upper is heterogeneously equal to the outer generated
equation transport.  Every computational field is supplied by the
actual-high-derived composition descents.
-/
theorem finiteGeneratedReflectedUpper_comp_equationTransport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    HEq
      (((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper).equationTransport)
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.equationTransport) := by
  exact equationSystemExactTransport_heq
    (finiteGeneratedReflectedUpper_comp_atomEquiv input lift base)
    (finiteGeneratedReflectedUpper_comp_objectMap input lift base)
    (finiteGeneratedReflectedUpper_comp_contextEquivalence input lift base)
    (finiteGeneratedReflectedUpper_comp_equationEquiv input lift base)
    (finiteGeneratedReflectedUpper_comp_observableEquiv input lift base)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
