import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalization

/-!
# Idempotent exchange normalization

The canonical object normalization is already idempotent on architecture
objects.  This module lifts that equality through the complete equation
transport and signed-reading data to the package total category.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation

/-- API support for G-116(b): heterogeneous extensionality for exact equation
transports whose Atom and object maps are propositionally equal.  Its equality
arguments compare the computational data needed by
`canonicalObjectNormalizationTotal_comp`; they are not material premises of
the G-116 theorem. -/
theorem equationSystemExactTransport_hext
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {firstAtom secondAtom : U.Atom ≃ U.Atom}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    {T : EquationSystemExactTransport E F firstAtom firstObject}
    {S : EquationSystemExactTransport E F secondAtom secondObject}
    (hatom : firstAtom = secondAtom)
    (hobject : firstObject = secondObject)
    (hcontext : T.contextEquivalence = S.contextEquivalence)
    (hequation : T.equationEquiv = S.equationEquiv)
    (hobservable : HEq T.observableEquiv S.observableEquiv) :
    HEq T S := by
  cases hatom
  cases hobject
  cases T
  cases S
  cases hcontext
  cases hequation
  cases hobservable
  rfl

/-- Equation-field API support for G-116(b): composing the canonical equation
transport with itself gives the same transport.  The package `P` is the GOAL
input and `admissible` is its declared direction-hypothesis; object-map
idempotence is supplied by `canonicalObjectNormalization_idempotent`. -/
theorem canonicalObjectNormalizationEquationTransport_comp_heq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    HEq
      ((canonicalObjectNormalizationEquationTransport P admissible).comp
        (canonicalObjectNormalizationEquationTransport P admissible))
      (canonicalObjectNormalizationEquationTransport P admissible) := by
  apply equationSystemExactTransport_hext
  · apply Equiv.ext
    intro atom
    rfl
  · funext object
    exact canonicalObjectNormalization_idempotent P object
  · rfl
  · rfl
  · rfl

/-- Operation-field API support for G-116(b): successive casts along two type
equalities are heterogeneously equal to the first cast.  The equality arguments
are the generic transport data used by `canonicalObjectNormalizationUpper_comp`,
not material premises of the package theorem. -/
theorem cast_cast_heq_first
    {alpha beta gamma : Sort v} (first : alpha = beta) (second : beta = gamma)
    (value : alpha) :
    HEq (cast second (cast first value)) (cast first value) := by
  cases first
  cases second
  rfl

/-- Upper-field API support for G-116(b): the complete signed-reading
normalization is idempotent.  The package `P` is the GOAL input and
`admissible` is its declared direction-hypothesis; no idempotence certificate
is accepted. -/
theorem canonicalObjectNormalizationUpper_comp
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (canonicalObjectNormalizationUpper P admissible).comp
        (canonicalObjectNormalizationUpper P admissible) =
      canonicalObjectNormalizationUpper P admissible := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    rfl
  · funext object
    exact canonicalObjectNormalization_idempotent P object
  · exact canonicalObjectNormalizationEquationTransport_comp_heq P admissible
  · apply Function.hfunext rfl
    intro first first' hfirst
    cases hfirst
    apply Function.hfunext rfl
    intro second second' hsecond
    cases hsecond
    apply Function.hfunext rfl
    intro operation operation' hoperation
    cases hoperation
    exact cast_cast_heq_first
      (admissible.operation_type_eq first second)
      (admissible.operation_type_eq
        (canonicalObjectNormalization P first)
        (canonicalObjectNormalization P second)) operation
  · rfl
  · rfl
  · rfl

/-- Main theorem for G-116(b): the canonical normalization is an idempotent
endomorphism in the package total category.  The package `P` is the GOAL input
and `admissible` is its declared direction-hypothesis; the conclusion is
constructed through the complete lower and upper morphism data. -/
theorem canonicalObjectNormalizationTotal_comp
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (canonicalObjectNormalizationTotal P admissible).comp
        (canonicalObjectNormalizationTotal P admissible) =
      canonicalObjectNormalizationTotal P admissible := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · exact canonicalObjectNormalizationUpper_comp P admissible

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
