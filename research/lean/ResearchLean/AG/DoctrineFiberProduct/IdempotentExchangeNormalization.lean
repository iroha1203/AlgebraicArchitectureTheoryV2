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

/-- Heterogeneous extensionality for exact equation transports whose Atom and
object maps are propositionally equal. -/
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

/-- Composing the canonical equation transport with itself gives the same
transport.  This is the equation-field step of package idempotence. -/
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

/-- Successive casts along two type equalities are heterogeneously equal to
the first cast. -/
theorem cast_cast_heq_first
    {alpha beta gamma : Sort v} (first : alpha = beta) (second : beta = gamma)
    (value : alpha) :
    HEq (cast second (cast first value)) (cast first value) := by
  cases first
  cases second
  rfl

/-- The complete signed-reading normalization is idempotent. -/
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

/-- The canonical normalization is an idempotent endomorphism in the package
total category. -/
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
