import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalization

/-!
# Canonical object-normalization API

Lightweight evaluation and same-configuration lemmas for clients of canonical
object normalization.  This module depends only on the definition-owning
normalization module, so downstream target proofs need not unfold the
definition or import a higher G-116 proof layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-- Canonical normalization evaluates the package's selected object at the
input object's configuration. -/
theorem canonicalObjectNormalization_apply
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    canonicalObjectNormalization P object =
      P.reading.objectReading.object object.configuration :=
  rfl

/-- Objects with the same configuration have the same canonical
normalization. -/
theorem canonicalObjectNormalization_eq_of_configuration_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    {first second : ArchitectureObject U}
    (configuration_eq : first.configuration = second.configuration) :
    canonicalObjectNormalization P first =
      canonicalObjectNormalization P second := by
  rw [canonicalObjectNormalization_apply,
    canonicalObjectNormalization_apply, configuration_eq]

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
