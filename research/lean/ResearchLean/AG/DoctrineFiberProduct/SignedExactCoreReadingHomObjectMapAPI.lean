import Formal.AG.ReadingFunctoriality.Core
import Formal.Util.AssertStandardAxioms

/-!
# Exact-reading object-map API

Lightweight evaluation lemmas for identity and composition keep downstream
ResearchLean proofs independent of the structure constructors' definitions.
-/

namespace AAT.AG

universe u

/-- The object map of a composite exact reading hom is function
composition. -/
theorem signedExactCoreReadingHom_comp_objectMap_apply
    {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    (first : SignedExactCoreReadingHom P Q)
    (second : SignedExactCoreReadingHom Q R)
    (object : ArchitectureObject U) :
    (first.comp second).objectMap object =
      second.objectMap (first.objectMap object) :=
  rfl

/-- The identity exact reading hom has the identity object map. -/
theorem signedExactCoreReadingHom_refl_objectMap_apply
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    (SignedExactCoreReadingHom.refl P).objectMap object = object :=
  rfl

#assert_standard_axioms_only AAT.AG

end AAT.AG
