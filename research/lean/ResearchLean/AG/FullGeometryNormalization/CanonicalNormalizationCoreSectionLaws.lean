import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationCoreSection
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization

/-!
# Functorial laws for the exact-core normalization section

The identity of a normalization Karoubi object is its idempotent, not the raw
identity.  This module proves that the Cycle 16 constructor sends that
normalization endomorphism to the raw identity and preserves composition.
The operation proof keeps the actual dependent casts visible: target
denormalization from the first lift cancels source normalization in the second
lift, while the remaining endpoint change is an equality of architecture
objects.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open AtomFoundation DoctrineFiberProduct

private theorem cast_symm_cancel_laws
    {alpha beta : Sort u} (h : alpha = beta) (x : beta) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

private theorem castOperation_heq
    {U : AtomCarrier.{u}} (R : OperationReading U)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B') (operation : R.Op A B) :
    HEq (castOperation R hA hB operation) operation := by
  cases hA
  cases hB
  rfl

private theorem operationMap_castOperation_heq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (g : SignedExactCoreReadingHom P P)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B')
    (operation : P.reading.operationReading.Op A B) :
    HEq (g.operationMap
      (castOperation P.reading.operationReading hA hB operation))
      (g.operationMap operation) := by
  cases hA
  cases hB
  rfl

/-- The Cycle 16 operation map is the input operation map applied after source
normalization, up to the actual endpoint and target-denormalization casts. -/
theorem canonicalNormalizationSectionOperationMap_heq_normalized
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P)
    {A B : ArchitectureObject U}
    (operation : P.reading.operationReading.Op A B) :
    HEq (canonicalNormalizationSectionOperationMap P admissible f operation)
      (f.operationMap (cast (admissible.operation_type_eq A B) operation)) := by
  unfold canonicalNormalizationSectionOperationMap
  exact (cast_heq _ _).trans (castOperation_heq _ _ _ _)

/-- Canonical normalization composed three times is canonical normalization. -/
theorem canonicalObjectNormalizationUpper_triple
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    ((canonicalObjectNormalizationUpper P admissible).comp
        (canonicalObjectNormalizationUpper P admissible)).comp
          (canonicalObjectNormalizationUpper P admissible) =
      canonicalObjectNormalizationUpper P admissible := by
  rw [canonicalObjectNormalizationUpper_comp,
    canonicalObjectNormalizationUpper_comp]

/-- The exact-core section sends the Karoubi identity (the normalization
idempotent) to the raw identity exact endomorphism. -/
theorem canonicalNormalizationSectionUpper_normalization
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    canonicalNormalizationSectionUpper P admissible
        (canonicalObjectNormalizationUpper P admissible) =
      SignedExactCoreReadingHom.refl P := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · exact canonicalNormalizationSectionObjectMap_refl P
  · apply equationSystemExactTransport_hext
    · rfl
    · exact canonicalNormalizationSectionObjectMap_refl P
    · rfl
    · rfl
    · rfl
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro operation operation' hoperation
    cases hoperation
    have hsection := canonicalNormalizationSectionOperationMap_heq_normalized
      P admissible (canonicalObjectNormalizationUpper P admissible) operation
    exact hsection.trans ((cast_heq _ _).trans (cast_heq _ _))
  · rfl
  · rfl
  · rfl

/-- The exact-core section preserves composition of endomorphisms. -/
theorem canonicalNormalizationSectionUpper_comp
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f g : SignedExactCoreReadingHom P P) :
    canonicalNormalizationSectionUpper P admissible (f.comp g) =
      (canonicalNormalizationSectionUpper P admissible f).comp
        (canonicalNormalizationSectionUpper P admissible g) := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · exact (canonicalNormalizationSectionObjectMap_trans
      P f.atomEquiv g.atomEquiv).symm
  · apply equationSystemExactTransport_hext
    · rfl
    · exact (canonicalNormalizationSectionObjectMap_trans
        P f.atomEquiv g.atomEquiv).symm
    · rfl
    · rfl
    · rfl
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro operation operation' hoperation
    cases hoperation
    have hleft := canonicalNormalizationSectionOperationMap_heq_normalized
      P admissible (f.comp g) operation
    have hsecond := canonicalNormalizationSectionOperationMap_heq_normalized
      P admissible g
        (canonicalNormalizationSectionOperationMap P admissible f operation)
    have hcancel :
        cast (admissible.operation_type_eq
            (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
            (canonicalNormalizationSectionObjectMap P f.atomEquiv B))
          (canonicalNormalizationSectionOperationMap P admissible f operation) =
        castOperation P.reading.operationReading
          (exactEndomorphism_map_normalization_eq_section_normalization P f A)
          (exactEndomorphism_map_normalization_eq_section_normalization P f B)
          (f.operationMap
            (cast (admissible.operation_type_eq A B) operation)) := by
      exact cast_symm_cancel_laws _ _
    rw [hcancel] at hsecond
    have hmiddle := operationMap_castOperation_heq g
      (exactEndomorphism_map_normalization_eq_section_normalization P f A)
      (exactEndomorphism_map_normalization_eq_section_normalization P f B)
      (f.operationMap (cast (admissible.operation_type_eq A B) operation))
    exact hleft.trans (hsecond.trans hmiddle).symm
  · rfl
  · rfl
  · rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
