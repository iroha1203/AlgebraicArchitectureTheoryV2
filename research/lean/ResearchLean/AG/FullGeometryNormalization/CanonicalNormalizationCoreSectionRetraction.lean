import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationCoreSectionLaws

/-!
# Retraction law for the exact-core normalization section

The raw exact-core section becomes a genuine section after restricting both
source and target by canonical normalization.  The first theorem proves the
computational sandwich equality without assuming that the input endomorphism
is fixed.  The second theorem then uses exactly the Karoubi fixed-morphism
condition to recover the input morphism.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open AtomFoundation DoctrineFiberProduct

private theorem castOperation_heq_retraction
    {U : AtomCarrier.{u}} (R : OperationReading U)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B') (operation : R.Op A B) :
    HEq (castOperation R hA hB operation) operation := by
  cases hA
  cases hB
  rfl

private theorem operationMap_castOperation_heq_retraction
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (f : SignedExactCoreReadingHom P P)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B')
    (operation : P.reading.operationReading.Op A B) :
    HEq (f.operationMap
      (castOperation P.reading.operationReading hA hB operation))
      (f.operationMap operation) := by
  cases hA
  cases hB
  rfl

private theorem normalized_section_object_eq_normalized_map
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (f : SignedExactCoreReadingHom P P) (A : ArchitectureObject U) :
    canonicalObjectNormalization P
        (canonicalNormalizationSectionObjectMap P f.atomEquiv
          (canonicalObjectNormalization P A)) =
      canonicalObjectNormalization P
        (f.objectMap (canonicalObjectNormalization P A)) := by
  rw [← exactEndomorphism_map_normalization_eq_section_normalization
    P f (canonicalObjectNormalization P A)]
  rw [canonicalObjectNormalization_idempotent]
  rw [exactEndomorphism_map_normalization_eq_section_normalization P f A]
  rw [canonicalObjectNormalization_idempotent]

/-- Restricting the raw section at both endpoints gives the same exact-core
morphism as restricting its input at both endpoints. -/
theorem canonicalNormalizationSectionUpper_sandwich
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    ((canonicalObjectNormalizationUpper P admissible).comp
        (canonicalNormalizationSectionUpper P admissible f)).comp
          (canonicalObjectNormalizationUpper P admissible) =
      ((canonicalObjectNormalizationUpper P admissible).comp f).comp
        (canonicalObjectNormalizationUpper P admissible) := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · funext A
    exact normalized_section_object_eq_normalized_map P f A
  · apply equationSystemExactTransport_hext
    · rfl
    · funext A
      exact normalized_section_object_eq_normalized_map P f A
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
      P admissible f
        (cast (admissible.operation_type_eq A B) operation)
    let normalizedOperation :=
      cast (admissible.operation_type_eq A B) operation
    have hAidem := canonicalObjectNormalization_idempotent P A
    have hBidem := canonicalObjectNormalization_idempotent P B
    have hcast :
        cast (admissible.operation_type_eq
            (canonicalObjectNormalization P A)
            (canonicalObjectNormalization P B)) normalizedOperation =
          castOperation P.reading.operationReading
            hAidem.symm hBidem.symm normalizedOperation := by
      exact eq_of_heq ((cast_heq _ _).trans
        (castOperation_heq_retraction _ _ _ _).symm)
    have hsource : HEq
        (f.operationMap
          (cast (admissible.operation_type_eq
              (canonicalObjectNormalization P A)
              (canonicalObjectNormalization P B)) normalizedOperation))
        (f.operationMap normalizedOperation) := by
      rw [hcast]
      exact operationMap_castOperation_heq_retraction f
        hAidem.symm hBidem.symm normalizedOperation
    have hmiddle : HEq
        ((canonicalNormalizationSectionUpper P admissible f).operationMap
          (cast (admissible.operation_type_eq A B) operation))
        (f.operationMap (cast (admissible.operation_type_eq A B) operation)) :=
      hsection.trans hsource
    exact
      (cast_heq _ _).trans
        (hmiddle.trans (cast_heq _ _).symm)
  · rfl
  · rfl
  · rfl

/-- The raw exact-core section is a section of normalization restriction on
the Karoubi-fixed endomorphisms.  The only premise is the defining fixed-point
equation for the supplied morphism. -/
theorem canonicalNormalizationSectionUpper_retraction
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P)
    (fixed :
      ((canonicalObjectNormalizationUpper P admissible).comp f).comp
          (canonicalObjectNormalizationUpper P admissible) = f) :
    ((canonicalObjectNormalizationUpper P admissible).comp
        (canonicalNormalizationSectionUpper P admissible f)).comp
          (canonicalObjectNormalizationUpper P admissible) = f := by
  rw [canonicalNormalizationSectionUpper_sandwich P admissible f]
  exact fixed

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
