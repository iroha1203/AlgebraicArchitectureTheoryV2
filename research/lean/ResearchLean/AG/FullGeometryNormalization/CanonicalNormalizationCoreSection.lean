import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationObjectSection

/-!
# Exact-core data for the canonical normalization section

This module lifts the object action from
`CanonicalNormalizationObjectSection` through the configuration and equation
components of an arbitrary exact core endomorphism of an admissible package.
It is the next construction step toward the endpoint group-homomorphic section
required by G-122(D).

## Implementation notes

The equation residual law is reconstructed.  It is not copied through an
ill-typed cast and no completed exact hom is accepted as a section.  The proof
first normalizes the source object, uses the supplied exact endomorphism on
that selected object, identifies its image with the normalization of the raw
section object, and finally removes target normalization by admissibility.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open AtomFoundation DoctrineFiberProduct

/-- An exact endomorphism sends the normalization of an object to the
normalization of its raw section lift. -/
theorem exactEndomorphism_map_normalization_eq_section_normalization
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (f : SignedExactCoreReadingHom P P) (A : ArchitectureObject U) :
    f.objectMap (canonicalObjectNormalization P A) =
      canonicalObjectNormalization P
        (canonicalNormalizationSectionObjectMap P f.atomEquiv A) := by
  unfold canonicalObjectNormalization
  rw [f.object_formation_eq]
  rw [canonicalNormalizationSectionObjectMap_configuration]

/-- The configuration hom underlying the raw section object action. -/
noncomputable def canonicalNormalizationSectionConfigurationHom
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (f : SignedExactCoreReadingHom P P) (A : ArchitectureObject U) :
    ConfigurationHom A.configuration
      (canonicalNormalizationSectionObjectMap P f.atomEquiv A).configuration :=
  AtomConfiguration.transportHom f.atomEquiv A.configuration

/-- The section configuration hom uses exactly the Atom equivalence of the
input exact endomorphism. -/
@[simp]
theorem canonicalNormalizationSectionConfigurationHom_atomMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (f : SignedExactCoreReadingHom P P) (A : ArchitectureObject U) :
    (canonicalNormalizationSectionConfigurationHom P f A).atomMap =
      f.atomEquiv := by
  rfl

/-- Reconstructed equation transport for the raw object-level section lift.

All context, equation-index, role, observable, and violation data are the
actual data of `f`.  Only the object-dependent residual law is reproved by the
two admissibility directions and the selected-object equation above. -/
noncomputable def canonicalNormalizationSectionEquationTransport
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    EquationSystemExactTransport
      P.algebra.equationSystem P.algebra.equationSystem
      f.atomEquiv
      (canonicalNormalizationSectionObjectMap P f.atomEquiv) where
  contextEquivalence := f.equationTransport.contextEquivalence
  equationEquiv := f.equationTransport.equationEquiv
  role_eq := f.equationTransport.role_eq
  observableEquiv := f.equationTransport.observableEquiv
  observable_naturality := f.equationTransport.observable_naturality
  violationCoordinate_eq := f.equationTransport.violationCoordinate_eq
  equationResidual_eq := by
    intro W A i atom
    calc
      f.equationTransport.observableEquiv W
          (P.algebra.equationSystem.equationResidual W A i atom) =
          f.equationTransport.observableEquiv W
            (P.algebra.equationSystem.equationResidual W
              (canonicalObjectNormalization P A) i atom) := by
            rw [admissible.equationResidual_eq]
      _ = P.algebra.equationSystem.equationResidual
            (f.equationTransport.contextEquivalence.functor.obj W)
            (f.objectMap (canonicalObjectNormalization P A))
            (f.equationTransport.equationEquiv i) (f.atomEquiv atom) :=
          f.equationTransport.equationResidual_eq W
            (canonicalObjectNormalization P A) i atom
      _ = P.algebra.equationSystem.equationResidual
            (f.equationTransport.contextEquivalence.functor.obj W)
            (canonicalObjectNormalization P
              (canonicalNormalizationSectionObjectMap P f.atomEquiv A))
            (f.equationTransport.equationEquiv i) (f.atomEquiv atom) := by
          rw [exactEndomorphism_map_normalization_eq_section_normalization]
      _ = P.algebra.equationSystem.equationResidual
            (f.equationTransport.contextEquivalence.functor.obj W)
            (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
            (f.equationTransport.equationEquiv i) (f.atomEquiv atom) :=
          (admissible.equationResidual_eq
            (f.equationTransport.contextEquivalence.functor.obj W)
            (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
            (f.equationTransport.equationEquiv i)
            (f.atomEquiv atom)).symm

/-- The reconstructed transport retains the input equation-index map. -/
@[simp]
theorem canonicalNormalizationSectionEquationTransport_equationMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    (canonicalNormalizationSectionEquationTransport P admissible f).equationMap =
      f.equationTransport.equationMap := by
  rfl

/-- Casting backward and then forward along the same dependent type equality
recovers the original value. -/
private theorem cast_symm_cancel
    {alpha beta : Sort u} (h : alpha = beta) (x : beta) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

/-- Operation action of the raw section lift.

The source operation is normalized, mapped by the actual exact endomorphism,
identified with the normalized raw-section endpoints, and then cast back using
the target admissibility equality. -/
noncomputable def canonicalNormalizationSectionOperationMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P)
    {A B : ArchitectureObject U}
    (operation : P.reading.operationReading.Op A B) :
    P.reading.operationReading.Op
      (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
      (canonicalNormalizationSectionObjectMap P f.atomEquiv B) :=
  cast (admissible.operation_type_eq
      (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
      (canonicalNormalizationSectionObjectMap P f.atomEquiv B)).symm
    (castOperation P.reading.operationReading
      (exactEndomorphism_map_normalization_eq_section_normalization P f A)
      (exactEndomorphism_map_normalization_eq_section_normalization P f B)
      (f.operationMap
        (cast (admissible.operation_type_eq A B) operation)))

/-- The reconstructed operation action is natural for the raw section
configuration homs. -/
theorem canonicalNormalizationSectionOperationMap_naturality
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P)
    {A B : ArchitectureObject U}
    (operation : P.reading.operationReading.Op A B) :
    ConfigurationHom.comp
        (P.reading.operationReading.configurationMap
          (canonicalNormalizationSectionOperationMap P admissible f operation))
        (canonicalNormalizationSectionConfigurationHom P f A) =
      ConfigurationHom.comp
        (canonicalNormalizationSectionConfigurationHom P f B)
        (P.reading.operationReading.configurationMap operation) := by
  apply ConfigurationHom.ext
  have hsource := congrArg ConfigurationHom.atomMap
    (admissible.operation_naturality A B operation)
  have hmiddle := congrArg ConfigurationHom.atomMap
    (f.operation_naturality
      (cast (admissible.operation_type_eq A B) operation))
  have htarget := congrArg ConfigurationHom.atomMap
    (admissible.operation_naturality
      (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
      (canonicalNormalizationSectionObjectMap P f.atomEquiv B)
      (canonicalNormalizationSectionOperationMap P admissible f operation))
  have hcast :
      cast (admissible.operation_type_eq
          (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
          (canonicalNormalizationSectionObjectMap P f.atomEquiv B))
        (canonicalNormalizationSectionOperationMap P admissible f operation) =
      castOperation P.reading.operationReading
        (exactEndomorphism_map_normalization_eq_section_normalization P f A)
        (exactEndomorphism_map_normalization_eq_section_normalization P f B)
        (f.operationMap
          (cast (admissible.operation_type_eq A B) operation)) := by
    exact cast_symm_cancel _ _
  rw [hcast] at htarget
  simp only [ConfigurationHom.comp,
    Function.id_comp, Function.comp_id,
    canonicalObjectNormalizationConfigurationHom_atomMap,
    canonicalNormalizationSectionConfigurationHom_atomMap,
    f.configurationMap_atomMap,
    castOperation_configurationMap_atomMap] at hsource hmiddle htarget ⊢
  exact
    (congrArg (fun map => map ∘ f.atomEquiv) htarget.symm).trans
      (hmiddle.trans (congrArg (fun map => f.atomEquiv ∘ map) hsource))

/-- Invariants transport along the raw section lift by normalizing before the
input exact map and removing normalization afterward. -/
theorem canonicalNormalizationSectionInvariantTransport
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P)
    (i : P.reading.invariantReading.Index) :
    Invariant.TransportedAlong
      (P.reading.invariantReading.invariant i)
      (P.reading.invariantReading.invariant (f.invariantMap i))
      _root_.id
      (canonicalNormalizationSectionObjectMap P f.atomEquiv) := by
  have hsource := admissible.invariant_transport i
  have hmiddle := f.invariant_transport i
  have htarget := admissible.invariant_transport (f.invariantMap i)
  generalize hI : P.reading.invariantReading.invariant i = I at hsource hmiddle ⊢
  generalize hJ : P.reading.invariantReading.invariant (f.invariantMap i) = J at hmiddle htarget ⊢
  cases I with
  | function I =>
      cases J with
      | function J =>
          rcases hsource with ⟨sourceEquiv, hsource⟩
          rcases hmiddle with ⟨middleEquiv, hmiddle⟩
          rcases htarget with ⟨targetEquiv, htarget⟩
          refine ⟨sourceEquiv.trans (middleEquiv.trans targetEquiv.symm), ?_⟩
          intro A
          have hmiddleA :
              middleEquiv
                  (I.evaluate (canonicalObjectNormalization P A)) =
                J.evaluate
                  (f.objectMap (canonicalObjectNormalization P A)) := by
            simpa using hmiddle (canonicalObjectNormalization P A)
          have htargetA :
              targetEquiv
                  (J.evaluate
                    (canonicalNormalizationSectionObjectMap P f.atomEquiv A)) =
                J.evaluate
                  (canonicalObjectNormalization P
                    (canonicalNormalizationSectionObjectMap P f.atomEquiv A)) := by
            simpa using htarget
              (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
          simp only [Equiv.trans_apply]
          rw [hsource A, hmiddleA]
          rw [exactEndomorphism_map_normalization_eq_section_normalization]
          rw [← htargetA]
          simp
      | predicate J =>
          exact False.elim hmiddle
  | predicate I =>
      cases J with
      | function J =>
          exact False.elim hmiddle
      | predicate J =>
          intro A
          calc
            I.holds A ↔ I.holds (canonicalObjectNormalization P A) := hsource A
            _ ↔ J.holds
                (f.objectMap (canonicalObjectNormalization P A)) :=
              hmiddle (canonicalObjectNormalization P A)
            _ ↔ J.holds
                (canonicalObjectNormalization P
                  (canonicalNormalizationSectionObjectMap P f.atomEquiv A)) := by
              rw [exactEndomorphism_map_normalization_eq_section_normalization]
            _ ↔ J.holds
                (canonicalNormalizationSectionObjectMap P f.atomEquiv A) :=
              (htarget
                (canonicalNormalizationSectionObjectMap P f.atomEquiv A)).symm

/-- Signature coordinates of the raw section lift are reconstructed from the
source and target admissibility equations around the input exact map. -/
theorem canonicalNormalizationSectionCoordinateEq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P)
    (A : ArchitectureObject U)
    (i : P.reading.signatureReading.Axis) :
    f.coordinateEquiv i (P.reading.signatureReading.coordinate A i) =
      P.reading.signatureReading.coordinate
        (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
        (f.axisMap i) := by
  calc
    f.coordinateEquiv i (P.reading.signatureReading.coordinate A i) =
        f.coordinateEquiv i
          (P.reading.signatureReading.coordinate
            (canonicalObjectNormalization P A) i) := by
      rw [← admissible.coordinate_eq]
    _ = P.reading.signatureReading.coordinate
          (f.objectMap (canonicalObjectNormalization P A))
          (f.axisMap i) := f.coordinate_eq _ _
    _ = P.reading.signatureReading.coordinate
          (canonicalObjectNormalization P
            (canonicalNormalizationSectionObjectMap P f.atomEquiv A))
          (f.axisMap i) := by
      rw [exactEndomorphism_map_normalization_eq_section_normalization]
    _ = P.reading.signatureReading.coordinate
          (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
          (f.axisMap i) := by
      rw [← admissible.coordinate_eq]

/-- Exact core endomorphism carried by the raw normalization-section action.

The non-object computational data are retained from `f`; the object-dependent
equation, operation, invariant, and coordinate laws are the reconstructed
theorems above. -/
noncomputable def canonicalNormalizationSectionUpper
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    SignedExactCoreReadingHom P P where
  atomEquiv := f.atomEquiv
  extraction_eq := f.extraction_eq
  composition_eq := f.composition_eq
  objectMap := canonicalNormalizationSectionObjectMap P f.atomEquiv
  object_formation_eq := canonicalNormalizationSectionObjectMap_selected P f.atomEquiv
  configurationMap := canonicalNormalizationSectionConfigurationHom P f
  configurationMap_atomMap := canonicalNormalizationSectionConfigurationHom_atomMap P f
  configuration_eq := canonicalNormalizationSectionObjectMap_configuration P f.atomEquiv
  equationTransport :=
    canonicalNormalizationSectionEquationTransport P admissible f
  detectorCode_eq := f.detectorCode_eq
  operationMap := canonicalNormalizationSectionOperationMap P admissible f
  operation_naturality :=
    canonicalNormalizationSectionOperationMap_naturality P admissible f
  invariantMap := f.invariantMap
  invariant_transport :=
    canonicalNormalizationSectionInvariantTransport P admissible f
  axisMap := f.axisMap
  coordinateEquiv := f.coordinateEquiv
  axis_selected_iff := f.axis_selected_iff
  coordinate_eq := canonicalNormalizationSectionCoordinateEq P admissible f

/-- The exact core section retains the input Atom equivalence. -/
@[simp]
theorem canonicalNormalizationSectionUpper_atomEquiv
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    (canonicalNormalizationSectionUpper P admissible f).atomEquiv =
      f.atomEquiv := by
  rfl

/-- The exact core section has the strict raw object action from Cycle 15. -/
@[simp]
theorem canonicalNormalizationSectionUpper_objectMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    (canonicalNormalizationSectionUpper P admissible f).objectMap =
      canonicalNormalizationSectionObjectMap P f.atomEquiv := by
  rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
