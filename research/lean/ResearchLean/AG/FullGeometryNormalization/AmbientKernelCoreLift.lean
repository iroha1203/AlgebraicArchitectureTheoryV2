import ResearchLean.AG.FullGeometryNormalization.AmbientKernelObjectSwap
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization

/-!
# Exact-core lift of the ambient normalization-kernel swap

The object permutation from `AmbientKernelObjectSwap` fixes configurations and
all package-selected objects.  For a package satisfying canonical object
normalization admissibility, every object-dependent non-object reading therefore
transports across this permutation.  This module packages those transports as an
exact core endomorphism and then as a total-package endomorphism over the identity
point.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open AtomFoundation DoctrineFiberProduct

/-- Canonical normalization cannot distinguish an object from its ambient-kernel
image. -/
theorem ambientKernel_normalization_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (A : ArchitectureObject U) :
    canonicalObjectNormalization P (ambientKernelObjectMap P A) =
      canonicalObjectNormalization P A := by
  exact canonicalObjectNormalization_ambientKernelObjectMap P A

/-- Equation residuals are invariant under the ambient-kernel object swap. -/
theorem ambientKernelEquationResidual_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (W : Site.ContextCategoryObject P.algebra.contextPreorder)
    (A : ArchitectureObject U)
    (i : P.algebra.equationSystem.Index) (atom : U.Atom) :
    P.algebra.equationSystem.equationResidual W A i atom =
      P.algebra.equationSystem.equationResidual W
        (ambientKernelObjectMap P A) i atom := by
  calc
    P.algebra.equationSystem.equationResidual W A i atom =
        P.algebra.equationSystem.equationResidual W
          (canonicalObjectNormalization P A) i atom :=
      admissible.equationResidual_eq W A i atom
    _ = P.algebra.equationSystem.equationResidual W
          (canonicalObjectNormalization P (ambientKernelObjectMap P A)) i atom := by
      rw [ambientKernel_normalization_eq]
    _ = P.algebra.equationSystem.equationResidual W
          (ambientKernelObjectMap P A) i atom :=
      (admissible.equationResidual_eq W (ambientKernelObjectMap P A) i atom).symm

/-- Exact equation transport with identity primitive data and the ambient-kernel
object action. -/
noncomputable def ambientKernelEquationTransport
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    EquationSystemExactTransport
      P.algebra.equationSystem P.algebra.equationSystem
      (Equiv.refl U.Atom) (ambientKernelObjectMap P) where
  contextEquivalence := CategoryTheory.Equivalence.refl
  equationEquiv := Equiv.refl _
  role_eq := by intros; rfl
  observableEquiv := fun _ => RingEquiv.refl _
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by
    intro W A i atom
    exact ambientKernelEquationResidual_eq P admissible W A i atom

/-- The operation type is unchanged by the ambient-kernel object swap. -/
theorem ambientKernelOperationType_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (A B : ArchitectureObject U) :
    P.reading.operationReading.Op A B =
      P.reading.operationReading.Op
        (ambientKernelObjectMap P A) (ambientKernelObjectMap P B) := by
  calc
    P.reading.operationReading.Op A B =
        P.reading.operationReading.Op
          (canonicalObjectNormalization P A)
          (canonicalObjectNormalization P B) :=
      admissible.operation_type_eq A B
    _ = P.reading.operationReading.Op
          (canonicalObjectNormalization P (ambientKernelObjectMap P A))
          (canonicalObjectNormalization P (ambientKernelObjectMap P B)) := by
      rw [ambientKernel_normalization_eq, ambientKernel_normalization_eq]
    _ = P.reading.operationReading.Op
          (ambientKernelObjectMap P A) (ambientKernelObjectMap P B) :=
      (admissible.operation_type_eq
        (ambientKernelObjectMap P A) (ambientKernelObjectMap P B)).symm

/-- The normalized operation endpoint types agree because the ambient swap
fixes both configurations. -/
theorem ambientKernelNormalizedOperationType_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (A B : ArchitectureObject U) :
    P.reading.operationReading.Op
        (canonicalObjectNormalization P A)
        (canonicalObjectNormalization P B) =
      P.reading.operationReading.Op
        (canonicalObjectNormalization P (ambientKernelObjectMap P A))
        (canonicalObjectNormalization P (ambientKernelObjectMap P B)) := by
  rw [ambientKernel_normalization_eq, ambientKernel_normalization_eq]

/-- Operation action obtained by normalizing the source endpoints, identifying
the normalized endpoints, and removing normalization at the target. -/
noncomputable def ambientKernelOperationMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    {A B : ArchitectureObject U}
    (operation : P.reading.operationReading.Op A B) :
    P.reading.operationReading.Op
      (ambientKernelObjectMap P A) (ambientKernelObjectMap P B) :=
  cast (admissible.operation_type_eq
      (ambientKernelObjectMap P A) (ambientKernelObjectMap P B)).symm
    (cast (ambientKernelNormalizedOperationType_eq P A B)
      (cast (admissible.operation_type_eq A B) operation))

/-- The ambient operation action changes only dependent endpoint casts. -/
theorem ambientKernelOperationMap_heq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    {A B : ArchitectureObject U}
    (operation : P.reading.operationReading.Op A B) :
    HEq (ambientKernelOperationMap P admissible operation) operation := by
  unfold ambientKernelOperationMap
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

/-- Normalizing the target of the ambient operation action recovers the
source-normalized operation. -/
theorem ambientKernelOperationMap_normalized
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    {A B : ArchitectureObject U}
    (operation : P.reading.operationReading.Op A B) :
    cast (admissible.operation_type_eq
        (ambientKernelObjectMap P A) (ambientKernelObjectMap P B))
      (ambientKernelOperationMap P admissible operation) =
    cast (admissible.operation_type_eq A B) operation := by
  have hA := ambientKernel_normalization_eq P A
  have hB := ambientKernel_normalization_eq P B
  cases hA
  cases hB
  unfold ambientKernelOperationMap
  simp

/-- Invariants are transported across the ambient-kernel object swap. -/
theorem ambientKernelInvariantTransport
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (i : P.reading.invariantReading.Index) :
    Invariant.TransportedAlong
      (P.reading.invariantReading.invariant i)
      (P.reading.invariantReading.invariant i)
      _root_.id (ambientKernelObjectMap P) := by
  have hsource := admissible.invariant_transport i
  generalize hI : P.reading.invariantReading.invariant i = I at hsource ⊢
  cases I with
  | function I =>
      rcases hsource with ⟨normalizationEquiv, hnormalization⟩
      refine ⟨Equiv.refl _, ?_⟩
      intro A
      have hA := hnormalization A
      have hKA := hnormalization (ambientKernelObjectMap P A)
      simpa [ambientKernel_normalization_eq] using hA.trans hKA.symm
  | predicate I =>
      intro A
      have htarget := hsource (ambientKernelObjectMap P A)
      rw [ambientKernel_normalization_eq] at htarget
      simpa using (hsource A).trans htarget.symm

/-- Signature coordinates are invariant under the ambient-kernel object swap. -/
theorem ambientKernelCoordinate_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (A : ArchitectureObject U)
    (i : P.reading.signatureReading.Axis) :
    P.reading.signatureReading.coordinate A i =
      P.reading.signatureReading.coordinate (ambientKernelObjectMap P A) i := by
  calc
    P.reading.signatureReading.coordinate A i =
        P.reading.signatureReading.coordinate
          (canonicalObjectNormalization P A) i := admissible.coordinate_eq A i
    _ = P.reading.signatureReading.coordinate
          (canonicalObjectNormalization P (ambientKernelObjectMap P A)) i := by
      rw [ambientKernel_normalization_eq]
    _ = P.reading.signatureReading.coordinate
          (ambientKernelObjectMap P A) i :=
      (admissible.coordinate_eq (ambientKernelObjectMap P A) i).symm

/-- Exact core endomorphism whose only nonidentity computational datum is the
ambient-kernel object permutation. -/
noncomputable def ambientKernelUpper
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    SignedExactCoreReadingHom P P where
  atomEquiv := Equiv.refl _
  extraction_eq := by simp
  composition_eq := by intros; simp
  objectMap := ambientKernelObjectMap P
  object_formation_eq := by
    intro C
    simpa using ambientKernelObjectMap_selected P C
  configurationMap := fun A => ConfigurationHom.id A.configuration
  configurationMap_atomMap := by intros; rfl
  configuration_eq := by
    intro A
    rw [ambientKernelObjectMap_configuration]
    exact (AtomFoundation.atomConfiguration_transport_id A.configuration).symm
  equationTransport := ambientKernelEquationTransport P admissible
  detectorCode_eq := by
    intro i
    exact (CircuitDetectorCode.transport_refl _).symm
  operationMap := ambientKernelOperationMap P admissible
  operation_naturality := by
    intro A B operation
    have hsource := congrArg ConfigurationHom.atomMap
      (admissible.operation_naturality A B operation)
    have htarget := congrArg ConfigurationHom.atomMap
      (admissible.operation_naturality
        (ambientKernelObjectMap P A) (ambientKernelObjectMap P B)
        (ambientKernelOperationMap P admissible operation))
    rw [ambientKernelOperationMap_normalized] at htarget
    apply ConfigurationHom.ext
    simp only [ConfigurationHom.comp, Function.id_comp, Function.comp_id,
      canonicalObjectNormalizationConfigurationHom_atomMap] at hsource htarget ⊢
    exact htarget.symm.trans hsource
  invariantMap := _root_.id
  invariant_transport := ambientKernelInvariantTransport P admissible
  axisMap := _root_.id
  coordinateEquiv := fun _ => Equiv.refl _
  axis_selected_iff := fun _ => Iff.rfl
  coordinate_eq := ambientKernelCoordinate_eq P admissible

/-- Total-package ambient-kernel endomorphism over the identity base. -/
noncomputable def ambientKernelTotal
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    PackageTotalHom P P where
  base := ExtInstHom.id (packagePoint P)
  upper := ambientKernelUpper P admissible
  atomEquiv_eq := rfl

/-- The exact core ambient-kernel endomorphism is nonidentity. -/
theorem ambientKernelUpper_ne_refl
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    ambientKernelUpper P admissible ≠ SignedExactCoreReadingHom.refl P := by
  intro h
  have hobject := congrArg SignedExactCoreReadingHom.objectMap h
  exact ambientKernelObjectMap_ne_id P hobject

/-- The total-package ambient-kernel endomorphism is nonidentity. -/
theorem ambientKernelTotal_ne_id
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    ambientKernelTotal P admissible ≠ PackageTotalHom.id P := by
  intro h
  have hupper := congrArg PackageTotalHom.upper h
  exact ambientKernelUpper_ne_refl P admissible hupper

/-- Applying the ambient-kernel exact core endomorphism twice is the identity. -/
theorem ambientKernelUpper_comp_self
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (ambientKernelUpper P admissible).comp (ambientKernelUpper P admissible) =
      SignedExactCoreReadingHom.refl P := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · exact ambientKernelObjectMap_involutive P
  · apply equationSystemExactTransport_hext
    · rfl
    · exact ambientKernelObjectMap_involutive P
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
    exact
      (ambientKernelOperationMap_heq P admissible
        (ambientKernelOperationMap P admissible operation)).trans
      (ambientKernelOperationMap_heq P admissible operation)
  · rfl
  · rfl
  · rfl

/-- Postcomposing canonical normalization by the ambient-kernel endomorphism
does not change canonical normalization. -/
theorem canonicalNormalizationUpper_comp_ambientKernelUpper
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (canonicalObjectNormalizationUpper P admissible).comp
        (ambientKernelUpper P admissible) =
      canonicalObjectNormalizationUpper P admissible := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · funext A
    exact ambientKernelObjectMap_selected P A.configuration
  · apply equationSystemExactTransport_hext
    · rfl
    · funext A
      exact ambientKernelObjectMap_selected P A.configuration
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
    exact ambientKernelOperationMap_heq P admissible
      ((canonicalObjectNormalizationUpper P admissible).operationMap operation)
  · rfl
  · rfl
  · rfl

/-- Precomposing canonical normalization by the ambient-kernel endomorphism
does not change canonical normalization. -/
theorem ambientKernelUpper_comp_canonicalNormalizationUpper
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (ambientKernelUpper P admissible).comp
        (canonicalObjectNormalizationUpper P admissible) =
      canonicalObjectNormalizationUpper P admissible := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · funext A
    exact ambientKernel_normalization_eq P A
  · apply equationSystemExactTransport_hext
    · rfl
    · funext A
      exact ambientKernel_normalization_eq P A
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
    exact
      (cast_heq _ _).trans
        (ambientKernelOperationMap_heq P admissible operation)
        |>.trans (cast_heq _ _).symm
  · rfl
  · rfl
  · rfl

/-- Applying the ambient-kernel total endomorphism twice is the identity. -/
theorem ambientKernelTotal_comp_self
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (ambientKernelTotal P admissible).comp (ambientKernelTotal P admissible) =
      PackageTotalHom.id P := by
  apply PackageTotalHom.ext
  · rfl
  · exact ambientKernelUpper_comp_self P admissible

/-- Canonical normalization absorbs the ambient-kernel total endomorphism on
the right. -/
theorem canonicalNormalizationTotal_comp_ambientKernelTotal
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (canonicalObjectNormalizationTotal P admissible).comp
        (ambientKernelTotal P admissible) =
      canonicalObjectNormalizationTotal P admissible := by
  apply PackageTotalHom.ext
  · rfl
  · exact canonicalNormalizationUpper_comp_ambientKernelUpper P admissible

/-- Canonical normalization absorbs the ambient-kernel total endomorphism on
the left. -/
theorem ambientKernelTotal_comp_canonicalNormalizationTotal
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    (ambientKernelTotal P admissible).comp
        (canonicalObjectNormalizationTotal P admissible) =
      canonicalObjectNormalizationTotal P admissible := by
  apply PackageTotalHom.ext
  · rfl
  · exact ambientKernelUpper_comp_canonicalNormalizationUpper P admissible

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
