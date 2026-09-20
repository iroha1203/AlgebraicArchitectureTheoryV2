import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeCorePreservation
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeEquationPreservation
import Formal.Util.AssertStandardAxioms

/-!
# Complete native core-package point laws and recovery

Every field of the existing package point predicate is discharged from the
native Hom and its common reader. The invariant quotient supplies its original
existence property while retaining the same table. Native package assembly then
recovers all computational fields by their existing extensionality APIs, including
the dependent equation, operation, and signature families.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U) (mode : Mode)
variable (f : PackageTotalHom (assemble s).core (assemble t).core)
variable (a : (assemble s).Coefficient →+* (assemble t).Coefficient)
variable (raw : RawQuery (assemble s).core.object (assemble t).core.object mode → Bool)
variable (realization : RealizationQuery (assemble s).core.object (assemble t).core.object mode → Bool)

/-- An arbitrary original package Hom satisfies every primitive core-package point law on its common reader. -/
theorem readWith_package : PackageAssembly.PointLaws s.1 t.1 (readWith mode f a raw realization) where
  atom := readWith_atom_rows mode f a raw realization
  extraction := readWith_extraction s t mode f a raw realization
  matching := readWith_matching mode f a raw realization
  generation := readWith_generation s t mode f a raw realization
  equationRows := readWith_equation_rows mode f a raw realization
  contextRows := readWith_context_rows mode f a raw realization
  observableRows := readWith_observable_rows mode f a raw realization
  equationPoints := readWith_equation_preservation s t mode f a raw realization
  detector := readWith_detector_preservation s t mode f a raw realization
  operationRows := readWith_operation_rows mode f a raw realization
  operationPoints := readWith_operation_preservation s t mode f a raw realization
  axisRows := readWith_axis_rows mode f a raw realization
  coordinateRows := readWith_signature_rows mode f a raw realization
  selected := readWith_selected s t mode f a raw realization
  coordinates := readWith_coordinate_preservation s t mode f a raw realization

/-- All package point laws hold on the actual common table retained by the invariant quotient. -/
theorem localWith_package : PackageAssembly.PointLaws s.1 t.1
    (PackageAssembly.retained s.1 t.1 (localWith mode f a raw realization)).table :=
  readWith_package s t mode f a raw realization

/-- Reading through the invariant quotient and assembling restores the entire original native core-package Hom. -/
theorem localWith_package_assemble : PackageAssembly.assemble s.1 t.1 (localWith mode f a raw realization)
    (localWith_package s t mode f a raw realization) = f := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · exact readWith_source_assemble mode f a raw realization
    · exact readWith_pointed_assemble mode f a raw realization
  · apply SignedExactCoreReadingHom.ext
    · exact readWith_atom_assemble mode f a raw realization
    · exact readWith_object_assemble mode f a raw realization
    · apply CompleteGeometryGraphAssembly.PackageGraphCode.equationTransport_heq
        (G := assemble s) (H := assemble t)
        (readWith_atom_assemble mode f a raw realization) (readWith_object_assemble mode f a raw realization)
      · exact readWith_context_assemble mode f a raw realization
      · exact readWith_equation_assemble mode f a raw realization
      · intro W value
        have he := congrArg
          (fun d : (Σ E : ContextCategoryObject (assemble s).core.contextPreorder ≌
              ContextCategoryObject (assemble t).core.contextPreorder,
              ∀ W, (assemble s).core.equationSystem.Observable W ≃+*
                (assemble t).core.equationSystem.Observable (E.functor.obj W)) =>
            (⟨d.1.functor.obj W, d.2 W value⟩ : Σ V, (assemble t).core.equationSystem.Observable V))
          (readWith_contextObservable_eq mode f a raw realization)
        exact (Sigma.mk.inj he).2
    · exact readWith_operation_assemble_heq mode f a raw realization
    · exact heq_of_eq (retainedWith_indexMap mode f a raw realization)
    · exact heq_of_eq (readWith_axis_assemble mode f a raw realization)
    · exact readWith_signature_assemble_heq mode f a raw realization

/-- The representative complete-Hom reader supplies all package laws on its actual local class. -/
theorem localRepresentative_package (F : GeometryTotalHom (assemble s) (assemble t)) :
    PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 (localRepresentative F)).table :=
  localWith_package s t .representative F.base F.geometry.coefficientHom _
    (representativeRealizationRead F.base (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry))

/-- The explicit complete-Hom reader supplies the same package laws with all explicit raw queries retained. -/
theorem localExplicit_package (F : ExplicitExactGeometryHom (assemble s) (assemble t)) :
    PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 (localExplicit F)).table :=
  localWith_package s t .explicit F.base F.coefficientHom (ExplicitRaw.readRaw F.base F.coefficientHom F.raw)
    (explicitRealizationRead F.base F.realization)

/-- Representative package assembly recovers the actual base of the original complete geometry Hom. -/
theorem localRepresentative_package_assemble (F : GeometryTotalHom (assemble s) (assemble t)) :
    GeometryComponents.base s t (localRepresentative F) (localRepresentative_package s t F) = F.base :=
  localWith_package_assemble s t .representative F.base F.geometry.coefficientHom _
    (representativeRealizationRead F.base (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry))

/-- Explicit package assembly recovers the actual base used by its coefficient, raw, and realization data. -/
theorem localExplicit_package_assemble (F : ExplicitExactGeometryHom (assemble s) (assemble t)) :
    GeometryComponents.base s t (localExplicit F) (localExplicit_package s t F) = F.base :=
  localWith_package_assemble s t .explicit F.base F.coefficientHom (ExplicitRaw.readRaw F.base F.coefficientHom F.raw)
    (explicitRealizationRead F.base F.realization)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
