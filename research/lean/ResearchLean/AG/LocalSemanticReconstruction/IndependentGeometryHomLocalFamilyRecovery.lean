import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalIndexRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeFamilies
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomReadingCongruence
import Formal.Util.AssertStandardAxioms

/-!
# Recovery of the original dependent Hom rows

The common native reader uses its reconstructed index table. Index recovery
and dependent reading congruence compare that table with the original local
table, and the existing component inverse laws then recover every candidate
operation, signature-coordinate, and observable row.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (a : (assemble s).Coefficient →+* (assemble t).Coefficient)

/-- The common operation reader restores every original endpoint and carrier candidate after core assembly. -/
theorem operationRows_assemble : operationRows mode (GeometryComponents.base s t p hp) a =
    Operation.points (PackageAssembly.retained s.1 t.1 p).table := by
  let f := GeometryComponents.base s t p hp
  exact (ReadingCongruence.operation (indices mode f a) (PackageAssembly.retained s.1 t.1 p).table
    (object_rows mode f a) (PackageAssembly.retained s.1 t.1 p).objectRows (indices_assemble_object s t p hp a)
    (assemble s).core.reading.operationReading.Op (assemble t).core.reading.operationReading.Op
    (operationFamily mode f a) (fun A B => f.upper.operationMap (A := A) (B := B))
    (operationFamily_heq mode f a)).trans (PackageAssembly.read_operation s.1 t.1 p hp)

/-- The common signature reader restores both directions at all original axis and coordinate candidates. -/
theorem signatureRows_assemble : signatureRows mode (GeometryComponents.base s t p hp) a =
    Signature.points (PackageAssembly.retained s.1 t.1 p).table := by
  let f := GeometryComponents.base s t p hp
  exact (ReadingCongruence.signature (indices mode f a) (PackageAssembly.retained s.1 t.1 p).table
    (assemble s).core.algebra.signatureReading.Axis (assemble t).core.algebra.signatureReading.Axis
    (axis_rows mode f a) hp.axisRows (indices_assemble_axis s t p hp a)
    (assemble s).core.algebra.signatureReading.Coordinate (assemble t).core.algebra.signatureReading.Coordinate
    (signatureFamily mode f a) f.upper.coordinateEquiv (signatureFamily_heq mode f a)).trans
      (PackageAssembly.read_signatureCoordinates s.1 t.1 p hp)

/-- The common observable reader restores both directions at every original context and carrier candidate. -/
theorem observableRows_assemble : observableRows mode (GeometryComponents.base s t p hp) a =
    Observable.points (PackageAssembly.retained s.1 t.1 p).table (assemble s).core.object (assemble t).core.object := by
  let f := GeometryComponents.base s t p hp
  exact (ReadingCongruence.observable (assemble s).core.contextPreorder (assemble t).core.contextPreorder
    (indices mode f a) (PackageAssembly.retained s.1 t.1 p).table (context_rows mode f a) hp.contextRows
    (indices_assemble_context s t p hp a)
    (fun W => (assemble s).core.equationSystem.Observable ⟨W⟩)
    (fun V => (assemble t).core.equationSystem.Observable ⟨V⟩)
    (observableFamily mode f a) f.upper.equationTransport.observableEquiv
    (observableFamily_heq mode f a)).trans (PackageAssembly.read_observables s.1 t.1 p hp)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
