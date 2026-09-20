import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeIndices
import Formal.Util.AssertStandardAxioms

/-!
# Recovery of primitive index rows from the assembled core Hom

The native index reader restores the scalar and index projections of an
arbitrary lawful local quotient. These comparisons identify the activation
graphs needed to recover dependent operation, signature, and observable rows.
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

/-- Reading the reconstructed lower source map restores every original carrier candidate. -/
theorem indices_assemble_source : source (indices mode (GeometryComponents.base s t p hp) a) =
    source (PackageAssembly.retained s.1 t.1 p).table :=
  (source_indices mode _ a).trans (PackageAssembly.read_source s.1 t.1 p hp)

/-- The native index reader restores both original lower pointed Atom directions. -/
theorem indices_assemble_pointed : Atom.pointed (indices mode (GeometryComponents.base s t p hp) a) =
    Atom.pointed (PackageAssembly.retained s.1 t.1 p).table :=
  (pointed_indices mode _ a).trans (PackageAssembly.read_pointedAtom s.1 t.1 p hp)

/-- The native index reader restores both original upper Atom directions. -/
theorem indices_assemble_atom : Atom.upper (indices mode (GeometryComponents.base s t p hp) a) =
    Atom.upper (PackageAssembly.retained s.1 t.1 p).table :=
  (atom_indices mode _ a).trans (PackageAssembly.read_atom s.1 t.1 p hp)

/-- Every original object flag is restored from the actual reconstructed object map. -/
theorem indices_assemble_object (A B : ArchitectureObject U) :
    indices mode (GeometryComponents.base s t p hp) a (.object A B) =
      (PackageAssembly.retained s.1 t.1 p).table (.object A B) := by
  apply Bool.eq_iff_iff.mpr
  exact (object_indices_iff mode _ a A B).trans (PackageAssembly.object_point_iff s.1 t.1 p hp A B).symm

/-- The original directed invariant-index rows survive native assembly and reading. -/
theorem indices_assemble_invariant : invariant (indices mode (GeometryComponents.base s t p hp) a) =
    invariant (PackageAssembly.retained s.1 t.1 p).table :=
  (invariant_indices mode _ a).trans (PackageAssembly.read_invariant s.1 t.1 p hp)

/-- The original directed axis rows survive native assembly and reading. -/
theorem indices_assemble_axis : signatureAxis (indices mode (GeometryComponents.base s t p hp) a) =
    signatureAxis (PackageAssembly.retained s.1 t.1 p).table :=
  (axis_indices mode _ a).trans (PackageAssembly.read_axis s.1 t.1 p hp)

/-- Both context directions of the native index reader restore the original active endpoint rows. -/
theorem indices_assemble_context : Context.points (indices mode (GeometryComponents.base s t p hp) a)
    (assemble s).core.object (assemble t).core.object =
      Context.points (PackageAssembly.retained s.1 t.1 p).table (assemble s).core.object (assemble t).core.object :=
  (context_indices mode _ a).trans (PackageAssembly.read_context s.1 t.1 p hp)

/-- Derived family flags are recovered from the original lawful Atom transport comparisons. -/
theorem indices_assemble_family (F F' : AtomFamily U) :
    indices mode (GeometryComponents.base s t p hp) a (.familyTransport F F') =
      (PackageAssembly.retained s.1 t.1 p).table (.familyTransport F F') := by
  classical
  apply Bool.eq_iff_iff.mpr
  change decide (F' = F.transport (GeometryComponents.base s t p hp).upper.atomEquiv) = true ↔ _
  exact decide_eq_true_iff.trans (TransportMatch.family_iff _ hp.atom.upper hp.matching F F').symm

/-- Derived configuration flags recover all original relation and identification comparisons. -/
theorem indices_assemble_configuration (C C' : AtomConfiguration U) :
    indices mode (GeometryComponents.base s t p hp) a (.configurationTransport C C') =
      (PackageAssembly.retained s.1 t.1 p).table (.configurationTransport C C') := by
  classical
  apply Bool.eq_iff_iff.mpr
  change decide (C' = C.transport (GeometryComponents.base s t p hp).upper.atomEquiv) = true ↔ _
  exact decide_eq_true_iff.trans (TransportMatch.configuration_iff _ hp.atom.upper hp.matching C C').symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
