import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPackageLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeFullAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitFullAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for complete geometry Hom laws

The complete representative and explicit `PointLaws` are decomposed into the
safe three-table formula families for package, coverage, overlap, coefficient,
raw, and realization data.  Source and target object lawfulness is included
through the object-side finite aggregate.  Inactive object rows use an ordinary
finite implication whose guard is equality of supplied object references; the
syntax has no constructor for arbitrary propositions or completed law proofs.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.LawFinite

noncomputable section

universe u v

open IndependentGeometryTableAssembly IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}} {mode : Mode}

abbrev CompleteFormula (mode : Mode) :=
  IndependentFiniteLawFormula.Formula.{u, v, u + 1} U mode

/-- One normalized inactive object row, with both endpoint references visible
as equality tests and the exact Hom cell visible as the conclusion. -/
def inactiveObjectFormula
    (s t : ObjectData.{u, v} U) (_h : Table.{u, v} U mode)
    (A B : ArchitectureObject U) (q : DependentQuery mode A B) :
    CompleteFormula.{u, v} (U := U) mode :=
  .implies
    (.or
      (.notEqual A (IndependentCoreTableAssembly.generatedObject s.1.val.1))
      (.notEqual B (IndependentCoreTableAssembly.generatedObject t.1.val.1)))
    (.hom (.atObjects A B q) false)

def InactiveInstances
    (s t : ObjectData.{u, v} U) (h : Table.{u, v} U mode) : Prop :=
  ∀ A B (q : DependentQuery mode A B),
    (inactiveObjectFormula s t h A B q).evaluate
      (IndependentGeometryPrimitive.flatten s)
      (IndependentGeometryPrimitive.flatten t) h

theorem inactiveObjects_iff_instances
    (s t : ObjectData.{u, v} U) (h : Table.{u, v} U mode) :
    (∀ A B (q : DependentQuery mode A B),
      (A ≠ IndependentCoreTableAssembly.generatedObject s.1.val.1 ∨
        B ≠ IndependentCoreTableAssembly.generatedObject t.1.val.1) →
      h (.atObjects A B q) = false) ↔
      InactiveInstances s t h := by
  rfl

structure RepresentativeInstances
    (s t : ObjectData.{u, v} U)
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .representative) : Prop where
  sourceObject : IndependentGeometryPrimitive.ObjectLawFinite.Instances
    (IndependentGeometryPrimitive.flatten s)
  targetObject : IndependentGeometryPrimitive.ObjectLawFinite.Instances
    (IndependentGeometryPrimitive.flatten t)
  inactiveObjects : InactiveInstances s t (PackageAssembly.retained s.1 t.1 p).table
  package : PackageLawFinite.Instances s t (PackageAssembly.retained s.1 t.1 p).table
  coverage : JointLawFinite.Coverage.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
    (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
    (assemble s).core.algebra.signatureReading.Axis
    (assemble t).core.algebra.signatureReading.Axis
  overlap : JointLawFinite.Overlap.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
  coefficient : JointLawFinite.Coefficient.Instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
    (IndependentRingPrimitive.Carrier.carrier s.2.2.1.val)
    (IndependentRingPrimitive.Carrier.carrier t.2.2.1.val)
  raw : RawLawFinite.Representative.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
    (GeometryComponents.primitiveCoefficientRef s) (GeometryComponents.primitiveCoefficientRef t)
  realization : RealizationLawFinite.Representative.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table

theorem representativePointLaws_iff_instances
    (s t : ObjectData.{u, v} U)
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .representative) :
    FullRepresentative.PointLaws s t p ↔ RepresentativeInstances s t p := by
  let h := (PackageAssembly.retained s.1 t.1 p).table
  constructor
  · intro hp
    exact {
      sourceObject := (IndependentGeometryPrimitive.ObjectLawFinite.lawful_iff_instances
        (IndependentGeometryPrimitive.flatten s)).1
          (IndependentGeometryPrimitive.flatten_lawful s)
      targetObject := (IndependentGeometryPrimitive.ObjectLawFinite.lawful_iff_instances
        (IndependentGeometryPrimitive.flatten t)).1
          (IndependentGeometryPrimitive.flatten_lawful t)
      inactiveObjects := (inactiveObjects_iff_instances s t h).1 hp.inactiveObjects
      package := (PackageLawFinite.pointLaws_iff_instances s t h).1 hp.package
      coverage := (JointLawFinite.Coverage.pointLaws_iff_instances s t h
        (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
        (assemble s).core.algebra.signatureReading.Axis
        (assemble t).core.algebra.signatureReading.Axis).1 hp.coverage
      overlap := (JointLawFinite.Overlap.pointLaws_iff_instances s t h).1 hp.overlap
      coefficient := (JointLawFinite.Coefficient.pointLaws_iff_instances s t h).1 hp.coefficient
      raw := (RawLawFinite.Representative.pointLaws_iff_instances s t
        (GeometryComponents.primitiveCoefficientRef s)
        (GeometryComponents.primitiveCoefficientRef t) h).1 hp.raw
      realization := (RealizationLawFinite.Representative.pointLaws_iff_instances s t h).1
        hp.realization }
  · intro hi
    exact {
      inactiveObjects := (inactiveObjects_iff_instances s t h).2 hi.inactiveObjects
      package := (PackageLawFinite.pointLaws_iff_instances s t h).2 hi.package
      coverage := (JointLawFinite.Coverage.pointLaws_iff_instances s t h
        (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
        (assemble s).core.algebra.signatureReading.Axis
        (assemble t).core.algebra.signatureReading.Axis).2 hi.coverage
      overlap := (JointLawFinite.Overlap.pointLaws_iff_instances s t h).2 hi.overlap
      coefficient := (JointLawFinite.Coefficient.pointLaws_iff_instances s t h).2 hi.coefficient
      raw := (RawLawFinite.Representative.pointLaws_iff_instances s t
        (GeometryComponents.primitiveCoefficientRef s)
        (GeometryComponents.primitiveCoefficientRef t) h).2 hi.raw
      realization := (RealizationLawFinite.Representative.pointLaws_iff_instances s t h).2
        hi.realization }

structure ExplicitInstances
    (s t : ObjectData.{u, v} U)
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .explicit) : Prop where
  sourceObject : IndependentGeometryPrimitive.ObjectLawFinite.Instances
    (IndependentGeometryPrimitive.flatten s)
  targetObject : IndependentGeometryPrimitive.ObjectLawFinite.Instances
    (IndependentGeometryPrimitive.flatten t)
  inactiveObjects : InactiveInstances s t (PackageAssembly.retained s.1 t.1 p).table
  package : PackageLawFinite.Instances s t (PackageAssembly.retained s.1 t.1 p).table
  coverage : JointLawFinite.Coverage.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
    (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
    (assemble s).core.algebra.signatureReading.Axis
    (assemble t).core.algebra.signatureReading.Axis
  overlap : JointLawFinite.Overlap.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
  coefficient : JointLawFinite.Coefficient.Instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
    (IndependentRingPrimitive.Carrier.carrier s.2.2.1.val)
    (IndependentRingPrimitive.Carrier.carrier t.2.2.1.val)
  raw : RawLawFinite.Explicit.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table
  realization : RealizationLawFinite.Explicit.Instances
    (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
    (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (PackageAssembly.retained s.1 t.1 p).table

theorem explicitPointLaws_iff_instances
    (s t : ObjectData.{u, v} U)
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .explicit) :
    FullExplicit.PointLaws s t p ↔ ExplicitInstances s t p := by
  let h := (PackageAssembly.retained s.1 t.1 p).table
  constructor
  · intro hp
    exact {
      sourceObject := (IndependentGeometryPrimitive.ObjectLawFinite.lawful_iff_instances
        (IndependentGeometryPrimitive.flatten s)).1
          (IndependentGeometryPrimitive.flatten_lawful s)
      targetObject := (IndependentGeometryPrimitive.ObjectLawFinite.lawful_iff_instances
        (IndependentGeometryPrimitive.flatten t)).1
          (IndependentGeometryPrimitive.flatten_lawful t)
      inactiveObjects := (inactiveObjects_iff_instances s t h).1 hp.inactiveObjects
      package := (PackageLawFinite.pointLaws_iff_instances s t h).1 hp.package
      coverage := (JointLawFinite.Coverage.pointLaws_iff_instances s t h
        (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
        (assemble s).core.algebra.signatureReading.Axis
        (assemble t).core.algebra.signatureReading.Axis).1 hp.coverage
      overlap := (JointLawFinite.Overlap.pointLaws_iff_instances s t h).1 hp.overlap
      coefficient := (JointLawFinite.Coefficient.pointLaws_iff_instances s t h).1 hp.coefficient
      raw := (RawLawFinite.Explicit.pointLaws_iff_instances s t h).1 hp.raw
      realization := (RealizationLawFinite.Explicit.pointLaws_iff_instances s t h).1
        hp.realization }
  · intro hi
    exact {
      inactiveObjects := (inactiveObjects_iff_instances s t h).2 hi.inactiveObjects
      package := (PackageLawFinite.pointLaws_iff_instances s t h).2 hi.package
      coverage := (JointLawFinite.Coverage.pointLaws_iff_instances s t h
        (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
        (assemble s).core.algebra.signatureReading.Axis
        (assemble t).core.algebra.signatureReading.Axis).2 hi.coverage
      overlap := (JointLawFinite.Overlap.pointLaws_iff_instances s t h).2 hi.overlap
      coefficient := (JointLawFinite.Coefficient.pointLaws_iff_instances s t h).2 hi.coefficient
      raw := (RawLawFinite.Explicit.pointLaws_iff_instances s t h).2 hi.raw
      realization := (RealizationLawFinite.Explicit.pointLaws_iff_instances s t h).2
        hi.realization }

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.LawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.LawFinite
