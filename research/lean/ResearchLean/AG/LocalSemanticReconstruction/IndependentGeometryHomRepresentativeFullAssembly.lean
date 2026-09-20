import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRawComponents
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationComponents
import Formal.Util.AssertStandardAxioms

/-!
# Full representative geometry Hom assembly from primitive data

Implementation notes: all original G-122 representative Hom fields are
constructed on the same independently assembled objects. The strict raw
equality is derived from primitive points; directed realization components
retain selected-restriction naturality. No explicit-context replacement is
used for this Hom meaning. The whole common reader and inverse laws remain
separate obligations. Inactive object rows are fixed to false because they
do not describe native Hom data; leaving them arbitrary would prevent exact
recovery of the whole table. This normalization is needed for readback, not
for the construction of the active native components.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.FullRepresentative

noncomputable section

universe u v

open GeometryTransport IndependentGeometryTableAssembly GeometryComponents

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)

/-- Primitive conditions for every component of the original complete representative geometry Hom. -/
structure PointLaws : Prop where
  /-- Candidate object rows outside the two primitive-generated endpoints are normalized for exact readback. -/
  inactiveObjects : ∀ A B (q : DependentQuery .representative A B),
    (A ≠ IndependentCoreTableAssembly.generatedObject s.1.val.1 ∨
      B ≠ IndependentCoreTableAssembly.generatedObject t.1.val.1) →
    (PackageAssembly.retained s.1 t.1 p).table (.atObjects A B q) = false
  /-- Primitive core maps, equations, and the invariant quotient. -/
  package : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table
  /-- The original nine coverage implications. -/
  coverage : CoveragePoints s t p
  /-- Both overlap order comparisons. -/
  overlap : OverlapPoints s t p
  /-- Directed coefficient graph and ring-operation points. -/
  coefficient : CoefficientPoints s t p
  /-- Strict raw declarations, optional responses, and coefficient points. -/
  raw : RepresentativeRawPoints s t p
  /-- Directed realization graphs and selected-restriction point squares. -/
  realization : RepresentativePoints s t p

/-- Assemble all fields of the original representative Hom from the independent common point data. -/
def assembleHom (hp : PointLaws s t p) : GeometryTotalHom (assemble s) (assemble t) := by
  let r := representativeRealization s t p hp.package hp.realization
  exact {
    base := base s t p hp.package
    geometry := {
      coverage := GeometryComponents.coverage s t p hp.package hp.coverage
      overlap := GeometryComponents.overlap s t p hp.package hp.overlap
      coefficientHom := coefficientMap s t p hp.coefficient
      raw_eq := representativeRaw s t p hp.package hp.coefficient hp.raw
      supportComp := r.supportComp
      axisComp := r.axisComp
      observableComp := r.observableComp
      supportReads := r.supportReads
      axisReads := r.axisReads
      observableReads := r.observableReads
      support_naturality := r.support_naturality
      axis_naturality := r.axis_naturality
      observable_naturality := r.observable_naturality } }

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.FullRepresentative

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.FullRepresentative
