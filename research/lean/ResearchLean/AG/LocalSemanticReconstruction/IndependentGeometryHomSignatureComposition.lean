import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCompositionIndices
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeFamilies
import Formal.Util.AssertStandardAxioms

/-!
# Direct signature-coordinate composition on the common Hom declaration

Implementation notes: the directed axis graph chooses the middle axis.
Coordinate fibers compose their forward and backward point rows there.
Outer candidate axes remain explicit and every other outer carrier gives
false. Native coordinate equivalences occur only in the comparison proof.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)

/-- Direct coordinate composition uses the first primitive axis image and both inverse fiber graphs. -/
def signatureRows : IndependentCandidateIndexedInverseGraph.Table.{u, u, u, u} :=
  IndependentCandidateIndexedInverseGraph.extend (assemble s).core.algebra.signatureReading.Axis
    (assemble r).core.algebra.signatureReading.Axis
    (IndependentIndexedInverseGraph.composeRows
      (Signature.axisPoints (PackageAssembly.retained s.1 t.1 p).table
        (assemble s).core.algebra.signatureReading.Axis (assemble t).core.algebra.signatureReading.Axis) hp.axisRows.2
      (assemble s).core.algebra.signatureReading.Coordinate (assemble t).core.algebra.signatureReading.Coordinate
      (assemble r).core.algebra.signatureReading.Coordinate
      (IndependentCandidateIndexedInverseGraph.project (Signature.points (PackageAssembly.retained s.1 t.1 p).table)
        (assemble s).core.algebra.signatureReading.Axis (assemble t).core.algebra.signatureReading.Axis)
      hp.coordinateRows.selected
      (Signature.axisPoints (PackageAssembly.retained t.1 r.1 q).table
        (assemble t).core.algebra.signatureReading.Axis (assemble r).core.algebra.signatureReading.Axis)
      (IndependentCandidateIndexedInverseGraph.project (Signature.points (PackageAssembly.retained t.1 r.1 q).table)
        (assemble t).core.algebra.signatureReading.Axis (assemble r).core.algebra.signatureReading.Axis)
      hq.coordinateRows.selected)

/-- The coordinate activation graph is the signature-axis role of the directly composed common table. -/
theorem signature_indices (cp : GeometryComponents.CoefficientPoints s t p) :
    IndependentIndexedCarrierGraph.composeIndex
      (Signature.axisPoints (PackageAssembly.retained s.1 t.1 p).table
        (assemble s).core.algebra.signatureReading.Axis (assemble t).core.algebra.signatureReading.Axis) hp.axisRows.2
      (Signature.axisPoints (PackageAssembly.retained t.1 r.1 q).table
        (assemble t).core.algebra.signatureReading.Axis (assemble r).core.algebra.signatureReading.Axis) =
      Signature.axisPoints (indices s t r p hp q hq cp)
        (assemble s).core.algebra.signatureReading.Axis (assemble r).core.algebra.signatureReading.Axis := by
  funext i l
  exact (IndependentCarrierGraph.compose_edge _ _ _ _ hp.axisRows
    (signatureAxis (PackageAssembly.retained t.1 r.1 q).table) i l).symm

/-- Every candidate coordinate point in direct composition equals the common native reader of the original composite. -/
theorem signatureRows_eq_native (cp : GeometryComponents.CoefficientPoints s t p)
    (cq : GeometryComponents.CoefficientPoints t r q) : signatureRows s t r p hp q hq =
    NativeReader.signatureRows mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) := by
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let k := (PackageAssembly.retained t.1 r.1 q).table
  let I := (assemble s).core.algebra.signatureReading.Axis
  let J := (assemble t).core.algebra.signatureReading.Axis
  let K := (assemble r).core.algebra.signatureReading.Axis
  let S := (assemble s).core.algebra.signatureReading.Coordinate
  let M := (assemble t).core.algebra.signatureReading.Coordinate
  let T := (assemble r).core.algebra.signatureReading.Coordinate
  let pi := Signature.axisPoints h I J
  let qi := Signature.axisPoints k J K
  let ht := IndependentCandidateIndexedInverseGraph.project (Signature.points h) I J
  let kt := IndependentCandidateIndexedInverseGraph.project (Signature.points k) J K
  let ci := IndependentIndexedCarrierGraph.composeIndex pi hp.axisRows.2 qi
  let hi := IndependentIndexedCarrierGraph.composeIndex_total pi hp.axisRows.2 qi hq.axisRows.2
  let ct := IndependentIndexedInverseGraph.composeRows pi hp.axisRows.2 S M T ht hp.coordinateRows.selected qi kt hq.coordinateRows.selected
  let hc := IndependentIndexedInverseGraph.composeRows_isLawful pi hp.axisRows.2 S M T ht hp.coordinateRows.selected qi kt hq.coordinateRows.selected
  let f := PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)
  let a := (GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)
  have he : ci = Signature.axisPoints (NativeReader.indices mode f a) I K :=
    (signature_indices s t r p hp q hq cp).trans
      (congrArg (fun h => Signature.axisPoints h I K) (indices_eq_native s t r p hp q hq cp cq))
  have hf : HEq (IndependentIndexedInverseGraph.assemble ci hi S T ct hc) (NativeReader.signatureFamily mode f a) :=
    (IndependentIndexedInverseGraph.assemble_composeRows_heq pi hp.axisRows.2 S M T ht hp.coordinateRows.selected
      qi kt hq.coordinateRows.selected hq.axisRows.2).trans (NativeReader.signatureFamily_heq mode f a).symm
  have hr := (IndependentIndexedInverseGraph.read_assemble ci hi S T ct hc).symm.trans
    (IndependentIndexedInverseGraph.read_eq_of_heq ci (Signature.axisPoints (NativeReader.indices mode f a) I K)
      hi (NativeReader.axis_rows mode f a).2 he S T _ _ hf)
  exact (congrArg (IndependentCandidateIndexedInverseGraph.extend I K) hr).trans
    (IndependentCandidateIndexedInverseGraph.extend_read I K (Signature.axisPoints (NativeReader.indices mode f a) I K)
      (NativeReader.axis_rows mode f a).2 S T (NativeReader.signatureFamily mode f a))

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
