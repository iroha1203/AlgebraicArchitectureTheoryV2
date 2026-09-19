import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPackagePoints
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoverageLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOverlapLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoefficientLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryTableAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Coverage, overlap, and coefficient transport on independently assembled objects

Implementation notes: object stages supply primitive coverage, context, overlap,
and ring tables. Their exact reading inverses identify the point laws used here
with the native comparison predicates. The map-identification premises of the
component APIs are discharged by the actual core-package assembler's point
theorems; they are not inputs of the resulting constructors.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

noncomputable section

universe u v

open Site GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode}
variable (s t : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hl : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)

/-- The reconstructed package Hom has exactly the native core endpoints of the assembled full objects. -/
def base : AtomFoundation.PackageTotalHom (assemble s).core (assemble t).core :=
  PackageAssembly.assemble s.1 t.1 p hl

/-- All nine native coverage predicates read back to the original primitive object table. -/
theorem read_coverage : IndependentCoveragePrimitive.read (assemble s).geometry.requirements = s.2.1.1.val :=
  IndependentCoveragePrimitive.read_assemble _ _ _ s.2.1.1.property

/-- Native overlap reading recovers every original context candidate and matching flag. -/
theorem read_overlap : IndependentOverlapCandidate.read (assemble s).core.contextPreorder
    (assemble s).geometry.overlap = s.2.1.2.val :=
  IndependentOverlapCandidate.read_assemble _ _ s.2.1.2.property.1 s.2.1.2.property.2

/-- Reading the reconstructed context preorder restores all primitive refinement points. -/
theorem read_context : IndependentContextPrimitive.read (assemble s).core.contextPreorder = s.1.val.2.1.val :=
  IndependentContextPrimitive.read_assemble _ s.1.val.2.1.property.choose s.1.val.2.1.property.choose_spec

/-- The coverage comparison API's four map premises follow from the actual package point recovery. -/
theorem coverage_maps : Coverage.Maps (G := assemble s) (H := assemble t) (base s t p hl) (PackageAssembly.retained s.1 t.1 p).table where
  atom := PackageAssembly.atom_point_iff s.1 t.1 p hl
  equation := PackageAssembly.equation_point_iff s.1 t.1 p hl
  axis := PackageAssembly.axis_point_iff s.1 t.1 p hl
  context := PackageAssembly.context_point_iff s.1 t.1 p hl

/-- The overlap comparison API's two map premises also follow from the package point recovery. -/
theorem overlap_maps : Overlap.Maps (G := assemble s) (H := assemble t) (base s t p hl) (PackageAssembly.retained s.1 t.1 p).table where
  forward := PackageAssembly.context_point_iff s.1 t.1 p hl
  backward := PackageAssembly.context_backward_point_iff s.1 t.1 p hl

/-- The nine coverage rules are imposed on the original independent primitive predicate tables. -/
abbrev CoveragePoints := Coverage.PointLaws
  (assemble s).core.equationSystem.Index (assemble t).core.equationSystem.Index
  (assemble s).core.algebra.signatureReading.Axis (assemble t).core.algebra.signatureReading.Axis
  s.2.1.1.val t.2.1.1.val (PackageAssembly.retained s.1 t.1 p).table

/-- Native coverage point rules and independently supplied primitive table rules agree exactly. -/
theorem coverage_points_iff : Coverage.NativePoints (assemble s) (assemble t)
    (PackageAssembly.retained s.1 t.1 p).table ↔ CoveragePoints s t p := by
  change Coverage.PointLaws _ _ _ _ _ _ _ ↔ _
  rw [read_coverage s, read_coverage t]

/-- Derive every original coverage field from independent predicate rules and the assembled core Hom. -/
theorem coverage (hp : CoveragePoints s t p) : CoverageTransport (assemble s) (assemble t) (base s t p hl) :=
  Coverage.assemble _ _ (coverage_maps s t p hl) ((coverage_points_iff s t p).2 hp)

/-- Overlap preservation reads original matching flags and the two target refinement points. -/
abbrev OverlapPoints := Overlap.PointLaws s.2.1.2.val t.2.1.2.val t.1.val.2.1.val
  (PackageAssembly.retained s.1 t.1 p).table

/-- Native overlap point rules are precisely the rules of the original primitive object stages. -/
theorem overlap_points_iff : Overlap.NativePoints (assemble s) (assemble t)
    (PackageAssembly.retained s.1 t.1 p).table ↔ OverlapPoints s t p := by
  change Overlap.PointLaws _ _ _ _ ↔ _
  rw [read_overlap s, read_overlap t, read_context t]

/-- Construct the original overlap comparison from both independent order directions. -/
def overlap (hp : OverlapPoints s t p) : OverlapTransport (assemble s) (assemble t) (base s t p hl) :=
  Overlap.assemble _ _ (overlap_maps s t p hl) ((overlap_points_iff s t p).2 hp)

/-- The original coefficient carrier and operation tables determine the directed Hom point laws. -/
abbrev CoefficientPoints := Coefficient.PointLaws s.2.2.1.val t.2.2.1.val
  s.2.2.1.property.choose t.2.2.1.property.choose (PackageAssembly.retained s.1 t.1 p).table

/-- Construct the complete coefficient ring hom without requiring invertibility. -/
def coefficientMap (hp : CoefficientPoints s t p) : (assemble s).Coefficient →+* (assemble t).Coefficient :=
  Coefficient.assemble s.2.2.1.val t.2.2.1.val s.2.2.1.property.choose t.2.2.1.property.choose
    s.2.2.1.property.choose_spec t.2.2.1.property.choose_spec (PackageAssembly.retained s.1 t.1 p).table hp

/-- Coefficient reading recovers every original candidate carrier graph cell of the reconstructed map. -/
theorem read_coefficient (hp : CoefficientPoints s t p) :
    IndependentCarrierGraph.read _ _ (coefficientMap s t p hp) =
      coefficient (PackageAssembly.retained s.1 t.1 p).table :=
  Coefficient.read_assemble _ _ _ _ _ _ _ hp

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents
