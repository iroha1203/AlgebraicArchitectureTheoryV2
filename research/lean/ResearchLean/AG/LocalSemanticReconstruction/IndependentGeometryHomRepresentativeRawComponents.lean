import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawComponents
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRawAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Representative raw preservation on independent geometry stages

Implementation notes: coefficient references are read directly from the
primitive carrier and zero responses. Raw and context reading inverses
identify the comparison laws with the original independent stages. The
actual core and coefficient assemblers discharge both map identifications.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

noncomputable section

universe u v

open Site GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U)

/-- Read the primitive coefficient carrier and its selected zero without a native ring input. -/
def primitiveCoefficientRef : IndependentRawCandidate.CoefficientRef.{v} :=
  ⟨IndependentRingPrimitive.Carrier.carrier s.2.2.1.val,
    IndependentRingPrimitive.Carrier.active s.2.2.1.val s.2.2.1.property.choose .zero⟩

/-- Native coefficient assembly preserves precisely the original primitive carrier/zero pair. -/
theorem coefficientRef_assemble : IndependentRawCandidate.coefficientRef (assemble s).Coefficient =
    primitiveCoefficientRef s := rfl

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
variable (hl : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (hc : CoefficientPoints s t p)

/-- Actual inverse-context and coefficient point recovery supplies both representative comparison premises. -/
theorem representativeRaw_maps : RepresentativeRaw.Maps (G := assemble s) (H := assemble t)
    (base s t p hl) (coefficientMap s t p hc) (PackageAssembly.retained s.1 t.1 p).table where
  context := PackageAssembly.context_backward_point_iff s.1 t.1 p hl
  coefficient x y := by
    change coefficient (PackageAssembly.retained s.1 t.1 p).table (.edge _ _ x y) = true ↔ _
    rw [← read_coefficient s t p hc]
    exact IndependentCarrierGraph.read_edge _ _ _ x y

/-- Representative raw laws use original raw/context tables and the original primitive coefficient references. -/
abbrev RepresentativeRawPoints := RepresentativeRaw.PointLaws s.2.2.2.val t.2.2.2.val t.1.val.2.1.val
  (primitiveCoefficientRef s) (primitiveCoefficientRef t) (PackageAssembly.retained s.1 t.1 p).table

/-- Native comparison readings recover exactly the original representative stage conditions. -/
theorem representativeRaw_points_iff : RepresentativeRaw.NativePoints (assemble s) (assemble t)
    (PackageAssembly.retained s.1 t.1 p).table ↔ RepresentativeRawPoints s t p := by
  change RepresentativeRaw.PointLaws _ _ _ _ _ _ ↔ _
  rw [read_raw s, read_raw t, read_context t, coefficientRef_assemble s, coefficientRef_assemble t]

/-- Construct the original strict raw equality on the actually assembled core Hom and coefficient map. -/
theorem representativeRaw (hp : RepresentativeRawPoints s t p) :
    (assemble t).raw = rawTransport (base s t p hl) (coefficientMap s t p hc) :=
  RepresentativeRaw.assemble _ _ _ (representativeRaw_maps s t p hl hc)
    ((representativeRaw_points_iff s t p).2 hp)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents
