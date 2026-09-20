import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomGeometryComponents
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Explicit raw transport on independently assembled geometry objects

Implementation notes: the raw laws refer to the original primitive raw stages.
Reading inverses connect those stages to the native comparison API. Both map
identification premises are discharged by the actual package and coefficient
assemblers, rather than retained as assumptions of the final raw constructor.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

noncomputable section

universe u v

open Site GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U)

/-- Native raw reading recovers the entire original primitive raw object stage. -/
theorem read_raw : IndependentRawCandidate.read (assemble s).site (assemble s).Coefficient (assemble s).raw =
    s.2.2.2.val := by
  letI : CommRing (IndependentGeometryTableAssembly.coefficient s.2.2.1).1 :=
    (IndependentGeometryTableAssembly.coefficient s.2.2.1).2
  exact IndependentRawCandidate.read_assemble _ _ _ s.2.2.2.property.choose s.2.2.2.property.choose_spec

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hl : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (hc : CoefficientPoints s t p)

/-- Both raw comparison premises follow from the actual independently assembled maps. -/
theorem explicitRaw_maps : ExplicitRaw.Maps (G := assemble s) (H := assemble t)
    (base s t p hl) (coefficientMap s t p hc) (PackageAssembly.retained s.1 t.1 p).table where
  context := PackageAssembly.context_backward_point_iff s.1 t.1 p hl
  coefficient x y := by
    change coefficient (PackageAssembly.retained s.1 t.1 p).table (.edge _ _ x y) = true ↔ _
    rw [← read_coefficient s t p hc]
    exact IndependentCarrierGraph.read_edge _ _ _ x y

/-- All raw inverse, label, polynomial, and image rules use the original primitive object stages. -/
abbrev ExplicitRawPoints := ExplicitRaw.PointLaws s.2.2.2.val t.2.2.2.val
  (PackageAssembly.retained s.1 t.1 p).table

/-- Raw reading inverses identify the native comparison predicate with the original stage laws. -/
theorem explicitRaw_points_iff : ExplicitRaw.NativePoints (assemble s) (assemble t)
    (PackageAssembly.retained s.1 t.1 p).table ↔ ExplicitRawPoints s t p := by
  change ExplicitRaw.PointLaws _ _ _ ↔ _
  rw [read_raw s, read_raw t]

/-- Construct the complete raw map on the actual assembled core Hom and directed coefficient map. -/
def explicitRaw (hp : ExplicitRawPoints s t p) :
    RawAmbientRestrictionSystemExactMapAgainst (assemble s).site (assemble t).site
      (coreContextInverse (base s t p hl)) (coefficientMap s t p hc) (assemble s).raw (assemble t).raw :=
  ExplicitRaw.assemble _ _ _ (explicitRaw_maps s t p hl hc) ((explicitRaw_points_iff s t p).2 hp)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents
