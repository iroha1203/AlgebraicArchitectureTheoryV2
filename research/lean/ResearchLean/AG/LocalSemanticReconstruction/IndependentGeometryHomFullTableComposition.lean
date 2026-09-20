import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreRawComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationCompositionRows
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRealizationReadings
import Formal.Util.AssertStandardAxioms

/-!
# All common Hom queries under primitive composition

Both modes fill the closed query declaration from primitive composition.
The explicit mode includes raw coordinates, relations, local data, both fiber
directions, and actual context actions. The representative mode retains its
directed realization maps. Native composites appear in comparison and law
proofs after construction of the complete point tables.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)

section Representative

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (ep : GeometryComponents.RepresentativePoints s t p)
variable (eq : GeometryComponents.RepresentativePoints t r q)
variable (cp : GeometryComponents.CoefficientPoints s t p)
variable (cq : GeometryComponents.CoefficientPoints t r q)

/-- Direct primitive composition fills every representative common Hom query. -/
def composeRepresentative : Table.{u, v} U .representative :=
  composeWith s t r p hp q hq (fun a => nomatch a) (representativeRealizationRows s t r p hp q ep) cp

include eq cq in
/-- The entire representative point table reads the original core, coefficient, and realization composites. -/
theorem composeRepresentative_eq_native : composeRepresentative s t r p hp q hq ep cp =
    NativeReader.readWith .representative
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
      (fun a => nomatch a)
      (NativeReader.representativeRealizationRead (G := assemble s) (H := assemble r)
        (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
        (RealizationTransportSupply.exactComp (G := assemble s) (H := assemble t) (K := assemble r)
          (GeometryComponents.representativeRealization s t p hp ep)
          (GeometryComponents.representativeRealization t r q hq eq))) := by
  change composeWith s t r p hp q hq _ _ cp = _
  rw [composeWith_eq_native s t r p hp q hq _ _ cp cq,
    representativeRealizationRows_eq_native s t r p hp q hq ep eq]

include eq cq in
/-- Direct representative composition preserves the original primitive realization and restriction laws. -/
theorem composeRepresentative_realization_points : RepresentativeRealization.PointLaws
    s.1.val.2.1.val r.1.val.2.1.val (composeRepresentative s t r p hp q hq ep cp) := by
  have he := NativeReader.readWith_representativeRealization_points
    (G := assemble s) (H := assemble r)
    (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
    ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
    (fun a => nomatch a)
    (RealizationTransportSupply.exactComp (G := assemble s) (H := assemble t) (K := assemble r)
      (GeometryComponents.representativeRealization s t p hp ep)
      (GeometryComponents.representativeRealization t r q hq eq))
  change RepresentativeRealization.PointLaws _ _ _ at he
  rw [GeometryComponents.read_context s, GeometryComponents.read_context r] at he
  rw [composeRepresentative_eq_native s t r p hp q hq ep eq cp cq]
  exact he

end Representative

section Explicit

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (rp : GeometryComponents.ExplicitRawPoints s t p) (rq : GeometryComponents.ExplicitRawPoints t r q)
variable (ep : GeometryComponents.ExplicitPoints s t p) (eq : GeometryComponents.ExplicitPoints t r q)
variable (cp : GeometryComponents.CoefficientPoints s t p) (cq : GeometryComponents.CoefficientPoints t r q)

/-- Direct primitive composition fills every explicit common Hom query, including actual actions. -/
def composeExplicit : Table.{u, v} U .explicit :=
  composeExplicitWith s t r p hp q hq rp rq (explicitRealizationRows s t r p hp q ep eq) cp

/-- The complete explicit table reads the original core, coefficient, raw, and realization composites. -/
theorem composeExplicit_eq_native : composeExplicit s t r p hp q hq rp rq ep eq cp =
    NativeReader.readWith .explicit
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
      (ExplicitRaw.readRaw
        (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
        ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
        ((GeometryComponents.explicitRaw s t p hp cp rp).trans (GeometryComponents.explicitRaw t r q hq cq rq)))
      (NativeReader.explicitRealizationRead (G := assemble s) (H := assemble r)
        (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
        (ExplicitRealizationTransportSupply.comp
          (GeometryComponents.explicitRealization s t p hp ep)
          (GeometryComponents.explicitRealization t r q hq eq))) := by
  change composeExplicitWith s t r p hp q hq rp rq _ cp = _
  rw [composeExplicitWith_eq_native s t r p hp q hq rp rq _ cp cq,
    explicitRealizationRows_eq_native s t r p hp q hq ep eq]

include cq in
/-- Complete primitive explicit composition preserves the original realization and actual-action laws. -/
theorem composeExplicit_realization_points : ExplicitRealization.PointLaws
    (assemble s).core.object (assemble r).core.object (composeExplicit s t r p hp q hq rp rq ep eq cp) := by
  rw [composeExplicit_eq_native s t r p hp q hq rp rq ep eq cp cq]
  exact NativeReader.readWith_explicitRealization_points
    (G := assemble s) (H := assemble r)
    (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
    ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) _
    (ExplicitRealizationTransportSupply.comp
      (GeometryComponents.explicitRealization s t p hp ep)
      (GeometryComponents.explicitRealization t r q hq eq))

include cq in
/-- The same complete explicit table also preserves all primitive raw inverse and polynomial laws. -/
theorem composeExplicit_raw_points : ExplicitRaw.PointLaws s.2.2.2.val r.2.2.2.val
    (composeExplicit s t r p hp q hq rp rq ep eq cp) :=
  composeExplicitWith_raw_points s t r p hp q hq rp rq (explicitRealizationRows s t r p hp q ep eq) cp cq

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
