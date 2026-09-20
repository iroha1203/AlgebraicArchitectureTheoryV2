import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealizationComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationComponents
import Formal.Util.AssertStandardAxioms

/-!
# Realization composition on the independent common object stages

The original context tables and retained common Hom queries supply both
realization compositions. Comparison with the native assemblers uses the
object reading inverses and discharges the context and Atom map premises.
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

/-- Compose the three directed realization rows on the original independent context stages. -/
def representativeRealizationRows : RealizationQuery (assemble s).core.object (assemble r).core.object .representative → Bool :=
  RepresentativeRealization.composeRealization s.1.val.2.1.val t.1.val.2.1.val
    (PackageAssembly.retained s.1 t.1 p).table ep hp.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q).table

/-- Every independent directed realization row reads the composite of the actual native assemblers. -/
theorem representativeRealizationRows_eq_native : representativeRealizationRows s t r p hp q ep =
    NativeReader.representativeRealizationRead (G := assemble s) (H := assemble r)
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      (RealizationTransportSupply.exactComp (G := assemble s) (H := assemble t) (K := assemble r)
        (GeometryComponents.representativeRealization s t p hp ep)
        (GeometryComponents.representativeRealization t r q hq eq)) := by
  have he := RepresentativeRealization.composeRealization_eq_native
    (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)
    (PackageAssembly.retained s.1 t.1 p).table (GeometryComponents.representative_maps s t p hp)
    ((GeometryComponents.representative_points_iff s t p).2 ep) hp.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q).table (GeometryComponents.representative_maps t r q hq)
    ((GeometryComponents.representative_points_iff t r q).2 eq)
  refine Eq.trans ?_ he
  change RepresentativeRealization.composeRealization s.1.val.2.1.val t.1.val.2.1.val
    (PackageAssembly.retained s.1 t.1 p).table ep hp.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q).table = _
  congr 1
  · exact (GeometryComponents.read_context s).symm
  · exact (GeometryComponents.read_context t).symm

end Representative

section Explicit

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (ep : GeometryComponents.ExplicitPoints s t p)
variable (eq : GeometryComponents.ExplicitPoints t r q)

/-- Compose all inverse fibers and actual-action rows on the retained common primitive tables. -/
def explicitRealizationRows : RealizationQuery (assemble s).core.object (assemble r).core.object .explicit → Bool :=
  ExplicitRealization.composeRealization (PackageAssembly.retained s.1 t.1 p).table ep hp.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q).table eq

/-- Every explicit realization row reads the original composite of the actual native assemblers. -/
theorem explicitRealizationRows_eq_native : explicitRealizationRows s t r p hp q ep eq =
    NativeReader.explicitRealizationRead (G := assemble s) (H := assemble r)
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      (ExplicitRealizationTransportSupply.comp
        (GeometryComponents.explicitRealization s t p hp ep)
        (GeometryComponents.explicitRealization t r q hq eq)) :=
  ExplicitRealization.composeRealization_eq_native
    (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)
    (PackageAssembly.retained s.1 t.1 p).table (GeometryComponents.explicit_maps s t p hp)
    ep hp.contextRows.forward (PackageAssembly.retained t.1 r.1 q).table
    (GeometryComponents.explicit_maps t r q hq) eq

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
