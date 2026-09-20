import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawComponents
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRawReadings
import Formal.Util.AssertStandardAxioms

/-!
# Primitive raw composition on the independently assembled common Hom table

Implementation notes: the raw composition uses the original independent object
stages and retained common Hom points. Reading inverses discharge the stage
comparison with native raw maps. The entire core and raw table is then compared
with native composition, retaining an explicit realization-point argument for
the remaining realization composition.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (rp : GeometryComponents.ExplicitRawPoints s t p) (rq : GeometryComponents.ExplicitRawPoints t r q)

/-- Direct raw composition on the original object stages and the retained common Hom points. -/
def explicitRawRows : RawQuery (assemble s).core.object (assemble r).core.object .explicit → Bool :=
  ExplicitRaw.composeRaw s.2.2.2.val t.2.2.2.val r.2.2.2.val
    (PackageAssembly.retained s.1 t.1 p).table rp (PackageAssembly.retained t.1 r.1 q).table
    hq.contextRows.backward rq

/-- Primitive raw composition agrees with the native raw composite from the actual common assemblers. -/
theorem explicitRawRows_eq_native (cp : GeometryComponents.CoefficientPoints s t p)
    (cq : GeometryComponents.CoefficientPoints t r q) : explicitRawRows s t r p q hq rp rq =
    ExplicitRaw.readRaw
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
      ((GeometryComponents.explicitRaw s t p hp cp rp).trans (GeometryComponents.explicitRaw t r q hq cq rq)) := by
  have he := ExplicitRaw.composeRaw_eq_native
    (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)
    (GeometryComponents.coefficientMap s t p cp) (GeometryComponents.coefficientMap t r q cq)
    (PackageAssembly.retained s.1 t.1 p).table (GeometryComponents.explicitRaw_maps s t p hp cp)
    ((GeometryComponents.explicitRaw_points_iff s t p).2 rp)
    (PackageAssembly.retained t.1 r.1 q).table (GeometryComponents.explicitRaw_maps t r q hq cq)
    ((GeometryComponents.explicitRaw_points_iff t r q).2 rq) hq.contextRows.backward
  refine Eq.trans ?_ he
  change ExplicitRaw.composeRaw s.2.2.2.val t.2.2.2.val r.2.2.2.val
    (PackageAssembly.retained s.1 t.1 p).table rp (PackageAssembly.retained t.1 r.1 q).table
    hq.contextRows.backward rq = _
  congr 1
  · exact (GeometryComponents.read_raw s).symm
  · exact (GeometryComponents.read_raw t).symm
  · exact (GeometryComponents.read_raw r).symm

variable (realization : RealizationQuery (assemble s).core.object (assemble r).core.object .explicit → Bool)
variable (cp : GeometryComponents.CoefficientPoints s t p)

/-- Fill every core and raw role by primitive composition, with the specified realization points. -/
def composeExplicitWith : Table.{u, v} U .explicit :=
  composeWith s t r p hp q hq (explicitRawRows s t r p q hq rp rq) realization cp

/-- The complete core/raw point table reads the native core, coefficient, and raw composites. -/
theorem composeExplicitWith_eq_native (cq : GeometryComponents.CoefficientPoints t r q) :
    composeExplicitWith s t r p hp q hq rp rq realization cp =
      NativeReader.readWith .explicit
        (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
        ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
        (ExplicitRaw.readRaw
          (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
          ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
          ((GeometryComponents.explicitRaw s t p hp cp rp).trans (GeometryComponents.explicitRaw t r q hq cq rq)))
        realization := by
  exact (composeWith_eq_native s t r p hp q hq (explicitRawRows s t r p q hq rp rq) realization cp cq).trans
    (congrArg (fun raw => NativeReader.readWith .explicit
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) raw realization)
      (explicitRawRows_eq_native s t r p hp q hq rp rq cp cq))

/-- Direct core/raw composition preserves all original raw inverse, label, polynomial, and restriction point laws. -/
theorem composeExplicitWith_raw_points (cq : GeometryComponents.CoefficientPoints t r q) :
    ExplicitRaw.PointLaws s.2.2.2.val r.2.2.2.val
      (composeExplicitWith s t r p hp q hq rp rq realization cp) := by
  have he := NativeReader.readWith_explicitRaw_points
    (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
    ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp))
    realization ((GeometryComponents.explicitRaw s t p hp cp rp).trans (GeometryComponents.explicitRaw t r q hq cq rq))
  change ExplicitRaw.PointLaws _ _ _ at he
  rw [GeometryComponents.read_raw s, GeometryComponents.read_raw r] at he
  rw [composeExplicitWith_eq_native s t r p hp q hq rp rq realization cp cq]
  exact he

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
