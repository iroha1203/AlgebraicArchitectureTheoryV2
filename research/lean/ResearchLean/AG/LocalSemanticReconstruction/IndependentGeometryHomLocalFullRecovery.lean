import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalTableRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeFullRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationPoints
import Formal.Util.AssertStandardAxioms

/-!
# Both complete Hom reading equivalences on independent objects

The actual raw and realization assemblers discharge the last comparisons in
full table recovery. Equality at every common query identifies the invariant
quotient, yielding the second inverse. Together with native recovery this
gives both original Hom meanings their full reading equivalences.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- The common representative realization reader recovers all candidate directed points of the actual assembler. -/
theorem representativeRealizationRead_assemble {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) (h : Table.{u, v} U .representative)
    (hm : RepresentativeRealization.Maps f h) (hp : RepresentativeRealization.NativePoints G.core H.core h)
    (q : RealizationQuery G.core.object H.core.object .representative) :
    representativeRealizationRead f (RepresentativeRealization.assemble f h hm hp) q = h (.atObjects _ _ (.realization q)) := by
  cases q with
  | representativeSupport W V x y => exact congrArg (fun r => r W V x y) (RepresentativeRealization.read_support f h hm hp)
  | representativeAxis W V x y => exact congrArg (fun r => r W V x y) (RepresentativeRealization.read_axis f h hm hp)
  | representativeObservable W V x y => exact congrArg (fun r => r W V x y) (RepresentativeRealization.read_observable f h hm hp)

/-- The common explicit realization reader recovers all candidate fibers and every actual context-action point. -/
theorem explicitRealizationRead_assemble {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) (h : Table.{u, v} U .explicit)
    (hm : ExplicitRealization.Maps f h) (hp : ExplicitRealization.PointLaws G.core.object H.core.object h)
    (q : RealizationQuery G.core.object H.core.object .explicit) :
    explicitRealizationRead f (ExplicitRealization.assemble f h hm hp) q = h (.atObjects _ _ (.realization q)) := by
  cases q with
  | explicitSupport d W V x y => exact congrArg (fun r => r W V x y) (ExplicitRealization.read_support f h hm hp d)
  | explicitAxis d W V x y => exact congrArg (fun r => r W V x y) (ExplicitRealization.read_axis f h hm hp d)
  | explicitObservable d W V x y => exact congrArg (fun r => r W V x y) (ExplicitRealization.read_observable f h hm hp d)
  | actualSupport W X V Y g x y => exact congrArg (fun r => r W X V Y g x y) (ExplicitRealization.read_actualSupport f h hm hp)
  | actualAxis W X V Y g x y => exact congrArg (fun r => r W X V Y g x y) (ExplicitRealization.read_actualAxis f h hm hp)
  | actualObservable W X V Y g x y => exact congrArg (fun r => r W X V Y g x y) (ExplicitRealization.read_actualObservable f h hm hp)

variable (s t : ObjectData.{u, v} U)

/-- The actual full representative Hom reader restores every original common query of any lawful local quotient. -/
theorem readRepresentative_assemble
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p) :
    readRepresentative (FullRepresentative.assembleHom s t p hp) = (PackageAssembly.retained s.1 t.1 p).table := by
  apply readWith_assemble s t p hp.package hp.coefficient _ _ hp.inactiveObjects
  · intro q
    cases q
  · exact representativeRealizationRead_assemble (GeometryComponents.base s t p hp.package) _
      (GeometryComponents.representative_maps s t p hp.package)
      ((GeometryComponents.representative_points_iff s t p).2 hp.realization)

/-- The actual full explicit Hom reader restores every original raw, core, coefficient, and actual-action query. -/
theorem readExplicit_assemble
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p) :
    readExplicit (FullExplicit.assembleHom s t p hp) = (PackageAssembly.retained s.1 t.1 p).table := by
  apply readWith_assemble s t p hp.package hp.coefficient _ _ hp.inactiveObjects
  · exact ExplicitRaw.read_raw (GeometryComponents.base s t p hp.package)
      (GeometryComponents.coefficientMap s t p hp.coefficient) _ (GeometryComponents.explicitRaw_maps s t p hp.package hp.coefficient)
      ((GeometryComponents.explicitRaw_points_iff s t p).2 hp.raw)
  · exact explicitRealizationRead_assemble (GeometryComponents.base s t p hp.package) _
      (GeometryComponents.explicit_maps s t p hp.package) hp.realization

/-- Full representative assembly followed by local reading restores the entire quotient, including every retained finite family. -/
theorem localRepresentative_read_assemble
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p) :
    localRepresentative (FullRepresentative.assembleHom s t p hp) = p := by
  apply InvariantWitness.point_ext
  intro q
  exact (point_localRepresentative _ q).trans (congrFun (readRepresentative_assemble s t p hp) q)

/-- Full explicit assembly followed by local reading restores the entire original quotient at every common query. -/
theorem localExplicit_read_assemble
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p) :
    localExplicit (FullExplicit.assembleHom s t p hp) = p := by
  apply InvariantWitness.point_ext
  intro q
  exact (point_localExplicit _ q).trans (congrFun (readExplicit_assemble s t p hp) q)

/-- On independent object presentations, the full original representative Hom is equivalent to precisely the lawful common local quotients. -/
def representativeHomReadingEquiv : GeometryTotalHom (assemble s) (assemble t) ≃
    {p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative //
        FullRepresentative.PointLaws s t p} where
  toFun F := ⟨localRepresentative F, localRepresentative_points s t F⟩
  invFun p := FullRepresentative.assembleHom s t p.val p.property
  left_inv := localRepresentative_assemble s t
  right_inv p := Subtype.ext (localRepresentative_read_assemble s t p.val p.property)

/-- On the same independent object presentations, the full original explicit Hom is equivalent to its lawful common local quotients. -/
def explicitHomReadingEquiv : ExplicitExactGeometryHom (assemble s) (assemble t) ≃
    {p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit //
        FullExplicit.PointLaws s t p} where
  toFun F := ⟨localExplicit F, localExplicit_points s t F⟩
  invFun p := FullExplicit.assembleHom s t p.val p.property
  left_inv := localExplicit_assemble s t
  right_inv p := Subtype.ext (localExplicit_read_assemble s t p.val p.property)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
